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
lean_object* l_Lean_privateToUserName_x3f(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
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
lean_object* l_Lean_Environment_getNamespaces(lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* l_Lean_Data_Trie_findPrefix___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_433_; lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_497_; 
v___x_433_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_427_, v_a_428_);
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_497_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_497_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_497_;
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
lean_object* v_val_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_492_; 
v_val_438_ = lean_ctor_get(v_a_434_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v_a_434_);
if (v_isSharedCheck_492_ == 0)
{
v___x_440_ = v_a_434_;
v_isShared_441_ = v_isSharedCheck_492_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_val_438_);
lean_dec(v_a_434_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_492_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
uint8_t v___x_442_; uint8_t v___x_443_; 
v___x_442_ = l_Lean_Name_isPrefixOf(v_ns_424_, v_val_438_);
v___x_443_ = lean_bool_not(v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_box(0);
v___x_445_ = l_Lean_Name_replacePrefix(v_val_438_, v_ns_424_, v___x_444_);
if (v_danglingDot_426_ == 0)
{
if (lean_obj_tag(v_id_425_) == 1)
{
if (lean_obj_tag(v___x_445_) == 1)
{
lean_object* v_pre_446_; lean_object* v_str_447_; lean_object* v_pre_448_; lean_object* v_str_449_; uint8_t v___x_450_; 
v_pre_446_ = lean_ctor_get(v_id_425_, 0);
v_str_447_ = lean_ctor_get(v_id_425_, 1);
v_pre_448_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_pre_448_);
v_str_449_ = lean_ctor_get(v___x_445_, 1);
lean_inc_ref(v_str_449_);
v___x_450_ = lean_name_eq(v_pre_446_, v_pre_448_);
lean_dec(v_pre_448_);
if (v___x_450_ == 0)
{
uint8_t v___x_451_; 
v___x_451_ = l_Lean_Name_isAnonymous(v_pre_446_);
if (v___x_451_ == 0)
{
lean_dec_ref(v_str_449_);
lean_dec_ref_known(v___x_445_, 2);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
goto v___jp_430_;
}
else
{
uint8_t v___x_452_; 
v___x_452_ = l_String_charactersIn(v_str_447_, v_str_449_);
lean_dec_ref(v_str_449_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_455_; 
lean_dec_ref_known(v___x_445_, 2);
lean_del_object(v___x_440_);
v___x_453_ = lean_box(0);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_453_);
v___x_455_ = v___x_436_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
else
{
lean_object* v___x_458_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_445_);
v___x_458_ = v___x_440_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_445_);
v___x_458_ = v_reuseFailAlloc_462_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_460_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_458_);
v___x_460_ = v___x_436_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
else
{
uint8_t v___x_463_; 
lean_dec_ref_known(v___x_445_, 2);
v___x_463_ = l_String_charactersIn(v_str_447_, v_str_449_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_466_; 
lean_dec_ref(v_str_449_);
lean_del_object(v___x_440_);
v___x_464_ = lean_box(0);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_464_);
v___x_466_ = v___x_436_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
else
{
lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_468_ = l_Lean_Name_str___override(v___x_444_, v_str_449_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_468_);
v___x_470_ = v___x_440_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_474_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___x_472_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_470_);
v___x_472_ = v___x_436_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
else
{
lean_dec(v___x_445_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
goto v___jp_430_;
}
}
else
{
lean_dec(v___x_445_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
goto v___jp_430_;
}
}
else
{
uint8_t v___x_475_; 
v___x_475_ = l_Lean_Name_isPrefixOf(v_id_425_, v___x_445_);
if (v___x_475_ == 0)
{
lean_dec(v___x_445_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
goto v___jp_430_;
}
else
{
lean_object* v___x_476_; uint8_t v___y_478_; uint8_t v___x_485_; 
v___x_476_ = l_Lean_Name_replacePrefix(v___x_445_, v_id_425_, v___x_444_);
v___x_485_ = l_Lean_Name_isAtomic(v___x_476_);
if (v___x_485_ == 0)
{
v___y_478_ = v___x_485_;
goto v___jp_477_;
}
else
{
uint8_t v___x_486_; uint8_t v___x_487_; 
v___x_486_ = l_Lean_Name_isAnonymous(v___x_476_);
v___x_487_ = lean_bool_not(v___x_486_);
v___y_478_ = v___x_487_;
goto v___jp_477_;
}
v___jp_477_:
{
if (v___y_478_ == 0)
{
lean_dec(v___x_476_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
goto v___jp_430_;
}
else
{
lean_object* v___x_480_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_476_);
v___x_480_ = v___x_440_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_476_);
v___x_480_ = v_reuseFailAlloc_484_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_482_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_480_);
v___x_482_ = v___x_436_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_488_; lean_object* v___x_490_; 
lean_del_object(v___x_440_);
lean_dec(v_val_438_);
v___x_488_ = lean_box(0);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_488_);
v___x_490_ = v___x_436_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
else
{
lean_object* v___x_493_; lean_object* v___x_495_; 
lean_dec(v_a_434_);
v___x_493_ = lean_box(0);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_493_);
v___x_495_ = v___x_436_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg___boxed(lean_object* v_ns_498_, lean_object* v_id_499_, lean_object* v_danglingDot_500_, lean_object* v_declName_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
uint8_t v_danglingDot_boxed_504_; lean_object* v_res_505_; 
v_danglingDot_boxed_504_ = lean_unbox(v_danglingDot_500_);
v_res_505_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_498_, v_id_499_, v_danglingDot_boxed_504_, v_declName_501_, v_a_502_);
lean_dec(v_a_502_);
lean_dec(v_id_499_);
lean_dec(v_ns_498_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f(lean_object* v_ns_506_, lean_object* v_id_507_, uint8_t v_danglingDot_508_, lean_object* v_declName_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_506_, v_id_507_, v_danglingDot_508_, v_declName_509_, v_a_513_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___boxed(lean_object* v_ns_516_, lean_object* v_id_517_, lean_object* v_danglingDot_518_, lean_object* v_declName_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
uint8_t v_danglingDot_boxed_525_; lean_object* v_res_526_; 
v_danglingDot_boxed_525_ = lean_unbox(v_danglingDot_518_);
v_res_526_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f(v_ns_516_, v_id_517_, v_danglingDot_boxed_525_, v_declName_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
lean_dec(v_id_517_);
lean_dec(v_ns_516_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__0(lean_object* v___y_527_, lean_object* v_toPure_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v_a_529_);
lean_ctor_set(v___x_530_, 1, v___y_527_);
v___x_531_ = lean_apply_2(v_toPure_528_, lean_box(0), v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__1(lean_object* v_f_532_, lean_object* v_decl_533_, lean_object* v_ci_534_, lean_object* v_toPure_535_, lean_object* v_toBind_536_, lean_object* v_____r_537_, lean_object* v___y_538_){
_start:
{
lean_object* v___x_539_; lean_object* v___f_540_; lean_object* v___x_541_; 
v___x_539_ = lean_apply_2(v_f_532_, v_decl_533_, v_ci_534_);
v___f_540_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_540_, 0, v___y_538_);
lean_closure_set(v___f_540_, 1, v_toPure_535_);
v___x_541_ = lean_apply_4(v_toBind_536_, lean_box(0), lean_box(0), v___x_539_, v___f_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__2(lean_object* v___f_542_, lean_object* v_____x_543_){
_start:
{
lean_object* v_fst_544_; lean_object* v_snd_545_; lean_object* v___x_546_; 
v_fst_544_ = lean_ctor_get(v_____x_543_, 0);
lean_inc(v_fst_544_);
v_snd_545_ = lean_ctor_get(v_____x_543_, 1);
lean_inc(v_snd_545_);
lean_dec_ref(v_____x_543_);
v___x_546_ = lean_apply_2(v___f_542_, v_fst_544_, v_snd_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3(lean_object* v_toPure_550_, lean_object* v_toBind_551_, lean_object* v___f_552_, lean_object* v_____x_553_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3___closed__0));
v___x_555_ = lean_apply_2(v_toPure_550_, lean_box(0), v___x_554_);
v___x_556_ = lean_apply_4(v_toBind_551_, lean_box(0), lean_box(0), v___x_555_, v___f_552_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3___boxed(lean_object* v_toPure_557_, lean_object* v_toBind_558_, lean_object* v___f_559_, lean_object* v_____x_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3(v_toPure_557_, v_toBind_558_, v___f_559_, v_____x_560_);
lean_dec_ref(v_____x_560_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__4(lean_object* v_snd_562_, lean_object* v_toPure_563_, lean_object* v_a_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v_a_564_);
lean_ctor_set(v___x_565_, 1, v_snd_562_);
v___x_566_ = lean_apply_2(v_toPure_563_, lean_box(0), v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__5(lean_object* v___f_567_, lean_object* v_toPure_568_, lean_object* v_toBind_569_, lean_object* v_inst_570_, lean_object* v___f_571_, lean_object* v_____x_572_){
_start:
{
lean_object* v_fst_573_; lean_object* v_snd_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v_fst_573_ = lean_ctor_get(v_____x_572_, 0);
lean_inc(v_fst_573_);
v_snd_574_ = lean_ctor_get(v_____x_572_, 1);
lean_inc(v_snd_574_);
lean_dec_ref(v_____x_572_);
v___x_575_ = lean_unsigned_to_nat(10000u);
v___x_576_ = lean_nat_dec_le(v___x_575_, v_fst_573_);
lean_dec(v_fst_573_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec(v___f_571_);
lean_dec(v_inst_570_);
lean_dec(v_toBind_569_);
lean_dec(v_toPure_568_);
v___x_577_ = lean_box(0);
v___x_578_ = lean_apply_2(v___f_567_, v___x_577_, v_snd_574_);
return v___x_578_;
}
else
{
lean_object* v___f_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v___f_567_);
v___f_579_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__4), 3, 2);
lean_closure_set(v___f_579_, 0, v_snd_574_);
lean_closure_set(v___f_579_, 1, v_toPure_568_);
lean_inc(v_toBind_569_);
v___x_580_ = lean_apply_4(v_toBind_569_, lean_box(0), lean_box(0), v_inst_570_, v___f_579_);
v___x_581_ = lean_apply_4(v_toBind_569_, lean_box(0), lean_box(0), v___x_580_, v___f_571_);
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__6(lean_object* v_toPure_582_, lean_object* v_toBind_583_, lean_object* v___f_584_, lean_object* v_____x_585_){
_start:
{
lean_object* v_snd_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_595_; 
v_snd_586_ = lean_ctor_get(v_____x_585_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v_____x_585_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; 
v_unused_596_ = lean_ctor_get(v_____x_585_, 0);
lean_dec(v_unused_596_);
v___x_588_ = v_____x_585_;
v_isShared_589_ = v_isSharedCheck_595_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_snd_586_);
lean_dec(v_____x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_595_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
lean_inc(v_snd_586_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v_snd_586_);
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_snd_586_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_snd_586_);
v___x_591_ = v_reuseFailAlloc_594_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_apply_2(v_toPure_582_, lean_box(0), v___x_591_);
v___x_593_ = lean_apply_4(v_toBind_583_, lean_box(0), lean_box(0), v___x_592_, v___f_584_);
return v___x_593_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__7(lean_object* v_f_597_, lean_object* v_toPure_598_, lean_object* v_toBind_599_, lean_object* v_inst_600_, lean_object* v_decl_601_, lean_object* v_ci_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___f_604_; lean_object* v___f_605_; lean_object* v___f_606_; lean_object* v___f_607_; lean_object* v___f_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
lean_inc_n(v_toBind_599_, 4);
lean_inc_n(v_toPure_598_, 4);
v___f_604_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__1), 7, 5);
lean_closure_set(v___f_604_, 0, v_f_597_);
lean_closure_set(v___f_604_, 1, v_decl_601_);
lean_closure_set(v___f_604_, 2, v_ci_602_);
lean_closure_set(v___f_604_, 3, v_toPure_598_);
lean_closure_set(v___f_604_, 4, v_toBind_599_);
lean_inc_ref(v___f_604_);
v___f_605_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__2), 2, 1);
lean_closure_set(v___f_605_, 0, v___f_604_);
v___f_606_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_606_, 0, v_toPure_598_);
lean_closure_set(v___f_606_, 1, v_toBind_599_);
lean_closure_set(v___f_606_, 2, v___f_605_);
v___f_607_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__5), 6, 5);
lean_closure_set(v___f_607_, 0, v___f_604_);
lean_closure_set(v___f_607_, 1, v_toPure_598_);
lean_closure_set(v___f_607_, 2, v_toBind_599_);
lean_closure_set(v___f_607_, 3, v_inst_600_);
lean_closure_set(v___f_607_, 4, v___f_606_);
v___f_608_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__6), 4, 3);
lean_closure_set(v___f_608_, 0, v_toPure_598_);
lean_closure_set(v___f_608_, 1, v_toBind_599_);
lean_closure_set(v___f_608_, 2, v___f_607_);
v___x_609_ = lean_box(0);
v___x_610_ = lean_unsigned_to_nat(1u);
v___x_611_ = lean_nat_add(v___y_603_, v___x_610_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_609_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = lean_apply_2(v_toPure_598_, lean_box(0), v___x_612_);
v___x_614_ = lean_apply_4(v_toBind_599_, lean_box(0), lean_box(0), v___x_613_, v___f_608_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__7___boxed(lean_object* v_f_615_, lean_object* v_toPure_616_, lean_object* v_toBind_617_, lean_object* v_inst_618_, lean_object* v_decl_619_, lean_object* v_ci_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__7(v_f_615_, v_toPure_616_, v_toBind_617_, v_inst_618_, v_decl_619_, v_ci_620_, v___y_621_);
lean_dec(v___y_621_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__8(lean_object* v_toPure_623_, lean_object* v_____x_624_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_box(0);
v___x_626_ = lean_apply_2(v_toPure_623_, lean_box(0), v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__8___boxed(lean_object* v_toPure_627_, lean_object* v_____x_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__8(v_toPure_627_, v_____x_628_);
lean_dec_ref(v_____x_628_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg(lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_f_634_){
_start:
{
lean_object* v_toApplicative_635_; lean_object* v_toBind_636_; lean_object* v___f_637_; lean_object* v___f_638_; lean_object* v___f_639_; lean_object* v___f_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v_getEnv_647_; lean_object* v_modifyEnv_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_666_; 
v_toApplicative_635_ = lean_ctor_get(v_inst_630_, 0);
lean_inc_ref(v_toApplicative_635_);
v_toBind_636_ = lean_ctor_get(v_inst_630_, 1);
lean_inc(v_toBind_636_);
lean_inc_ref_n(v_inst_630_, 7);
v___f_637_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_637_, 0, v_inst_630_);
v___f_638_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_638_, 0, v_inst_630_);
v___f_639_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_639_, 0, v_inst_630_);
v___f_640_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_640_, 0, v_inst_630_);
v___x_641_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_641_, 0, lean_box(0));
lean_closure_set(v___x_641_, 1, lean_box(0));
lean_closure_set(v___x_641_, 2, v_inst_630_);
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v___f_637_);
v___x_643_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_643_, 0, lean_box(0));
lean_closure_set(v___x_643_, 1, lean_box(0));
lean_closure_set(v___x_643_, 2, v_inst_630_);
v___x_644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
lean_ctor_set(v___x_644_, 2, v___f_638_);
lean_ctor_set(v___x_644_, 3, v___f_639_);
lean_ctor_set(v___x_644_, 4, v___f_640_);
v___x_645_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_645_, 0, lean_box(0));
lean_closure_set(v___x_645_, 1, lean_box(0));
lean_closure_set(v___x_645_, 2, v_inst_630_);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v_getEnv_647_ = lean_ctor_get(v_inst_631_, 0);
v_modifyEnv_648_ = lean_ctor_get(v_inst_631_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_inst_631_);
if (v_isSharedCheck_666_ == 0)
{
v___x_650_ = v_inst_631_;
v_isShared_651_ = v_isSharedCheck_666_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_modifyEnv_648_);
lean_inc(v_getEnv_647_);
lean_dec(v_inst_631_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_666_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v___f_653_; lean_object* v___x_654_; lean_object* v___x_656_; 
lean_inc_ref(v_inst_630_);
v___x_652_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_652_, 0, lean_box(0));
lean_closure_set(v___x_652_, 1, lean_box(0));
lean_closure_set(v___x_652_, 2, v_inst_630_);
lean_inc_ref(v___x_652_);
v___f_653_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_653_, 0, v_modifyEnv_648_);
lean_closure_set(v___f_653_, 1, v___x_652_);
v___x_654_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 5);
lean_closure_set(v___x_654_, 0, lean_box(0));
lean_closure_set(v___x_654_, 1, lean_box(0));
lean_closure_set(v___x_654_, 2, v_inst_630_);
lean_closure_set(v___x_654_, 3, lean_box(0));
lean_closure_set(v___x_654_, 4, v_getEnv_647_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v___f_653_);
lean_ctor_set(v___x_650_, 0, v___x_654_);
v___x_656_ = v___x_650_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___f_653_);
v___x_656_ = v_reuseFailAlloc_665_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v_toPure_657_; lean_object* v___f_658_; lean_object* v___f_659_; lean_object* v___f_660_; lean_object* v___x_661_; lean_object* v___x_450__overap_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_toPure_657_ = lean_ctor_get(v_toApplicative_635_, 1);
lean_inc_n(v_toPure_657_, 2);
lean_dec_ref(v_toApplicative_635_);
lean_inc(v_toBind_636_);
v___f_658_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_658_, 0, v_f_634_);
lean_closure_set(v___f_658_, 1, v_toPure_657_);
lean_closure_set(v___f_658_, 2, v_toBind_636_);
lean_closure_set(v___f_658_, 3, v_inst_633_);
v___f_659_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_659_, 0, v_inst_632_);
lean_closure_set(v___f_659_, 1, v___x_652_);
v___f_660_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__8___boxed), 2, 1);
lean_closure_set(v___f_660_, 0, v_toPure_657_);
v___x_661_ = lean_unsigned_to_nat(0u);
v___x_450__overap_662_ = l_Lean_Server_Completion_forEligibleDeclsM___redArg(v___x_646_, v___x_656_, v___f_659_, v___f_658_);
v___x_663_ = lean_apply_1(v___x_450__overap_662_, v___x_661_);
v___x_664_ = lean_apply_4(v_toBind_636_, lean_box(0), lean_box(0), v___x_663_, v___f_660_);
return v___x_664_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM(lean_object* v_m_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_f_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg(v_inst_668_, v_inst_669_, v_inst_670_, v_inst_671_, v_f_672_);
return v___x_673_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(lean_object* v_id_674_, lean_object* v_declName_675_, uint8_t v_danglingDot_676_){
_start:
{
if (v_danglingDot_676_ == 0)
{
if (lean_obj_tag(v_id_674_) == 1)
{
lean_object* v_pre_677_; 
v_pre_677_ = lean_ctor_get(v_id_674_, 0);
if (lean_obj_tag(v_pre_677_) == 0)
{
if (lean_obj_tag(v_declName_675_) == 1)
{
lean_object* v_pre_678_; 
v_pre_678_ = lean_ctor_get(v_declName_675_, 0);
if (lean_obj_tag(v_pre_678_) == 0)
{
lean_object* v_str_679_; lean_object* v_str_680_; uint8_t v___x_681_; 
v_str_679_ = lean_ctor_get(v_id_674_, 1);
v_str_680_ = lean_ctor_get(v_declName_675_, 1);
v___x_681_ = l_String_charactersIn(v_str_679_, v_str_680_);
return v___x_681_;
}
else
{
return v_danglingDot_676_;
}
}
else
{
return v_danglingDot_676_;
}
}
else
{
return v_danglingDot_676_;
}
}
else
{
return v_danglingDot_676_;
}
}
else
{
uint8_t v___x_682_; 
v___x_682_ = 0;
return v___x_682_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic___boxed(lean_object* v_id_683_, lean_object* v_declName_684_, lean_object* v_danglingDot_685_){
_start:
{
uint8_t v_danglingDot_boxed_686_; uint8_t v_res_687_; lean_object* v_r_688_; 
v_danglingDot_boxed_686_ = lean_unbox(v_danglingDot_685_);
v_res_687_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_683_, v_declName_684_, v_danglingDot_boxed_686_);
lean_dec(v_declName_684_);
lean_dec(v_id_683_);
v_r_688_ = lean_box(v_res_687_);
return v_r_688_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go_spec__0(lean_object* v_msg_692_){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go_spec__0___closed__0));
v___x_694_ = lean_panic_fn_borrowed(v___x_693_, v_msg_692_);
return v___x_694_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_698_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__2));
v___x_699_ = lean_unsigned_to_nat(26u);
v___x_700_ = lean_unsigned_to_nat(177u);
v___x_701_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__1));
v___x_702_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__0));
v___x_703_ = l_mkPanicMessageWithDecl(v___x_702_, v___x_701_, v___x_700_, v___x_699_, v___x_698_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go(lean_object* v_newLen_704_, lean_object* v_id_705_){
_start:
{
switch(lean_obj_tag(v_id_705_))
{
case 0:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
lean_dec(v_newLen_704_);
v___x_706_ = lean_unsigned_to_nat(0u);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v_id_705_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
return v___x_707_;
}
case 1:
{
lean_object* v_pre_708_; lean_object* v_str_709_; lean_object* v___x_710_; lean_object* v_snd_711_; lean_object* v___y_713_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_pre_708_ = lean_ctor_get(v_id_705_, 0);
v_str_709_ = lean_ctor_get(v_id_705_, 1);
lean_inc(v_pre_708_);
lean_inc(v_newLen_704_);
v___x_710_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go(v_newLen_704_, v_pre_708_);
v_snd_711_ = lean_ctor_get(v___x_710_, 1);
lean_inc(v_snd_711_);
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_nat_add(v_snd_711_, v___x_725_);
v___x_727_ = lean_nat_dec_le(v_newLen_704_, v___x_726_);
lean_dec(v___x_726_);
if (v___x_727_ == 0)
{
uint8_t v___x_728_; 
lean_dec_ref(v___x_710_);
v___x_728_ = l_Lean_Name_isAnonymous(v_pre_708_);
if (v___x_728_ == 0)
{
v___y_713_ = v___x_725_;
goto v___jp_712_;
}
else
{
lean_object* v___x_729_; 
v___x_729_ = lean_unsigned_to_nat(0u);
v___y_713_ = v___x_729_;
goto v___jp_712_;
}
}
else
{
lean_dec(v_snd_711_);
lean_dec_ref_known(v_id_705_, 2);
lean_dec(v_newLen_704_);
return v___x_710_;
}
v___jp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v_len_x27_716_; uint8_t v___x_717_; 
v___x_714_ = lean_nat_add(v_snd_711_, v___y_713_);
v___x_715_ = lean_string_length(v_str_709_);
v_len_x27_716_ = lean_nat_add(v___x_714_, v___x_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_nat_dec_le(v_len_x27_716_, v_newLen_704_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
lean_inc_ref(v_str_709_);
lean_inc(v_pre_708_);
lean_dec(v_len_x27_716_);
lean_dec_ref_known(v_id_705_, 2);
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = lean_nat_sub(v_newLen_704_, v___y_713_);
v___x_720_ = lean_nat_sub(v___x_719_, v_snd_711_);
lean_dec(v_snd_711_);
lean_dec(v___x_719_);
v___x_721_ = lean_string_utf8_extract(v_str_709_, v___x_718_, v___x_720_);
lean_dec(v___x_720_);
lean_dec_ref(v_str_709_);
v___x_722_ = l_Lean_Name_str___override(v_pre_708_, v___x_721_);
v___x_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v_newLen_704_);
return v___x_723_;
}
else
{
lean_object* v___x_724_; 
lean_dec(v_snd_711_);
lean_dec(v_newLen_704_);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v_id_705_);
lean_ctor_set(v___x_724_, 1, v_len_x27_716_);
return v___x_724_;
}
}
}
default: 
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec_ref_known(v_id_705_, 2);
lean_dec(v_newLen_704_);
v___x_730_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3);
v___x_731_ = l_panic___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go_spec__0(v___x_730_);
return v___x_731_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate(lean_object* v_id_732_, lean_object* v_newLen_733_){
_start:
{
lean_object* v___x_734_; lean_object* v_fst_735_; 
v___x_734_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go(v_newLen_733_, v_id_732_);
v_fst_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_fst_735_);
lean_dec_ref(v___x_734_);
return v_fst_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces(lean_object* v_matchUsingNamespace_736_, lean_object* v_ns_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
if (lean_obj_tag(v_ns_737_) == 1)
{
lean_object* v_pre_747_; lean_object* v___x_748_; 
v_pre_747_ = lean_ctor_get(v_ns_737_, 0);
lean_inc(v_pre_747_);
lean_inc_ref(v_matchUsingNamespace_736_);
lean_inc(v_a_745_);
lean_inc_ref(v_a_744_);
lean_inc(v_a_743_);
lean_inc_ref(v_a_742_);
lean_inc_ref(v_a_741_);
lean_inc(v_a_740_);
lean_inc_ref(v_a_739_);
v___x_748_ = lean_apply_10(v_matchUsingNamespace_736_, v_ns_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, lean_box(0));
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
if (lean_obj_tag(v_a_749_) == 0)
{
lean_dec_ref_known(v_a_749_, 1);
lean_dec(v_pre_747_);
lean_dec_ref(v_matchUsingNamespace_736_);
return v___x_748_;
}
else
{
lean_object* v_a_750_; lean_object* v_snd_751_; 
lean_dec_ref_known(v___x_748_, 1);
v_a_750_ = lean_ctor_get(v_a_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v_a_749_, 1);
v_snd_751_ = lean_ctor_get(v_a_750_, 1);
lean_inc(v_snd_751_);
lean_dec(v_a_750_);
v_ns_737_ = v_pre_747_;
v_a_738_ = v_snd_751_;
goto _start;
}
}
else
{
lean_dec(v_pre_747_);
lean_dec_ref(v_matchUsingNamespace_736_);
return v___x_748_;
}
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
lean_dec(v_ns_737_);
lean_dec_ref(v_matchUsingNamespace_736_);
v___x_753_ = lean_box(0);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v_a_738_);
v___x_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces___boxed(lean_object* v_matchUsingNamespace_757_, lean_object* v_ns_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces(v_matchUsingNamespace_757_, v_ns_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0(lean_object* v_id_769_, uint8_t v_danglingDot_770_, lean_object* v_declName_771_, lean_object* v_ns_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v___x_782_; lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_804_; 
v___x_782_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_772_, v_id_769_, v_danglingDot_770_, v_declName_771_, v___y_780_);
v_a_783_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_804_ == 0)
{
v___x_785_ = v___x_782_;
v_isShared_786_ = v_isSharedCheck_804_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_804_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
if (lean_obj_tag(v_a_783_) == 1)
{
lean_object* v_val_787_; lean_object* v___x_788_; lean_object* v___y_790_; 
v_val_787_ = lean_ctor_get(v_a_783_, 0);
v___x_788_ = lean_box(0);
if (lean_obj_tag(v___y_773_) == 0)
{
v___y_790_ = v_a_783_;
goto v___jp_789_;
}
else
{
lean_object* v_val_796_; uint8_t v___x_797_; 
v_val_796_ = lean_ctor_get(v___y_773_, 0);
v___x_797_ = l_Lean_Name_isSuffixOf(v_val_787_, v_val_796_);
if (v___x_797_ == 0)
{
lean_dec_ref_known(v_a_783_, 1);
v___y_790_ = v___y_773_;
goto v___jp_789_;
}
else
{
lean_dec_ref_known(v___y_773_, 1);
v___y_790_ = v_a_783_;
goto v___jp_789_;
}
}
v___jp_789_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_788_);
lean_ctor_set(v___x_791_, 1, v___y_790_);
v___x_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_792_);
v___x_794_ = v___x_785_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_802_; 
lean_dec(v_a_783_);
v___x_798_ = lean_box(0);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
lean_ctor_set(v___x_799_, 1, v___y_773_);
v___x_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_800_);
v___x_802_ = v___x_785_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0___boxed(lean_object* v_id_805_, lean_object* v_danglingDot_806_, lean_object* v_declName_807_, lean_object* v_ns_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
uint8_t v_danglingDot_boxed_818_; lean_object* v_res_819_; 
v_danglingDot_boxed_818_ = lean_unbox(v_danglingDot_806_);
v_res_819_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0(v_id_805_, v_danglingDot_boxed_818_, v_declName_807_, v_ns_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v_ns_808_);
lean_dec(v_id_805_);
return v_res_819_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0(lean_object* v_a_820_, lean_object* v_x_821_){
_start:
{
if (lean_obj_tag(v_x_821_) == 0)
{
uint8_t v___x_822_; 
v___x_822_ = 0;
return v___x_822_;
}
else
{
lean_object* v_head_823_; lean_object* v_tail_824_; uint8_t v___x_825_; 
v_head_823_ = lean_ctor_get(v_x_821_, 0);
v_tail_824_ = lean_ctor_get(v_x_821_, 1);
v___x_825_ = lean_name_eq(v_a_820_, v_head_823_);
if (v___x_825_ == 0)
{
v_x_821_ = v_tail_824_;
goto _start;
}
else
{
return v___x_825_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0___boxed(lean_object* v_a_827_, lean_object* v_x_828_){
_start:
{
uint8_t v_res_829_; lean_object* v_r_830_; 
v_res_829_ = l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0(v_a_827_, v_x_828_);
lean_dec(v_x_828_);
lean_dec(v_a_827_);
v_r_830_ = lean_box(v_res_829_);
return v_r_830_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(lean_object* v_declName_831_, lean_object* v_id_832_, uint8_t v_danglingDot_833_, lean_object* v_as_x27_834_, lean_object* v_b_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
if (lean_obj_tag(v_as_x27_834_) == 0)
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec(v_declName_831_);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v_b_835_);
lean_ctor_set(v___x_839_, 1, v___y_836_);
v___x_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
else
{
lean_object* v_head_842_; lean_object* v_tail_843_; lean_object* v___x_844_; 
v_head_842_ = lean_ctor_get(v_as_x27_834_, 0);
v_tail_843_ = lean_ctor_get(v_as_x27_834_, 1);
v___x_844_ = lean_box(0);
if (lean_obj_tag(v_head_842_) == 0)
{
lean_object* v_ns_845_; lean_object* v_except_846_; uint8_t v___x_847_; 
v_ns_845_ = lean_ctor_get(v_head_842_, 0);
v_except_846_ = lean_ctor_get(v_head_842_, 1);
v___x_847_ = l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0(v_declName_831_, v_except_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; lean_object* v_a_849_; 
lean_inc(v_declName_831_);
v___x_848_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_845_, v_id_832_, v_danglingDot_833_, v_declName_831_, v___y_837_);
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref(v___x_848_);
if (lean_obj_tag(v_a_849_) == 1)
{
if (lean_obj_tag(v___y_836_) == 0)
{
v_as_x27_834_ = v_tail_843_;
v_b_835_ = v___x_844_;
v___y_836_ = v_a_849_;
goto _start;
}
else
{
lean_object* v_val_851_; lean_object* v_val_852_; uint8_t v___x_853_; 
v_val_851_ = lean_ctor_get(v_a_849_, 0);
v_val_852_ = lean_ctor_get(v___y_836_, 0);
v___x_853_ = l_Lean_Name_isSuffixOf(v_val_851_, v_val_852_);
if (v___x_853_ == 0)
{
lean_dec_ref_known(v_a_849_, 1);
v_as_x27_834_ = v_tail_843_;
v_b_835_ = v___x_844_;
goto _start;
}
else
{
lean_dec_ref_known(v___y_836_, 1);
v_as_x27_834_ = v_tail_843_;
v_b_835_ = v___x_844_;
v___y_836_ = v_a_849_;
goto _start;
}
}
}
else
{
lean_dec(v_a_849_);
v_as_x27_834_ = v_tail_843_;
v_b_835_ = v___x_844_;
goto _start;
}
}
else
{
v_as_x27_834_ = v_tail_843_;
v_b_835_ = v___x_844_;
goto _start;
}
}
else
{
v_as_x27_834_ = v_tail_843_;
v_b_835_ = v___x_844_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_declName_859_, lean_object* v_id_860_, lean_object* v_danglingDot_861_, lean_object* v_as_x27_862_, lean_object* v_b_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
uint8_t v_danglingDot_boxed_867_; lean_object* v_res_868_; 
v_danglingDot_boxed_867_ = lean_unbox(v_danglingDot_861_);
v_res_868_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_859_, v_id_860_, v_danglingDot_boxed_867_, v_as_x27_862_, v_b_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec(v_as_x27_862_);
lean_dec(v_id_860_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg(lean_object* v_declName_869_, lean_object* v_id_870_, uint8_t v_danglingDot_871_, lean_object* v_as_872_, lean_object* v_as_x27_873_, lean_object* v_b_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
if (lean_obj_tag(v_as_x27_873_) == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
lean_dec(v_declName_869_);
v___x_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_884_, 0, v_b_874_);
lean_ctor_set(v___x_884_, 1, v___y_875_);
v___x_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
v___x_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
return v___x_886_;
}
else
{
lean_object* v_head_887_; lean_object* v_tail_888_; lean_object* v___x_889_; 
v_head_887_ = lean_ctor_get(v_as_x27_873_, 0);
v_tail_888_ = lean_ctor_get(v_as_x27_873_, 1);
v___x_889_ = lean_box(0);
if (lean_obj_tag(v_head_887_) == 0)
{
lean_object* v_ns_890_; lean_object* v_except_891_; uint8_t v___x_892_; 
v_ns_890_ = lean_ctor_get(v_head_887_, 0);
v_except_891_ = lean_ctor_get(v_head_887_, 1);
v___x_892_ = l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0(v_declName_869_, v_except_891_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; lean_object* v_a_894_; 
lean_inc(v_declName_869_);
v___x_893_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_890_, v_id_870_, v_danglingDot_871_, v_declName_869_, v___y_882_);
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
lean_dec_ref(v___x_893_);
if (lean_obj_tag(v_a_894_) == 1)
{
if (lean_obj_tag(v___y_875_) == 0)
{
lean_object* v___x_895_; 
v___x_895_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_869_, v_id_870_, v_danglingDot_871_, v_tail_888_, v___x_889_, v_a_894_, v___y_882_);
return v___x_895_;
}
else
{
lean_object* v_val_896_; lean_object* v_val_897_; uint8_t v___x_898_; 
v_val_896_ = lean_ctor_get(v_a_894_, 0);
v_val_897_ = lean_ctor_get(v___y_875_, 0);
v___x_898_ = l_Lean_Name_isSuffixOf(v_val_896_, v_val_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; 
lean_dec_ref_known(v_a_894_, 1);
v___x_899_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_869_, v_id_870_, v_danglingDot_871_, v_tail_888_, v___x_889_, v___y_875_, v___y_882_);
return v___x_899_;
}
else
{
lean_object* v___x_900_; 
lean_dec_ref_known(v___y_875_, 1);
v___x_900_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_869_, v_id_870_, v_danglingDot_871_, v_tail_888_, v___x_889_, v_a_894_, v___y_882_);
return v___x_900_;
}
}
}
else
{
lean_object* v___x_901_; 
lean_dec(v_a_894_);
v___x_901_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_869_, v_id_870_, v_danglingDot_871_, v_tail_888_, v___x_889_, v___y_875_, v___y_882_);
return v___x_901_;
}
}
else
{
lean_object* v___x_902_; 
v___x_902_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_869_, v_id_870_, v_danglingDot_871_, v_tail_888_, v___x_889_, v___y_875_, v___y_882_);
return v___x_902_;
}
}
else
{
lean_object* v___x_903_; 
v___x_903_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_869_, v_id_870_, v_danglingDot_871_, v_tail_888_, v___x_889_, v___y_875_, v___y_882_);
return v___x_903_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg___boxed(lean_object* v_declName_904_, lean_object* v_id_905_, lean_object* v_danglingDot_906_, lean_object* v_as_907_, lean_object* v_as_x27_908_, lean_object* v_b_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
uint8_t v_danglingDot_boxed_919_; lean_object* v_res_920_; 
v_danglingDot_boxed_919_ = lean_unbox(v_danglingDot_906_);
v_res_920_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg(v_declName_904_, v_id_905_, v_danglingDot_boxed_919_, v_as_907_, v_as_x27_908_, v_b_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v_as_x27_908_);
lean_dec(v_as_907_);
lean_dec(v_id_905_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(lean_object* v_ctx_921_, lean_object* v_declName_922_, lean_object* v_id_923_, uint8_t v_danglingDot_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v___y_934_; lean_object* v_toCommandContextInfo_971_; lean_object* v_currNamespace_972_; lean_object* v_openDecls_973_; lean_object* v___x_974_; lean_object* v_matchUsingNamespace_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_toCommandContextInfo_971_ = lean_ctor_get(v_ctx_921_, 0);
lean_inc_ref(v_toCommandContextInfo_971_);
lean_dec_ref(v_ctx_921_);
v_currNamespace_972_ = lean_ctor_get(v_toCommandContextInfo_971_, 5);
lean_inc(v_currNamespace_972_);
v_openDecls_973_ = lean_ctor_get(v_toCommandContextInfo_971_, 6);
lean_inc(v_openDecls_973_);
lean_dec_ref(v_toCommandContextInfo_971_);
v___x_974_ = lean_box(v_danglingDot_924_);
lean_inc(v_declName_922_);
lean_inc(v_id_923_);
v_matchUsingNamespace_975_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0___boxed), 13, 3);
lean_closure_set(v_matchUsingNamespace_975_, 0, v_id_923_);
lean_closure_set(v_matchUsingNamespace_975_, 1, v___x_974_);
lean_closure_set(v_matchUsingNamespace_975_, 2, v_declName_922_);
v___x_976_ = lean_box(0);
v___x_977_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces(v_matchUsingNamespace_975_, v_currNamespace_972_, v___x_976_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
if (lean_obj_tag(v_a_978_) == 0)
{
lean_dec_ref_known(v_a_978_, 1);
lean_dec(v_openDecls_973_);
lean_dec(v_id_923_);
lean_dec(v_declName_922_);
v___y_934_ = v___x_977_;
goto v___jp_933_;
}
else
{
lean_object* v_a_979_; lean_object* v_snd_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
lean_dec_ref_known(v___x_977_, 1);
v_a_979_ = lean_ctor_get(v_a_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v_a_978_, 1);
v_snd_980_ = lean_ctor_get(v_a_979_, 1);
lean_inc(v_snd_980_);
lean_dec(v_a_979_);
v___x_981_ = lean_box(0);
lean_inc(v_declName_922_);
v___x_982_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg(v_declName_922_, v_id_923_, v_danglingDot_924_, v_openDecls_973_, v_openDecls_973_, v___x_981_, v_snd_980_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
lean_dec(v_openDecls_973_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v_a_984_; lean_object* v_snd_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_982_, 1);
v_a_984_ = lean_ctor_get(v_a_983_, 0);
lean_inc(v_a_984_);
lean_dec(v_a_983_);
v_snd_985_ = lean_ctor_get(v_a_984_, 1);
lean_inc(v_snd_985_);
lean_dec(v_a_984_);
v___x_986_ = lean_box(0);
v___x_987_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0(v_id_923_, v_danglingDot_924_, v_declName_922_, v___x_986_, v_snd_985_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
lean_dec(v_id_923_);
v___y_934_ = v___x_987_;
goto v___jp_933_;
}
else
{
lean_dec(v_id_923_);
lean_dec(v_declName_922_);
v___y_934_ = v___x_982_;
goto v___jp_933_;
}
}
}
else
{
lean_dec(v_openDecls_973_);
lean_dec(v_id_923_);
lean_dec(v_declName_922_);
v___y_934_ = v___x_977_;
goto v___jp_933_;
}
v___jp_933_:
{
if (lean_obj_tag(v___y_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_962_; 
v_a_935_ = lean_ctor_get(v___y_934_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___y_934_);
if (v_isSharedCheck_962_ == 0)
{
v___x_937_ = v___y_934_;
v_isShared_938_ = v_isSharedCheck_962_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___y_934_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_962_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
if (lean_obj_tag(v_a_935_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_949_; 
v_a_939_ = lean_ctor_get(v_a_935_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v_a_935_);
if (v_isSharedCheck_949_ == 0)
{
v___x_941_ = v_a_935_;
v_isShared_942_ = v_isSharedCheck_949_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v_a_935_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_949_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_948_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_944_);
v___x_946_ = v___x_937_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_961_; 
v_a_950_ = lean_ctor_get(v_a_935_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v_a_935_);
if (v_isSharedCheck_961_ == 0)
{
v___x_952_ = v_a_935_;
v_isShared_953_ = v_isSharedCheck_961_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v_a_935_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_961_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v_snd_954_; lean_object* v___x_956_; 
v_snd_954_ = lean_ctor_get(v_a_950_, 1);
lean_inc(v_snd_954_);
lean_dec(v_a_950_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v_snd_954_);
v___x_956_ = v___x_952_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_snd_954_);
v___x_956_ = v_reuseFailAlloc_960_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_958_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_956_);
v___x_958_ = v___x_937_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
v_a_963_ = lean_ctor_get(v___y_934_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___y_934_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___y_934_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___y_934_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___boxed(lean_object* v_ctx_988_, lean_object* v_declName_989_, lean_object* v_id_990_, lean_object* v_danglingDot_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
uint8_t v_danglingDot_boxed_1000_; lean_object* v_res_1001_; 
v_danglingDot_boxed_1000_ = lean_unbox(v_danglingDot_991_);
v_res_1001_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(v_ctx_988_, v_declName_989_, v_id_990_, v_danglingDot_boxed_1000_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1(lean_object* v_declName_1002_, lean_object* v_id_1003_, uint8_t v_danglingDot_1004_, lean_object* v_as_1005_, lean_object* v_as_x27_1006_, lean_object* v_b_1007_, lean_object* v_a_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg(v_declName_1002_, v_id_1003_, v_danglingDot_1004_, v_as_1005_, v_as_x27_1006_, v_b_1007_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___boxed(lean_object* v_declName_1019_, lean_object* v_id_1020_, lean_object* v_danglingDot_1021_, lean_object* v_as_1022_, lean_object* v_as_x27_1023_, lean_object* v_b_1024_, lean_object* v_a_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
uint8_t v_danglingDot_boxed_1035_; lean_object* v_res_1036_; 
v_danglingDot_boxed_1035_ = lean_unbox(v_danglingDot_1021_);
v_res_1036_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1(v_declName_1019_, v_id_1020_, v_danglingDot_boxed_1035_, v_as_1022_, v_as_x27_1023_, v_b_1024_, v_a_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v_as_x27_1023_);
lean_dec(v_as_1022_);
lean_dec(v_id_1020_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1(lean_object* v_declName_1037_, lean_object* v_id_1038_, uint8_t v_danglingDot_1039_, lean_object* v_as_1040_, lean_object* v_as_x27_1041_, lean_object* v_b_1042_, lean_object* v_a_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_1037_, v_id_1038_, v_danglingDot_1039_, v_as_x27_1041_, v_b_1042_, v___y_1044_, v___y_1051_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___boxed(lean_object* v_declName_1054_, lean_object* v_id_1055_, lean_object* v_danglingDot_1056_, lean_object* v_as_1057_, lean_object* v_as_x27_1058_, lean_object* v_b_1059_, lean_object* v_a_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
uint8_t v_danglingDot_boxed_1070_; lean_object* v_res_1071_; 
v_danglingDot_boxed_1070_ = lean_unbox(v_danglingDot_1056_);
v_res_1071_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1(v_declName_1054_, v_id_1055_, v_danglingDot_boxed_1070_, v_as_1057_, v_as_x27_1058_, v_b_1059_, v_a_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v_as_x27_1058_);
lean_dec(v_as_1057_);
lean_dec(v_id_1055_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(lean_object* v_ctx_1072_, lean_object* v_id_1073_, uint8_t v_danglingDot_1074_, lean_object* v___x_1075_, lean_object* v_a_1076_, lean_object* v_b_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_it_1087_; lean_object* v_a_1091_; lean_object* v___x_1094_; lean_object* v___y_1096_; lean_object* v___y_1097_; uint8_t v___y_1098_; lean_object* v_it_1119_; lean_object* v_fst_1120_; lean_object* v_it_1125_; lean_object* v_fst_1126_; 
v___x_1094_ = lean_box(0);
if (lean_obj_tag(v_a_1076_) == 0)
{
lean_object* v_a_1128_; lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1196_; 
v_a_1128_ = lean_ctor_get(v_a_1076_, 0);
v_a_1129_ = lean_ctor_get(v_a_1076_, 1);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_a_1076_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1131_ = v_a_1076_;
v_isShared_1132_ = v_isSharedCheck_1196_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_inc(v_a_1128_);
lean_dec(v_a_1076_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1196_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v_it_1134_; lean_object* v_it_u2082_1139_; 
v_it_u2082_1139_ = lean_ctor_get(v_a_1128_, 1);
lean_inc(v_it_u2082_1139_);
if (lean_obj_tag(v_it_u2082_1139_) == 0)
{
lean_object* v_it_u2081_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1164_; 
v_it_u2081_1140_ = lean_ctor_get(v_a_1128_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_a_1128_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; 
v_unused_1165_ = lean_ctor_get(v_a_1128_, 1);
lean_dec(v_unused_1165_);
v___x_1142_ = v_a_1128_;
v_isShared_1143_ = v_isSharedCheck_1164_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_it_u2081_1140_);
lean_dec(v_a_1128_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1164_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v_array_1144_; lean_object* v_pos_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1163_; 
v_array_1144_ = lean_ctor_get(v_it_u2081_1140_, 0);
v_pos_1145_ = lean_ctor_get(v_it_u2081_1140_, 1);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_it_u2081_1140_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1147_ = v_it_u2081_1140_;
v_isShared_1148_ = v_isSharedCheck_1163_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_pos_1145_);
lean_inc(v_array_1144_);
lean_dec(v_it_u2081_1140_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1163_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = lean_array_get_size(v_array_1144_);
v___x_1150_ = lean_nat_dec_lt(v_pos_1145_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; 
lean_del_object(v___x_1147_);
lean_dec(v_pos_1145_);
lean_dec_ref(v_array_1144_);
lean_del_object(v___x_1142_);
lean_del_object(v___x_1131_);
v___x_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1151_, 0, v_a_1129_);
v_a_1076_ = v___x_1151_;
goto _start;
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1153_ = lean_unsigned_to_nat(1u);
v___x_1154_ = lean_nat_add(v_pos_1145_, v___x_1153_);
lean_inc_ref(v_array_1144_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 1, v___x_1154_);
v___x_1156_ = v___x_1147_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_array_1144_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1157_ = lean_array_fget(v_array_1144_, v_pos_1145_);
lean_dec(v_pos_1145_);
lean_dec_ref(v_array_1144_);
v___x_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v___x_1158_);
lean_ctor_set(v___x_1142_, 0, v___x_1156_);
v___x_1160_ = v___x_1142_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
v_it_1134_ = v___x_1160_;
goto v___jp_1133_;
}
}
}
}
}
}
else
{
lean_object* v_val_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1195_; 
v_val_1166_ = lean_ctor_get(v_it_u2082_1139_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_it_u2082_1139_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1168_ = v_it_u2082_1139_;
v_isShared_1169_ = v_isSharedCheck_1195_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_val_1166_);
lean_dec(v_it_u2082_1139_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1195_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
if (lean_obj_tag(v_val_1166_) == 0)
{
lean_object* v_it_u2081_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1178_; 
lean_del_object(v___x_1168_);
v_it_u2081_1170_ = lean_ctor_get(v_a_1128_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_a_1128_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; 
v_unused_1179_ = lean_ctor_get(v_a_1128_, 1);
lean_dec(v_unused_1179_);
v___x_1172_ = v_a_1128_;
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_it_u2081_1170_);
lean_dec(v_a_1128_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_1174_ = lean_box(0);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v___x_1174_);
v___x_1176_ = v___x_1172_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_it_u2081_1170_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
v_it_1134_ = v___x_1176_;
goto v___jp_1133_;
}
}
}
else
{
lean_object* v_it_u2081_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1193_; 
lean_del_object(v___x_1131_);
v_it_u2081_1180_ = lean_ctor_get(v_a_1128_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_a_1128_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; 
v_unused_1194_ = lean_ctor_get(v_a_1128_, 1);
lean_dec(v_unused_1194_);
v___x_1182_ = v_a_1128_;
v_isShared_1183_ = v_isSharedCheck_1193_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_it_u2081_1180_);
lean_dec(v_a_1128_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1193_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v_key_1184_; lean_object* v_tail_1185_; lean_object* v___x_1187_; 
v_key_1184_ = lean_ctor_get(v_val_1166_, 0);
lean_inc(v_key_1184_);
v_tail_1185_ = lean_ctor_get(v_val_1166_, 2);
lean_inc(v_tail_1185_);
lean_dec_ref_known(v_val_1166_, 3);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v_tail_1185_);
v___x_1187_ = v___x_1168_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_tail_1185_);
v___x_1187_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1189_; 
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 1, v___x_1187_);
v___x_1189_ = v___x_1182_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_it_u2081_1180_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
lean_ctor_set(v___x_1190_, 1, v_a_1129_);
v_it_1119_ = v___x_1190_;
v_fst_1120_ = v_key_1184_;
goto v___jp_1118_;
}
}
}
}
}
}
v___jp_1133_:
{
lean_object* v___x_1136_; 
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v_it_1134_);
v___x_1136_ = v___x_1131_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_it_1134_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_a_1129_);
v___x_1136_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
v_a_1076_ = v___x_1136_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1197_; 
v_a_1197_ = lean_ctor_get(v_a_1076_, 0);
lean_inc(v_a_1197_);
lean_dec_ref_known(v_a_1076_, 1);
switch(lean_obj_tag(v_a_1197_))
{
case 0:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_dec_ref(v___x_1075_);
lean_dec(v_id_1073_);
lean_dec_ref(v_ctx_1072_);
v___x_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1198_, 0, v_b_1077_);
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
return v___x_1199_;
}
case 1:
{
lean_object* v_a_1200_; lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1219_; 
v_a_1200_ = lean_ctor_get(v_a_1197_, 0);
v_a_1201_ = lean_ctor_get(v_a_1197_, 1);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_a_1197_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1203_ = v_a_1197_;
v_isShared_1204_ = v_isSharedCheck_1219_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_inc(v_a_1200_);
lean_dec(v_a_1197_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1219_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_start_1205_; lean_object* v_stop_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; uint8_t v___x_1209_; 
v_start_1205_ = lean_ctor_get(v_a_1200_, 1);
v_stop_1206_ = lean_ctor_get(v_a_1200_, 2);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = lean_nat_sub(v_stop_1206_, v_start_1205_);
v___x_1209_ = lean_nat_dec_lt(v___x_1207_, v___x_1208_);
lean_dec(v___x_1208_);
if (v___x_1209_ == 0)
{
lean_del_object(v___x_1203_);
lean_dec_ref(v_a_1200_);
v_it_1087_ = v_a_1201_;
goto v___jp_1086_;
}
else
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v_z_1213_; 
v___x_1210_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_a_1200_);
v___x_1211_ = l_Subarray_drop___redArg(v_a_1200_, v___x_1210_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1211_);
v_z_1213_ = v___x_1203_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_a_1201_);
v_z_1213_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Subarray_get___redArg(v_a_1200_, v___x_1207_);
lean_dec_ref(v_a_1200_);
switch(lean_obj_tag(v___x_1214_))
{
case 0:
{
lean_object* v_key_1215_; 
v_key_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_key_1215_);
lean_dec_ref_known(v___x_1214_, 2);
v_it_1125_ = v_z_1213_;
v_fst_1126_ = v_key_1215_;
goto v___jp_1124_;
}
case 1:
{
lean_object* v_node_1216_; lean_object* v___x_1217_; 
v_node_1216_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_node_1216_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1217_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_1216_, v_z_1213_);
v_it_1087_ = v___x_1217_;
goto v___jp_1086_;
}
default: 
{
v_it_1087_ = v_z_1213_;
goto v___jp_1086_;
}
}
}
}
}
}
default: 
{
lean_object* v_vals_1220_; lean_object* v_keys_1221_; lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1238_; 
v_vals_1220_ = lean_ctor_get(v_a_1197_, 1);
v_keys_1221_ = lean_ctor_get(v_a_1197_, 0);
v_a_1222_ = lean_ctor_get(v_a_1197_, 2);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_a_1197_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1224_ = v_a_1197_;
v_isShared_1225_ = v_isSharedCheck_1238_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_inc(v_vals_1220_);
lean_inc(v_keys_1221_);
lean_dec(v_a_1197_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1238_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v_start_1226_; lean_object* v_stop_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v_start_1226_ = lean_ctor_get(v_vals_1220_, 1);
v_stop_1227_ = lean_ctor_get(v_vals_1220_, 2);
v___x_1228_ = lean_unsigned_to_nat(0u);
v___x_1229_ = lean_nat_sub(v_stop_1227_, v_start_1226_);
v___x_1230_ = lean_nat_dec_lt(v___x_1228_, v___x_1229_);
lean_dec(v___x_1229_);
if (v___x_1230_ == 0)
{
lean_del_object(v___x_1224_);
lean_dec_ref(v_keys_1221_);
lean_dec_ref(v_vals_1220_);
v_it_1087_ = v_a_1222_;
goto v___jp_1086_;
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1231_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_keys_1221_);
v___x_1232_ = l_Subarray_drop___redArg(v_keys_1221_, v___x_1231_);
v___x_1233_ = l_Subarray_drop___redArg(v_vals_1220_, v___x_1231_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 1, v___x_1233_);
lean_ctor_set(v___x_1224_, 0, v___x_1232_);
v___x_1235_ = v___x_1224_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1237_, 2, v_a_1222_);
v___x_1235_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Subarray_get___redArg(v_keys_1221_, v___x_1228_);
lean_dec_ref(v_keys_1221_);
v_it_1125_ = v___x_1235_;
v_fst_1126_ = v___x_1236_;
goto v___jp_1124_;
}
}
}
}
}
}
v___jp_1086_:
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_it_1087_);
v_a_1076_ = v___x_1088_;
goto _start;
}
v___jp_1090_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v_a_1091_);
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
return v___x_1093_;
}
v___jp_1095_:
{
if (v___y_1098_ == 0)
{
lean_object* v___x_1099_; 
lean_inc(v_id_1073_);
lean_inc_ref(v_ctx_1072_);
v___x_1099_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(v_ctx_1072_, v___y_1096_, v_id_1073_, v_danglingDot_1074_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1099_, 1);
if (lean_obj_tag(v_a_1100_) == 0)
{
lean_object* v_a_1101_; 
lean_dec_ref(v___y_1097_);
lean_dec_ref(v___x_1075_);
lean_dec(v_id_1073_);
lean_dec_ref(v_ctx_1072_);
v_a_1101_ = lean_ctor_get(v_a_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v_a_1100_, 1);
v_a_1091_ = v_a_1101_;
goto v___jp_1090_;
}
else
{
lean_object* v_a_1102_; 
v_a_1102_ = lean_ctor_get(v_a_1100_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v_a_1100_, 1);
if (lean_obj_tag(v_a_1102_) == 1)
{
lean_object* v_val_1103_; lean_object* v___x_1104_; 
v_val_1103_ = lean_ctor_get(v_a_1102_, 0);
lean_inc(v_val_1103_);
lean_dec_ref_known(v_a_1102_, 1);
v___x_1104_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg(v_val_1103_, v___y_1078_, v___y_1079_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___x_1104_, 1);
if (lean_obj_tag(v_a_1105_) == 0)
{
lean_object* v_a_1106_; 
lean_dec_ref(v___y_1097_);
lean_dec_ref(v___x_1075_);
lean_dec(v_id_1073_);
lean_dec_ref(v_ctx_1072_);
v_a_1106_ = lean_ctor_get(v_a_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v_a_1105_, 1);
v_a_1091_ = v_a_1106_;
goto v___jp_1090_;
}
else
{
lean_dec_ref_known(v_a_1105_, 1);
v_a_1076_ = v___y_1097_;
v_b_1077_ = v___x_1094_;
goto _start;
}
}
else
{
lean_dec_ref(v___y_1097_);
lean_dec_ref(v___x_1075_);
lean_dec(v_id_1073_);
lean_dec_ref(v_ctx_1072_);
return v___x_1104_;
}
}
else
{
lean_dec(v_a_1102_);
v_a_1076_ = v___y_1097_;
v_b_1077_ = v___x_1094_;
goto _start;
}
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec_ref(v___y_1097_);
lean_dec_ref(v___x_1075_);
lean_dec(v_id_1073_);
lean_dec_ref(v_ctx_1072_);
v_a_1109_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1099_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1099_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
else
{
lean_dec(v___y_1096_);
v_a_1076_ = v___y_1097_;
v_b_1077_ = v___x_1094_;
goto _start;
}
}
v___jp_1118_:
{
uint8_t v___x_1121_; 
v___x_1121_ = l_Lean_Name_isInternal(v_fst_1120_);
if (v___x_1121_ == 0)
{
uint8_t v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = 1;
lean_inc(v_fst_1120_);
lean_inc_ref(v___x_1075_);
v___x_1123_ = l_Lean_Environment_contains(v___x_1075_, v_fst_1120_, v___x_1122_);
v___y_1096_ = v_fst_1120_;
v___y_1097_ = v_it_1119_;
v___y_1098_ = v___x_1123_;
goto v___jp_1095_;
}
else
{
v___y_1096_ = v_fst_1120_;
v___y_1097_ = v_it_1119_;
v___y_1098_ = v___x_1121_;
goto v___jp_1095_;
}
}
v___jp_1124_:
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1127_, 0, v_it_1125_);
v_it_1119_ = v___x_1127_;
v_fst_1120_ = v_fst_1126_;
goto v___jp_1118_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg___boxed(lean_object* v_ctx_1239_, lean_object* v_id_1240_, lean_object* v_danglingDot_1241_, lean_object* v___x_1242_, lean_object* v_a_1243_, lean_object* v_b_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
uint8_t v_danglingDot_boxed_1253_; lean_object* v_res_1254_; 
v_danglingDot_boxed_1253_ = lean_unbox(v_danglingDot_1241_);
v_res_1254_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v_ctx_1239_, v_id_1240_, v_danglingDot_boxed_1253_, v___x_1242_, v_a_1243_, v_b_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(lean_object* v_ctx_1255_, lean_object* v_id_1256_, uint8_t v_danglingDot_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v___x_1266_; lean_object* v_env_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1266_ = lean_st_ref_get(v_a_1264_);
v_env_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc_ref_n(v_env_1267_, 2);
lean_dec(v___x_1266_);
v___x_1268_ = l_Lean_Environment_getNamespaces(v_env_1267_);
v___x_1269_ = lean_box(0);
v___x_1270_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v_ctx_1255_, v_id_1256_, v_danglingDot_1257_, v_env_1267_, v___x_1268_, v___x_1269_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
if (lean_obj_tag(v_a_1271_) == 0)
{
lean_dec_ref_known(v_a_1271_, 1);
return v___x_1270_;
}
else
{
lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1279_; 
lean_dec_ref_known(v_a_1271_, 1);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; 
v_unused_1280_ = lean_ctor_get(v___x_1270_, 0);
lean_dec(v_unused_1280_);
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1279_;
goto v_resetjp_1272_;
}
else
{
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1279_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1275_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v___x_1275_);
v___x_1277_ = v___x_1273_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
else
{
return v___x_1270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces___boxed(lean_object* v_ctx_1281_, lean_object* v_id_1282_, lean_object* v_danglingDot_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
uint8_t v_danglingDot_boxed_1292_; lean_object* v_res_1293_; 
v_danglingDot_boxed_1292_ = lean_unbox(v_danglingDot_1283_);
v_res_1293_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_1281_, v_id_1282_, v_danglingDot_boxed_1292_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0(lean_object* v_ctx_1294_, lean_object* v_id_1295_, uint8_t v_danglingDot_1296_, lean_object* v___x_1297_, lean_object* v_inst_1298_, lean_object* v_R_1299_, lean_object* v_a_1300_, lean_object* v_b_1301_, lean_object* v_c_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v_ctx_1294_, v_id_1295_, v_danglingDot_1296_, v___x_1297_, v_a_1300_, v_b_1301_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___boxed(lean_object** _args){
lean_object* v_ctx_1312_ = _args[0];
lean_object* v_id_1313_ = _args[1];
lean_object* v_danglingDot_1314_ = _args[2];
lean_object* v___x_1315_ = _args[3];
lean_object* v_inst_1316_ = _args[4];
lean_object* v_R_1317_ = _args[5];
lean_object* v_a_1318_ = _args[6];
lean_object* v_b_1319_ = _args[7];
lean_object* v_c_1320_ = _args[8];
lean_object* v___y_1321_ = _args[9];
lean_object* v___y_1322_ = _args[10];
lean_object* v___y_1323_ = _args[11];
lean_object* v___y_1324_ = _args[12];
lean_object* v___y_1325_ = _args[13];
lean_object* v___y_1326_ = _args[14];
lean_object* v___y_1327_ = _args[15];
lean_object* v___y_1328_ = _args[16];
_start:
{
uint8_t v_danglingDot_boxed_1329_; lean_object* v_res_1330_; 
v_danglingDot_boxed_1329_ = lean_unbox(v_danglingDot_1314_);
v_res_1330_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0(v_ctx_1312_, v_id_1313_, v_danglingDot_boxed_1329_, v___x_1315_, v_inst_1316_, v_R_1317_, v_a_1318_, v_b_1319_, v_c_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(lean_object* v_n_1331_){
_start:
{
if (lean_obj_tag(v_n_1331_) == 2)
{
lean_object* v_i_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v_i_1332_ = lean_ctor_get(v_n_1331_, 1);
v___x_1333_ = lean_unsigned_to_nat(0u);
v___x_1334_ = lean_nat_dec_eq(v_i_1332_, v___x_1333_);
if (v___x_1334_ == 0)
{
lean_inc_ref(v_n_1331_);
return v_n_1331_;
}
else
{
uint8_t v___x_1335_; 
v___x_1335_ = l_Lean_isPrivatePrefix(v_n_1331_);
if (v___x_1335_ == 0)
{
lean_inc_ref(v_n_1331_);
return v_n_1331_;
}
else
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_box(0);
return v___x_1336_;
}
}
}
else
{
lean_inc(v_n_1331_);
return v_n_1331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix___boxed(lean_object* v_n_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(v_n_1337_);
lean_dec(v_n_1337_);
return v_res_1338_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(lean_object* v_n_u2081_1339_, lean_object* v_n_u2082_1340_){
_start:
{
lean_object* v_n_u2081_1341_; lean_object* v_n_u2082_1342_; 
v_n_u2081_1341_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(v_n_u2081_1339_);
lean_dec(v_n_u2081_1339_);
v_n_u2082_1342_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(v_n_u2082_1340_);
lean_dec(v_n_u2082_1340_);
switch(lean_obj_tag(v_n_u2081_1341_))
{
case 0:
{
if (lean_obj_tag(v_n_u2082_1342_) == 0)
{
uint8_t v___x_1343_; 
v___x_1343_ = 1;
return v___x_1343_;
}
else
{
uint8_t v___x_1344_; 
lean_dec(v_n_u2082_1342_);
v___x_1344_ = 0;
return v___x_1344_;
}
}
case 1:
{
if (lean_obj_tag(v_n_u2082_1342_) == 1)
{
lean_object* v_pre_1345_; lean_object* v_str_1346_; lean_object* v_pre_1347_; lean_object* v_str_1348_; uint8_t v___x_1349_; 
v_pre_1345_ = lean_ctor_get(v_n_u2081_1341_, 0);
lean_inc(v_pre_1345_);
v_str_1346_ = lean_ctor_get(v_n_u2081_1341_, 1);
lean_inc_ref(v_str_1346_);
lean_dec_ref_known(v_n_u2081_1341_, 2);
v_pre_1347_ = lean_ctor_get(v_n_u2082_1342_, 0);
lean_inc(v_pre_1347_);
v_str_1348_ = lean_ctor_get(v_n_u2082_1342_, 1);
lean_inc_ref(v_str_1348_);
lean_dec_ref_known(v_n_u2082_1342_, 2);
v___x_1349_ = lean_string_compare(v_str_1346_, v_str_1348_);
lean_dec_ref(v_str_1348_);
lean_dec_ref(v_str_1346_);
if (v___x_1349_ == 1)
{
v_n_u2081_1339_ = v_pre_1345_;
v_n_u2082_1340_ = v_pre_1347_;
goto _start;
}
else
{
lean_dec(v_pre_1347_);
lean_dec(v_pre_1345_);
return v___x_1349_;
}
}
else
{
uint8_t v___x_1351_; 
lean_dec_ref_known(v_n_u2081_1341_, 2);
lean_dec(v_n_u2082_1342_);
v___x_1351_ = 2;
return v___x_1351_;
}
}
default: 
{
switch(lean_obj_tag(v_n_u2082_1342_))
{
case 0:
{
uint8_t v___x_1352_; 
lean_dec_ref_known(v_n_u2081_1341_, 2);
v___x_1352_ = 2;
return v___x_1352_;
}
case 1:
{
uint8_t v___x_1353_; 
lean_dec_ref_known(v_n_u2082_1342_, 2);
lean_dec_ref_known(v_n_u2081_1341_, 2);
v___x_1353_ = 0;
return v___x_1353_;
}
default: 
{
lean_object* v_pre_1354_; lean_object* v_i_1355_; lean_object* v_pre_1356_; lean_object* v_i_1357_; uint8_t v___x_1358_; 
v_pre_1354_ = lean_ctor_get(v_n_u2081_1341_, 0);
lean_inc(v_pre_1354_);
v_i_1355_ = lean_ctor_get(v_n_u2081_1341_, 1);
lean_inc(v_i_1355_);
lean_dec_ref_known(v_n_u2081_1341_, 2);
v_pre_1356_ = lean_ctor_get(v_n_u2082_1342_, 0);
lean_inc(v_pre_1356_);
v_i_1357_ = lean_ctor_get(v_n_u2082_1342_, 1);
lean_inc(v_i_1357_);
lean_dec_ref_known(v_n_u2082_1342_, 2);
v___x_1358_ = lean_nat_dec_lt(v_i_1355_, v_i_1357_);
if (v___x_1358_ == 0)
{
uint8_t v___x_1359_; 
v___x_1359_ = lean_nat_dec_eq(v_i_1355_, v_i_1357_);
lean_dec(v_i_1357_);
lean_dec(v_i_1355_);
if (v___x_1359_ == 0)
{
uint8_t v___x_1360_; 
lean_dec(v_pre_1356_);
lean_dec(v_pre_1354_);
v___x_1360_ = 2;
return v___x_1360_;
}
else
{
v_n_u2081_1339_ = v_pre_1354_;
v_n_u2082_1340_ = v_pre_1356_;
goto _start;
}
}
else
{
uint8_t v___x_1362_; 
lean_dec(v_i_1357_);
lean_dec(v_pre_1356_);
lean_dec(v_i_1355_);
lean_dec(v_pre_1354_);
v___x_1362_ = 0;
return v___x_1362_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate___boxed(lean_object* v_n_u2081_1363_, lean_object* v_n_u2082_1364_){
_start:
{
uint8_t v_res_1365_; lean_object* v_r_1366_; 
v_res_1365_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_n_u2081_1363_, v_n_u2082_1364_);
v_r_1366_ = lean_box(v_res_1365_);
return v_r_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(lean_object* v_names_1368_){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray___closed__0));
v___x_1370_ = l_Std_TreeSet_ofArray___redArg(v_names_1368_, v___x_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray___boxed(lean_object* v_names_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(v_names_1371_);
lean_dec_ref(v_names_1371_);
return v_res_1372_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(lean_object* v_k_1373_, lean_object* v_t_1374_){
_start:
{
if (lean_obj_tag(v_t_1374_) == 0)
{
lean_object* v_k_1375_; lean_object* v_l_1376_; lean_object* v_r_1377_; uint8_t v___x_1378_; 
v_k_1375_ = lean_ctor_get(v_t_1374_, 1);
lean_inc(v_k_1375_);
v_l_1376_ = lean_ctor_get(v_t_1374_, 3);
lean_inc(v_l_1376_);
v_r_1377_ = lean_ctor_get(v_t_1374_, 4);
lean_inc(v_r_1377_);
lean_dec_ref_known(v_t_1374_, 5);
lean_inc(v_k_1373_);
v___x_1378_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_k_1373_, v_k_1375_);
switch(v___x_1378_)
{
case 0:
{
lean_dec(v_r_1377_);
v_t_1374_ = v_l_1376_;
goto _start;
}
case 1:
{
uint8_t v___x_1380_; 
lean_dec(v_r_1377_);
lean_dec(v_l_1376_);
lean_dec(v_k_1373_);
v___x_1380_ = 1;
return v___x_1380_;
}
default: 
{
lean_dec(v_l_1376_);
v_t_1374_ = v_r_1377_;
goto _start;
}
}
}
else
{
uint8_t v___x_1382_; 
lean_dec(v_k_1373_);
v___x_1382_ = 0;
return v___x_1382_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg___boxed(lean_object* v_k_1383_, lean_object* v_t_1384_){
_start:
{
uint8_t v_res_1385_; lean_object* v_r_1386_; 
v_res_1385_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_k_1383_, v_t_1384_);
v_r_1386_ = lean_box(v_res_1385_);
return v_r_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(lean_object* v_k_1387_, lean_object* v_v_1388_, lean_object* v_t_1389_){
_start:
{
if (lean_obj_tag(v_t_1389_) == 0)
{
lean_object* v_size_1390_; lean_object* v_k_1391_; lean_object* v_v_1392_; lean_object* v_l_1393_; lean_object* v_r_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1674_; 
v_size_1390_ = lean_ctor_get(v_t_1389_, 0);
v_k_1391_ = lean_ctor_get(v_t_1389_, 1);
v_v_1392_ = lean_ctor_get(v_t_1389_, 2);
v_l_1393_ = lean_ctor_get(v_t_1389_, 3);
v_r_1394_ = lean_ctor_get(v_t_1389_, 4);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_t_1389_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1396_ = v_t_1389_;
v_isShared_1397_ = v_isSharedCheck_1674_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_r_1394_);
lean_inc(v_l_1393_);
lean_inc(v_v_1392_);
lean_inc(v_k_1391_);
lean_inc(v_size_1390_);
lean_dec(v_t_1389_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1674_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
uint8_t v___x_1398_; 
lean_inc(v_k_1391_);
lean_inc(v_k_1387_);
v___x_1398_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_k_1387_, v_k_1391_);
switch(v___x_1398_)
{
case 0:
{
lean_object* v_impl_1399_; lean_object* v___x_1400_; 
lean_dec(v_size_1390_);
v_impl_1399_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1387_, v_v_1388_, v_l_1393_);
v___x_1400_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1394_) == 0)
{
lean_object* v_size_1401_; lean_object* v_size_1402_; lean_object* v_k_1403_; lean_object* v_v_1404_; lean_object* v_l_1405_; lean_object* v_r_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v_size_1401_ = lean_ctor_get(v_r_1394_, 0);
v_size_1402_ = lean_ctor_get(v_impl_1399_, 0);
lean_inc(v_size_1402_);
v_k_1403_ = lean_ctor_get(v_impl_1399_, 1);
lean_inc(v_k_1403_);
v_v_1404_ = lean_ctor_get(v_impl_1399_, 2);
lean_inc(v_v_1404_);
v_l_1405_ = lean_ctor_get(v_impl_1399_, 3);
lean_inc(v_l_1405_);
v_r_1406_ = lean_ctor_get(v_impl_1399_, 4);
lean_inc(v_r_1406_);
v___x_1407_ = lean_unsigned_to_nat(3u);
v___x_1408_ = lean_nat_mul(v___x_1407_, v_size_1401_);
v___x_1409_ = lean_nat_dec_lt(v___x_1408_, v_size_1402_);
lean_dec(v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1413_; 
lean_dec(v_r_1406_);
lean_dec(v_l_1405_);
lean_dec(v_v_1404_);
lean_dec(v_k_1403_);
v___x_1410_ = lean_nat_add(v___x_1400_, v_size_1402_);
lean_dec(v_size_1402_);
v___x_1411_ = lean_nat_add(v___x_1410_, v_size_1401_);
lean_dec(v___x_1410_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 3, v_impl_1399_);
lean_ctor_set(v___x_1396_, 0, v___x_1411_);
v___x_1413_ = v___x_1396_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_k_1391_);
lean_ctor_set(v_reuseFailAlloc_1414_, 2, v_v_1392_);
lean_ctor_set(v_reuseFailAlloc_1414_, 3, v_impl_1399_);
lean_ctor_set(v_reuseFailAlloc_1414_, 4, v_r_1394_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
else
{
lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1480_; 
v_isSharedCheck_1480_ = !lean_is_exclusive(v_impl_1399_);
if (v_isSharedCheck_1480_ == 0)
{
lean_object* v_unused_1481_; lean_object* v_unused_1482_; lean_object* v_unused_1483_; lean_object* v_unused_1484_; lean_object* v_unused_1485_; 
v_unused_1481_ = lean_ctor_get(v_impl_1399_, 4);
lean_dec(v_unused_1481_);
v_unused_1482_ = lean_ctor_get(v_impl_1399_, 3);
lean_dec(v_unused_1482_);
v_unused_1483_ = lean_ctor_get(v_impl_1399_, 2);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v_impl_1399_, 1);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v_impl_1399_, 0);
lean_dec(v_unused_1485_);
v___x_1416_ = v_impl_1399_;
v_isShared_1417_ = v_isSharedCheck_1480_;
goto v_resetjp_1415_;
}
else
{
lean_dec(v_impl_1399_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1480_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v_size_1418_; lean_object* v_size_1419_; lean_object* v_k_1420_; lean_object* v_v_1421_; lean_object* v_l_1422_; lean_object* v_r_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; 
v_size_1418_ = lean_ctor_get(v_l_1405_, 0);
v_size_1419_ = lean_ctor_get(v_r_1406_, 0);
v_k_1420_ = lean_ctor_get(v_r_1406_, 1);
v_v_1421_ = lean_ctor_get(v_r_1406_, 2);
v_l_1422_ = lean_ctor_get(v_r_1406_, 3);
v_r_1423_ = lean_ctor_get(v_r_1406_, 4);
v___x_1424_ = lean_unsigned_to_nat(2u);
v___x_1425_ = lean_nat_mul(v___x_1424_, v_size_1418_);
v___x_1426_ = lean_nat_dec_lt(v_size_1419_, v___x_1425_);
lean_dec(v___x_1425_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1455_; 
lean_inc(v_r_1423_);
lean_inc(v_l_1422_);
lean_inc(v_v_1421_);
lean_inc(v_k_1420_);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_r_1406_);
if (v_isSharedCheck_1455_ == 0)
{
lean_object* v_unused_1456_; lean_object* v_unused_1457_; lean_object* v_unused_1458_; lean_object* v_unused_1459_; lean_object* v_unused_1460_; 
v_unused_1456_ = lean_ctor_get(v_r_1406_, 4);
lean_dec(v_unused_1456_);
v_unused_1457_ = lean_ctor_get(v_r_1406_, 3);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v_r_1406_, 2);
lean_dec(v_unused_1458_);
v_unused_1459_ = lean_ctor_get(v_r_1406_, 1);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_r_1406_, 0);
lean_dec(v_unused_1460_);
v___x_1428_ = v_r_1406_;
v_isShared_1429_ = v_isSharedCheck_1455_;
goto v_resetjp_1427_;
}
else
{
lean_dec(v_r_1406_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1455_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___x_1443_; lean_object* v___y_1445_; 
v___x_1430_ = lean_nat_add(v___x_1400_, v_size_1402_);
lean_dec(v_size_1402_);
v___x_1431_ = lean_nat_add(v___x_1430_, v_size_1401_);
lean_dec(v___x_1430_);
v___x_1443_ = lean_nat_add(v___x_1400_, v_size_1418_);
if (lean_obj_tag(v_l_1422_) == 0)
{
lean_object* v_size_1453_; 
v_size_1453_ = lean_ctor_get(v_l_1422_, 0);
lean_inc(v_size_1453_);
v___y_1445_ = v_size_1453_;
goto v___jp_1444_;
}
else
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_unsigned_to_nat(0u);
v___y_1445_ = v___x_1454_;
goto v___jp_1444_;
}
v___jp_1432_:
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = lean_nat_add(v___y_1433_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec(v___y_1433_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 4, v_r_1394_);
lean_ctor_set(v___x_1428_, 3, v_r_1423_);
lean_ctor_set(v___x_1428_, 2, v_v_1392_);
lean_ctor_set(v___x_1428_, 1, v_k_1391_);
lean_ctor_set(v___x_1428_, 0, v___x_1436_);
v___x_1438_ = v___x_1428_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_k_1391_);
lean_ctor_set(v_reuseFailAlloc_1442_, 2, v_v_1392_);
lean_ctor_set(v_reuseFailAlloc_1442_, 3, v_r_1423_);
lean_ctor_set(v_reuseFailAlloc_1442_, 4, v_r_1394_);
v___x_1438_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1440_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 4, v___x_1438_);
lean_ctor_set(v___x_1416_, 3, v___y_1434_);
lean_ctor_set(v___x_1416_, 2, v_v_1421_);
lean_ctor_set(v___x_1416_, 1, v_k_1420_);
lean_ctor_set(v___x_1416_, 0, v___x_1431_);
v___x_1440_ = v___x_1416_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_k_1420_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v_v_1421_);
lean_ctor_set(v_reuseFailAlloc_1441_, 3, v___y_1434_);
lean_ctor_set(v_reuseFailAlloc_1441_, 4, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
v___jp_1444_:
{
lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1446_ = lean_nat_add(v___x_1443_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec(v___x_1443_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v_l_1422_);
lean_ctor_set(v___x_1396_, 3, v_l_1405_);
lean_ctor_set(v___x_1396_, 2, v_v_1404_);
lean_ctor_set(v___x_1396_, 1, v_k_1403_);
lean_ctor_set(v___x_1396_, 0, v___x_1446_);
v___x_1448_ = v___x_1396_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_k_1403_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_v_1404_);
lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_l_1405_);
lean_ctor_set(v_reuseFailAlloc_1452_, 4, v_l_1422_);
v___x_1448_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_nat_add(v___x_1400_, v_size_1401_);
if (lean_obj_tag(v_r_1423_) == 0)
{
lean_object* v_size_1450_; 
v_size_1450_ = lean_ctor_get(v_r_1423_, 0);
lean_inc(v_size_1450_);
v___y_1433_ = v___x_1449_;
v___y_1434_ = v___x_1448_;
v___y_1435_ = v_size_1450_;
goto v___jp_1432_;
}
else
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_unsigned_to_nat(0u);
v___y_1433_ = v___x_1449_;
v___y_1434_ = v___x_1448_;
v___y_1435_ = v___x_1451_;
goto v___jp_1432_;
}
}
}
}
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; 
lean_del_object(v___x_1396_);
v___x_1461_ = lean_nat_add(v___x_1400_, v_size_1402_);
lean_dec(v_size_1402_);
v___x_1462_ = lean_nat_add(v___x_1461_, v_size_1401_);
lean_dec(v___x_1461_);
v___x_1463_ = lean_nat_add(v___x_1400_, v_size_1401_);
v___x_1464_ = lean_nat_add(v___x_1463_, v_size_1419_);
lean_dec(v___x_1463_);
lean_inc_ref(v_r_1394_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 4, v_r_1394_);
lean_ctor_set(v___x_1416_, 3, v_r_1406_);
lean_ctor_set(v___x_1416_, 2, v_v_1392_);
lean_ctor_set(v___x_1416_, 1, v_k_1391_);
lean_ctor_set(v___x_1416_, 0, v___x_1464_);
v___x_1466_ = v___x_1416_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1464_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_k_1391_);
lean_ctor_set(v_reuseFailAlloc_1479_, 2, v_v_1392_);
lean_ctor_set(v_reuseFailAlloc_1479_, 3, v_r_1406_);
lean_ctor_set(v_reuseFailAlloc_1479_, 4, v_r_1394_);
v___x_1466_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
v_isSharedCheck_1473_ = !lean_is_exclusive(v_r_1394_);
if (v_isSharedCheck_1473_ == 0)
{
lean_object* v_unused_1474_; lean_object* v_unused_1475_; lean_object* v_unused_1476_; lean_object* v_unused_1477_; lean_object* v_unused_1478_; 
v_unused_1474_ = lean_ctor_get(v_r_1394_, 4);
lean_dec(v_unused_1474_);
v_unused_1475_ = lean_ctor_get(v_r_1394_, 3);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v_r_1394_, 2);
lean_dec(v_unused_1476_);
v_unused_1477_ = lean_ctor_get(v_r_1394_, 1);
lean_dec(v_unused_1477_);
v_unused_1478_ = lean_ctor_get(v_r_1394_, 0);
lean_dec(v_unused_1478_);
v___x_1468_ = v_r_1394_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_dec(v_r_1394_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 4, v___x_1466_);
lean_ctor_set(v___x_1468_, 3, v_l_1405_);
lean_ctor_set(v___x_1468_, 2, v_v_1404_);
lean_ctor_set(v___x_1468_, 1, v_k_1403_);
lean_ctor_set(v___x_1468_, 0, v___x_1462_);
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_k_1403_);
lean_ctor_set(v_reuseFailAlloc_1472_, 2, v_v_1404_);
lean_ctor_set(v_reuseFailAlloc_1472_, 3, v_l_1405_);
lean_ctor_set(v_reuseFailAlloc_1472_, 4, v___x_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1486_; 
v_l_1486_ = lean_ctor_get(v_impl_1399_, 3);
lean_inc(v_l_1486_);
if (lean_obj_tag(v_l_1486_) == 0)
{
lean_object* v_r_1487_; lean_object* v_k_1488_; lean_object* v_v_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1500_; 
v_r_1487_ = lean_ctor_get(v_impl_1399_, 4);
v_k_1488_ = lean_ctor_get(v_impl_1399_, 1);
v_v_1489_ = lean_ctor_get(v_impl_1399_, 2);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_impl_1399_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; lean_object* v_unused_1502_; 
v_unused_1501_ = lean_ctor_get(v_impl_1399_, 3);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v_impl_1399_, 0);
lean_dec(v_unused_1502_);
v___x_1491_ = v_impl_1399_;
v_isShared_1492_ = v_isSharedCheck_1500_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_r_1487_);
lean_inc(v_v_1489_);
lean_inc(v_k_1488_);
lean_dec(v_impl_1399_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1500_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1493_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1487_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 3, v_r_1487_);
lean_ctor_set(v___x_1491_, 2, v_v_1392_);
lean_ctor_set(v___x_1491_, 1, v_k_1391_);
lean_ctor_set(v___x_1491_, 0, v___x_1400_);
v___x_1495_ = v___x_1491_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_k_1391_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_v_1392_);
lean_ctor_set(v_reuseFailAlloc_1499_, 3, v_r_1487_);
lean_ctor_set(v_reuseFailAlloc_1499_, 4, v_r_1487_);
v___x_1495_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1497_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v___x_1495_);
lean_ctor_set(v___x_1396_, 3, v_l_1486_);
lean_ctor_set(v___x_1396_, 2, v_v_1489_);
lean_ctor_set(v___x_1396_, 1, v_k_1488_);
lean_ctor_set(v___x_1396_, 0, v___x_1493_);
v___x_1497_ = v___x_1396_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_k_1488_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_v_1489_);
lean_ctor_set(v_reuseFailAlloc_1498_, 3, v_l_1486_);
lean_ctor_set(v_reuseFailAlloc_1498_, 4, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
else
{
lean_object* v_r_1503_; 
v_r_1503_ = lean_ctor_get(v_impl_1399_, 4);
lean_inc(v_r_1503_);
if (lean_obj_tag(v_r_1503_) == 0)
{
lean_object* v_k_1504_; lean_object* v_v_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1528_; 
v_k_1504_ = lean_ctor_get(v_impl_1399_, 1);
v_v_1505_ = lean_ctor_get(v_impl_1399_, 2);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_impl_1399_);
if (v_isSharedCheck_1528_ == 0)
{
lean_object* v_unused_1529_; lean_object* v_unused_1530_; lean_object* v_unused_1531_; 
v_unused_1529_ = lean_ctor_get(v_impl_1399_, 4);
lean_dec(v_unused_1529_);
v_unused_1530_ = lean_ctor_get(v_impl_1399_, 3);
lean_dec(v_unused_1530_);
v_unused_1531_ = lean_ctor_get(v_impl_1399_, 0);
lean_dec(v_unused_1531_);
v___x_1507_ = v_impl_1399_;
v_isShared_1508_ = v_isSharedCheck_1528_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_v_1505_);
lean_inc(v_k_1504_);
lean_dec(v_impl_1399_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1528_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v_k_1509_; lean_object* v_v_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1524_; 
v_k_1509_ = lean_ctor_get(v_r_1503_, 1);
v_v_1510_ = lean_ctor_get(v_r_1503_, 2);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_r_1503_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; lean_object* v_unused_1526_; lean_object* v_unused_1527_; 
v_unused_1525_ = lean_ctor_get(v_r_1503_, 4);
lean_dec(v_unused_1525_);
v_unused_1526_ = lean_ctor_get(v_r_1503_, 3);
lean_dec(v_unused_1526_);
v_unused_1527_ = lean_ctor_get(v_r_1503_, 0);
lean_dec(v_unused_1527_);
v___x_1512_ = v_r_1503_;
v_isShared_1513_ = v_isSharedCheck_1524_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_v_1510_);
lean_inc(v_k_1509_);
lean_dec(v_r_1503_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1524_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1514_ = lean_unsigned_to_nat(3u);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 4, v_l_1486_);
lean_ctor_set(v___x_1512_, 3, v_l_1486_);
lean_ctor_set(v___x_1512_, 2, v_v_1505_);
lean_ctor_set(v___x_1512_, 1, v_k_1504_);
lean_ctor_set(v___x_1512_, 0, v___x_1400_);
v___x_1516_ = v___x_1512_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_k_1504_);
lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_v_1505_);
lean_ctor_set(v_reuseFailAlloc_1523_, 3, v_l_1486_);
lean_ctor_set(v_reuseFailAlloc_1523_, 4, v_l_1486_);
v___x_1516_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1518_; 
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 4, v_l_1486_);
lean_ctor_set(v___x_1507_, 2, v_v_1392_);
lean_ctor_set(v___x_1507_, 1, v_k_1391_);
lean_ctor_set(v___x_1507_, 0, v___x_1400_);
v___x_1518_ = v___x_1507_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_k_1391_);
lean_ctor_set(v_reuseFailAlloc_1522_, 2, v_v_1392_);
lean_ctor_set(v_reuseFailAlloc_1522_, 3, v_l_1486_);
lean_ctor_set(v_reuseFailAlloc_1522_, 4, v_l_1486_);
v___x_1518_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1520_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v___x_1518_);
lean_ctor_set(v___x_1396_, 3, v___x_1516_);
lean_ctor_set(v___x_1396_, 2, v_v_1510_);
lean_ctor_set(v___x_1396_, 1, v_k_1509_);
lean_ctor_set(v___x_1396_, 0, v___x_1514_);
v___x_1520_ = v___x_1396_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_k_1509_);
lean_ctor_set(v_reuseFailAlloc_1521_, 2, v_v_1510_);
lean_ctor_set(v_reuseFailAlloc_1521_, 3, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1521_, 4, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
}
else
{
lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1532_ = lean_unsigned_to_nat(2u);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v_r_1503_);
lean_ctor_set(v___x_1396_, 3, v_impl_1399_);
lean_ctor_set(v___x_1396_, 0, v___x_1532_);
v___x_1534_ = v___x_1396_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_k_1391_);
lean_ctor_set(v_reuseFailAlloc_1535_, 2, v_v_1392_);
lean_ctor_set(v_reuseFailAlloc_1535_, 3, v_impl_1399_);
lean_ctor_set(v_reuseFailAlloc_1535_, 4, v_r_1503_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1537_; 
lean_dec(v_v_1392_);
lean_dec(v_k_1391_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 2, v_v_1388_);
lean_ctor_set(v___x_1396_, 1, v_k_1387_);
v___x_1537_ = v___x_1396_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_size_1390_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1538_, 3, v_l_1393_);
lean_ctor_set(v_reuseFailAlloc_1538_, 4, v_r_1394_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
default: 
{
lean_object* v_impl_1539_; lean_object* v___x_1540_; 
lean_dec(v_size_1390_);
v_impl_1539_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1387_, v_v_1388_, v_r_1394_);
v___x_1540_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1393_) == 0)
{
lean_object* v_size_1541_; lean_object* v_size_1542_; lean_object* v_k_1543_; lean_object* v_v_1544_; lean_object* v_l_1545_; lean_object* v_r_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; 
v_size_1541_ = lean_ctor_get(v_l_1393_, 0);
v_size_1542_ = lean_ctor_get(v_impl_1539_, 0);
lean_inc(v_size_1542_);
v_k_1543_ = lean_ctor_get(v_impl_1539_, 1);
lean_inc(v_k_1543_);
v_v_1544_ = lean_ctor_get(v_impl_1539_, 2);
lean_inc(v_v_1544_);
v_l_1545_ = lean_ctor_get(v_impl_1539_, 3);
lean_inc(v_l_1545_);
v_r_1546_ = lean_ctor_get(v_impl_1539_, 4);
lean_inc(v_r_1546_);
v___x_1547_ = lean_unsigned_to_nat(3u);
v___x_1548_ = lean_nat_mul(v___x_1547_, v_size_1541_);
v___x_1549_ = lean_nat_dec_lt(v___x_1548_, v_size_1542_);
lean_dec(v___x_1548_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1553_; 
lean_dec(v_r_1546_);
lean_dec(v_l_1545_);
lean_dec(v_v_1544_);
lean_dec(v_k_1543_);
v___x_1550_ = lean_nat_add(v___x_1540_, v_size_1541_);
v___x_1551_ = lean_nat_add(v___x_1550_, v_size_1542_);
lean_dec(v_size_1542_);
lean_dec(v___x_1550_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v_impl_1539_);
lean_ctor_set(v___x_1396_, 0, v___x_1551_);
v___x_1553_ = v___x_1396_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_k_1391_);
lean_ctor_set(v_reuseFailAlloc_1554_, 2, v_v_1392_);
lean_ctor_set(v_reuseFailAlloc_1554_, 3, v_l_1393_);
lean_ctor_set(v_reuseFailAlloc_1554_, 4, v_impl_1539_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
else
{
lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1618_; 
v_isSharedCheck_1618_ = !lean_is_exclusive(v_impl_1539_);
if (v_isSharedCheck_1618_ == 0)
{
lean_object* v_unused_1619_; lean_object* v_unused_1620_; lean_object* v_unused_1621_; lean_object* v_unused_1622_; lean_object* v_unused_1623_; 
v_unused_1619_ = lean_ctor_get(v_impl_1539_, 4);
lean_dec(v_unused_1619_);
v_unused_1620_ = lean_ctor_get(v_impl_1539_, 3);
lean_dec(v_unused_1620_);
v_unused_1621_ = lean_ctor_get(v_impl_1539_, 2);
lean_dec(v_unused_1621_);
v_unused_1622_ = lean_ctor_get(v_impl_1539_, 1);
lean_dec(v_unused_1622_);
v_unused_1623_ = lean_ctor_get(v_impl_1539_, 0);
lean_dec(v_unused_1623_);
v___x_1556_ = v_impl_1539_;
v_isShared_1557_ = v_isSharedCheck_1618_;
goto v_resetjp_1555_;
}
else
{
lean_dec(v_impl_1539_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1618_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v_size_1558_; lean_object* v_k_1559_; lean_object* v_v_1560_; lean_object* v_l_1561_; lean_object* v_r_1562_; lean_object* v_size_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v_size_1558_ = lean_ctor_get(v_l_1545_, 0);
v_k_1559_ = lean_ctor_get(v_l_1545_, 1);
v_v_1560_ = lean_ctor_get(v_l_1545_, 2);
v_l_1561_ = lean_ctor_get(v_l_1545_, 3);
v_r_1562_ = lean_ctor_get(v_l_1545_, 4);
v_size_1563_ = lean_ctor_get(v_r_1546_, 0);
v___x_1564_ = lean_unsigned_to_nat(2u);
v___x_1565_ = lean_nat_mul(v___x_1564_, v_size_1563_);
v___x_1566_ = lean_nat_dec_lt(v_size_1558_, v___x_1565_);
lean_dec(v___x_1565_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1594_; 
lean_inc(v_r_1562_);
lean_inc(v_l_1561_);
lean_inc(v_v_1560_);
lean_inc(v_k_1559_);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_l_1545_);
if (v_isSharedCheck_1594_ == 0)
{
lean_object* v_unused_1595_; lean_object* v_unused_1596_; lean_object* v_unused_1597_; lean_object* v_unused_1598_; lean_object* v_unused_1599_; 
v_unused_1595_ = lean_ctor_get(v_l_1545_, 4);
lean_dec(v_unused_1595_);
v_unused_1596_ = lean_ctor_get(v_l_1545_, 3);
lean_dec(v_unused_1596_);
v_unused_1597_ = lean_ctor_get(v_l_1545_, 2);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v_l_1545_, 1);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_l_1545_, 0);
lean_dec(v_unused_1599_);
v___x_1568_ = v_l_1545_;
v_isShared_1569_ = v_isSharedCheck_1594_;
goto v_resetjp_1567_;
}
else
{
lean_dec(v_l_1545_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1594_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1584_; 
v___x_1570_ = lean_nat_add(v___x_1540_, v_size_1541_);
v___x_1571_ = lean_nat_add(v___x_1570_, v_size_1542_);
lean_dec(v_size_1542_);
if (lean_obj_tag(v_l_1561_) == 0)
{
lean_object* v_size_1592_; 
v_size_1592_ = lean_ctor_get(v_l_1561_, 0);
lean_inc(v_size_1592_);
v___y_1584_ = v_size_1592_;
goto v___jp_1583_;
}
else
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_unsigned_to_nat(0u);
v___y_1584_ = v___x_1593_;
goto v___jp_1583_;
}
v___jp_1572_:
{
lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1576_ = lean_nat_add(v___y_1573_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec(v___y_1573_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 4, v_r_1546_);
lean_ctor_set(v___x_1568_, 3, v_r_1562_);
lean_ctor_set(v___x_1568_, 2, v_v_1544_);
lean_ctor_set(v___x_1568_, 1, v_k_1543_);
lean_ctor_set(v___x_1568_, 0, v___x_1576_);
v___x_1578_ = v___x_1568_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_k_1543_);
lean_ctor_set(v_reuseFailAlloc_1582_, 2, v_v_1544_);
lean_ctor_set(v_reuseFailAlloc_1582_, 3, v_r_1562_);
lean_ctor_set(v_reuseFailAlloc_1582_, 4, v_r_1546_);
v___x_1578_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1580_; 
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 4, v___x_1578_);
lean_ctor_set(v___x_1556_, 3, v___y_1574_);
lean_ctor_set(v___x_1556_, 2, v_v_1560_);
lean_ctor_set(v___x_1556_, 1, v_k_1559_);
lean_ctor_set(v___x_1556_, 0, v___x_1571_);
v___x_1580_ = v___x_1556_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_k_1559_);
lean_ctor_set(v_reuseFailAlloc_1581_, 2, v_v_1560_);
lean_ctor_set(v_reuseFailAlloc_1581_, 3, v___y_1574_);
lean_ctor_set(v_reuseFailAlloc_1581_, 4, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
v___jp_1583_:
{
lean_object* v___x_1585_; lean_object* v___x_1587_; 
v___x_1585_ = lean_nat_add(v___x_1570_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec(v___x_1570_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v_l_1561_);
lean_ctor_set(v___x_1396_, 0, v___x_1585_);
v___x_1587_ = v___x_1396_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_k_1391_);
lean_ctor_set(v_reuseFailAlloc_1591_, 2, v_v_1392_);
lean_ctor_set(v_reuseFailAlloc_1591_, 3, v_l_1393_);
lean_ctor_set(v_reuseFailAlloc_1591_, 4, v_l_1561_);
v___x_1587_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_nat_add(v___x_1540_, v_size_1563_);
if (lean_obj_tag(v_r_1562_) == 0)
{
lean_object* v_size_1589_; 
v_size_1589_ = lean_ctor_get(v_r_1562_, 0);
lean_inc(v_size_1589_);
v___y_1573_ = v___x_1588_;
v___y_1574_ = v___x_1587_;
v___y_1575_ = v_size_1589_;
goto v___jp_1572_;
}
else
{
lean_object* v___x_1590_; 
v___x_1590_ = lean_unsigned_to_nat(0u);
v___y_1573_ = v___x_1588_;
v___y_1574_ = v___x_1587_;
v___y_1575_ = v___x_1590_;
goto v___jp_1572_;
}
}
}
}
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1604_; 
lean_del_object(v___x_1396_);
v___x_1600_ = lean_nat_add(v___x_1540_, v_size_1541_);
v___x_1601_ = lean_nat_add(v___x_1600_, v_size_1542_);
lean_dec(v_size_1542_);
v___x_1602_ = lean_nat_add(v___x_1600_, v_size_1558_);
lean_dec(v___x_1600_);
lean_inc_ref(v_l_1393_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 4, v_l_1545_);
lean_ctor_set(v___x_1556_, 3, v_l_1393_);
lean_ctor_set(v___x_1556_, 2, v_v_1392_);
lean_ctor_set(v___x_1556_, 1, v_k_1391_);
lean_ctor_set(v___x_1556_, 0, v___x_1602_);
v___x_1604_ = v___x_1556_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_k_1391_);
lean_ctor_set(v_reuseFailAlloc_1617_, 2, v_v_1392_);
lean_ctor_set(v_reuseFailAlloc_1617_, 3, v_l_1393_);
lean_ctor_set(v_reuseFailAlloc_1617_, 4, v_l_1545_);
v___x_1604_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
v_isSharedCheck_1611_ = !lean_is_exclusive(v_l_1393_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; lean_object* v_unused_1613_; lean_object* v_unused_1614_; lean_object* v_unused_1615_; lean_object* v_unused_1616_; 
v_unused_1612_ = lean_ctor_get(v_l_1393_, 4);
lean_dec(v_unused_1612_);
v_unused_1613_ = lean_ctor_get(v_l_1393_, 3);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_l_1393_, 2);
lean_dec(v_unused_1614_);
v_unused_1615_ = lean_ctor_get(v_l_1393_, 1);
lean_dec(v_unused_1615_);
v_unused_1616_ = lean_ctor_get(v_l_1393_, 0);
lean_dec(v_unused_1616_);
v___x_1606_ = v_l_1393_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_dec(v_l_1393_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 4, v_r_1546_);
lean_ctor_set(v___x_1606_, 3, v___x_1604_);
lean_ctor_set(v___x_1606_, 2, v_v_1544_);
lean_ctor_set(v___x_1606_, 1, v_k_1543_);
lean_ctor_set(v___x_1606_, 0, v___x_1601_);
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1601_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_k_1543_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_v_1544_);
lean_ctor_set(v_reuseFailAlloc_1610_, 3, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1610_, 4, v_r_1546_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1624_; 
v_l_1624_ = lean_ctor_get(v_impl_1539_, 3);
lean_inc(v_l_1624_);
if (lean_obj_tag(v_l_1624_) == 0)
{
lean_object* v_r_1625_; lean_object* v_k_1626_; lean_object* v_v_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1650_; 
v_r_1625_ = lean_ctor_get(v_impl_1539_, 4);
v_k_1626_ = lean_ctor_get(v_impl_1539_, 1);
v_v_1627_ = lean_ctor_get(v_impl_1539_, 2);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_impl_1539_);
if (v_isSharedCheck_1650_ == 0)
{
lean_object* v_unused_1651_; lean_object* v_unused_1652_; 
v_unused_1651_ = lean_ctor_get(v_impl_1539_, 3);
lean_dec(v_unused_1651_);
v_unused_1652_ = lean_ctor_get(v_impl_1539_, 0);
lean_dec(v_unused_1652_);
v___x_1629_ = v_impl_1539_;
v_isShared_1630_ = v_isSharedCheck_1650_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_r_1625_);
lean_inc(v_v_1627_);
lean_inc(v_k_1626_);
lean_dec(v_impl_1539_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1650_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v_k_1631_; lean_object* v_v_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1646_; 
v_k_1631_ = lean_ctor_get(v_l_1624_, 1);
v_v_1632_ = lean_ctor_get(v_l_1624_, 2);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_l_1624_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; lean_object* v_unused_1648_; lean_object* v_unused_1649_; 
v_unused_1647_ = lean_ctor_get(v_l_1624_, 4);
lean_dec(v_unused_1647_);
v_unused_1648_ = lean_ctor_get(v_l_1624_, 3);
lean_dec(v_unused_1648_);
v_unused_1649_ = lean_ctor_get(v_l_1624_, 0);
lean_dec(v_unused_1649_);
v___x_1634_ = v_l_1624_;
v_isShared_1635_ = v_isSharedCheck_1646_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_v_1632_);
lean_inc(v_k_1631_);
lean_dec(v_l_1624_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1646_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v___x_1638_; 
v___x_1636_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1625_, 2);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 4, v_r_1625_);
lean_ctor_set(v___x_1634_, 3, v_r_1625_);
lean_ctor_set(v___x_1634_, 2, v_v_1392_);
lean_ctor_set(v___x_1634_, 1, v_k_1391_);
lean_ctor_set(v___x_1634_, 0, v___x_1540_);
v___x_1638_ = v___x_1634_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_k_1391_);
lean_ctor_set(v_reuseFailAlloc_1645_, 2, v_v_1392_);
lean_ctor_set(v_reuseFailAlloc_1645_, 3, v_r_1625_);
lean_ctor_set(v_reuseFailAlloc_1645_, 4, v_r_1625_);
v___x_1638_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v___x_1640_; 
lean_inc(v_r_1625_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 3, v_r_1625_);
lean_ctor_set(v___x_1629_, 0, v___x_1540_);
v___x_1640_ = v___x_1629_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_k_1626_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_v_1627_);
lean_ctor_set(v_reuseFailAlloc_1644_, 3, v_r_1625_);
lean_ctor_set(v_reuseFailAlloc_1644_, 4, v_r_1625_);
v___x_1640_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
lean_object* v___x_1642_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v___x_1640_);
lean_ctor_set(v___x_1396_, 3, v___x_1638_);
lean_ctor_set(v___x_1396_, 2, v_v_1632_);
lean_ctor_set(v___x_1396_, 1, v_k_1631_);
lean_ctor_set(v___x_1396_, 0, v___x_1636_);
v___x_1642_ = v___x_1396_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1636_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_k_1631_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_v_1632_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v___x_1638_);
lean_ctor_set(v_reuseFailAlloc_1643_, 4, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
}
else
{
lean_object* v_r_1653_; 
v_r_1653_ = lean_ctor_get(v_impl_1539_, 4);
lean_inc(v_r_1653_);
if (lean_obj_tag(v_r_1653_) == 0)
{
lean_object* v_k_1654_; lean_object* v_v_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1666_; 
v_k_1654_ = lean_ctor_get(v_impl_1539_, 1);
v_v_1655_ = lean_ctor_get(v_impl_1539_, 2);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_impl_1539_);
if (v_isSharedCheck_1666_ == 0)
{
lean_object* v_unused_1667_; lean_object* v_unused_1668_; lean_object* v_unused_1669_; 
v_unused_1667_ = lean_ctor_get(v_impl_1539_, 4);
lean_dec(v_unused_1667_);
v_unused_1668_ = lean_ctor_get(v_impl_1539_, 3);
lean_dec(v_unused_1668_);
v_unused_1669_ = lean_ctor_get(v_impl_1539_, 0);
lean_dec(v_unused_1669_);
v___x_1657_ = v_impl_1539_;
v_isShared_1658_ = v_isSharedCheck_1666_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_v_1655_);
lean_inc(v_k_1654_);
lean_dec(v_impl_1539_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1666_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1659_ = lean_unsigned_to_nat(3u);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 4, v_l_1624_);
lean_ctor_set(v___x_1657_, 2, v_v_1392_);
lean_ctor_set(v___x_1657_, 1, v_k_1391_);
lean_ctor_set(v___x_1657_, 0, v___x_1540_);
v___x_1661_ = v___x_1657_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_k_1391_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v_v_1392_);
lean_ctor_set(v_reuseFailAlloc_1665_, 3, v_l_1624_);
lean_ctor_set(v_reuseFailAlloc_1665_, 4, v_l_1624_);
v___x_1661_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1663_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v_r_1653_);
lean_ctor_set(v___x_1396_, 3, v___x_1661_);
lean_ctor_set(v___x_1396_, 2, v_v_1655_);
lean_ctor_set(v___x_1396_, 1, v_k_1654_);
lean_ctor_set(v___x_1396_, 0, v___x_1659_);
v___x_1663_ = v___x_1396_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_k_1654_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_v_1655_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1664_, 4, v_r_1653_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1670_ = lean_unsigned_to_nat(2u);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v_impl_1539_);
lean_ctor_set(v___x_1396_, 3, v_r_1653_);
lean_ctor_set(v___x_1396_, 0, v___x_1670_);
v___x_1672_ = v___x_1396_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_k_1391_);
lean_ctor_set(v_reuseFailAlloc_1673_, 2, v_v_1392_);
lean_ctor_set(v_reuseFailAlloc_1673_, 3, v_r_1653_);
lean_ctor_set(v_reuseFailAlloc_1673_, 4, v_impl_1539_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
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
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = lean_unsigned_to_nat(1u);
v___x_1676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1675_);
lean_ctor_set(v___x_1676_, 1, v_k_1387_);
lean_ctor_set(v___x_1676_, 2, v_v_1388_);
lean_ctor_set(v___x_1676_, 3, v_t_1389_);
lean_ctor_set(v___x_1676_, 4, v_t_1389_);
return v___x_1676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(lean_object* v_as_1677_, size_t v_sz_1678_, size_t v_i_1679_, lean_object* v_b_1680_){
_start:
{
lean_object* v___y_1683_; uint8_t v___x_1687_; 
v___x_1687_ = lean_usize_dec_lt(v_i_1679_, v_sz_1678_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; 
v___x_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1688_, 0, v_b_1680_);
return v___x_1688_;
}
else
{
lean_object* v_a_1689_; uint8_t v___x_1690_; 
v_a_1689_ = lean_array_uget_borrowed(v_as_1677_, v_i_1679_);
lean_inc(v_b_1680_);
lean_inc(v_a_1689_);
v___x_1690_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_a_1689_, v_b_1680_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = lean_box(0);
lean_inc(v_a_1689_);
v___x_1692_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_a_1689_, v___x_1691_, v_b_1680_);
v___y_1683_ = v___x_1692_;
goto v___jp_1682_;
}
else
{
v___y_1683_ = v_b_1680_;
goto v___jp_1682_;
}
}
v___jp_1682_:
{
size_t v___x_1684_; size_t v___x_1685_; 
v___x_1684_ = ((size_t)1ULL);
v___x_1685_ = lean_usize_add(v_i_1679_, v___x_1684_);
v_i_1679_ = v___x_1685_;
v_b_1680_ = v___y_1683_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg___boxed(lean_object* v_as_1693_, lean_object* v_sz_1694_, lean_object* v_i_1695_, lean_object* v_b_1696_, lean_object* v___y_1697_){
_start:
{
size_t v_sz_boxed_1698_; size_t v_i_boxed_1699_; lean_object* v_res_1700_; 
v_sz_boxed_1698_ = lean_unbox_usize(v_sz_1694_);
lean_dec(v_sz_1694_);
v_i_boxed_1699_ = lean_unbox_usize(v_i_1695_);
lean_dec(v_i_1695_);
v_res_1700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_as_1693_, v_sz_boxed_1698_, v_i_boxed_1699_, v_b_1696_);
lean_dec_ref(v_as_1693_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(lean_object* v_type_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_Server_Completion_getDotCompletionTypeNames(v_type_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v_set_1709_; size_t v_sz_1710_; size_t v___x_1711_; lean_object* v___x_1712_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1707_, 1);
v_set_1709_ = lean_box(1);
v_sz_1710_ = lean_array_size(v_a_1708_);
v___x_1711_ = ((size_t)0ULL);
v___x_1712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_a_1708_, v_sz_1710_, v___x_1711_, v_set_1709_);
lean_dec(v_a_1708_);
return v___x_1712_;
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
v_a_1713_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1707_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1707_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet___boxed(lean_object* v_type_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(v_type_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
lean_dec(v_a_1725_);
lean_dec_ref(v_a_1724_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
return v_res_1727_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0(lean_object* v_00_u03b2_1728_, lean_object* v_k_1729_, lean_object* v_t_1730_){
_start:
{
uint8_t v___x_1731_; 
v___x_1731_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_k_1729_, v_t_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___boxed(lean_object* v_00_u03b2_1732_, lean_object* v_k_1733_, lean_object* v_t_1734_){
_start:
{
uint8_t v_res_1735_; lean_object* v_r_1736_; 
v_res_1735_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0(v_00_u03b2_1732_, v_k_1733_, v_t_1734_);
v_r_1736_ = lean_box(v_res_1735_);
return v_r_1736_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1(lean_object* v_00_u03b2_1737_, lean_object* v_k_1738_, lean_object* v_v_1739_, lean_object* v_t_1740_, lean_object* v_hl_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1738_, v_v_1739_, v_t_1740_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2(lean_object* v_as_1743_, size_t v_sz_1744_, size_t v_i_1745_, lean_object* v_b_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_as_1743_, v_sz_1744_, v_i_1745_, v_b_1746_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___boxed(lean_object* v_as_1753_, lean_object* v_sz_1754_, lean_object* v_i_1755_, lean_object* v_b_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
size_t v_sz_boxed_1762_; size_t v_i_boxed_1763_; lean_object* v_res_1764_; 
v_sz_boxed_1762_ = lean_unbox_usize(v_sz_1754_);
lean_dec(v_sz_1754_);
v_i_boxed_1763_ = lean_unbox_usize(v_i_1755_);
lean_dec(v_i_1755_);
v_res_1764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2(v_as_1753_, v_sz_boxed_1762_, v_i_boxed_1763_, v_b_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec_ref(v_as_1753_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(lean_object* v_e_1765_, lean_object* v_declName_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
uint8_t v___y_1773_; uint8_t v___y_1795_; lean_object* v___x_1798_; 
v___x_1798_ = l_Lean_Expr_getAppFn(v_e_1765_);
if (lean_obj_tag(v___x_1798_) == 4)
{
lean_object* v_declName_1799_; lean_object* v___x_1800_; 
v_declName_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc_n(v_declName_1799_, 2);
lean_dec_ref_known(v___x_1798_, 2);
v___x_1800_ = l_Lean_privateToUserName_x3f(v_declName_1799_);
if (lean_obj_tag(v___x_1800_) == 0)
{
uint8_t v___x_1801_; 
v___x_1801_ = lean_name_eq(v_declName_1799_, v_declName_1766_);
lean_dec(v_declName_1799_);
v___y_1795_ = v___x_1801_;
goto v___jp_1794_;
}
else
{
lean_object* v_val_1802_; uint8_t v___x_1803_; 
lean_dec(v_declName_1799_);
v_val_1802_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_val_1802_);
lean_dec_ref_known(v___x_1800_, 1);
v___x_1803_ = lean_name_eq(v_val_1802_, v_declName_1766_);
lean_dec(v_val_1802_);
v___y_1795_ = v___x_1803_;
goto v___jp_1794_;
}
}
else
{
uint8_t v___x_1804_; 
lean_dec_ref(v___x_1798_);
v___x_1804_ = 0;
v___y_1773_ = v___x_1804_;
goto v___jp_1772_;
}
v___jp_1772_:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f(v_e_1765_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1785_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1777_ = v___x_1774_;
v_isShared_1778_ = v_isSharedCheck_1785_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1774_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1785_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
if (lean_obj_tag(v_a_1775_) == 1)
{
lean_object* v_val_1779_; 
lean_del_object(v___x_1777_);
v_val_1779_ = lean_ctor_get(v_a_1775_, 0);
lean_inc(v_val_1779_);
lean_dec_ref_known(v_a_1775_, 1);
v_e_1765_ = v_val_1779_;
goto _start;
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1783_; 
lean_dec(v_a_1775_);
v___x_1781_ = lean_box(v___y_1773_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1781_);
v___x_1783_ = v___x_1777_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
v_a_1786_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1774_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1774_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
v___jp_1794_:
{
if (v___y_1795_ == 0)
{
v___y_1773_ = v___y_1795_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_dec_ref(v_e_1765_);
v___x_1796_ = lean_box(v___y_1795_);
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
return v___x_1797_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf___boxed(lean_object* v_e_1805_, lean_object* v_declName_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(v_e_1805_, v_declName_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
lean_dec(v_declName_1806_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0(lean_object* v_k_1813_, lean_object* v_b_1814_, lean_object* v_c_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___x_1821_; 
lean_inc(v___y_1819_);
lean_inc_ref(v___y_1818_);
lean_inc(v___y_1817_);
lean_inc_ref(v___y_1816_);
v___x_1821_ = lean_apply_7(v_k_1813_, v_b_1814_, v_c_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, lean_box(0));
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed(lean_object* v_k_1822_, lean_object* v_b_1823_, lean_object* v_c_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0(v_k_1822_, v_b_1823_, v_c_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(lean_object* v_type_1831_, lean_object* v_k_1832_, uint8_t v_cleanupAnnotations_1833_, uint8_t v_whnfType_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v___f_1840_; lean_object* v___x_1841_; 
v___f_1840_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1840_, 0, v_k_1832_);
v___x_1841_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1831_, v___f_1840_, v_cleanupAnnotations_1833_, v_whnfType_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
v_a_1850_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1841_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1841_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___boxed(lean_object* v_type_1858_, lean_object* v_k_1859_, lean_object* v_cleanupAnnotations_1860_, lean_object* v_whnfType_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1867_; uint8_t v_whnfType_boxed_1868_; lean_object* v_res_1869_; 
v_cleanupAnnotations_boxed_1867_ = lean_unbox(v_cleanupAnnotations_1860_);
v_whnfType_boxed_1868_ = lean_unbox(v_whnfType_1861_);
v_res_1869_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v_type_1858_, v_k_1859_, v_cleanupAnnotations_boxed_1867_, v_whnfType_boxed_1868_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1(lean_object* v_00_u03b1_1870_, lean_object* v_type_1871_, lean_object* v_k_1872_, uint8_t v_cleanupAnnotations_1873_, uint8_t v_whnfType_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v_type_1871_, v_k_1872_, v_cleanupAnnotations_1873_, v_whnfType_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___boxed(lean_object* v_00_u03b1_1881_, lean_object* v_type_1882_, lean_object* v_k_1883_, lean_object* v_cleanupAnnotations_1884_, lean_object* v_whnfType_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1891_; uint8_t v_whnfType_boxed_1892_; lean_object* v_res_1893_; 
v_cleanupAnnotations_boxed_1891_ = lean_unbox(v_cleanupAnnotations_1884_);
v_whnfType_boxed_1892_ = lean_unbox(v_whnfType_1885_);
v_res_1893_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1(v_00_u03b1_1881_, v_type_1882_, v_k_1883_, v_cleanupAnnotations_boxed_1891_, v_whnfType_boxed_1892_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(lean_object* v_typeName_1897_, lean_object* v_as_1898_, size_t v_sz_1899_, size_t v_i_1900_, lean_object* v_b_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
uint8_t v___x_1907_; 
v___x_1907_ = lean_usize_dec_lt(v_i_1900_, v_sz_1899_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; 
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v_b_1901_);
return v___x_1908_;
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
lean_dec_ref(v_b_1901_);
v_a_1909_ = lean_array_uget_borrowed(v_as_1898_, v_i_1900_);
v___x_1910_ = l_Lean_Expr_fvarId_x21(v_a_1909_);
v___x_1911_ = l_Lean_FVarId_getDecl___redArg(v___x_1910_, v___y_1902_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
v___x_1913_ = l_Lean_LocalDecl_type(v_a_1912_);
lean_dec(v_a_1912_);
v___x_1914_ = l_Lean_Expr_consumeMData(v___x_1913_);
lean_dec_ref(v___x_1913_);
v___x_1915_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(v___x_1914_, v_typeName_1897_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1931_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1918_ = v___x_1915_;
v_isShared_1919_ = v_isSharedCheck_1931_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1915_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1931_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; uint8_t v___x_1921_; 
v___x_1920_ = lean_box(0);
v___x_1921_ = lean_unbox(v_a_1916_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; size_t v___x_1923_; size_t v___x_1924_; 
lean_del_object(v___x_1918_);
lean_dec(v_a_1916_);
v___x_1922_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___closed__0));
v___x_1923_ = ((size_t)1ULL);
v___x_1924_ = lean_usize_add(v_i_1900_, v___x_1923_);
v_i_1900_ = v___x_1924_;
v_b_1901_ = v___x_1922_;
goto _start;
}
else
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___x_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1926_, 0, v_a_1916_);
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v___x_1920_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v___x_1927_);
v___x_1929_ = v___x_1918_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
v_a_1932_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1915_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1915_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
v_a_1940_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1911_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1911_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___boxed(lean_object* v_typeName_1948_, lean_object* v_as_1949_, lean_object* v_sz_1950_, lean_object* v_i_1951_, lean_object* v_b_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
size_t v_sz_boxed_1958_; size_t v_i_boxed_1959_; lean_object* v_res_1960_; 
v_sz_boxed_1958_ = lean_unbox_usize(v_sz_1950_);
lean_dec(v_sz_1950_);
v_i_boxed_1959_ = lean_unbox_usize(v_i_1951_);
lean_dec(v_i_1951_);
v_res_1960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(v_typeName_1948_, v_as_1949_, v_sz_boxed_1958_, v_i_boxed_1959_, v_b_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec_ref(v_as_1949_);
lean_dec(v_typeName_1948_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0(lean_object* v_typeName_1961_, lean_object* v_xs_1962_, lean_object* v_x_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v___x_1969_; size_t v_sz_1970_; size_t v___x_1971_; lean_object* v___x_1972_; 
v___x_1969_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___closed__0));
v_sz_1970_ = lean_array_size(v_xs_1962_);
v___x_1971_ = ((size_t)0ULL);
v___x_1972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(v_typeName_1961_, v_xs_1962_, v_sz_1970_, v___x_1971_, v___x_1969_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1987_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_1987_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1987_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v_fst_1977_; 
v_fst_1977_ = lean_ctor_get(v_a_1973_, 0);
lean_inc(v_fst_1977_);
lean_dec(v_a_1973_);
if (lean_obj_tag(v_fst_1977_) == 0)
{
uint8_t v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1978_ = 0;
v___x_1979_ = lean_box(v___x_1978_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1979_);
v___x_1981_ = v___x_1975_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
else
{
lean_object* v_val_1983_; lean_object* v___x_1985_; 
v_val_1983_ = lean_ctor_get(v_fst_1977_, 0);
lean_inc(v_val_1983_);
lean_dec_ref_known(v_fst_1977_, 1);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v_val_1983_);
v___x_1985_ = v___x_1975_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_val_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
v_a_1988_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1972_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1972_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0___boxed(lean_object* v_typeName_1996_, lean_object* v_xs_1997_, lean_object* v_x_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0(v_typeName_1996_, v_xs_1997_, v_x_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v_x_1998_);
lean_dec_ref(v_xs_1997_);
lean_dec(v_typeName_1996_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(lean_object* v_typeName_2005_, lean_object* v_info_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v___f_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; lean_object* v___x_2015_; 
v___f_2012_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2012_, 0, v_typeName_2005_);
v___x_2013_ = l_Lean_ConstantInfo_type(v_info_2006_);
v___x_2014_ = 0;
v___x_2015_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v___x_2013_, v___f_2012_, v___x_2014_, v___x_2014_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___boxed(lean_object* v_typeName_2016_, lean_object* v_info_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(v_typeName_2016_, v_info_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec_ref(v_info_2017_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(lean_object* v_e_2024_, lean_object* v___y_2025_){
_start:
{
uint8_t v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = l_Lean_Expr_hasMVar(v_e_2024_);
v___x_2028_ = lean_bool_not(v___x_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v_mctx_2030_; lean_object* v___x_2031_; lean_object* v_fst_2032_; lean_object* v_snd_2033_; lean_object* v___x_2034_; lean_object* v_cache_2035_; lean_object* v_zetaDeltaFVarIds_2036_; lean_object* v_postponed_2037_; lean_object* v_diag_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2047_; 
v___x_2029_ = lean_st_ref_get(v___y_2025_);
v_mctx_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc_ref(v_mctx_2030_);
lean_dec(v___x_2029_);
v___x_2031_ = l_Lean_instantiateMVarsCore(v_mctx_2030_, v_e_2024_);
v_fst_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_fst_2032_);
v_snd_2033_ = lean_ctor_get(v___x_2031_, 1);
lean_inc(v_snd_2033_);
lean_dec_ref(v___x_2031_);
v___x_2034_ = lean_st_ref_take(v___y_2025_);
v_cache_2035_ = lean_ctor_get(v___x_2034_, 1);
v_zetaDeltaFVarIds_2036_ = lean_ctor_get(v___x_2034_, 2);
v_postponed_2037_ = lean_ctor_get(v___x_2034_, 3);
v_diag_2038_ = lean_ctor_get(v___x_2034_, 4);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; 
v_unused_2048_ = lean_ctor_get(v___x_2034_, 0);
lean_dec(v_unused_2048_);
v___x_2040_ = v___x_2034_;
v_isShared_2041_ = v_isSharedCheck_2047_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_diag_2038_);
lean_inc(v_postponed_2037_);
lean_inc(v_zetaDeltaFVarIds_2036_);
lean_inc(v_cache_2035_);
lean_dec(v___x_2034_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2047_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v_snd_2033_);
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_snd_2033_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_cache_2035_);
lean_ctor_set(v_reuseFailAlloc_2046_, 2, v_zetaDeltaFVarIds_2036_);
lean_ctor_set(v_reuseFailAlloc_2046_, 3, v_postponed_2037_);
lean_ctor_set(v_reuseFailAlloc_2046_, 4, v_diag_2038_);
v___x_2043_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = lean_st_ref_set(v___y_2025_, v___x_2043_);
v___x_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2045_, 0, v_fst_2032_);
return v___x_2045_;
}
}
}
else
{
lean_object* v___x_2049_; 
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v_e_2024_);
return v___x_2049_;
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
lean_dec_ref_known(v___x_2205_, 1);
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
lean_dec_ref_known(v___x_2152_, 2);
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
lean_dec_ref_known(v_a_2156_, 1);
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
lean_dec_ref_known(v___y_2195_, 1);
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
lean_dec_ref_known(v_ns_2249_, 2);
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
lean_dec_ref_known(v_a_2319_, 1);
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
lean_dec_ref_known(v___x_2341_, 1);
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
lean_dec_ref_known(v___x_2343_, 1);
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
lean_dec_ref_known(v_as_2413_, 2);
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
lean_dec_ref_known(v___x_2430_, 1);
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
lean_dec_ref_known(v_x_2500_, 3);
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
lean_dec_ref_known(v_a_2515_, 1);
lean_dec(v_tail_2513_);
lean_dec_ref(v_f_2498_);
return v___x_2514_;
}
else
{
lean_object* v_a_2516_; 
lean_dec_ref_known(v___x_2514_, 1);
v_a_2516_ = lean_ctor_get(v_a_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref_known(v_a_2515_, 1);
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
lean_dec_ref_known(v_a_2547_, 1);
lean_dec_ref(v_f_2530_);
return v___x_2546_;
}
else
{
lean_object* v_a_2548_; size_t v___x_2549_; size_t v___x_2550_; 
lean_dec_ref_known(v___x_2546_, 1);
v_a_2548_ = lean_ctor_get(v_a_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref_known(v_a_2547_, 1);
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
lean_dec_ref_known(v_a_2616_, 1);
lean_dec(v_i_2599_);
lean_dec_ref(v_f_2596_);
return v___x_2615_;
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
lean_dec_ref_known(v___x_2615_, 1);
v_a_2617_ = lean_ctor_get(v_a_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v_a_2616_, 1);
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
lean_dec_ref_known(v_x_2636_, 2);
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
lean_dec_ref_known(v___y_2692_, 1);
v_a_2694_ = lean_ctor_get(v_a_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v_a_2693_, 1);
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
lean_dec_ref_known(v_a_2779_, 1);
lean_dec_ref(v_map_u2082_2767_);
lean_dec_ref(v_f_2757_);
return v___x_2778_;
}
else
{
lean_object* v___x_2780_; 
lean_dec_ref_known(v_a_2779_, 1);
lean_dec_ref_known(v___x_2778_, 1);
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
lean_dec_ref_known(v_a_2784_, 1);
lean_dec_ref(v_map_u2082_2767_);
lean_dec_ref(v_f_2757_);
return v___x_2783_;
}
else
{
lean_object* v___x_2785_; 
lean_dec_ref_known(v_a_2784_, 1);
lean_dec_ref_known(v___x_2783_, 1);
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
lean_dec_ref_known(v_a_2853_, 1);
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
lean_dec_ref_known(v_a_2905_, 1);
lean_dec(v_i_2886_);
lean_dec_ref(v_f_2883_);
return v___x_2904_;
}
else
{
lean_object* v_a_2906_; lean_object* v_fst_2907_; lean_object* v_snd_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
lean_dec_ref_known(v___x_2904_, 1);
v_a_2906_ = lean_ctor_get(v_a_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref_known(v_a_2905_, 1);
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
lean_dec_ref_known(v_x_2928_, 2);
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
lean_dec_ref_known(v___y_2989_, 1);
v_a_2991_ = lean_ctor_get(v_a_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref_known(v_a_2990_, 1);
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
lean_dec_ref_known(v_x_3090_, 3);
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
lean_dec_ref_known(v_a_3107_, 1);
lean_dec(v_tail_3105_);
lean_dec_ref(v_f_3088_);
return v___x_3106_;
}
else
{
lean_object* v_a_3108_; lean_object* v_fst_3109_; lean_object* v_snd_3110_; 
lean_dec_ref_known(v___x_3106_, 1);
v_a_3108_ = lean_ctor_get(v_a_3107_, 0);
lean_inc(v_a_3108_);
lean_dec_ref_known(v_a_3107_, 1);
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
lean_dec_ref_known(v_a_3143_, 1);
lean_dec_ref(v_f_3125_);
return v___x_3142_;
}
else
{
lean_object* v_a_3144_; lean_object* v_fst_3145_; lean_object* v_snd_3146_; size_t v___x_3147_; size_t v___x_3148_; 
lean_dec_ref_known(v___x_3142_, 1);
v_a_3144_ = lean_ctor_get(v_a_3143_, 0);
lean_inc(v_a_3144_);
lean_dec_ref_known(v_a_3143_, 1);
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
lean_dec_ref_known(v___x_3218_, 1);
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
lean_dec_ref_known(v_a_3245_, 1);
lean_dec_ref(v___f_3221_);
lean_dec_ref(v_env_3217_);
return v___x_3244_;
}
else
{
lean_object* v_a_3246_; lean_object* v_snd_3247_; 
lean_dec_ref_known(v___x_3244_, 1);
v_a_3246_ = lean_ctor_get(v_a_3245_, 0);
lean_inc(v_a_3246_);
lean_dec_ref_known(v_a_3245_, 1);
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
lean_dec_ref_known(v_a_3251_, 1);
lean_dec_ref(v___f_3221_);
lean_dec_ref(v_env_3217_);
return v___x_3250_;
}
else
{
lean_object* v_a_3252_; lean_object* v_snd_3253_; 
lean_dec_ref_known(v___x_3250_, 1);
v_a_3252_ = lean_ctor_get(v_a_3251_, 0);
lean_inc(v_a_3252_);
lean_dec_ref_known(v_a_3251_, 1);
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
lean_dec_ref_known(v_a_3285_, 1);
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
lean_dec_ref_known(v_a_3364_, 1);
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
lean_dec_ref_known(v_a_3449_, 1);
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
lean_object* v_cs_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; size_t v_sz_3511_; size_t v___x_3512_; lean_object* v___x_3513_; 
v_cs_3508_ = lean_ctor_get(v_n_3498_, 0);
v___x_3509_ = lean_box(0);
v___x_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3509_);
lean_ctor_set(v___x_3510_, 1, v_b_3499_);
v_sz_3511_ = lean_array_size(v_cs_3508_);
v___x_3512_ = ((size_t)0ULL);
v___x_3513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16(v_init_3495_, v_id_3496_, v_danglingDot_3497_, v_cs_3508_, v_sz_3511_, v___x_3512_, v___x_3510_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3550_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3516_ = v___x_3513_;
v_isShared_3517_ = v_isSharedCheck_3550_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3513_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3550_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
if (lean_obj_tag(v_a_3514_) == 0)
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3528_; 
v_a_3518_ = lean_ctor_get(v_a_3514_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v_a_3514_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3520_ = v_a_3514_;
v_isShared_3521_ = v_isSharedCheck_3528_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v_a_3514_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3528_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
lean_object* v___x_3525_; 
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 0, v___x_3523_);
v___x_3525_ = v___x_3516_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3549_; 
v_a_3529_ = lean_ctor_get(v_a_3514_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v_a_3514_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3531_ = v_a_3514_;
v_isShared_3532_ = v_isSharedCheck_3549_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v_a_3514_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3549_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v_fst_3533_; 
v_fst_3533_ = lean_ctor_get(v_a_3529_, 0);
if (lean_obj_tag(v_fst_3533_) == 0)
{
lean_object* v_snd_3534_; lean_object* v___x_3535_; lean_object* v___x_3537_; 
v_snd_3534_ = lean_ctor_get(v_a_3529_, 1);
lean_inc(v_snd_3534_);
lean_dec(v_a_3529_);
v___x_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3535_, 0, v_snd_3534_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3535_);
v___x_3537_ = v___x_3531_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3535_);
v___x_3537_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
lean_object* v___x_3539_; 
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 0, v___x_3537_);
v___x_3539_ = v___x_3516_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3537_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
else
{
lean_object* v_val_3542_; lean_object* v___x_3544_; 
lean_inc_ref(v_fst_3533_);
lean_dec(v_a_3529_);
v_val_3542_ = lean_ctor_get(v_fst_3533_, 0);
lean_inc(v_val_3542_);
lean_dec_ref_known(v_fst_3533_, 1);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v_val_3542_);
v___x_3544_ = v___x_3531_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_val_3542_);
v___x_3544_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
lean_object* v___x_3546_; 
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 0, v___x_3544_);
v___x_3546_ = v___x_3516_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3544_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
v_a_3551_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3513_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3513_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
else
{
lean_object* v_vs_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; size_t v_sz_3562_; size_t v___x_3563_; lean_object* v___x_3564_; 
v_vs_3559_ = lean_ctor_get(v_n_3498_, 0);
v___x_3560_ = lean_box(0);
v___x_3561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3560_);
lean_ctor_set(v___x_3561_, 1, v_b_3499_);
v_sz_3562_ = lean_array_size(v_vs_3559_);
v___x_3563_ = ((size_t)0ULL);
v___x_3564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17(v_id_3496_, v_danglingDot_3497_, v_vs_3559_, v_sz_3562_, v___x_3563_, v___x_3561_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3601_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3567_ = v___x_3564_;
v_isShared_3568_ = v_isSharedCheck_3601_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3564_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3601_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
if (lean_obj_tag(v_a_3565_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3579_; 
v_a_3569_ = lean_ctor_get(v_a_3565_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v_a_3565_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3571_ = v_a_3565_;
v_isShared_3572_ = v_isSharedCheck_3579_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v_a_3565_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3579_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
lean_object* v___x_3576_; 
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 0, v___x_3574_);
v___x_3576_ = v___x_3567_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3574_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3600_; 
v_a_3580_ = lean_ctor_get(v_a_3565_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v_a_3565_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3582_ = v_a_3565_;
v_isShared_3583_ = v_isSharedCheck_3600_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v_a_3565_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3600_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v_fst_3584_; 
v_fst_3584_ = lean_ctor_get(v_a_3580_, 0);
if (lean_obj_tag(v_fst_3584_) == 0)
{
lean_object* v_snd_3585_; lean_object* v___x_3586_; lean_object* v___x_3588_; 
v_snd_3585_ = lean_ctor_get(v_a_3580_, 1);
lean_inc(v_snd_3585_);
lean_dec(v_a_3580_);
v___x_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3586_, 0, v_snd_3585_);
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 0, v___x_3586_);
v___x_3588_ = v___x_3582_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3586_);
v___x_3588_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
lean_object* v___x_3590_; 
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 0, v___x_3588_);
v___x_3590_ = v___x_3567_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3588_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
else
{
lean_object* v_val_3593_; lean_object* v___x_3595_; 
lean_inc_ref(v_fst_3584_);
lean_dec(v_a_3580_);
v_val_3593_ = lean_ctor_get(v_fst_3584_, 0);
lean_inc(v_val_3593_);
lean_dec_ref_known(v_fst_3584_, 1);
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 0, v_val_3593_);
v___x_3595_ = v___x_3582_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_val_3593_);
v___x_3595_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
lean_object* v___x_3597_; 
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 0, v___x_3595_);
v___x_3597_ = v___x_3567_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3595_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
v_a_3602_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3564_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3564_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16(lean_object* v_init_3610_, lean_object* v_id_3611_, uint8_t v_danglingDot_3612_, lean_object* v_as_3613_, size_t v_sz_3614_, size_t v_i_3615_, lean_object* v_b_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
uint8_t v___x_3625_; 
v___x_3625_ = lean_usize_dec_lt(v_i_3615_, v_sz_3614_);
if (v___x_3625_ == 0)
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3626_, 0, v_b_3616_);
v___x_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3626_);
return v___x_3627_;
}
else
{
lean_object* v_snd_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3681_; 
v_snd_3628_ = lean_ctor_get(v_b_3616_, 1);
v_isSharedCheck_3681_ = !lean_is_exclusive(v_b_3616_);
if (v_isSharedCheck_3681_ == 0)
{
lean_object* v_unused_3682_; 
v_unused_3682_ = lean_ctor_get(v_b_3616_, 0);
lean_dec(v_unused_3682_);
v___x_3630_ = v_b_3616_;
v_isShared_3631_ = v_isSharedCheck_3681_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_snd_3628_);
lean_dec(v_b_3616_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3681_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v_a_3632_; lean_object* v___x_3633_; 
v_a_3632_ = lean_array_uget_borrowed(v_as_3613_, v_i_3615_);
lean_inc(v_snd_3628_);
v___x_3633_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(v_init_3610_, v_id_3611_, v_danglingDot_3612_, v_a_3632_, v_snd_3628_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3672_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3636_ = v___x_3633_;
v_isShared_3637_ = v_isSharedCheck_3672_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3633_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3672_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
if (lean_obj_tag(v_a_3634_) == 0)
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3648_; 
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
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
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3671_; 
v_a_3649_ = lean_ctor_get(v_a_3634_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v_a_3634_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3651_ = v_a_3634_;
v_isShared_3652_ = v_isSharedCheck_3671_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v_a_3634_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3671_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
if (lean_obj_tag(v_a_3649_) == 0)
{
lean_object* v___x_3653_; lean_object* v___x_3655_; 
v___x_3653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3653_, 0, v_a_3649_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 0, v___x_3653_);
v___x_3655_ = v___x_3630_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3653_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_snd_3628_);
v___x_3655_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3657_; 
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 0, v___x_3655_);
v___x_3657_ = v___x_3651_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3655_);
v___x_3657_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
lean_object* v___x_3659_; 
if (v_isShared_3637_ == 0)
{
lean_ctor_set(v___x_3636_, 0, v___x_3657_);
v___x_3659_ = v___x_3636_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3657_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3664_; lean_object* v___x_3666_; 
lean_del_object(v___x_3651_);
lean_del_object(v___x_3636_);
lean_dec(v_snd_3628_);
v_a_3663_ = lean_ctor_get(v_a_3649_, 0);
lean_inc(v_a_3663_);
lean_dec_ref_known(v_a_3649_, 1);
v___x_3664_ = lean_box(0);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 1, v_a_3663_);
lean_ctor_set(v___x_3630_, 0, v___x_3664_);
v___x_3666_ = v___x_3630_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3664_);
lean_ctor_set(v_reuseFailAlloc_3670_, 1, v_a_3663_);
v___x_3666_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
size_t v___x_3667_; size_t v___x_3668_; 
v___x_3667_ = ((size_t)1ULL);
v___x_3668_ = lean_usize_add(v_i_3615_, v___x_3667_);
v_i_3615_ = v___x_3668_;
v_b_3616_ = v___x_3666_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
v_a_3673_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3675_ = v___x_3633_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3633_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16___boxed(lean_object* v_init_3683_, lean_object* v_id_3684_, lean_object* v_danglingDot_3685_, lean_object* v_as_3686_, lean_object* v_sz_3687_, lean_object* v_i_3688_, lean_object* v_b_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_){
_start:
{
uint8_t v_danglingDot_boxed_3698_; size_t v_sz_boxed_3699_; size_t v_i_boxed_3700_; lean_object* v_res_3701_; 
v_danglingDot_boxed_3698_ = lean_unbox(v_danglingDot_3685_);
v_sz_boxed_3699_ = lean_unbox_usize(v_sz_3687_);
lean_dec(v_sz_3687_);
v_i_boxed_3700_ = lean_unbox_usize(v_i_3688_);
lean_dec(v_i_3688_);
v_res_3701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16(v_init_3683_, v_id_3684_, v_danglingDot_boxed_3698_, v_as_3686_, v_sz_boxed_3699_, v_i_boxed_3700_, v_b_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec_ref(v_as_3686_);
lean_dec(v_id_3684_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11___boxed(lean_object* v_init_3702_, lean_object* v_id_3703_, lean_object* v_danglingDot_3704_, lean_object* v_n_3705_, lean_object* v_b_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
uint8_t v_danglingDot_boxed_3715_; lean_object* v_res_3716_; 
v_danglingDot_boxed_3715_ = lean_unbox(v_danglingDot_3704_);
v_res_3716_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(v_init_3702_, v_id_3703_, v_danglingDot_boxed_3715_, v_n_3705_, v_b_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v_n_3705_);
lean_dec(v_id_3703_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(lean_object* v_id_3717_, uint8_t v_danglingDot_3718_, lean_object* v_as_3719_, size_t v_sz_3720_, size_t v_i_3721_, lean_object* v_b_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
uint8_t v___x_3726_; 
v___x_3726_ = lean_usize_dec_lt(v_i_3721_, v_sz_3720_);
if (v___x_3726_ == 0)
{
lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3727_, 0, v_b_3722_);
v___x_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3727_);
return v___x_3728_;
}
else
{
lean_object* v_snd_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3782_; 
v_snd_3729_ = lean_ctor_get(v_b_3722_, 1);
v_isSharedCheck_3782_ = !lean_is_exclusive(v_b_3722_);
if (v_isSharedCheck_3782_ == 0)
{
lean_object* v_unused_3783_; 
v_unused_3783_ = lean_ctor_get(v_b_3722_, 0);
lean_dec(v_unused_3783_);
v___x_3731_ = v_b_3722_;
v_isShared_3732_ = v_isSharedCheck_3782_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_snd_3729_);
lean_dec(v_b_3722_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3782_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3733_; lean_object* v_a_3735_; lean_object* v_a_3742_; 
v___x_3733_ = lean_box(0);
v_a_3742_ = lean_array_uget(v_as_3719_, v_i_3721_);
if (lean_obj_tag(v_a_3742_) == 0)
{
v_a_3735_ = v_snd_3729_;
goto v___jp_3734_;
}
else
{
lean_object* v_val_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3781_; 
lean_dec(v_snd_3729_);
v_val_3743_ = lean_ctor_get(v_a_3742_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v_a_3742_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3745_ = v_a_3742_;
v_isShared_3746_ = v_isSharedCheck_3781_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_val_3743_);
lean_dec(v_a_3742_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3781_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3747_; lean_object* v___x_3748_; uint8_t v___x_3749_; 
v___x_3747_ = lean_box(0);
v___x_3748_ = l_Lean_LocalDecl_userName(v_val_3743_);
v___x_3749_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3717_, v___x_3748_, v_danglingDot_3718_);
if (v___x_3749_ == 0)
{
lean_dec(v___x_3748_);
lean_del_object(v___x_3745_);
lean_dec(v_val_3743_);
v_a_3735_ = v___x_3747_;
goto v___jp_3734_;
}
else
{
lean_object* v___x_3750_; lean_object* v___x_3752_; 
v___x_3750_ = l_Lean_LocalDecl_fvarId(v_val_3743_);
lean_dec(v_val_3743_);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 0, v___x_3750_);
v___x_3752_ = v___x_3745_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3750_);
v___x_3752_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
uint8_t v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3753_ = 5;
v___x_3754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_3755_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3748_, v___x_3752_, v___x_3753_, v___x_3754_, v___y_3723_, v___y_3724_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3771_; 
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3758_ = v___x_3755_;
v_isShared_3759_ = v_isSharedCheck_3771_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3755_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3771_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
if (lean_obj_tag(v_a_3756_) == 0)
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3770_; 
lean_del_object(v___x_3731_);
v_a_3760_ = lean_ctor_get(v_a_3756_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v_a_3756_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3762_ = v_a_3756_;
v_isShared_3763_ = v_isSharedCheck_3770_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v_a_3756_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3770_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
lean_object* v___x_3767_; 
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 0, v___x_3765_);
v___x_3767_ = v___x_3758_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v___x_3765_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3756_, 1);
lean_del_object(v___x_3758_);
v_a_3735_ = v___x_3747_;
goto v___jp_3734_;
}
}
}
else
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
lean_del_object(v___x_3731_);
v_a_3772_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v___x_3755_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3755_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
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
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3772_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
}
}
}
v___jp_3734_:
{
lean_object* v___x_3737_; 
if (v_isShared_3732_ == 0)
{
lean_ctor_set(v___x_3731_, 1, v_a_3735_);
lean_ctor_set(v___x_3731_, 0, v___x_3733_);
v___x_3737_ = v___x_3731_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3733_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v_a_3735_);
v___x_3737_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
size_t v___x_3738_; size_t v___x_3739_; 
v___x_3738_ = ((size_t)1ULL);
v___x_3739_ = lean_usize_add(v_i_3721_, v___x_3738_);
v_i_3721_ = v___x_3739_;
v_b_3722_ = v___x_3737_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg___boxed(lean_object* v_id_3784_, lean_object* v_danglingDot_3785_, lean_object* v_as_3786_, lean_object* v_sz_3787_, lean_object* v_i_3788_, lean_object* v_b_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
uint8_t v_danglingDot_boxed_3793_; size_t v_sz_boxed_3794_; size_t v_i_boxed_3795_; lean_object* v_res_3796_; 
v_danglingDot_boxed_3793_ = lean_unbox(v_danglingDot_3785_);
v_sz_boxed_3794_ = lean_unbox_usize(v_sz_3787_);
lean_dec(v_sz_3787_);
v_i_boxed_3795_ = lean_unbox_usize(v_i_3788_);
lean_dec(v_i_3788_);
v_res_3796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(v_id_3784_, v_danglingDot_boxed_3793_, v_as_3786_, v_sz_boxed_3794_, v_i_boxed_3795_, v_b_3789_, v___y_3790_, v___y_3791_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec_ref(v_as_3786_);
lean_dec(v_id_3784_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12(lean_object* v_id_3797_, uint8_t v_danglingDot_3798_, lean_object* v_as_3799_, size_t v_sz_3800_, size_t v_i_3801_, lean_object* v_b_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
uint8_t v___x_3811_; 
v___x_3811_ = lean_usize_dec_lt(v_i_3801_, v_sz_3800_);
if (v___x_3811_ == 0)
{
lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3812_, 0, v_b_3802_);
v___x_3813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3812_);
return v___x_3813_;
}
else
{
lean_object* v_snd_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3867_; 
v_snd_3814_ = lean_ctor_get(v_b_3802_, 1);
v_isSharedCheck_3867_ = !lean_is_exclusive(v_b_3802_);
if (v_isSharedCheck_3867_ == 0)
{
lean_object* v_unused_3868_; 
v_unused_3868_ = lean_ctor_get(v_b_3802_, 0);
lean_dec(v_unused_3868_);
v___x_3816_ = v_b_3802_;
v_isShared_3817_ = v_isSharedCheck_3867_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_snd_3814_);
lean_dec(v_b_3802_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3867_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3818_; lean_object* v_a_3820_; lean_object* v_a_3827_; 
v___x_3818_ = lean_box(0);
v_a_3827_ = lean_array_uget(v_as_3799_, v_i_3801_);
if (lean_obj_tag(v_a_3827_) == 0)
{
v_a_3820_ = v_snd_3814_;
goto v___jp_3819_;
}
else
{
lean_object* v_val_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3866_; 
lean_dec(v_snd_3814_);
v_val_3828_ = lean_ctor_get(v_a_3827_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v_a_3827_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3830_ = v_a_3827_;
v_isShared_3831_ = v_isSharedCheck_3866_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_val_3828_);
lean_dec(v_a_3827_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3866_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; uint8_t v___x_3834_; 
v___x_3832_ = lean_box(0);
v___x_3833_ = l_Lean_LocalDecl_userName(v_val_3828_);
v___x_3834_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3797_, v___x_3833_, v_danglingDot_3798_);
if (v___x_3834_ == 0)
{
lean_dec(v___x_3833_);
lean_del_object(v___x_3830_);
lean_dec(v_val_3828_);
v_a_3820_ = v___x_3832_;
goto v___jp_3819_;
}
else
{
lean_object* v___x_3835_; lean_object* v___x_3837_; 
v___x_3835_ = l_Lean_LocalDecl_fvarId(v_val_3828_);
lean_dec(v_val_3828_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 0, v___x_3835_);
v___x_3837_ = v___x_3830_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3835_);
v___x_3837_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
uint8_t v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3838_ = 5;
v___x_3839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_3840_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3833_, v___x_3837_, v___x_3838_, v___x_3839_, v___y_3803_, v___y_3804_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3856_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3843_ = v___x_3840_;
v_isShared_3844_ = v_isSharedCheck_3856_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3840_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3856_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
if (lean_obj_tag(v_a_3841_) == 0)
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3855_; 
lean_del_object(v___x_3816_);
v_a_3845_ = lean_ctor_get(v_a_3841_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v_a_3841_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3847_ = v_a_3841_;
v_isShared_3848_ = v_isSharedCheck_3855_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v_a_3841_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3855_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
lean_object* v___x_3852_; 
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 0, v___x_3850_);
v___x_3852_ = v___x_3843_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v___x_3850_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3841_, 1);
lean_del_object(v___x_3843_);
v_a_3820_ = v___x_3832_;
goto v___jp_3819_;
}
}
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
lean_del_object(v___x_3816_);
v_a_3857_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3840_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3840_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
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
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
}
}
}
}
v___jp_3819_:
{
lean_object* v___x_3822_; 
if (v_isShared_3817_ == 0)
{
lean_ctor_set(v___x_3816_, 1, v_a_3820_);
lean_ctor_set(v___x_3816_, 0, v___x_3818_);
v___x_3822_ = v___x_3816_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3818_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v_a_3820_);
v___x_3822_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
size_t v___x_3823_; size_t v___x_3824_; lean_object* v___x_3825_; 
v___x_3823_ = ((size_t)1ULL);
v___x_3824_ = lean_usize_add(v_i_3801_, v___x_3823_);
v___x_3825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(v_id_3797_, v_danglingDot_3798_, v_as_3799_, v_sz_3800_, v___x_3824_, v___x_3822_, v___y_3803_, v___y_3804_);
return v___x_3825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12___boxed(lean_object* v_id_3869_, lean_object* v_danglingDot_3870_, lean_object* v_as_3871_, lean_object* v_sz_3872_, lean_object* v_i_3873_, lean_object* v_b_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_){
_start:
{
uint8_t v_danglingDot_boxed_3883_; size_t v_sz_boxed_3884_; size_t v_i_boxed_3885_; lean_object* v_res_3886_; 
v_danglingDot_boxed_3883_ = lean_unbox(v_danglingDot_3870_);
v_sz_boxed_3884_ = lean_unbox_usize(v_sz_3872_);
lean_dec(v_sz_3872_);
v_i_boxed_3885_ = lean_unbox_usize(v_i_3873_);
lean_dec(v_i_3873_);
v_res_3886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12(v_id_3869_, v_danglingDot_boxed_3883_, v_as_3871_, v_sz_boxed_3884_, v_i_boxed_3885_, v_b_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec_ref(v_as_3871_);
lean_dec(v_id_3869_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(lean_object* v_id_3887_, uint8_t v_danglingDot_3888_, lean_object* v_t_3889_, lean_object* v_init_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v_b_3900_; lean_object* v_root_3903_; lean_object* v_tail_3904_; lean_object* v___x_3905_; 
v_root_3903_ = lean_ctor_get(v_t_3889_, 0);
v_tail_3904_ = lean_ctor_get(v_t_3889_, 1);
v___x_3905_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(v_init_3890_, v_id_3887_, v_danglingDot_3888_, v_root_3903_, v_init_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3967_; 
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3908_ = v___x_3905_;
v_isShared_3909_ = v_isSharedCheck_3967_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3905_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3967_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
if (lean_obj_tag(v_a_3906_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3920_; 
v_a_3910_ = lean_ctor_get(v_a_3906_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v_a_3906_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3912_ = v_a_3906_;
v_isShared_3913_ = v_isSharedCheck_3920_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v_a_3906_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3920_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3915_; 
if (v_isShared_3913_ == 0)
{
v___x_3915_ = v___x_3912_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3910_);
v___x_3915_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
lean_object* v___x_3917_; 
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v___x_3915_);
v___x_3917_ = v___x_3908_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3915_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
else
{
lean_object* v_a_3921_; 
lean_del_object(v___x_3908_);
v_a_3921_ = lean_ctor_get(v_a_3906_, 0);
lean_inc(v_a_3921_);
lean_dec_ref_known(v_a_3906_, 1);
if (lean_obj_tag(v_a_3921_) == 0)
{
lean_object* v_a_3922_; 
v_a_3922_ = lean_ctor_get(v_a_3921_, 0);
lean_inc(v_a_3922_);
lean_dec_ref_known(v_a_3921_, 1);
v_b_3900_ = v_a_3922_;
goto v___jp_3899_;
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; size_t v_sz_3926_; size_t v___x_3927_; lean_object* v___x_3928_; 
v_a_3923_ = lean_ctor_get(v_a_3921_, 0);
lean_inc(v_a_3923_);
lean_dec_ref_known(v_a_3921_, 1);
v___x_3924_ = lean_box(0);
v___x_3925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
lean_ctor_set(v___x_3925_, 1, v_a_3923_);
v_sz_3926_ = lean_array_size(v_tail_3904_);
v___x_3927_ = ((size_t)0ULL);
v___x_3928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12(v_id_3887_, v_danglingDot_3888_, v_tail_3904_, v_sz_3926_, v___x_3927_, v___x_3925_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3958_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3931_ = v___x_3928_;
v_isShared_3932_ = v_isSharedCheck_3958_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3928_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3958_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
if (lean_obj_tag(v_a_3929_) == 0)
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3943_; 
v_a_3933_ = lean_ctor_get(v_a_3929_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v_a_3929_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3935_ = v_a_3929_;
v_isShared_3936_ = v_isSharedCheck_3943_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v_a_3929_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3943_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3933_);
v___x_3938_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
lean_object* v___x_3940_; 
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 0, v___x_3938_);
v___x_3940_ = v___x_3931_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v___x_3938_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
else
{
lean_object* v_a_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3957_; 
v_a_3944_ = lean_ctor_get(v_a_3929_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v_a_3929_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3946_ = v_a_3929_;
v_isShared_3947_ = v_isSharedCheck_3957_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_a_3944_);
lean_dec(v_a_3929_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3957_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v_fst_3948_; 
v_fst_3948_ = lean_ctor_get(v_a_3944_, 0);
if (lean_obj_tag(v_fst_3948_) == 0)
{
lean_object* v_snd_3949_; lean_object* v___x_3951_; 
v_snd_3949_ = lean_ctor_get(v_a_3944_, 1);
lean_inc(v_snd_3949_);
lean_dec(v_a_3944_);
if (v_isShared_3947_ == 0)
{
lean_ctor_set(v___x_3946_, 0, v_snd_3949_);
v___x_3951_ = v___x_3946_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_snd_3949_);
v___x_3951_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
lean_object* v___x_3953_; 
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 0, v___x_3951_);
v___x_3953_ = v___x_3931_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v___x_3951_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
else
{
lean_object* v_val_3956_; 
lean_inc_ref(v_fst_3948_);
lean_del_object(v___x_3946_);
lean_dec(v_a_3944_);
lean_del_object(v___x_3931_);
v_val_3956_ = lean_ctor_get(v_fst_3948_, 0);
lean_inc(v_val_3956_);
lean_dec_ref_known(v_fst_3948_, 1);
v_b_3900_ = v_val_3956_;
goto v___jp_3899_;
}
}
}
}
}
else
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3966_; 
v_a_3959_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3961_ = v___x_3928_;
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3928_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_a_3959_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3975_; 
v_a_3968_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3970_ = v___x_3905_;
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3905_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3973_; 
if (v_isShared_3971_ == 0)
{
v___x_3973_ = v___x_3970_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_a_3968_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
v___jp_3899_:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3901_, 0, v_b_3900_);
v___x_3902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3901_);
return v___x_3902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6___boxed(lean_object* v_id_3976_, lean_object* v_danglingDot_3977_, lean_object* v_t_3978_, lean_object* v_init_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
uint8_t v_danglingDot_boxed_3988_; lean_object* v_res_3989_; 
v_danglingDot_boxed_3988_ = lean_unbox(v_danglingDot_3977_);
v_res_3989_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(v_id_3976_, v_danglingDot_boxed_3988_, v_t_3978_, v_init_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec_ref(v_t_3978_);
lean_dec(v_id_3976_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(lean_object* v_as_3990_, size_t v_sz_3991_, size_t v_i_3992_, lean_object* v_b_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
uint8_t v___x_3997_; 
v___x_3997_ = lean_usize_dec_lt(v_i_3992_, v_sz_3991_);
if (v___x_3997_ == 0)
{
lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3998_, 0, v_b_3993_);
v___x_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3998_);
return v___x_3999_;
}
else
{
lean_object* v_a_4000_; lean_object* v___x_4001_; 
v_a_4000_ = lean_array_uget_borrowed(v_as_3990_, v_i_3992_);
lean_inc(v_a_4000_);
v___x_4001_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg(v_a_4000_, v___y_3994_, v___y_3995_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_a_4002_; 
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc(v_a_4002_);
if (lean_obj_tag(v_a_4002_) == 0)
{
lean_dec_ref_known(v_a_4002_, 1);
return v___x_4001_;
}
else
{
lean_object* v___x_4003_; size_t v___x_4004_; size_t v___x_4005_; 
lean_dec_ref_known(v_a_4002_, 1);
lean_dec_ref_known(v___x_4001_, 1);
v___x_4003_ = lean_box(0);
v___x_4004_ = ((size_t)1ULL);
v___x_4005_ = lean_usize_add(v_i_3992_, v___x_4004_);
v_i_3992_ = v___x_4005_;
v_b_3993_ = v___x_4003_;
goto _start;
}
}
else
{
return v___x_4001_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg___boxed(lean_object* v_as_4007_, lean_object* v_sz_4008_, lean_object* v_i_4009_, lean_object* v_b_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
size_t v_sz_boxed_4014_; size_t v_i_boxed_4015_; lean_object* v_res_4016_; 
v_sz_boxed_4014_ = lean_unbox_usize(v_sz_4008_);
lean_dec(v_sz_4008_);
v_i_boxed_4015_ = lean_unbox_usize(v_i_4009_);
lean_dec(v_i_4009_);
v_res_4016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(v_as_4007_, v_sz_boxed_4014_, v_i_boxed_4015_, v_b_4010_, v___y_4011_, v___y_4012_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec_ref(v_as_4007_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0(lean_object* v___x_4017_, lean_object* v_a_4018_, lean_object* v___x_4019_, lean_object* v_ns_4020_, lean_object* v_id_4021_, uint8_t v_danglingDot_4022_, lean_object* v_alias_4023_, lean_object* v_declNames_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
uint8_t v___y_4034_; uint8_t v___x_4038_; 
v___x_4038_ = l_Lean_Name_isPrefixOf(v_ns_4020_, v_alias_4023_);
if (v___x_4038_ == 0)
{
v___y_4034_ = v___x_4038_;
goto v___jp_4033_;
}
else
{
lean_object* v___x_4039_; lean_object* v___x_4040_; uint8_t v___x_4041_; 
v___x_4039_ = lean_box(0);
lean_inc(v_alias_4023_);
v___x_4040_ = l_Lean_Name_replacePrefix(v_alias_4023_, v_ns_4020_, v___x_4039_);
v___x_4041_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_4021_, v___x_4040_, v_danglingDot_4022_);
lean_dec(v___x_4040_);
v___y_4034_ = v___x_4041_;
goto v___jp_4033_;
}
v___jp_4033_:
{
if (v___y_4034_ == 0)
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
lean_dec(v_declNames_4024_);
lean_dec(v_alias_4023_);
lean_dec_ref(v___x_4019_);
v___x_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4017_);
v___x_4036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4035_);
return v___x_4036_;
}
else
{
lean_object* v___x_4037_; 
v___x_4037_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_4018_, v___x_4019_, v_alias_4023_, v_declNames_4024_, v___y_4025_, v___y_4026_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
lean_dec(v_alias_4023_);
return v___x_4037_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed(lean_object* v___x_4042_, lean_object* v_a_4043_, lean_object* v___x_4044_, lean_object* v_ns_4045_, lean_object* v_id_4046_, lean_object* v_danglingDot_4047_, lean_object* v_alias_4048_, lean_object* v_declNames_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
uint8_t v_danglingDot_boxed_4058_; lean_object* v_res_4059_; 
v_danglingDot_boxed_4058_ = lean_unbox(v_danglingDot_4047_);
v_res_4059_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0(v___x_4042_, v_a_4043_, v___x_4044_, v_ns_4045_, v_id_4046_, v_danglingDot_boxed_4058_, v_alias_4048_, v_declNames_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
lean_dec(v___y_4056_);
lean_dec_ref(v___y_4055_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec_ref(v___y_4052_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec(v_id_4046_);
lean_dec(v_ns_4045_);
lean_dec_ref(v_a_4043_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(lean_object* v_a_4060_, lean_object* v___x_4061_, lean_object* v_id_4062_, uint8_t v_danglingDot_4063_, lean_object* v_as_x27_4064_, lean_object* v_b_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
lean_object* v_a_4075_; 
if (lean_obj_tag(v_as_x27_4064_) == 0)
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
lean_dec(v_id_4062_);
lean_dec_ref(v___x_4061_);
lean_dec_ref(v_a_4060_);
v___x_4078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4078_, 0, v_b_4065_);
v___x_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
return v___x_4079_;
}
else
{
lean_object* v_head_4080_; lean_object* v_tail_4081_; lean_object* v___x_4082_; 
v_head_4080_ = lean_ctor_get(v_as_x27_4064_, 0);
v_tail_4081_ = lean_ctor_get(v_as_x27_4064_, 1);
v___x_4082_ = lean_box(0);
if (lean_obj_tag(v_head_4080_) == 0)
{
lean_object* v_ns_4083_; lean_object* v___x_4084_; lean_object* v___f_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v_ns_4083_ = lean_ctor_get(v_head_4080_, 0);
v___x_4084_ = lean_box(v_danglingDot_4063_);
lean_inc(v_id_4062_);
lean_inc(v_ns_4083_);
lean_inc_ref_n(v___x_4061_, 2);
lean_inc_ref(v_a_4060_);
v___f_4085_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed), 16, 6);
lean_closure_set(v___f_4085_, 0, v___x_4082_);
lean_closure_set(v___f_4085_, 1, v_a_4060_);
lean_closure_set(v___f_4085_, 2, v___x_4061_);
lean_closure_set(v___f_4085_, 3, v_ns_4083_);
lean_closure_set(v___f_4085_, 4, v_id_4062_);
lean_closure_set(v___f_4085_, 5, v___x_4084_);
v___x_4086_ = l_Lean_getAliasState(v___x_4061_);
v___x_4087_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v___x_4086_, v___f_4085_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v_a_4088_; 
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
lean_inc(v_a_4088_);
lean_dec_ref_known(v___x_4087_, 1);
if (lean_obj_tag(v_a_4088_) == 0)
{
lean_object* v_a_4089_; 
lean_dec(v_id_4062_);
lean_dec_ref(v___x_4061_);
lean_dec_ref(v_a_4060_);
v_a_4089_ = lean_ctor_get(v_a_4088_, 0);
lean_inc(v_a_4089_);
lean_dec_ref_known(v_a_4088_, 1);
v_a_4075_ = v_a_4089_;
goto v___jp_4074_;
}
else
{
lean_dec_ref_known(v_a_4088_, 1);
v_as_x27_4064_ = v_tail_4081_;
v_b_4065_ = v___x_4082_;
goto _start;
}
}
else
{
lean_dec(v_id_4062_);
lean_dec_ref(v___x_4061_);
lean_dec_ref(v_a_4060_);
return v___x_4087_;
}
}
else
{
lean_object* v_id_4091_; lean_object* v_declName_4092_; uint8_t v___x_4093_; 
v_id_4091_ = lean_ctor_get(v_head_4080_, 0);
v_declName_4092_ = lean_ctor_get(v_head_4080_, 1);
lean_inc(v_declName_4092_);
lean_inc_ref(v___x_4061_);
v___x_4093_ = l_Lean_Server_Completion_allowCompletion(v_a_4060_, v___x_4061_, v_declName_4092_);
if (v___x_4093_ == 0)
{
v_as_x27_4064_ = v_tail_4081_;
v_b_4065_ = v___x_4082_;
goto _start;
}
else
{
uint8_t v___x_4095_; 
v___x_4095_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_4062_, v_id_4091_, v_danglingDot_4063_);
if (v___x_4095_ == 0)
{
v_as_x27_4064_ = v_tail_4081_;
v_b_4065_ = v___x_4082_;
goto _start;
}
else
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4097_ = l_Lean_Name_getString_x21(v_id_4091_);
v___x_4098_ = lean_box(0);
v___x_4099_ = l_Lean_Name_str___override(v___x_4098_, v___x_4097_);
lean_inc(v_declName_4092_);
v___x_4100_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_4099_, v_declName_4092_, v___y_4066_, v___y_4067_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_dec_ref_known(v___x_4100_, 1);
v_as_x27_4064_ = v_tail_4081_;
v_b_4065_ = v___x_4082_;
goto _start;
}
else
{
lean_dec(v_id_4062_);
lean_dec_ref(v___x_4061_);
lean_dec_ref(v_a_4060_);
return v___x_4100_;
}
}
}
}
}
v___jp_4074_:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4076_, 0, v_a_4075_);
v___x_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
return v___x_4077_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg___boxed(lean_object* v_a_4102_, lean_object* v___x_4103_, lean_object* v_id_4104_, lean_object* v_danglingDot_4105_, lean_object* v_as_x27_4106_, lean_object* v_b_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
uint8_t v_danglingDot_boxed_4116_; lean_object* v_res_4117_; 
v_danglingDot_boxed_4116_ = lean_unbox(v_danglingDot_4105_);
v_res_4117_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4102_, v___x_4103_, v_id_4104_, v_danglingDot_boxed_4116_, v_as_x27_4106_, v_b_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec_ref(v___y_4110_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
lean_dec(v_as_x27_4106_);
return v_res_4117_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(lean_object* v_id_4118_, uint8_t v_danglingDot_4119_, lean_object* v_a_4120_, lean_object* v___x_4121_, lean_object* v_as_4122_, lean_object* v_as_x27_4123_, lean_object* v_b_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v_a_4134_; 
if (lean_obj_tag(v_as_x27_4123_) == 0)
{
lean_object* v___x_4137_; lean_object* v___x_4138_; 
lean_dec_ref(v___x_4121_);
lean_dec_ref(v_a_4120_);
lean_dec(v_id_4118_);
v___x_4137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4137_, 0, v_b_4124_);
v___x_4138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4137_);
return v___x_4138_;
}
else
{
lean_object* v_head_4139_; lean_object* v_tail_4140_; lean_object* v___x_4141_; 
v_head_4139_ = lean_ctor_get(v_as_x27_4123_, 0);
v_tail_4140_ = lean_ctor_get(v_as_x27_4123_, 1);
v___x_4141_ = lean_box(0);
if (lean_obj_tag(v_head_4139_) == 0)
{
lean_object* v_ns_4142_; lean_object* v___x_4143_; lean_object* v___f_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v_ns_4142_ = lean_ctor_get(v_head_4139_, 0);
v___x_4143_ = lean_box(v_danglingDot_4119_);
lean_inc(v_id_4118_);
lean_inc(v_ns_4142_);
lean_inc_ref_n(v___x_4121_, 2);
lean_inc_ref(v_a_4120_);
v___f_4144_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed), 16, 6);
lean_closure_set(v___f_4144_, 0, v___x_4141_);
lean_closure_set(v___f_4144_, 1, v_a_4120_);
lean_closure_set(v___f_4144_, 2, v___x_4121_);
lean_closure_set(v___f_4144_, 3, v_ns_4142_);
lean_closure_set(v___f_4144_, 4, v_id_4118_);
lean_closure_set(v___f_4144_, 5, v___x_4143_);
v___x_4145_ = l_Lean_getAliasState(v___x_4121_);
v___x_4146_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v___x_4145_, v___f_4144_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
if (lean_obj_tag(v___x_4146_) == 0)
{
lean_object* v_a_4147_; 
v_a_4147_ = lean_ctor_get(v___x_4146_, 0);
lean_inc(v_a_4147_);
lean_dec_ref_known(v___x_4146_, 1);
if (lean_obj_tag(v_a_4147_) == 0)
{
lean_object* v_a_4148_; 
lean_dec_ref(v___x_4121_);
lean_dec_ref(v_a_4120_);
lean_dec(v_id_4118_);
v_a_4148_ = lean_ctor_get(v_a_4147_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v_a_4147_, 1);
v_a_4134_ = v_a_4148_;
goto v___jp_4133_;
}
else
{
lean_object* v___x_4149_; 
lean_dec_ref_known(v_a_4147_, 1);
v___x_4149_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4120_, v___x_4121_, v_id_4118_, v_danglingDot_4119_, v_tail_4140_, v___x_4141_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
return v___x_4149_;
}
}
else
{
lean_dec_ref(v___x_4121_);
lean_dec_ref(v_a_4120_);
lean_dec(v_id_4118_);
return v___x_4146_;
}
}
else
{
lean_object* v_id_4150_; lean_object* v_declName_4151_; uint8_t v___x_4152_; 
v_id_4150_ = lean_ctor_get(v_head_4139_, 0);
v_declName_4151_ = lean_ctor_get(v_head_4139_, 1);
lean_inc(v_declName_4151_);
lean_inc_ref(v___x_4121_);
v___x_4152_ = l_Lean_Server_Completion_allowCompletion(v_a_4120_, v___x_4121_, v_declName_4151_);
if (v___x_4152_ == 0)
{
lean_object* v___x_4153_; 
v___x_4153_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4120_, v___x_4121_, v_id_4118_, v_danglingDot_4119_, v_tail_4140_, v___x_4141_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
return v___x_4153_;
}
else
{
uint8_t v___x_4154_; 
v___x_4154_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_4118_, v_id_4150_, v_danglingDot_4119_);
if (v___x_4154_ == 0)
{
lean_object* v___x_4155_; 
v___x_4155_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4120_, v___x_4121_, v_id_4118_, v_danglingDot_4119_, v_tail_4140_, v___x_4141_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
return v___x_4155_;
}
else
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4156_ = l_Lean_Name_getString_x21(v_id_4150_);
v___x_4157_ = lean_box(0);
v___x_4158_ = l_Lean_Name_str___override(v___x_4157_, v___x_4156_);
lean_inc(v_declName_4151_);
v___x_4159_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_4158_, v_declName_4151_, v___y_4125_, v___y_4126_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v___x_4160_; 
lean_dec_ref_known(v___x_4159_, 1);
v___x_4160_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4120_, v___x_4121_, v_id_4118_, v_danglingDot_4119_, v_tail_4140_, v___x_4141_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
return v___x_4160_;
}
else
{
lean_dec_ref(v___x_4121_);
lean_dec_ref(v_a_4120_);
lean_dec(v_id_4118_);
return v___x_4159_;
}
}
}
}
}
v___jp_4133_:
{
lean_object* v___x_4135_; lean_object* v___x_4136_; 
v___x_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4135_, 0, v_a_4134_);
v___x_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4135_);
return v___x_4136_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___boxed(lean_object* v_id_4161_, lean_object* v_danglingDot_4162_, lean_object* v_a_4163_, lean_object* v___x_4164_, lean_object* v_as_4165_, lean_object* v_as_x27_4166_, lean_object* v_b_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_){
_start:
{
uint8_t v_danglingDot_boxed_4176_; lean_object* v_res_4177_; 
v_danglingDot_boxed_4176_ = lean_unbox(v_danglingDot_4162_);
v_res_4177_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v_id_4161_, v_danglingDot_boxed_4176_, v_a_4163_, v___x_4164_, v_as_4165_, v_as_x27_4166_, v_b_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
lean_dec(v_as_x27_4166_);
lean_dec(v_as_4165_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(lean_object* v_ctx_4178_, lean_object* v_stx_4179_, lean_object* v_id_4180_, lean_object* v_hoverInfo_4181_, uint8_t v_danglingDot_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_){
_start:
{
lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; uint8_t v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v_id_4244_; uint8_t v_danglingDot_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v_id_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; uint8_t v___x_4275_; 
v___x_4275_ = l_Lean_Name_hasMacroScopes(v_id_4180_);
if (v___x_4275_ == 0)
{
v_id_4264_ = v_id_4180_;
v___y_4265_ = v_a_4183_;
v___y_4266_ = v_a_4184_;
v___y_4267_ = v_a_4185_;
v___y_4268_ = v_a_4186_;
v___y_4269_ = v_a_4187_;
v___y_4270_ = v_a_4188_;
v___y_4271_ = v_a_4189_;
goto v___jp_4263_;
}
else
{
lean_object* v___x_4276_; 
v___x_4276_ = l_Lean_Syntax_getHeadInfo(v_stx_4179_);
if (lean_obj_tag(v___x_4276_) == 0)
{
lean_object* v_id_4277_; 
lean_dec_ref_known(v___x_4276_, 4);
v_id_4277_ = l_Lean_Name_eraseMacroScopes(v_id_4180_);
lean_dec(v_id_4180_);
v_id_4264_ = v_id_4277_;
v___y_4265_ = v_a_4183_;
v___y_4266_ = v_a_4184_;
v___y_4267_ = v_a_4185_;
v___y_4268_ = v_a_4186_;
v___y_4269_ = v_a_4187_;
v___y_4270_ = v_a_4188_;
v___y_4271_ = v_a_4189_;
goto v___jp_4263_;
}
else
{
lean_object* v___x_4278_; lean_object* v___x_4279_; 
lean_dec(v___x_4276_);
lean_dec(v_hoverInfo_4181_);
lean_dec(v_id_4180_);
lean_dec_ref(v_ctx_4178_);
v___x_4278_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_4279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4278_);
return v___x_4279_;
}
}
v___jp_4191_:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4203_ = lean_st_ref_get(v___y_4198_);
v___x_4204_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___y_4200_, v___y_4202_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4196_, v___y_4201_, v___y_4198_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
lean_inc(v_a_4205_);
if (lean_obj_tag(v_a_4205_) == 0)
{
lean_dec_ref_known(v_a_4205_, 1);
lean_dec(v___x_4203_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4195_);
lean_dec_ref(v_ctx_4178_);
return v___x_4204_;
}
else
{
lean_object* v___x_4206_; lean_object* v_a_4207_; 
lean_dec_ref_known(v_a_4205_, 1);
lean_dec_ref_known(v___x_4204_, 1);
v___x_4206_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v___y_4193_);
v_a_4207_ = lean_ctor_get(v___x_4206_, 0);
lean_inc(v_a_4207_);
if (lean_obj_tag(v_a_4207_) == 0)
{
lean_dec_ref_known(v_a_4207_, 1);
lean_dec(v___x_4203_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4195_);
lean_dec_ref(v_ctx_4178_);
return v___x_4206_;
}
else
{
lean_object* v_env_4208_; lean_object* v___x_4209_; 
lean_dec_ref_known(v_a_4207_, 1);
lean_dec_ref(v___x_4206_);
v_env_4208_ = lean_ctor_get(v___x_4203_, 0);
lean_inc_ref_n(v_env_4208_, 2);
lean_dec(v___x_4203_);
v___x_4209_ = l_Lean_Server_Completion_getEligibleHeaderDecls(v_env_4208_, v___y_4194_, v___y_4196_, v___y_4201_, v___y_4198_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v_toCommandContextInfo_4210_; lean_object* v_a_4211_; lean_object* v_currNamespace_4212_; lean_object* v_openDecls_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v_toCommandContextInfo_4210_ = lean_ctor_get(v_ctx_4178_, 0);
v_a_4211_ = lean_ctor_get(v___x_4209_, 0);
lean_inc_n(v_a_4211_, 2);
lean_dec_ref_known(v___x_4209_, 1);
v_currNamespace_4212_ = lean_ctor_get(v_toCommandContextInfo_4210_, 5);
v_openDecls_4213_ = lean_ctor_get(v_toCommandContextInfo_4210_, 6);
v___x_4214_ = lean_box(0);
lean_inc_ref(v_env_4208_);
lean_inc(v___y_4195_);
v___x_4215_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v___y_4195_, v___y_4197_, v_a_4211_, v_env_4208_, v_openDecls_4213_, v_openDecls_4213_, v___x_4214_, v___y_4202_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4196_, v___y_4201_, v___y_4198_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v_a_4216_; 
v_a_4216_ = lean_ctor_get(v___x_4215_, 0);
lean_inc(v_a_4216_);
if (lean_obj_tag(v_a_4216_) == 0)
{
lean_dec_ref_known(v_a_4216_, 1);
lean_dec(v_a_4211_);
lean_dec_ref(v_env_4208_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4195_);
lean_dec_ref(v_ctx_4178_);
return v___x_4215_;
}
else
{
lean_object* v___f_4217_; lean_object* v___f_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; 
lean_dec_ref_known(v_a_4216_, 1);
lean_dec_ref_known(v___x_4215_, 1);
lean_inc_ref_n(v_env_4208_, 2);
v___f_4217_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2___boxed), 12, 2);
lean_closure_set(v___f_4217_, 0, v_a_4211_);
lean_closure_set(v___f_4217_, 1, v_env_4208_);
lean_inc(v_currNamespace_4212_);
v___f_4218_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3___boxed), 13, 3);
lean_closure_set(v___f_4218_, 0, v___y_4199_);
lean_closure_set(v___f_4218_, 1, v___f_4217_);
lean_closure_set(v___f_4218_, 2, v_currNamespace_4212_);
v___x_4219_ = l_Lean_getAliasState(v_env_4208_);
v___x_4220_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v___x_4219_, v___f_4218_, v___y_4202_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4196_, v___y_4201_, v___y_4198_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_a_4221_; 
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
lean_inc(v_a_4221_);
if (lean_obj_tag(v_a_4221_) == 0)
{
lean_dec_ref_known(v_a_4221_, 1);
lean_dec_ref(v_env_4208_);
lean_dec(v___y_4195_);
lean_dec_ref(v_ctx_4178_);
return v___x_4220_;
}
else
{
uint8_t v___x_4222_; 
lean_dec_ref_known(v_a_4221_, 1);
lean_dec_ref_known(v___x_4220_, 1);
v___x_4222_ = lean_bool_not(v___y_4197_);
if (v___x_4222_ == 0)
{
lean_object* v___x_4223_; 
lean_dec_ref(v_env_4208_);
v___x_4223_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4178_, v___y_4195_, v___y_4197_, v___y_4202_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4196_, v___y_4201_, v___y_4198_);
return v___x_4223_;
}
else
{
if (lean_obj_tag(v___y_4195_) == 1)
{
lean_object* v_pre_4224_; 
v_pre_4224_ = lean_ctor_get(v___y_4195_, 0);
if (lean_obj_tag(v_pre_4224_) == 0)
{
lean_object* v_str_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; size_t v_sz_4228_; size_t v___x_4229_; lean_object* v___x_4230_; 
v_str_4225_ = lean_ctor_get(v___y_4195_, 1);
v___x_4226_ = l_Lean_Parser_getTokenTable(v_env_4208_);
v___x_4227_ = l_Lean_Data_Trie_findPrefix___redArg(v___x_4226_, v_str_4225_);
lean_dec_ref(v___x_4226_);
v_sz_4228_ = lean_array_size(v___x_4227_);
v___x_4229_ = ((size_t)0ULL);
v___x_4230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(v___x_4227_, v_sz_4228_, v___x_4229_, v___x_4214_, v___y_4202_, v___y_4192_);
lean_dec_ref(v___x_4227_);
if (lean_obj_tag(v___x_4230_) == 0)
{
lean_object* v_a_4231_; 
v_a_4231_ = lean_ctor_get(v___x_4230_, 0);
lean_inc(v_a_4231_);
if (lean_obj_tag(v_a_4231_) == 0)
{
lean_dec_ref_known(v_a_4231_, 1);
lean_dec_ref_known(v___y_4195_, 2);
lean_dec_ref(v_ctx_4178_);
return v___x_4230_;
}
else
{
lean_object* v___x_4232_; 
lean_dec_ref_known(v_a_4231_, 1);
lean_dec_ref_known(v___x_4230_, 1);
v___x_4232_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4178_, v___y_4195_, v___y_4197_, v___y_4202_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4196_, v___y_4201_, v___y_4198_);
return v___x_4232_;
}
}
else
{
lean_dec_ref_known(v___y_4195_, 2);
lean_dec_ref(v_ctx_4178_);
return v___x_4230_;
}
}
else
{
lean_object* v___x_4233_; 
lean_dec_ref(v_env_4208_);
v___x_4233_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4178_, v___y_4195_, v___y_4197_, v___y_4202_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4196_, v___y_4201_, v___y_4198_);
return v___x_4233_;
}
}
else
{
lean_object* v___x_4234_; 
lean_dec_ref(v_env_4208_);
v___x_4234_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4178_, v___y_4195_, v___y_4197_, v___y_4202_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4196_, v___y_4201_, v___y_4198_);
return v___x_4234_;
}
}
}
}
else
{
lean_dec_ref(v_env_4208_);
lean_dec(v___y_4195_);
lean_dec_ref(v_ctx_4178_);
return v___x_4220_;
}
}
}
else
{
lean_dec(v_a_4211_);
lean_dec_ref(v_env_4208_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4195_);
lean_dec_ref(v_ctx_4178_);
return v___x_4215_;
}
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
lean_dec_ref(v_env_4208_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4195_);
lean_dec_ref(v_ctx_4178_);
v_a_4235_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4209_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4209_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
}
}
else
{
lean_dec(v___x_4203_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4195_);
lean_dec_ref(v_ctx_4178_);
return v___x_4204_;
}
}
v___jp_4243_:
{
lean_object* v___x_4253_; lean_object* v___f_4254_; lean_object* v___x_4255_; lean_object* v___f_4256_; uint8_t v___x_4257_; 
v___x_4253_ = lean_box(v_danglingDot_4245_);
lean_inc_n(v_id_4244_, 2);
lean_inc_ref(v_ctx_4178_);
v___f_4254_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0___boxed), 13, 3);
lean_closure_set(v___f_4254_, 0, v_ctx_4178_);
lean_closure_set(v___f_4254_, 1, v_id_4244_);
lean_closure_set(v___f_4254_, 2, v___x_4253_);
v___x_4255_ = lean_box(v_danglingDot_4245_);
v___f_4256_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4256_, 0, v_id_4244_);
lean_closure_set(v___f_4256_, 1, v___x_4255_);
v___x_4257_ = l_Lean_Name_isAtomic(v_id_4244_);
if (v___x_4257_ == 0)
{
v___y_4192_ = v___y_4247_;
v___y_4193_ = v___y_4248_;
v___y_4194_ = v___y_4249_;
v___y_4195_ = v_id_4244_;
v___y_4196_ = v___y_4250_;
v___y_4197_ = v_danglingDot_4245_;
v___y_4198_ = v___y_4252_;
v___y_4199_ = v___f_4256_;
v___y_4200_ = v___f_4254_;
v___y_4201_ = v___y_4251_;
v___y_4202_ = v___y_4246_;
goto v___jp_4191_;
}
else
{
lean_object* v_lctx_4258_; lean_object* v_decls_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v_lctx_4258_ = lean_ctor_get(v___y_4249_, 2);
v_decls_4259_ = lean_ctor_get(v_lctx_4258_, 1);
v___x_4260_ = lean_box(0);
v___x_4261_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(v_id_4244_, v_danglingDot_4245_, v_decls_4259_, v___x_4260_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v_a_4262_; 
v_a_4262_ = lean_ctor_get(v___x_4261_, 0);
lean_inc(v_a_4262_);
if (lean_obj_tag(v_a_4262_) == 0)
{
lean_dec_ref_known(v_a_4262_, 1);
lean_dec_ref(v___f_4256_);
lean_dec_ref(v___f_4254_);
lean_dec(v_id_4244_);
lean_dec_ref(v_ctx_4178_);
return v___x_4261_;
}
else
{
lean_dec_ref_known(v_a_4262_, 1);
lean_dec_ref_known(v___x_4261_, 1);
v___y_4192_ = v___y_4247_;
v___y_4193_ = v___y_4248_;
v___y_4194_ = v___y_4249_;
v___y_4195_ = v_id_4244_;
v___y_4196_ = v___y_4250_;
v___y_4197_ = v_danglingDot_4245_;
v___y_4198_ = v___y_4252_;
v___y_4199_ = v___f_4256_;
v___y_4200_ = v___f_4254_;
v___y_4201_ = v___y_4251_;
v___y_4202_ = v___y_4246_;
goto v___jp_4191_;
}
}
else
{
lean_dec_ref(v___f_4256_);
lean_dec_ref(v___f_4254_);
lean_dec(v_id_4244_);
lean_dec_ref(v_ctx_4178_);
return v___x_4261_;
}
}
}
v___jp_4263_:
{
if (lean_obj_tag(v_hoverInfo_4181_) == 1)
{
lean_object* v_delta_4272_; lean_object* v_id_4273_; uint8_t v_danglingDot_4274_; 
v_delta_4272_ = lean_ctor_get(v_hoverInfo_4181_, 0);
lean_inc(v_delta_4272_);
lean_dec_ref_known(v_hoverInfo_4181_, 1);
v_id_4273_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate(v_id_4264_, v_delta_4272_);
v_danglingDot_4274_ = 0;
v_id_4244_ = v_id_4273_;
v_danglingDot_4245_ = v_danglingDot_4274_;
v___y_4246_ = v___y_4265_;
v___y_4247_ = v___y_4266_;
v___y_4248_ = v___y_4267_;
v___y_4249_ = v___y_4268_;
v___y_4250_ = v___y_4269_;
v___y_4251_ = v___y_4270_;
v___y_4252_ = v___y_4271_;
goto v___jp_4243_;
}
else
{
lean_dec(v_hoverInfo_4181_);
v_id_4244_ = v_id_4264_;
v_danglingDot_4245_ = v_danglingDot_4182_;
v___y_4246_ = v___y_4265_;
v___y_4247_ = v___y_4266_;
v___y_4248_ = v___y_4267_;
v___y_4249_ = v___y_4268_;
v___y_4250_ = v___y_4269_;
v___y_4251_ = v___y_4270_;
v___y_4252_ = v___y_4271_;
goto v___jp_4243_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___boxed(lean_object* v_ctx_4280_, lean_object* v_stx_4281_, lean_object* v_id_4282_, lean_object* v_hoverInfo_4283_, lean_object* v_danglingDot_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_){
_start:
{
uint8_t v_danglingDot_boxed_4293_; lean_object* v_res_4294_; 
v_danglingDot_boxed_4293_ = lean_unbox(v_danglingDot_4284_);
v_res_4294_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(v_ctx_4280_, v_stx_4281_, v_id_4282_, v_hoverInfo_4283_, v_danglingDot_boxed_4293_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_);
lean_dec(v_a_4291_);
lean_dec_ref(v_a_4290_);
lean_dec(v_a_4289_);
lean_dec_ref(v_a_4288_);
lean_dec_ref(v_a_4287_);
lean_dec(v_a_4286_);
lean_dec_ref(v_a_4285_);
lean_dec(v_stx_4281_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2(lean_object* v_a_4295_, lean_object* v___x_4296_, lean_object* v_alias_4297_, lean_object* v_as_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v___x_4307_; 
v___x_4307_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_4295_, v___x_4296_, v_alias_4297_, v_as_4298_, v___y_4299_, v___y_4300_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_);
return v___x_4307_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___boxed(lean_object* v_a_4308_, lean_object* v___x_4309_, lean_object* v_alias_4310_, lean_object* v_as_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2(v_a_4308_, v___x_4309_, v_alias_4310_, v_as_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4312_);
lean_dec(v_alias_4310_);
lean_dec_ref(v_a_4308_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3(lean_object* v_00_u03b2_4321_, lean_object* v_s_4322_, lean_object* v_f_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_){
_start:
{
lean_object* v___x_4332_; 
v___x_4332_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v_s_4322_, v_f_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_);
return v___x_4332_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___boxed(lean_object* v_00_u03b2_4333_, lean_object* v_s_4334_, lean_object* v_f_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3(v_00_u03b2_4333_, v_s_4334_, v_f_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4(lean_object* v_id_4345_, uint8_t v_danglingDot_4346_, lean_object* v_a_4347_, lean_object* v___x_4348_, lean_object* v_as_4349_, lean_object* v_as_x27_4350_, lean_object* v_b_4351_, lean_object* v_a_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_){
_start:
{
lean_object* v___x_4361_; 
v___x_4361_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v_id_4345_, v_danglingDot_4346_, v_a_4347_, v___x_4348_, v_as_4349_, v_as_x27_4350_, v_b_4351_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_);
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___boxed(lean_object* v_id_4362_, lean_object* v_danglingDot_4363_, lean_object* v_a_4364_, lean_object* v___x_4365_, lean_object* v_as_4366_, lean_object* v_as_x27_4367_, lean_object* v_b_4368_, lean_object* v_a_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
uint8_t v_danglingDot_boxed_4378_; lean_object* v_res_4379_; 
v_danglingDot_boxed_4378_ = lean_unbox(v_danglingDot_4363_);
v_res_4379_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4(v_id_4362_, v_danglingDot_boxed_4378_, v_a_4364_, v___x_4365_, v_as_4366_, v_as_x27_4367_, v_b_4368_, v_a_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
lean_dec(v___y_4376_);
lean_dec_ref(v___y_4375_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec_ref(v___y_4372_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v_as_x27_4367_);
lean_dec(v_as_4366_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5(lean_object* v_as_4380_, size_t v_sz_4381_, size_t v_i_4382_, lean_object* v_b_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
lean_object* v___x_4392_; 
v___x_4392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(v_as_4380_, v_sz_4381_, v_i_4382_, v_b_4383_, v___y_4384_, v___y_4385_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___boxed(lean_object* v_as_4393_, lean_object* v_sz_4394_, lean_object* v_i_4395_, lean_object* v_b_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
size_t v_sz_boxed_4405_; size_t v_i_boxed_4406_; lean_object* v_res_4407_; 
v_sz_boxed_4405_ = lean_unbox_usize(v_sz_4394_);
lean_dec(v_sz_4394_);
v_i_boxed_4406_ = lean_unbox_usize(v_i_4395_);
lean_dec(v_i_4395_);
v_res_4407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5(v_as_4393_, v_sz_boxed_4405_, v_i_boxed_4406_, v_b_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
lean_dec(v___y_4401_);
lean_dec_ref(v___y_4400_);
lean_dec_ref(v___y_4399_);
lean_dec(v___y_4398_);
lean_dec_ref(v___y_4397_);
lean_dec_ref(v_as_4393_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4(lean_object* v_00_u03b2_4408_, lean_object* v_f_4409_, lean_object* v_x_4410_, lean_object* v_x_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v___x_4420_; 
v___x_4420_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_f_4409_, v_x_4410_, v_x_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4421_, lean_object* v_f_4422_, lean_object* v_x_4423_, lean_object* v_x_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v_res_4433_; 
v_res_4433_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4(v_00_u03b2_4421_, v_f_4422_, v_x_4423_, v_x_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_dec_ref(v___y_4427_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
return v_res_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5(lean_object* v_00_u03b2_4434_, lean_object* v_map_4435_, lean_object* v_f_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_){
_start:
{
lean_object* v___x_4445_; 
v___x_4445_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_4435_, v_f_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4446_, lean_object* v_map_4447_, lean_object* v_f_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
lean_object* v_res_4457_; 
v_res_4457_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5(v_00_u03b2_4446_, v_map_4447_, v_f_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
return v_res_4457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6(lean_object* v_00_u03b2_4458_, lean_object* v_f_4459_, lean_object* v_as_4460_, size_t v_i_4461_, size_t v_stop_4462_, lean_object* v_b_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_){
_start:
{
lean_object* v___x_4472_; 
v___x_4472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(v_f_4459_, v_as_4460_, v_i_4461_, v_stop_4462_, v_b_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
return v___x_4472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___boxed(lean_object* v_00_u03b2_4473_, lean_object* v_f_4474_, lean_object* v_as_4475_, lean_object* v_i_4476_, lean_object* v_stop_4477_, lean_object* v_b_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_){
_start:
{
size_t v_i_boxed_4487_; size_t v_stop_boxed_4488_; lean_object* v_res_4489_; 
v_i_boxed_4487_ = lean_unbox_usize(v_i_4476_);
lean_dec(v_i_4476_);
v_stop_boxed_4488_ = lean_unbox_usize(v_stop_4477_);
lean_dec(v_stop_4477_);
v_res_4489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6(v_00_u03b2_4473_, v_f_4474_, v_as_4475_, v_i_boxed_4487_, v_stop_boxed_4488_, v_b_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_);
lean_dec(v___y_4485_);
lean_dec_ref(v___y_4484_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec_ref(v_as_4475_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8(lean_object* v_a_4490_, lean_object* v___x_4491_, lean_object* v_id_4492_, uint8_t v_danglingDot_4493_, lean_object* v_as_4494_, lean_object* v_as_x27_4495_, lean_object* v_b_4496_, lean_object* v_a_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
lean_object* v___x_4506_; 
v___x_4506_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4490_, v___x_4491_, v_id_4492_, v_danglingDot_4493_, v_as_x27_4495_, v_b_4496_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
return v___x_4506_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___boxed(lean_object* v_a_4507_, lean_object* v___x_4508_, lean_object* v_id_4509_, lean_object* v_danglingDot_4510_, lean_object* v_as_4511_, lean_object* v_as_x27_4512_, lean_object* v_b_4513_, lean_object* v_a_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
uint8_t v_danglingDot_boxed_4523_; lean_object* v_res_4524_; 
v_danglingDot_boxed_4523_ = lean_unbox(v_danglingDot_4510_);
v_res_4524_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8(v_a_4507_, v___x_4508_, v_id_4509_, v_danglingDot_boxed_4523_, v_as_4511_, v_as_x27_4512_, v_b_4513_, v_a_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec_ref(v___y_4517_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec(v_as_x27_4512_);
lean_dec(v_as_4511_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_4525_, lean_object* v_map_4526_, lean_object* v_f_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_){
_start:
{
lean_object* v___x_4537_; 
v___x_4537_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_4526_, v_f_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_4538_, lean_object* v_map_4539_, lean_object* v_f_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3(v_00_u03b2_4538_, v_map_4539_, v_f_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg(lean_object* v_map_4551_, lean_object* v_f_4552_, lean_object* v_init_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_){
_start:
{
lean_object* v___x_4562_; 
v___x_4562_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_4552_, v_map_4551_, v_init_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
return v___x_4562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_map_4563_, lean_object* v_f_4564_, lean_object* v_init_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg(v_map_4563_, v_f_4564_, v_init_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec_ref(v___y_4568_);
lean_dec(v___y_4567_);
lean_dec_ref(v___y_4566_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_4575_, lean_object* v_00_u03b2_4576_, lean_object* v_map_4577_, lean_object* v_f_4578_, lean_object* v_init_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_){
_start:
{
lean_object* v___x_4588_; 
v___x_4588_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_4578_, v_map_4577_, v_init_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
return v___x_4588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_4589_, lean_object* v_00_u03b2_4590_, lean_object* v_map_4591_, lean_object* v_f_4592_, lean_object* v_init_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9(v_00_u03c3_4589_, v_00_u03b2_4590_, v_map_4591_, v_f_4592_, v_init_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
lean_dec(v___y_4598_);
lean_dec_ref(v___y_4597_);
lean_dec_ref(v___y_4596_);
lean_dec(v___y_4595_);
lean_dec_ref(v___y_4594_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19(lean_object* v_id_4603_, uint8_t v_danglingDot_4604_, lean_object* v_as_4605_, size_t v_sz_4606_, size_t v_i_4607_, lean_object* v_b_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_){
_start:
{
lean_object* v___x_4617_; 
v___x_4617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(v_id_4603_, v_danglingDot_4604_, v_as_4605_, v_sz_4606_, v_i_4607_, v_b_4608_, v___y_4609_, v___y_4610_);
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___boxed(lean_object* v_id_4618_, lean_object* v_danglingDot_4619_, lean_object* v_as_4620_, lean_object* v_sz_4621_, lean_object* v_i_4622_, lean_object* v_b_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_){
_start:
{
uint8_t v_danglingDot_boxed_4632_; size_t v_sz_boxed_4633_; size_t v_i_boxed_4634_; lean_object* v_res_4635_; 
v_danglingDot_boxed_4632_ = lean_unbox(v_danglingDot_4619_);
v_sz_boxed_4633_ = lean_unbox_usize(v_sz_4621_);
lean_dec(v_sz_4621_);
v_i_boxed_4634_ = lean_unbox_usize(v_i_4622_);
lean_dec(v_i_4622_);
v_res_4635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19(v_id_4618_, v_danglingDot_boxed_4632_, v_as_4620_, v_sz_boxed_4633_, v_i_boxed_4634_, v_b_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_);
lean_dec(v___y_4630_);
lean_dec_ref(v___y_4629_);
lean_dec(v___y_4628_);
lean_dec_ref(v___y_4627_);
lean_dec_ref(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec_ref(v___y_4624_);
lean_dec_ref(v_as_4620_);
lean_dec(v_id_4618_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___redArg(lean_object* v_map_4636_, lean_object* v_f_4637_, lean_object* v_init_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_){
_start:
{
lean_object* v___x_4648_; 
v___x_4648_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_4637_, v_map_4636_, v_init_4638_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_);
return v___x_4648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___redArg___boxed(lean_object* v_map_4649_, lean_object* v_f_4650_, lean_object* v_init_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_){
_start:
{
lean_object* v_res_4661_; 
v_res_4661_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___redArg(v_map_4649_, v_f_4650_, v_init_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
lean_dec(v___y_4659_);
lean_dec_ref(v___y_4658_);
lean_dec(v___y_4657_);
lean_dec_ref(v___y_4656_);
lean_dec_ref(v___y_4655_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
return v_res_4661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9(lean_object* v_00_u03c3_4662_, lean_object* v_00_u03b2_4663_, lean_object* v_map_4664_, lean_object* v_f_4665_, lean_object* v_init_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_){
_start:
{
lean_object* v___x_4676_; 
v___x_4676_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_4665_, v_map_4664_, v_init_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_);
return v___x_4676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___boxed(lean_object* v_00_u03c3_4677_, lean_object* v_00_u03b2_4678_, lean_object* v_map_4679_, lean_object* v_f_4680_, lean_object* v_init_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9(v_00_u03c3_4677_, v_00_u03b2_4678_, v_map_4679_, v_f_4680_, v_init_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_);
lean_dec(v___y_4689_);
lean_dec_ref(v___y_4688_);
lean_dec(v___y_4687_);
lean_dec_ref(v___y_4686_);
lean_dec_ref(v___y_4685_);
lean_dec(v___y_4684_);
lean_dec_ref(v___y_4683_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14(lean_object* v_00_u03c3_4692_, lean_object* v_00_u03b1_4693_, lean_object* v_00_u03b2_4694_, lean_object* v_f_4695_, lean_object* v_x_4696_, lean_object* v_x_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_){
_start:
{
lean_object* v___x_4706_; 
v___x_4706_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_4695_, v_x_4696_, v_x_4697_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_);
return v___x_4706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___boxed(lean_object* v_00_u03c3_4707_, lean_object* v_00_u03b1_4708_, lean_object* v_00_u03b2_4709_, lean_object* v_f_4710_, lean_object* v_x_4711_, lean_object* v_x_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_){
_start:
{
lean_object* v_res_4721_; 
v_res_4721_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14(v_00_u03c3_4707_, v_00_u03b1_4708_, v_00_u03b2_4709_, v_f_4710_, v_x_4711_, v_x_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_);
lean_dec(v___y_4719_);
lean_dec_ref(v___y_4718_);
lean_dec(v___y_4717_);
lean_dec_ref(v___y_4716_);
lean_dec_ref(v___y_4715_);
lean_dec(v___y_4714_);
lean_dec_ref(v___y_4713_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20(lean_object* v_id_4722_, uint8_t v_danglingDot_4723_, lean_object* v_as_4724_, size_t v_sz_4725_, size_t v_i_4726_, lean_object* v_b_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_){
_start:
{
lean_object* v___x_4736_; 
v___x_4736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg(v_id_4722_, v_danglingDot_4723_, v_as_4724_, v_sz_4725_, v_i_4726_, v_b_4727_, v___y_4728_, v___y_4729_);
return v___x_4736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___boxed(lean_object* v_id_4737_, lean_object* v_danglingDot_4738_, lean_object* v_as_4739_, lean_object* v_sz_4740_, lean_object* v_i_4741_, lean_object* v_b_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_){
_start:
{
uint8_t v_danglingDot_boxed_4751_; size_t v_sz_boxed_4752_; size_t v_i_boxed_4753_; lean_object* v_res_4754_; 
v_danglingDot_boxed_4751_ = lean_unbox(v_danglingDot_4738_);
v_sz_boxed_4752_ = lean_unbox_usize(v_sz_4740_);
lean_dec(v_sz_4740_);
v_i_boxed_4753_ = lean_unbox_usize(v_i_4741_);
lean_dec(v_i_4741_);
v_res_4754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20(v_id_4737_, v_danglingDot_boxed_4751_, v_as_4739_, v_sz_boxed_4752_, v_i_boxed_4753_, v_b_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_);
lean_dec(v___y_4749_);
lean_dec_ref(v___y_4748_);
lean_dec(v___y_4747_);
lean_dec_ref(v___y_4746_);
lean_dec_ref(v___y_4745_);
lean_dec(v___y_4744_);
lean_dec_ref(v___y_4743_);
lean_dec_ref(v_as_4739_);
lean_dec(v_id_4737_);
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16(lean_object* v_00_u03c3_4755_, lean_object* v_00_u03b1_4756_, lean_object* v_00_u03b2_4757_, lean_object* v_f_4758_, lean_object* v_x_4759_, lean_object* v_x_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_){
_start:
{
lean_object* v___x_4770_; 
v___x_4770_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_4758_, v_x_4759_, v_x_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_);
return v___x_4770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___boxed(lean_object* v_00_u03c3_4771_, lean_object* v_00_u03b1_4772_, lean_object* v_00_u03b2_4773_, lean_object* v_f_4774_, lean_object* v_x_4775_, lean_object* v_x_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_){
_start:
{
lean_object* v_res_4786_; 
v_res_4786_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16(v_00_u03c3_4771_, v_00_u03b1_4772_, v_00_u03b2_4773_, v_f_4774_, v_x_4775_, v_x_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_);
lean_dec(v___y_4784_);
lean_dec_ref(v___y_4783_);
lean_dec(v___y_4782_);
lean_dec_ref(v___y_4781_);
lean_dec_ref(v___y_4780_);
lean_dec(v___y_4779_);
lean_dec_ref(v___y_4778_);
return v_res_4786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20(lean_object* v_00_u03b1_4787_, lean_object* v_00_u03b2_4788_, lean_object* v_00_u03c3_4789_, lean_object* v_f_4790_, lean_object* v_as_4791_, size_t v_i_4792_, size_t v_stop_4793_, lean_object* v_b_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_){
_start:
{
lean_object* v___x_4803_; 
v___x_4803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(v_f_4790_, v_as_4791_, v_i_4792_, v_stop_4793_, v_b_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
return v___x_4803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___boxed(lean_object* v_00_u03b1_4804_, lean_object* v_00_u03b2_4805_, lean_object* v_00_u03c3_4806_, lean_object* v_f_4807_, lean_object* v_as_4808_, lean_object* v_i_4809_, lean_object* v_stop_4810_, lean_object* v_b_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_){
_start:
{
size_t v_i_boxed_4820_; size_t v_stop_boxed_4821_; lean_object* v_res_4822_; 
v_i_boxed_4820_ = lean_unbox_usize(v_i_4809_);
lean_dec(v_i_4809_);
v_stop_boxed_4821_ = lean_unbox_usize(v_stop_4810_);
lean_dec(v_stop_4810_);
v_res_4822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20(v_00_u03b1_4804_, v_00_u03b2_4805_, v_00_u03c3_4806_, v_f_4807_, v_as_4808_, v_i_boxed_4820_, v_stop_boxed_4821_, v_b_4811_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_, v___y_4816_, v___y_4817_, v___y_4818_);
lean_dec(v___y_4818_);
lean_dec_ref(v___y_4817_);
lean_dec(v___y_4816_);
lean_dec_ref(v___y_4815_);
lean_dec_ref(v___y_4814_);
lean_dec(v___y_4813_);
lean_dec_ref(v___y_4812_);
lean_dec_ref(v_as_4808_);
return v_res_4822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21(lean_object* v_00_u03c3_4823_, lean_object* v_00_u03b1_4824_, lean_object* v_00_u03b2_4825_, lean_object* v_f_4826_, lean_object* v_keys_4827_, lean_object* v_vals_4828_, lean_object* v_heq_4829_, lean_object* v_i_4830_, lean_object* v_acc_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_){
_start:
{
lean_object* v___x_4840_; 
v___x_4840_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(v_f_4826_, v_keys_4827_, v_vals_4828_, v_i_4830_, v_acc_4831_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_);
return v___x_4840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___boxed(lean_object** _args){
lean_object* v_00_u03c3_4841_ = _args[0];
lean_object* v_00_u03b1_4842_ = _args[1];
lean_object* v_00_u03b2_4843_ = _args[2];
lean_object* v_f_4844_ = _args[3];
lean_object* v_keys_4845_ = _args[4];
lean_object* v_vals_4846_ = _args[5];
lean_object* v_heq_4847_ = _args[6];
lean_object* v_i_4848_ = _args[7];
lean_object* v_acc_4849_ = _args[8];
lean_object* v___y_4850_ = _args[9];
lean_object* v___y_4851_ = _args[10];
lean_object* v___y_4852_ = _args[11];
lean_object* v___y_4853_ = _args[12];
lean_object* v___y_4854_ = _args[13];
lean_object* v___y_4855_ = _args[14];
lean_object* v___y_4856_ = _args[15];
lean_object* v___y_4857_ = _args[16];
_start:
{
lean_object* v_res_4858_; 
v_res_4858_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21(v_00_u03c3_4841_, v_00_u03b1_4842_, v_00_u03b2_4843_, v_f_4844_, v_keys_4845_, v_vals_4846_, v_heq_4847_, v_i_4848_, v_acc_4849_, v___y_4850_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
lean_dec(v___y_4856_);
lean_dec_ref(v___y_4855_);
lean_dec(v___y_4854_);
lean_dec_ref(v___y_4853_);
lean_dec_ref(v___y_4852_);
lean_dec(v___y_4851_);
lean_dec_ref(v___y_4850_);
lean_dec_ref(v_vals_4846_);
lean_dec_ref(v_keys_4845_);
return v_res_4858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22(lean_object* v_00_u03b1_4859_, lean_object* v_00_u03b2_4860_, lean_object* v_00_u03c3_4861_, lean_object* v_f_4862_, lean_object* v_as_4863_, size_t v_i_4864_, size_t v_stop_4865_, lean_object* v_b_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_){
_start:
{
lean_object* v___x_4876_; 
v___x_4876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(v_f_4862_, v_as_4863_, v_i_4864_, v_stop_4865_, v_b_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_);
return v___x_4876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___boxed(lean_object** _args){
lean_object* v_00_u03b1_4877_ = _args[0];
lean_object* v_00_u03b2_4878_ = _args[1];
lean_object* v_00_u03c3_4879_ = _args[2];
lean_object* v_f_4880_ = _args[3];
lean_object* v_as_4881_ = _args[4];
lean_object* v_i_4882_ = _args[5];
lean_object* v_stop_4883_ = _args[6];
lean_object* v_b_4884_ = _args[7];
lean_object* v___y_4885_ = _args[8];
lean_object* v___y_4886_ = _args[9];
lean_object* v___y_4887_ = _args[10];
lean_object* v___y_4888_ = _args[11];
lean_object* v___y_4889_ = _args[12];
lean_object* v___y_4890_ = _args[13];
lean_object* v___y_4891_ = _args[14];
lean_object* v___y_4892_ = _args[15];
lean_object* v___y_4893_ = _args[16];
_start:
{
size_t v_i_boxed_4894_; size_t v_stop_boxed_4895_; lean_object* v_res_4896_; 
v_i_boxed_4894_ = lean_unbox_usize(v_i_4882_);
lean_dec(v_i_4882_);
v_stop_boxed_4895_ = lean_unbox_usize(v_stop_4883_);
lean_dec(v_stop_4883_);
v_res_4896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22(v_00_u03b1_4877_, v_00_u03b2_4878_, v_00_u03c3_4879_, v_f_4880_, v_as_4881_, v_i_boxed_4894_, v_stop_boxed_4895_, v_b_4884_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_);
lean_dec(v___y_4892_);
lean_dec_ref(v___y_4891_);
lean_dec(v___y_4890_);
lean_dec_ref(v___y_4889_);
lean_dec_ref(v___y_4888_);
lean_dec(v___y_4887_);
lean_dec_ref(v___y_4886_);
lean_dec_ref(v_as_4881_);
return v_res_4896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23(lean_object* v_00_u03c3_4897_, lean_object* v_00_u03b1_4898_, lean_object* v_00_u03b2_4899_, lean_object* v_f_4900_, lean_object* v_keys_4901_, lean_object* v_vals_4902_, lean_object* v_heq_4903_, lean_object* v_i_4904_, lean_object* v_acc_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_){
_start:
{
lean_object* v___x_4915_; 
v___x_4915_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(v_f_4900_, v_keys_4901_, v_vals_4902_, v_i_4904_, v_acc_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_);
return v___x_4915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___boxed(lean_object** _args){
lean_object* v_00_u03c3_4916_ = _args[0];
lean_object* v_00_u03b1_4917_ = _args[1];
lean_object* v_00_u03b2_4918_ = _args[2];
lean_object* v_f_4919_ = _args[3];
lean_object* v_keys_4920_ = _args[4];
lean_object* v_vals_4921_ = _args[5];
lean_object* v_heq_4922_ = _args[6];
lean_object* v_i_4923_ = _args[7];
lean_object* v_acc_4924_ = _args[8];
lean_object* v___y_4925_ = _args[9];
lean_object* v___y_4926_ = _args[10];
lean_object* v___y_4927_ = _args[11];
lean_object* v___y_4928_ = _args[12];
lean_object* v___y_4929_ = _args[13];
lean_object* v___y_4930_ = _args[14];
lean_object* v___y_4931_ = _args[15];
lean_object* v___y_4932_ = _args[16];
lean_object* v___y_4933_ = _args[17];
_start:
{
lean_object* v_res_4934_; 
v_res_4934_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23(v_00_u03c3_4916_, v_00_u03b1_4917_, v_00_u03b2_4918_, v_f_4919_, v_keys_4920_, v_vals_4921_, v_heq_4922_, v_i_4923_, v_acc_4924_, v___y_4925_, v___y_4926_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_, v___y_4932_);
lean_dec(v___y_4932_);
lean_dec_ref(v___y_4931_);
lean_dec(v___y_4930_);
lean_dec_ref(v___y_4929_);
lean_dec_ref(v___y_4928_);
lean_dec(v___y_4927_);
lean_dec_ref(v___y_4926_);
lean_dec_ref(v_vals_4921_);
lean_dec_ref(v_keys_4920_);
return v_res_4934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_idCompletion(lean_object* v_uri_4935_, lean_object* v_pos_4936_, lean_object* v_completionInfoPos_4937_, lean_object* v_ctx_4938_, lean_object* v_lctx_4939_, lean_object* v_stx_4940_, lean_object* v_id_4941_, lean_object* v_hoverInfo_4942_, uint8_t v_danglingDot_4943_, lean_object* v_a_4944_){
_start:
{
lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4946_ = lean_box(v_danglingDot_4943_);
lean_inc_ref(v_ctx_4938_);
v___x_4947_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___boxed), 13, 5);
lean_closure_set(v___x_4947_, 0, v_ctx_4938_);
lean_closure_set(v___x_4947_, 1, v_stx_4940_);
lean_closure_set(v___x_4947_, 2, v_id_4941_);
lean_closure_set(v___x_4947_, 3, v_hoverInfo_4942_);
lean_closure_set(v___x_4947_, 4, v___x_4946_);
v___x_4948_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_4935_, v_pos_4936_, v_completionInfoPos_4937_, v_ctx_4938_, v_lctx_4939_, v___x_4947_, v_a_4944_);
return v___x_4948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_idCompletion___boxed(lean_object* v_uri_4949_, lean_object* v_pos_4950_, lean_object* v_completionInfoPos_4951_, lean_object* v_ctx_4952_, lean_object* v_lctx_4953_, lean_object* v_stx_4954_, lean_object* v_id_4955_, lean_object* v_hoverInfo_4956_, lean_object* v_danglingDot_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_){
_start:
{
uint8_t v_danglingDot_boxed_4960_; lean_object* v_res_4961_; 
v_danglingDot_boxed_4960_ = lean_unbox(v_danglingDot_4957_);
v_res_4961_ = l_Lean_Server_Completion_idCompletion(v_uri_4949_, v_pos_4950_, v_completionInfoPos_4951_, v_ctx_4952_, v_lctx_4953_, v_stx_4954_, v_id_4955_, v_hoverInfo_4956_, v_danglingDot_boxed_4960_, v_a_4958_);
lean_dec_ref(v_a_4958_);
return v_res_4961_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(lean_object* v_e_4962_, lean_object* v___y_4963_){
_start:
{
uint8_t v___x_4965_; uint8_t v___x_4966_; 
v___x_4965_ = l_Lean_Expr_hasMVar(v_e_4962_);
v___x_4966_ = lean_bool_not(v___x_4965_);
if (v___x_4966_ == 0)
{
lean_object* v___x_4967_; lean_object* v_mctx_4968_; lean_object* v___x_4969_; lean_object* v_fst_4970_; lean_object* v_snd_4971_; lean_object* v___x_4972_; lean_object* v_cache_4973_; lean_object* v_zetaDeltaFVarIds_4974_; lean_object* v_postponed_4975_; lean_object* v_diag_4976_; lean_object* v___x_4978_; uint8_t v_isShared_4979_; uint8_t v_isSharedCheck_4986_; 
v___x_4967_ = lean_st_ref_get(v___y_4963_);
v_mctx_4968_ = lean_ctor_get(v___x_4967_, 0);
lean_inc_ref(v_mctx_4968_);
lean_dec(v___x_4967_);
v___x_4969_ = l_Lean_instantiateMVarsCore(v_mctx_4968_, v_e_4962_);
v_fst_4970_ = lean_ctor_get(v___x_4969_, 0);
lean_inc(v_fst_4970_);
v_snd_4971_ = lean_ctor_get(v___x_4969_, 1);
lean_inc(v_snd_4971_);
lean_dec_ref(v___x_4969_);
v___x_4972_ = lean_st_ref_take(v___y_4963_);
v_cache_4973_ = lean_ctor_get(v___x_4972_, 1);
v_zetaDeltaFVarIds_4974_ = lean_ctor_get(v___x_4972_, 2);
v_postponed_4975_ = lean_ctor_get(v___x_4972_, 3);
v_diag_4976_ = lean_ctor_get(v___x_4972_, 4);
v_isSharedCheck_4986_ = !lean_is_exclusive(v___x_4972_);
if (v_isSharedCheck_4986_ == 0)
{
lean_object* v_unused_4987_; 
v_unused_4987_ = lean_ctor_get(v___x_4972_, 0);
lean_dec(v_unused_4987_);
v___x_4978_ = v___x_4972_;
v_isShared_4979_ = v_isSharedCheck_4986_;
goto v_resetjp_4977_;
}
else
{
lean_inc(v_diag_4976_);
lean_inc(v_postponed_4975_);
lean_inc(v_zetaDeltaFVarIds_4974_);
lean_inc(v_cache_4973_);
lean_dec(v___x_4972_);
v___x_4978_ = lean_box(0);
v_isShared_4979_ = v_isSharedCheck_4986_;
goto v_resetjp_4977_;
}
v_resetjp_4977_:
{
lean_object* v___x_4981_; 
if (v_isShared_4979_ == 0)
{
lean_ctor_set(v___x_4978_, 0, v_snd_4971_);
v___x_4981_ = v___x_4978_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4985_; 
v_reuseFailAlloc_4985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4985_, 0, v_snd_4971_);
lean_ctor_set(v_reuseFailAlloc_4985_, 1, v_cache_4973_);
lean_ctor_set(v_reuseFailAlloc_4985_, 2, v_zetaDeltaFVarIds_4974_);
lean_ctor_set(v_reuseFailAlloc_4985_, 3, v_postponed_4975_);
lean_ctor_set(v_reuseFailAlloc_4985_, 4, v_diag_4976_);
v___x_4981_ = v_reuseFailAlloc_4985_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; 
v___x_4982_ = lean_st_ref_set(v___y_4963_, v___x_4981_);
v___x_4983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4983_, 0, v_fst_4970_);
v___x_4984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4984_, 0, v___x_4983_);
return v___x_4984_;
}
}
}
else
{
lean_object* v___x_4988_; lean_object* v___x_4989_; 
v___x_4988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4988_, 0, v_e_4962_);
v___x_4989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4989_, 0, v___x_4988_);
return v___x_4989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg___boxed(lean_object* v_e_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_){
_start:
{
lean_object* v_res_4993_; 
v_res_4993_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_e_4990_, v___y_4991_);
lean_dec(v___y_4991_);
return v_res_4993_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0(lean_object* v_e_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_){
_start:
{
lean_object* v___x_5003_; 
v___x_5003_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_e_4994_, v___y_4999_);
return v___x_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___boxed(lean_object* v_e_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_){
_start:
{
lean_object* v_res_5013_; 
v_res_5013_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0(v_e_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_);
lean_dec(v___y_5011_);
lean_dec_ref(v___y_5010_);
lean_dec(v___y_5009_);
lean_dec_ref(v___y_5008_);
lean_dec_ref(v___y_5007_);
lean_dec(v___y_5006_);
lean_dec_ref(v___y_5005_);
return v_res_5013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__0(lean_object* v_a_5014_, lean_object* v_declName_5015_, lean_object* v_decl_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_){
_start:
{
lean_object* v_unnormedTypeName_5025_; uint8_t v___x_5026_; uint8_t v___x_5027_; 
v_unnormedTypeName_5025_ = l_Lean_Name_getPrefix(v_declName_5015_);
v___x_5026_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_unnormedTypeName_5025_, v_a_5014_);
v___x_5027_ = lean_bool_not(v___x_5026_);
if (v___x_5027_ == 0)
{
lean_object* v___x_5028_; lean_object* v_a_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5095_; 
v___x_5028_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_5015_, v___y_5023_);
v_a_5029_ = lean_ctor_get(v___x_5028_, 0);
v_isSharedCheck_5095_ = !lean_is_exclusive(v___x_5028_);
if (v_isSharedCheck_5095_ == 0)
{
v___x_5031_ = v___x_5028_;
v_isShared_5032_ = v_isSharedCheck_5095_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_a_5029_);
lean_dec(v___x_5028_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5095_;
goto v_resetjp_5030_;
}
v_resetjp_5030_:
{
if (lean_obj_tag(v_a_5029_) == 1)
{
lean_object* v_val_5033_; lean_object* v___x_5035_; uint8_t v_isShared_5036_; uint8_t v_isSharedCheck_5090_; 
lean_del_object(v___x_5031_);
v_val_5033_ = lean_ctor_get(v_a_5029_, 0);
v_isSharedCheck_5090_ = !lean_is_exclusive(v_a_5029_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5035_ = v_a_5029_;
v_isShared_5036_ = v_isSharedCheck_5090_;
goto v_resetjp_5034_;
}
else
{
lean_inc(v_val_5033_);
lean_dec(v_a_5029_);
v___x_5035_ = lean_box(0);
v_isShared_5036_ = v_isSharedCheck_5090_;
goto v_resetjp_5034_;
}
v_resetjp_5034_:
{
lean_object* v_info_5037_; lean_object* v_kind_5038_; lean_object* v_tags_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; 
v_info_5037_ = lean_ctor_get(v_decl_5016_, 0);
lean_inc_ref(v_info_5037_);
v_kind_5038_ = lean_ctor_get(v_decl_5016_, 1);
lean_inc_ref(v_kind_5038_);
v_tags_5039_ = lean_ctor_get(v_decl_5016_, 2);
lean_inc_ref(v_tags_5039_);
lean_dec_ref(v_decl_5016_);
v___x_5040_ = l_Lean_Name_getPrefix(v_val_5033_);
lean_dec(v_val_5033_);
v___x_5041_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(v___x_5040_, v_info_5037_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_);
if (lean_obj_tag(v___x_5041_) == 0)
{
lean_object* v_a_5042_; lean_object* v___x_5044_; uint8_t v_isShared_5045_; uint8_t v_isSharedCheck_5081_; 
v_a_5042_ = lean_ctor_get(v___x_5041_, 0);
v_isSharedCheck_5081_ = !lean_is_exclusive(v___x_5041_);
if (v_isSharedCheck_5081_ == 0)
{
v___x_5044_ = v___x_5041_;
v_isShared_5045_ = v_isSharedCheck_5081_;
goto v_resetjp_5043_;
}
else
{
lean_inc(v_a_5042_);
lean_dec(v___x_5041_);
v___x_5044_ = lean_box(0);
v_isShared_5045_ = v_isSharedCheck_5081_;
goto v_resetjp_5043_;
}
v_resetjp_5043_:
{
uint8_t v___x_5046_; uint8_t v___x_5047_; 
v___x_5046_ = lean_unbox(v_a_5042_);
lean_dec(v_a_5042_);
v___x_5047_ = lean_bool_not(v___x_5046_);
if (v___x_5047_ == 0)
{
lean_object* v___x_5048_; 
lean_del_object(v___x_5044_);
lean_inc(v___y_5023_);
lean_inc_ref(v___y_5022_);
lean_inc(v___y_5021_);
lean_inc_ref(v___y_5020_);
v___x_5048_ = lean_apply_5(v_kind_5038_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_, lean_box(0));
if (lean_obj_tag(v___x_5048_) == 0)
{
lean_object* v_a_5049_; lean_object* v___x_5050_; 
v_a_5049_ = lean_ctor_get(v___x_5048_, 0);
lean_inc(v_a_5049_);
lean_dec_ref_known(v___x_5048_, 1);
lean_inc(v___y_5023_);
lean_inc_ref(v___y_5022_);
lean_inc(v___y_5021_);
lean_inc_ref(v___y_5020_);
v___x_5050_ = lean_apply_5(v_tags_5039_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_, lean_box(0));
if (lean_obj_tag(v___x_5050_) == 0)
{
lean_object* v_a_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5057_; 
v_a_5051_ = lean_ctor_get(v___x_5050_, 0);
lean_inc(v_a_5051_);
lean_dec_ref_known(v___x_5050_, 1);
v___x_5052_ = l_Lean_ConstantInfo_name(v_info_5037_);
lean_dec_ref(v_info_5037_);
v___x_5053_ = l_Lean_Name_getString_x21(v___x_5052_);
v___x_5054_ = lean_box(0);
v___x_5055_ = l_Lean_Name_str___override(v___x_5054_, v___x_5053_);
if (v_isShared_5036_ == 0)
{
lean_ctor_set_tag(v___x_5035_, 0);
lean_ctor_set(v___x_5035_, 0, v___x_5052_);
v___x_5057_ = v___x_5035_;
goto v_reusejp_5056_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v___x_5052_);
v___x_5057_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5056_;
}
v_reusejp_5056_:
{
uint8_t v___x_5058_; lean_object* v___x_5059_; 
v___x_5058_ = lean_unbox(v_a_5049_);
lean_dec(v_a_5049_);
v___x_5059_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_5055_, v___x_5057_, v___x_5058_, v_a_5051_, v___y_5017_, v___y_5018_);
return v___x_5059_;
}
}
else
{
lean_object* v_a_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5068_; 
lean_dec(v_a_5049_);
lean_dec_ref(v_info_5037_);
lean_del_object(v___x_5035_);
v_a_5061_ = lean_ctor_get(v___x_5050_, 0);
v_isSharedCheck_5068_ = !lean_is_exclusive(v___x_5050_);
if (v_isSharedCheck_5068_ == 0)
{
v___x_5063_ = v___x_5050_;
v_isShared_5064_ = v_isSharedCheck_5068_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_a_5061_);
lean_dec(v___x_5050_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5068_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
lean_object* v___x_5066_; 
if (v_isShared_5064_ == 0)
{
v___x_5066_ = v___x_5063_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5067_; 
v_reuseFailAlloc_5067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5067_, 0, v_a_5061_);
v___x_5066_ = v_reuseFailAlloc_5067_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
return v___x_5066_;
}
}
}
}
else
{
lean_object* v_a_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5076_; 
lean_dec_ref(v_tags_5039_);
lean_dec_ref(v_info_5037_);
lean_del_object(v___x_5035_);
v_a_5069_ = lean_ctor_get(v___x_5048_, 0);
v_isSharedCheck_5076_ = !lean_is_exclusive(v___x_5048_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_5071_ = v___x_5048_;
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
else
{
lean_inc(v_a_5069_);
lean_dec(v___x_5048_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5074_; 
if (v_isShared_5072_ == 0)
{
v___x_5074_ = v___x_5071_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v_a_5069_);
v___x_5074_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
return v___x_5074_;
}
}
}
}
else
{
lean_object* v___x_5077_; lean_object* v___x_5079_; 
lean_dec_ref(v_tags_5039_);
lean_dec_ref(v_kind_5038_);
lean_dec_ref(v_info_5037_);
lean_del_object(v___x_5035_);
v___x_5077_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5045_ == 0)
{
lean_ctor_set(v___x_5044_, 0, v___x_5077_);
v___x_5079_ = v___x_5044_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v___x_5077_);
v___x_5079_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
return v___x_5079_;
}
}
}
}
else
{
lean_object* v_a_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5089_; 
lean_dec_ref(v_tags_5039_);
lean_dec_ref(v_kind_5038_);
lean_dec_ref(v_info_5037_);
lean_del_object(v___x_5035_);
v_a_5082_ = lean_ctor_get(v___x_5041_, 0);
v_isSharedCheck_5089_ = !lean_is_exclusive(v___x_5041_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5084_ = v___x_5041_;
v_isShared_5085_ = v_isSharedCheck_5089_;
goto v_resetjp_5083_;
}
else
{
lean_inc(v_a_5082_);
lean_dec(v___x_5041_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5089_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
lean_object* v___x_5087_; 
if (v_isShared_5085_ == 0)
{
v___x_5087_ = v___x_5084_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_a_5082_);
v___x_5087_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
return v___x_5087_;
}
}
}
}
}
else
{
lean_object* v___x_5091_; lean_object* v___x_5093_; 
lean_dec(v_a_5029_);
lean_dec_ref(v_decl_5016_);
v___x_5091_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5032_ == 0)
{
lean_ctor_set(v___x_5031_, 0, v___x_5091_);
v___x_5093_ = v___x_5031_;
goto v_reusejp_5092_;
}
else
{
lean_object* v_reuseFailAlloc_5094_; 
v_reuseFailAlloc_5094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5094_, 0, v___x_5091_);
v___x_5093_ = v_reuseFailAlloc_5094_;
goto v_reusejp_5092_;
}
v_reusejp_5092_:
{
return v___x_5093_;
}
}
}
}
else
{
lean_object* v___x_5096_; lean_object* v___x_5097_; 
lean_dec_ref(v_decl_5016_);
lean_dec(v_declName_5015_);
v___x_5096_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5097_, 0, v___x_5096_);
return v___x_5097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__0___boxed(lean_object* v_a_5098_, lean_object* v_declName_5099_, lean_object* v_decl_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_){
_start:
{
lean_object* v_res_5109_; 
v_res_5109_ = l_Lean_Server_Completion_dotCompletion___lam__0(v_a_5098_, v_declName_5099_, v_decl_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_);
lean_dec(v___y_5107_);
lean_dec_ref(v___y_5106_);
lean_dec(v___y_5105_);
lean_dec_ref(v___y_5104_);
lean_dec_ref(v___y_5103_);
lean_dec(v___y_5102_);
lean_dec_ref(v___y_5101_);
return v_res_5109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__1(lean_object* v_expr_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_){
_start:
{
lean_object* v_a_5123_; lean_object* v___y_5127_; uint8_t v___y_5128_; lean_object* v___y_5138_; lean_object* v_a_5139_; lean_object* v___x_5142_; 
lean_inc(v___y_5117_);
lean_inc_ref(v___y_5116_);
lean_inc(v___y_5115_);
lean_inc_ref(v___y_5114_);
v___x_5142_ = lean_infer_type(v_expr_5110_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_);
if (lean_obj_tag(v___x_5142_) == 0)
{
lean_object* v_a_5143_; lean_object* v___x_5144_; lean_object* v_a_5145_; lean_object* v_a_5146_; lean_object* v___x_5147_; 
v_a_5143_ = lean_ctor_get(v___x_5142_, 0);
lean_inc(v_a_5143_);
lean_dec_ref_known(v___x_5142_, 1);
v___x_5144_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_a_5143_, v___y_5115_);
v_a_5145_ = lean_ctor_get(v___x_5144_, 0);
lean_inc(v_a_5145_);
lean_dec_ref(v___x_5144_);
v_a_5146_ = lean_ctor_get(v_a_5145_, 0);
lean_inc(v_a_5146_);
lean_dec(v_a_5145_);
v___x_5147_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(v_a_5146_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_);
if (lean_obj_tag(v___x_5147_) == 0)
{
lean_object* v_a_5148_; 
v_a_5148_ = lean_ctor_get(v___x_5147_, 0);
lean_inc(v_a_5148_);
lean_dec_ref_known(v___x_5147_, 1);
v_a_5123_ = v_a_5148_;
goto v___jp_5122_;
}
else
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5156_; 
v_a_5149_ = lean_ctor_get(v___x_5147_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5147_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5151_ = v___x_5147_;
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5147_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5154_; 
lean_inc(v_a_5149_);
if (v_isShared_5152_ == 0)
{
v___x_5154_ = v___x_5151_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_a_5149_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
v___y_5138_ = v___x_5154_;
v_a_5139_ = v_a_5149_;
goto v___jp_5137_;
}
}
}
}
else
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5164_; 
v_a_5157_ = lean_ctor_get(v___x_5142_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5142_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5159_ = v___x_5142_;
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___x_5142_);
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
v___y_5138_ = v___x_5162_;
v_a_5139_ = v_a_5157_;
goto v___jp_5137_;
}
}
}
v___jp_5119_:
{
lean_object* v___x_5120_; lean_object* v___x_5121_; 
v___x_5120_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5121_, 0, v___x_5120_);
return v___x_5121_;
}
v___jp_5122_:
{
if (lean_obj_tag(v_a_5123_) == 0)
{
lean_object* v___f_5124_; lean_object* v___x_5125_; 
v___f_5124_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotCompletion___lam__0___boxed), 11, 1);
lean_closure_set(v___f_5124_, 0, v_a_5123_);
v___x_5125_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___f_5124_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_);
return v___x_5125_;
}
else
{
goto v___jp_5119_;
}
}
v___jp_5126_:
{
if (v___y_5128_ == 0)
{
lean_dec_ref(v___y_5127_);
goto v___jp_5119_;
}
else
{
lean_object* v_a_5129_; lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5136_; 
v_a_5129_ = lean_ctor_get(v___y_5127_, 0);
v_isSharedCheck_5136_ = !lean_is_exclusive(v___y_5127_);
if (v_isSharedCheck_5136_ == 0)
{
v___x_5131_ = v___y_5127_;
v_isShared_5132_ = v_isSharedCheck_5136_;
goto v_resetjp_5130_;
}
else
{
lean_inc(v_a_5129_);
lean_dec(v___y_5127_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5136_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
lean_object* v___x_5134_; 
if (v_isShared_5132_ == 0)
{
v___x_5134_ = v___x_5131_;
goto v_reusejp_5133_;
}
else
{
lean_object* v_reuseFailAlloc_5135_; 
v_reuseFailAlloc_5135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5135_, 0, v_a_5129_);
v___x_5134_ = v_reuseFailAlloc_5135_;
goto v_reusejp_5133_;
}
v_reusejp_5133_:
{
return v___x_5134_;
}
}
}
}
v___jp_5137_:
{
uint8_t v___x_5140_; 
v___x_5140_ = l_Lean_Exception_isInterrupt(v_a_5139_);
if (v___x_5140_ == 0)
{
uint8_t v___x_5141_; 
v___x_5141_ = l_Lean_Exception_isRuntime(v_a_5139_);
v___y_5127_ = v___y_5138_;
v___y_5128_ = v___x_5141_;
goto v___jp_5126_;
}
else
{
lean_dec_ref(v_a_5139_);
v___y_5127_ = v___y_5138_;
v___y_5128_ = v___x_5140_;
goto v___jp_5126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__1___boxed(lean_object* v_expr_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_){
_start:
{
lean_object* v_res_5174_; 
v_res_5174_ = l_Lean_Server_Completion_dotCompletion___lam__1(v_expr_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_);
lean_dec(v___y_5172_);
lean_dec_ref(v___y_5171_);
lean_dec(v___y_5170_);
lean_dec_ref(v___y_5169_);
lean_dec_ref(v___y_5168_);
lean_dec(v___y_5167_);
lean_dec_ref(v___y_5166_);
return v_res_5174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion(lean_object* v_uri_5175_, lean_object* v_pos_5176_, lean_object* v_completionInfoPos_5177_, lean_object* v_ctx_5178_, lean_object* v_info_5179_, lean_object* v_a_5180_){
_start:
{
lean_object* v_lctx_5182_; lean_object* v_expr_5183_; lean_object* v___f_5184_; lean_object* v___x_5185_; 
v_lctx_5182_ = lean_ctor_get(v_info_5179_, 1);
lean_inc_ref(v_lctx_5182_);
v_expr_5183_ = lean_ctor_get(v_info_5179_, 3);
lean_inc_ref(v_expr_5183_);
lean_dec_ref(v_info_5179_);
v___f_5184_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotCompletion___lam__1___boxed), 9, 1);
lean_closure_set(v___f_5184_, 0, v_expr_5183_);
v___x_5185_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5175_, v_pos_5176_, v_completionInfoPos_5177_, v_ctx_5178_, v_lctx_5182_, v___f_5184_, v_a_5180_);
return v___x_5185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___boxed(lean_object* v_uri_5186_, lean_object* v_pos_5187_, lean_object* v_completionInfoPos_5188_, lean_object* v_ctx_5189_, lean_object* v_info_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_){
_start:
{
lean_object* v_res_5193_; 
v_res_5193_ = l_Lean_Server_Completion_dotCompletion(v_uri_5186_, v_pos_5187_, v_completionInfoPos_5188_, v_ctx_5189_, v_info_5190_, v_a_5191_);
lean_dec_ref(v_a_5191_);
return v_res_5193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__0(lean_object* v___x_5194_, lean_object* v_id_5195_, lean_object* v_declName_5196_, lean_object* v_decl_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_){
_start:
{
lean_object* v___x_5206_; uint8_t v___x_5207_; uint8_t v___x_5208_; 
v___x_5206_ = l_Lean_Name_getPrefix(v_declName_5196_);
lean_inc(v___x_5194_);
v___x_5207_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v___x_5206_, v___x_5194_);
v___x_5208_ = lean_bool_not(v___x_5207_);
if (v___x_5208_ == 0)
{
lean_object* v___x_5209_; lean_object* v_a_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5307_; 
v___x_5209_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_5196_, v___y_5204_);
v_a_5210_ = lean_ctor_get(v___x_5209_, 0);
v_isSharedCheck_5307_ = !lean_is_exclusive(v___x_5209_);
if (v_isSharedCheck_5307_ == 0)
{
v___x_5212_ = v___x_5209_;
v_isShared_5213_ = v_isSharedCheck_5307_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_a_5210_);
lean_dec(v___x_5209_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5307_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
if (lean_obj_tag(v_a_5210_) == 1)
{
lean_object* v_val_5214_; lean_object* v___x_5216_; uint8_t v_isShared_5217_; uint8_t v_isSharedCheck_5302_; 
lean_del_object(v___x_5212_);
v_val_5214_ = lean_ctor_get(v_a_5210_, 0);
v_isSharedCheck_5302_ = !lean_is_exclusive(v_a_5210_);
if (v_isSharedCheck_5302_ == 0)
{
v___x_5216_ = v_a_5210_;
v_isShared_5217_ = v_isSharedCheck_5302_;
goto v_resetjp_5215_;
}
else
{
lean_inc(v_val_5214_);
lean_dec(v_a_5210_);
v___x_5216_ = lean_box(0);
v_isShared_5217_ = v_isSharedCheck_5302_;
goto v_resetjp_5215_;
}
v_resetjp_5215_:
{
lean_object* v_info_5218_; lean_object* v_kind_5219_; lean_object* v_tags_5220_; lean_object* v___x_5221_; 
v_info_5218_ = lean_ctor_get(v_decl_5197_, 0);
lean_inc_ref(v_info_5218_);
v_kind_5219_ = lean_ctor_get(v_decl_5197_, 1);
lean_inc_ref(v_kind_5219_);
v_tags_5220_ = lean_ctor_get(v_decl_5197_, 2);
lean_inc_ref(v_tags_5220_);
lean_dec_ref(v_decl_5197_);
v___x_5221_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(v___x_5194_, v_info_5218_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_);
if (lean_obj_tag(v___x_5221_) == 0)
{
lean_object* v_a_5222_; lean_object* v___x_5224_; uint8_t v_isShared_5225_; uint8_t v_isSharedCheck_5293_; 
v_a_5222_ = lean_ctor_get(v___x_5221_, 0);
v_isSharedCheck_5293_ = !lean_is_exclusive(v___x_5221_);
if (v_isSharedCheck_5293_ == 0)
{
v___x_5224_ = v___x_5221_;
v_isShared_5225_ = v_isSharedCheck_5293_;
goto v_resetjp_5223_;
}
else
{
lean_inc(v_a_5222_);
lean_dec(v___x_5221_);
v___x_5224_ = lean_box(0);
v_isShared_5225_ = v_isSharedCheck_5293_;
goto v_resetjp_5223_;
}
v_resetjp_5223_:
{
uint8_t v___x_5226_; uint8_t v___x_5227_; 
v___x_5226_ = lean_unbox(v_a_5222_);
lean_dec(v_a_5222_);
v___x_5227_ = lean_bool_not(v___x_5226_);
if (v___x_5227_ == 0)
{
lean_object* v___x_5228_; 
lean_del_object(v___x_5224_);
lean_inc(v___y_5204_);
lean_inc_ref(v___y_5203_);
lean_inc(v___y_5202_);
lean_inc_ref(v___y_5201_);
v___x_5228_ = lean_apply_5(v_kind_5219_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, lean_box(0));
if (lean_obj_tag(v___x_5228_) == 0)
{
lean_object* v_a_5229_; lean_object* v___x_5230_; 
v_a_5229_ = lean_ctor_get(v___x_5228_, 0);
lean_inc(v_a_5229_);
lean_dec_ref_known(v___x_5228_, 1);
lean_inc(v___y_5204_);
lean_inc_ref(v___y_5203_);
lean_inc(v___y_5202_);
lean_inc_ref(v___y_5201_);
v___x_5230_ = lean_apply_5(v_tags_5220_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, lean_box(0));
if (lean_obj_tag(v___x_5230_) == 0)
{
lean_object* v_a_5231_; uint8_t v___x_5232_; 
v_a_5231_ = lean_ctor_get(v___x_5230_, 0);
lean_inc(v_a_5231_);
lean_dec_ref_known(v___x_5230_, 1);
v___x_5232_ = l_Lean_Name_isAnonymous(v_id_5195_);
if (v___x_5232_ == 0)
{
lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v_a_5235_; lean_object* v___x_5237_; uint8_t v_isShared_5238_; uint8_t v_isSharedCheck_5254_; 
lean_del_object(v___x_5216_);
v___x_5233_ = l_Lean_Name_getPrefix(v_val_5214_);
v___x_5234_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v___x_5233_, v_id_5195_, v___x_5232_, v_val_5214_, v___y_5204_);
lean_dec(v___x_5233_);
v_a_5235_ = lean_ctor_get(v___x_5234_, 0);
v_isSharedCheck_5254_ = !lean_is_exclusive(v___x_5234_);
if (v_isSharedCheck_5254_ == 0)
{
v___x_5237_ = v___x_5234_;
v_isShared_5238_ = v_isSharedCheck_5254_;
goto v_resetjp_5236_;
}
else
{
lean_inc(v_a_5235_);
lean_dec(v___x_5234_);
v___x_5237_ = lean_box(0);
v_isShared_5238_ = v_isSharedCheck_5254_;
goto v_resetjp_5236_;
}
v_resetjp_5236_:
{
if (lean_obj_tag(v_a_5235_) == 1)
{
lean_object* v_val_5239_; lean_object* v___x_5241_; uint8_t v_isShared_5242_; uint8_t v_isSharedCheck_5249_; 
lean_del_object(v___x_5237_);
v_val_5239_ = lean_ctor_get(v_a_5235_, 0);
v_isSharedCheck_5249_ = !lean_is_exclusive(v_a_5235_);
if (v_isSharedCheck_5249_ == 0)
{
v___x_5241_ = v_a_5235_;
v_isShared_5242_ = v_isSharedCheck_5249_;
goto v_resetjp_5240_;
}
else
{
lean_inc(v_val_5239_);
lean_dec(v_a_5235_);
v___x_5241_ = lean_box(0);
v_isShared_5242_ = v_isSharedCheck_5249_;
goto v_resetjp_5240_;
}
v_resetjp_5240_:
{
lean_object* v___x_5243_; lean_object* v___x_5245_; 
v___x_5243_ = l_Lean_ConstantInfo_name(v_info_5218_);
lean_dec_ref(v_info_5218_);
if (v_isShared_5242_ == 0)
{
lean_ctor_set_tag(v___x_5241_, 0);
lean_ctor_set(v___x_5241_, 0, v___x_5243_);
v___x_5245_ = v___x_5241_;
goto v_reusejp_5244_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v___x_5243_);
v___x_5245_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5244_;
}
v_reusejp_5244_:
{
uint8_t v___x_5246_; lean_object* v___x_5247_; 
v___x_5246_ = lean_unbox(v_a_5229_);
lean_dec(v_a_5229_);
v___x_5247_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_val_5239_, v___x_5245_, v___x_5246_, v_a_5231_, v___y_5198_, v___y_5199_);
return v___x_5247_;
}
}
}
else
{
lean_object* v___x_5250_; lean_object* v___x_5252_; 
lean_dec(v_a_5235_);
lean_dec(v_a_5231_);
lean_dec(v_a_5229_);
lean_dec_ref(v_info_5218_);
v___x_5250_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5238_ == 0)
{
lean_ctor_set(v___x_5237_, 0, v___x_5250_);
v___x_5252_ = v___x_5237_;
goto v_reusejp_5251_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v___x_5250_);
v___x_5252_ = v_reuseFailAlloc_5253_;
goto v_reusejp_5251_;
}
v_reusejp_5251_:
{
return v___x_5252_;
}
}
}
}
else
{
lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5260_; 
lean_dec(v_val_5214_);
v___x_5255_ = l_Lean_ConstantInfo_name(v_info_5218_);
lean_dec_ref(v_info_5218_);
v___x_5256_ = l_Lean_Name_getString_x21(v___x_5255_);
v___x_5257_ = lean_box(0);
v___x_5258_ = l_Lean_Name_str___override(v___x_5257_, v___x_5256_);
if (v_isShared_5217_ == 0)
{
lean_ctor_set_tag(v___x_5216_, 0);
lean_ctor_set(v___x_5216_, 0, v___x_5255_);
v___x_5260_ = v___x_5216_;
goto v_reusejp_5259_;
}
else
{
lean_object* v_reuseFailAlloc_5272_; 
v_reuseFailAlloc_5272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5272_, 0, v___x_5255_);
v___x_5260_ = v_reuseFailAlloc_5272_;
goto v_reusejp_5259_;
}
v_reusejp_5259_:
{
uint8_t v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5264_; uint8_t v_isShared_5265_; uint8_t v_isSharedCheck_5270_; 
v___x_5261_ = lean_unbox(v_a_5229_);
lean_dec(v_a_5229_);
v___x_5262_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_5258_, v___x_5260_, v___x_5261_, v_a_5231_, v___y_5198_, v___y_5199_);
v_isSharedCheck_5270_ = !lean_is_exclusive(v___x_5262_);
if (v_isSharedCheck_5270_ == 0)
{
lean_object* v_unused_5271_; 
v_unused_5271_ = lean_ctor_get(v___x_5262_, 0);
lean_dec(v_unused_5271_);
v___x_5264_ = v___x_5262_;
v_isShared_5265_ = v_isSharedCheck_5270_;
goto v_resetjp_5263_;
}
else
{
lean_dec(v___x_5262_);
v___x_5264_ = lean_box(0);
v_isShared_5265_ = v_isSharedCheck_5270_;
goto v_resetjp_5263_;
}
v_resetjp_5263_:
{
lean_object* v___x_5266_; lean_object* v___x_5268_; 
v___x_5266_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 0, v___x_5266_);
v___x_5268_ = v___x_5264_;
goto v_reusejp_5267_;
}
else
{
lean_object* v_reuseFailAlloc_5269_; 
v_reuseFailAlloc_5269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5269_, 0, v___x_5266_);
v___x_5268_ = v_reuseFailAlloc_5269_;
goto v_reusejp_5267_;
}
v_reusejp_5267_:
{
return v___x_5268_;
}
}
}
}
}
else
{
lean_object* v_a_5273_; lean_object* v___x_5275_; uint8_t v_isShared_5276_; uint8_t v_isSharedCheck_5280_; 
lean_dec(v_a_5229_);
lean_dec_ref(v_info_5218_);
lean_del_object(v___x_5216_);
lean_dec(v_val_5214_);
v_a_5273_ = lean_ctor_get(v___x_5230_, 0);
v_isSharedCheck_5280_ = !lean_is_exclusive(v___x_5230_);
if (v_isSharedCheck_5280_ == 0)
{
v___x_5275_ = v___x_5230_;
v_isShared_5276_ = v_isSharedCheck_5280_;
goto v_resetjp_5274_;
}
else
{
lean_inc(v_a_5273_);
lean_dec(v___x_5230_);
v___x_5275_ = lean_box(0);
v_isShared_5276_ = v_isSharedCheck_5280_;
goto v_resetjp_5274_;
}
v_resetjp_5274_:
{
lean_object* v___x_5278_; 
if (v_isShared_5276_ == 0)
{
v___x_5278_ = v___x_5275_;
goto v_reusejp_5277_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v_a_5273_);
v___x_5278_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5277_;
}
v_reusejp_5277_:
{
return v___x_5278_;
}
}
}
}
else
{
lean_object* v_a_5281_; lean_object* v___x_5283_; uint8_t v_isShared_5284_; uint8_t v_isSharedCheck_5288_; 
lean_dec_ref(v_tags_5220_);
lean_dec_ref(v_info_5218_);
lean_del_object(v___x_5216_);
lean_dec(v_val_5214_);
v_a_5281_ = lean_ctor_get(v___x_5228_, 0);
v_isSharedCheck_5288_ = !lean_is_exclusive(v___x_5228_);
if (v_isSharedCheck_5288_ == 0)
{
v___x_5283_ = v___x_5228_;
v_isShared_5284_ = v_isSharedCheck_5288_;
goto v_resetjp_5282_;
}
else
{
lean_inc(v_a_5281_);
lean_dec(v___x_5228_);
v___x_5283_ = lean_box(0);
v_isShared_5284_ = v_isSharedCheck_5288_;
goto v_resetjp_5282_;
}
v_resetjp_5282_:
{
lean_object* v___x_5286_; 
if (v_isShared_5284_ == 0)
{
v___x_5286_ = v___x_5283_;
goto v_reusejp_5285_;
}
else
{
lean_object* v_reuseFailAlloc_5287_; 
v_reuseFailAlloc_5287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5287_, 0, v_a_5281_);
v___x_5286_ = v_reuseFailAlloc_5287_;
goto v_reusejp_5285_;
}
v_reusejp_5285_:
{
return v___x_5286_;
}
}
}
}
else
{
lean_object* v___x_5289_; lean_object* v___x_5291_; 
lean_dec_ref(v_tags_5220_);
lean_dec_ref(v_kind_5219_);
lean_dec_ref(v_info_5218_);
lean_del_object(v___x_5216_);
lean_dec(v_val_5214_);
v___x_5289_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5225_ == 0)
{
lean_ctor_set(v___x_5224_, 0, v___x_5289_);
v___x_5291_ = v___x_5224_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v___x_5289_);
v___x_5291_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
return v___x_5291_;
}
}
}
}
else
{
lean_object* v_a_5294_; lean_object* v___x_5296_; uint8_t v_isShared_5297_; uint8_t v_isSharedCheck_5301_; 
lean_dec_ref(v_tags_5220_);
lean_dec_ref(v_kind_5219_);
lean_dec_ref(v_info_5218_);
lean_del_object(v___x_5216_);
lean_dec(v_val_5214_);
v_a_5294_ = lean_ctor_get(v___x_5221_, 0);
v_isSharedCheck_5301_ = !lean_is_exclusive(v___x_5221_);
if (v_isSharedCheck_5301_ == 0)
{
v___x_5296_ = v___x_5221_;
v_isShared_5297_ = v_isSharedCheck_5301_;
goto v_resetjp_5295_;
}
else
{
lean_inc(v_a_5294_);
lean_dec(v___x_5221_);
v___x_5296_ = lean_box(0);
v_isShared_5297_ = v_isSharedCheck_5301_;
goto v_resetjp_5295_;
}
v_resetjp_5295_:
{
lean_object* v___x_5299_; 
if (v_isShared_5297_ == 0)
{
v___x_5299_ = v___x_5296_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5300_; 
v_reuseFailAlloc_5300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5300_, 0, v_a_5294_);
v___x_5299_ = v_reuseFailAlloc_5300_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
return v___x_5299_;
}
}
}
}
}
else
{
lean_object* v___x_5303_; lean_object* v___x_5305_; 
lean_dec(v_a_5210_);
lean_dec_ref(v_decl_5197_);
lean_dec(v___x_5194_);
v___x_5303_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5213_ == 0)
{
lean_ctor_set(v___x_5212_, 0, v___x_5303_);
v___x_5305_ = v___x_5212_;
goto v_reusejp_5304_;
}
else
{
lean_object* v_reuseFailAlloc_5306_; 
v_reuseFailAlloc_5306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5306_, 0, v___x_5303_);
v___x_5305_ = v_reuseFailAlloc_5306_;
goto v_reusejp_5304_;
}
v_reusejp_5304_:
{
return v___x_5305_;
}
}
}
}
else
{
lean_object* v___x_5308_; lean_object* v___x_5309_; 
lean_dec_ref(v_decl_5197_);
lean_dec(v_declName_5196_);
lean_dec(v___x_5194_);
v___x_5308_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5309_, 0, v___x_5308_);
return v___x_5309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__0___boxed(lean_object* v___x_5310_, lean_object* v_id_5311_, lean_object* v_declName_5312_, lean_object* v_decl_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_){
_start:
{
lean_object* v_res_5322_; 
v_res_5322_ = l_Lean_Server_Completion_dotIdCompletion___lam__0(v___x_5310_, v_id_5311_, v_declName_5312_, v_decl_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_);
lean_dec(v___y_5320_);
lean_dec_ref(v___y_5319_);
lean_dec(v___y_5318_);
lean_dec_ref(v___y_5317_);
lean_dec_ref(v___y_5316_);
lean_dec(v___y_5315_);
lean_dec_ref(v___y_5314_);
lean_dec(v_id_5311_);
return v_res_5322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__1(lean_object* v_expectedType_x3f_5323_, lean_object* v_id_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_){
_start:
{
if (lean_obj_tag(v_expectedType_x3f_5323_) == 1)
{
lean_object* v_val_5333_; lean_object* v___x_5334_; 
v_val_5333_ = lean_ctor_get(v_expectedType_x3f_5323_, 0);
lean_inc(v_val_5333_);
lean_dec_ref_known(v_expectedType_x3f_5323_, 1);
v___x_5334_ = l_Lean_Server_Completion_getDotIdCompletionTypeNames(v_val_5333_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_);
if (lean_obj_tag(v___x_5334_) == 0)
{
lean_object* v_a_5335_; lean_object* v___x_5337_; uint8_t v_isShared_5338_; uint8_t v_isSharedCheck_5349_; 
v_a_5335_ = lean_ctor_get(v___x_5334_, 0);
v_isSharedCheck_5349_ = !lean_is_exclusive(v___x_5334_);
if (v_isSharedCheck_5349_ == 0)
{
v___x_5337_ = v___x_5334_;
v_isShared_5338_ = v_isSharedCheck_5349_;
goto v_resetjp_5336_;
}
else
{
lean_inc(v_a_5335_);
lean_dec(v___x_5334_);
v___x_5337_ = lean_box(0);
v_isShared_5338_ = v_isSharedCheck_5349_;
goto v_resetjp_5336_;
}
v_resetjp_5336_:
{
lean_object* v___x_5339_; lean_object* v___x_5340_; uint8_t v___x_5341_; 
v___x_5339_ = lean_array_get_size(v_a_5335_);
v___x_5340_ = lean_unsigned_to_nat(0u);
v___x_5341_ = lean_nat_dec_eq(v___x_5339_, v___x_5340_);
if (v___x_5341_ == 0)
{
lean_object* v___x_5342_; lean_object* v___f_5343_; lean_object* v___x_5344_; 
lean_del_object(v___x_5337_);
v___x_5342_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(v_a_5335_);
lean_dec(v_a_5335_);
v___f_5343_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotIdCompletion___lam__0___boxed), 12, 2);
lean_closure_set(v___f_5343_, 0, v___x_5342_);
lean_closure_set(v___f_5343_, 1, v_id_5324_);
v___x_5344_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___f_5343_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_);
return v___x_5344_;
}
else
{
lean_object* v___x_5345_; lean_object* v___x_5347_; 
lean_dec(v_a_5335_);
lean_dec(v_id_5324_);
v___x_5345_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5338_ == 0)
{
lean_ctor_set(v___x_5337_, 0, v___x_5345_);
v___x_5347_ = v___x_5337_;
goto v_reusejp_5346_;
}
else
{
lean_object* v_reuseFailAlloc_5348_; 
v_reuseFailAlloc_5348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5348_, 0, v___x_5345_);
v___x_5347_ = v_reuseFailAlloc_5348_;
goto v_reusejp_5346_;
}
v_reusejp_5346_:
{
return v___x_5347_;
}
}
}
}
else
{
lean_object* v_a_5350_; lean_object* v___x_5352_; uint8_t v_isShared_5353_; uint8_t v_isSharedCheck_5357_; 
lean_dec(v_id_5324_);
v_a_5350_ = lean_ctor_get(v___x_5334_, 0);
v_isSharedCheck_5357_ = !lean_is_exclusive(v___x_5334_);
if (v_isSharedCheck_5357_ == 0)
{
v___x_5352_ = v___x_5334_;
v_isShared_5353_ = v_isSharedCheck_5357_;
goto v_resetjp_5351_;
}
else
{
lean_inc(v_a_5350_);
lean_dec(v___x_5334_);
v___x_5352_ = lean_box(0);
v_isShared_5353_ = v_isSharedCheck_5357_;
goto v_resetjp_5351_;
}
v_resetjp_5351_:
{
lean_object* v___x_5355_; 
if (v_isShared_5353_ == 0)
{
v___x_5355_ = v___x_5352_;
goto v_reusejp_5354_;
}
else
{
lean_object* v_reuseFailAlloc_5356_; 
v_reuseFailAlloc_5356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5356_, 0, v_a_5350_);
v___x_5355_ = v_reuseFailAlloc_5356_;
goto v_reusejp_5354_;
}
v_reusejp_5354_:
{
return v___x_5355_;
}
}
}
}
else
{
lean_object* v___x_5358_; lean_object* v___x_5359_; 
lean_dec(v_id_5324_);
lean_dec(v_expectedType_x3f_5323_);
v___x_5358_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5359_, 0, v___x_5358_);
return v___x_5359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__1___boxed(lean_object* v_expectedType_x3f_5360_, lean_object* v_id_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_){
_start:
{
lean_object* v_res_5370_; 
v_res_5370_ = l_Lean_Server_Completion_dotIdCompletion___lam__1(v_expectedType_x3f_5360_, v_id_5361_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_);
lean_dec(v___y_5368_);
lean_dec_ref(v___y_5367_);
lean_dec(v___y_5366_);
lean_dec_ref(v___y_5365_);
lean_dec_ref(v___y_5364_);
lean_dec(v___y_5363_);
lean_dec_ref(v___y_5362_);
return v_res_5370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion(lean_object* v_uri_5371_, lean_object* v_pos_5372_, lean_object* v_completionInfoPos_5373_, lean_object* v_ctx_5374_, lean_object* v_lctx_5375_, lean_object* v_id_5376_, lean_object* v_expectedType_x3f_5377_, lean_object* v_a_5378_){
_start:
{
lean_object* v___y_5380_; lean_object* v___x_5381_; 
v___y_5380_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotIdCompletion___lam__1___boxed), 10, 2);
lean_closure_set(v___y_5380_, 0, v_expectedType_x3f_5377_);
lean_closure_set(v___y_5380_, 1, v_id_5376_);
v___x_5381_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5371_, v_pos_5372_, v_completionInfoPos_5373_, v_ctx_5374_, v_lctx_5375_, v___y_5380_, v_a_5378_);
return v___x_5381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___boxed(lean_object* v_uri_5382_, lean_object* v_pos_5383_, lean_object* v_completionInfoPos_5384_, lean_object* v_ctx_5385_, lean_object* v_lctx_5386_, lean_object* v_id_5387_, lean_object* v_expectedType_x3f_5388_, lean_object* v_a_5389_, lean_object* v_a_5390_){
_start:
{
lean_object* v_res_5391_; 
v_res_5391_ = l_Lean_Server_Completion_dotIdCompletion(v_uri_5382_, v_pos_5383_, v_completionInfoPos_5384_, v_ctx_5385_, v_lctx_5386_, v_id_5387_, v_expectedType_x3f_5388_, v_a_5389_);
lean_dec_ref(v_a_5389_);
return v_res_5391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(lean_object* v___y_5398_, lean_object* v_as_5399_, size_t v_sz_5400_, size_t v_i_5401_, lean_object* v_b_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_){
_start:
{
lean_object* v_a_5407_; uint8_t v___x_5411_; 
v___x_5411_ = lean_usize_dec_lt(v_i_5401_, v_sz_5400_);
if (v___x_5411_ == 0)
{
lean_object* v___x_5412_; lean_object* v___x_5413_; 
v___x_5412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5412_, 0, v_b_5402_);
v___x_5413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5413_, 0, v___x_5412_);
return v___x_5413_;
}
else
{
lean_object* v___x_5414_; lean_object* v_a_5415_; 
v___x_5414_ = lean_box(0);
v_a_5415_ = lean_array_uget_borrowed(v_as_5399_, v_i_5401_);
if (lean_obj_tag(v_a_5415_) == 1)
{
lean_object* v_str_5416_; uint8_t v___x_5417_; uint8_t v___x_5418_; 
v_str_5416_ = lean_ctor_get(v_a_5415_, 1);
v___x_5417_ = l_String_charactersIn(v___y_5398_, v_str_5416_);
v___x_5418_ = lean_bool_not(v___x_5417_);
if (v___x_5418_ == 0)
{
lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; 
v___x_5419_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__1));
v___x_5420_ = lean_box(0);
v___x_5421_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__2));
lean_inc_ref(v_str_5416_);
v___x_5422_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5422_, 0, v_str_5416_);
lean_ctor_set(v___x_5422_, 1, v___x_5419_);
lean_ctor_set(v___x_5422_, 2, v___x_5420_);
lean_ctor_set(v___x_5422_, 3, v___x_5421_);
lean_ctor_set(v___x_5422_, 4, v___x_5420_);
lean_ctor_set(v___x_5422_, 5, v___x_5420_);
lean_ctor_set(v___x_5422_, 6, v___x_5420_);
lean_ctor_set(v___x_5422_, 7, v___x_5420_);
v___x_5423_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(v___x_5422_, v___x_5420_, v___y_5403_, v___y_5404_);
if (lean_obj_tag(v___x_5423_) == 0)
{
lean_object* v_a_5424_; 
v_a_5424_ = lean_ctor_get(v___x_5423_, 0);
lean_inc(v_a_5424_);
if (lean_obj_tag(v_a_5424_) == 0)
{
lean_dec_ref_known(v_a_5424_, 1);
return v___x_5423_;
}
else
{
lean_dec_ref_known(v_a_5424_, 1);
lean_dec_ref_known(v___x_5423_, 1);
v_a_5407_ = v___x_5414_;
goto v___jp_5406_;
}
}
else
{
return v___x_5423_;
}
}
else
{
v_a_5407_ = v___x_5414_;
goto v___jp_5406_;
}
}
else
{
v_a_5407_ = v___x_5414_;
goto v___jp_5406_;
}
}
v___jp_5406_:
{
size_t v___x_5408_; size_t v___x_5409_; 
v___x_5408_ = ((size_t)1ULL);
v___x_5409_ = lean_usize_add(v_i_5401_, v___x_5408_);
v_i_5401_ = v___x_5409_;
v_b_5402_ = v_a_5407_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___boxed(lean_object* v___y_5425_, lean_object* v_as_5426_, lean_object* v_sz_5427_, lean_object* v_i_5428_, lean_object* v_b_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_){
_start:
{
size_t v_sz_boxed_5433_; size_t v_i_boxed_5434_; lean_object* v_res_5435_; 
v_sz_boxed_5433_ = lean_unbox_usize(v_sz_5427_);
lean_dec(v_sz_5427_);
v_i_boxed_5434_ = lean_unbox_usize(v_i_5428_);
lean_dec(v_i_5428_);
v_res_5435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5425_, v_as_5426_, v_sz_boxed_5433_, v_i_boxed_5434_, v_b_5429_, v___y_5430_, v___y_5431_);
lean_dec(v___y_5431_);
lean_dec_ref(v___y_5430_);
lean_dec_ref(v_as_5426_);
lean_dec_ref(v___y_5425_);
return v_res_5435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lam__0(lean_object* v_structName_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_){
_start:
{
lean_object* v___x_5446_; lean_object* v_env_5447_; uint8_t v___x_5448_; lean_object* v_fieldNames_5449_; lean_object* v___x_5450_; size_t v_sz_5451_; size_t v___x_5452_; lean_object* v___x_5453_; 
v___x_5446_ = lean_st_ref_get(v___y_5444_);
v_env_5447_ = lean_ctor_get(v___x_5446_, 0);
lean_inc_ref(v_env_5447_);
lean_dec(v___x_5446_);
v___x_5448_ = 0;
v_fieldNames_5449_ = l_Lean_getStructureFieldsFlattened(v_env_5447_, v_structName_5436_, v___x_5448_);
v___x_5450_ = lean_box(0);
v_sz_5451_ = lean_array_size(v_fieldNames_5449_);
v___x_5452_ = ((size_t)0ULL);
v___x_5453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5437_, v_fieldNames_5449_, v_sz_5451_, v___x_5452_, v___x_5450_, v___y_5438_, v___y_5439_);
lean_dec_ref(v_fieldNames_5449_);
if (lean_obj_tag(v___x_5453_) == 0)
{
lean_object* v_a_5454_; 
v_a_5454_ = lean_ctor_get(v___x_5453_, 0);
lean_inc(v_a_5454_);
if (lean_obj_tag(v_a_5454_) == 0)
{
lean_dec_ref_known(v_a_5454_, 1);
return v___x_5453_;
}
else
{
lean_object* v___x_5456_; uint8_t v_isShared_5457_; uint8_t v_isSharedCheck_5462_; 
lean_dec_ref_known(v_a_5454_, 1);
v_isSharedCheck_5462_ = !lean_is_exclusive(v___x_5453_);
if (v_isSharedCheck_5462_ == 0)
{
lean_object* v_unused_5463_; 
v_unused_5463_ = lean_ctor_get(v___x_5453_, 0);
lean_dec(v_unused_5463_);
v___x_5456_ = v___x_5453_;
v_isShared_5457_ = v_isSharedCheck_5462_;
goto v_resetjp_5455_;
}
else
{
lean_dec(v___x_5453_);
v___x_5456_ = lean_box(0);
v_isShared_5457_ = v_isSharedCheck_5462_;
goto v_resetjp_5455_;
}
v_resetjp_5455_:
{
lean_object* v___x_5458_; lean_object* v___x_5460_; 
v___x_5458_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5457_ == 0)
{
lean_ctor_set(v___x_5456_, 0, v___x_5458_);
v___x_5460_ = v___x_5456_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v___x_5458_);
v___x_5460_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
return v___x_5460_;
}
}
}
}
else
{
return v___x_5453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lam__0___boxed(lean_object* v_structName_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_){
_start:
{
lean_object* v_res_5474_; 
v_res_5474_ = l_Lean_Server_Completion_fieldIdCompletion___lam__0(v_structName_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_);
lean_dec(v___y_5472_);
lean_dec_ref(v___y_5471_);
lean_dec(v___y_5470_);
lean_dec_ref(v___y_5469_);
lean_dec_ref(v___y_5468_);
lean_dec(v___y_5467_);
lean_dec_ref(v___y_5466_);
lean_dec_ref(v___y_5465_);
return v_res_5474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion(lean_object* v_uri_5476_, lean_object* v_pos_5477_, lean_object* v_completionInfoPos_5478_, lean_object* v_ctx_5479_, lean_object* v_lctx_5480_, lean_object* v_id_5481_, lean_object* v_structName_5482_, lean_object* v_a_5483_){
_start:
{
lean_object* v___y_5486_; 
if (lean_obj_tag(v_id_5481_) == 0)
{
lean_object* v___x_5489_; 
v___x_5489_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v___y_5486_ = v___x_5489_;
goto v___jp_5485_;
}
else
{
lean_object* v_val_5490_; uint8_t v___x_5491_; lean_object* v___x_5492_; 
v_val_5490_ = lean_ctor_get(v_id_5481_, 0);
lean_inc(v_val_5490_);
lean_dec_ref_known(v_id_5481_, 1);
v___x_5491_ = 1;
v___x_5492_ = l_Lean_Name_toString(v_val_5490_, v___x_5491_);
v___y_5486_ = v___x_5492_;
goto v___jp_5485_;
}
v___jp_5485_:
{
lean_object* v___f_5487_; lean_object* v___x_5488_; 
v___f_5487_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_fieldIdCompletion___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5487_, 0, v_structName_5482_);
lean_closure_set(v___f_5487_, 1, v___y_5486_);
v___x_5488_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5476_, v_pos_5477_, v_completionInfoPos_5478_, v_ctx_5479_, v_lctx_5480_, v___f_5487_, v_a_5483_);
return v___x_5488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___boxed(lean_object* v_uri_5493_, lean_object* v_pos_5494_, lean_object* v_completionInfoPos_5495_, lean_object* v_ctx_5496_, lean_object* v_lctx_5497_, lean_object* v_id_5498_, lean_object* v_structName_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_){
_start:
{
lean_object* v_res_5502_; 
v_res_5502_ = l_Lean_Server_Completion_fieldIdCompletion(v_uri_5493_, v_pos_5494_, v_completionInfoPos_5495_, v_ctx_5496_, v_lctx_5497_, v_id_5498_, v_structName_5499_, v_a_5500_);
lean_dec_ref(v_a_5500_);
return v_res_5502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0(lean_object* v___y_5503_, lean_object* v_as_5504_, size_t v_sz_5505_, size_t v_i_5506_, lean_object* v_b_5507_, lean_object* v___y_5508_, lean_object* v___y_5509_, lean_object* v___y_5510_, lean_object* v___y_5511_, lean_object* v___y_5512_, lean_object* v___y_5513_, lean_object* v___y_5514_){
_start:
{
lean_object* v___x_5516_; 
v___x_5516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5503_, v_as_5504_, v_sz_5505_, v_i_5506_, v_b_5507_, v___y_5508_, v___y_5509_);
return v___x_5516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___boxed(lean_object* v___y_5517_, lean_object* v_as_5518_, lean_object* v_sz_5519_, lean_object* v_i_5520_, lean_object* v_b_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_, lean_object* v___y_5527_, lean_object* v___y_5528_, lean_object* v___y_5529_){
_start:
{
size_t v_sz_boxed_5530_; size_t v_i_boxed_5531_; lean_object* v_res_5532_; 
v_sz_boxed_5530_ = lean_unbox_usize(v_sz_5519_);
lean_dec(v_sz_5519_);
v_i_boxed_5531_ = lean_unbox_usize(v_i_5520_);
lean_dec(v_i_5520_);
v_res_5532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0(v___y_5517_, v_as_5518_, v_sz_boxed_5530_, v_i_boxed_5531_, v_b_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_, v___y_5528_);
lean_dec(v___y_5528_);
lean_dec_ref(v___y_5527_);
lean_dec(v___y_5526_);
lean_dec_ref(v___y_5525_);
lean_dec_ref(v___y_5524_);
lean_dec(v___y_5523_);
lean_dec_ref(v___y_5522_);
lean_dec_ref(v_as_5518_);
lean_dec_ref(v___y_5517_);
return v_res_5532_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0(void){
_start:
{
uint32_t v___x_5533_; lean_object* v___x_5534_; 
v___x_5533_ = 32;
v___x_5534_ = l_Char_utf8Size(v___x_5533_);
return v___x_5534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0(lean_object* v_fst_5535_, lean_object* v_caps_5536_, lean_object* v_mkItem_5537_, lean_object* v_ctx_5538_, lean_object* v_stx_5539_, uint8_t v_snd_5540_, lean_object* v_x_5541_, lean_object* v_____s_5542_){
_start:
{
lean_object* v_fst_5543_; lean_object* v_snd_5544_; lean_object* v___x_5546_; uint8_t v_isShared_5547_; uint8_t v_isSharedCheck_5601_; 
v_fst_5543_ = lean_ctor_get(v_x_5541_, 0);
v_snd_5544_ = lean_ctor_get(v_x_5541_, 1);
v_isSharedCheck_5601_ = !lean_is_exclusive(v_x_5541_);
if (v_isSharedCheck_5601_ == 0)
{
v___x_5546_ = v_x_5541_;
v_isShared_5547_ = v_isSharedCheck_5601_;
goto v_resetjp_5545_;
}
else
{
lean_inc(v_snd_5544_);
lean_inc(v_fst_5543_);
lean_dec(v_x_5541_);
v___x_5546_ = lean_box(0);
v_isShared_5547_ = v_isSharedCheck_5601_;
goto v_resetjp_5545_;
}
v_resetjp_5545_:
{
lean_object* v___y_5549_; uint8_t v___x_5553_; lean_object* v___x_5554_; lean_object* v___y_5556_; lean_object* v___y_5557_; uint8_t v___y_5576_; uint8_t v___x_5588_; 
v___x_5553_ = 1;
lean_inc(v_fst_5543_);
v___x_5554_ = l_Lean_Name_toString(v_fst_5543_, v___x_5553_);
v___x_5588_ = l_String_charactersIn(v_fst_5535_, v___x_5554_);
if (v___x_5588_ == 0)
{
lean_object* v___x_5589_; 
lean_dec_ref(v___x_5554_);
lean_del_object(v___x_5546_);
lean_dec(v_snd_5544_);
lean_dec(v_fst_5543_);
lean_dec_ref(v_ctx_5538_);
lean_dec_ref(v_mkItem_5537_);
v___x_5589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5589_, 0, v_____s_5542_);
return v___x_5589_;
}
else
{
lean_object* v_textDocument_x3f_5590_; 
v_textDocument_x3f_5590_ = lean_ctor_get(v_caps_5536_, 0);
if (lean_obj_tag(v_textDocument_x3f_5590_) == 0)
{
uint8_t v___x_5591_; 
v___x_5591_ = 0;
v___y_5576_ = v___x_5591_;
goto v___jp_5575_;
}
else
{
lean_object* v_val_5592_; lean_object* v_completion_x3f_5593_; 
v_val_5592_ = lean_ctor_get(v_textDocument_x3f_5590_, 0);
v_completion_x3f_5593_ = lean_ctor_get(v_val_5592_, 0);
if (lean_obj_tag(v_completion_x3f_5593_) == 0)
{
uint8_t v___x_5594_; 
v___x_5594_ = 0;
v___y_5576_ = v___x_5594_;
goto v___jp_5575_;
}
else
{
lean_object* v_val_5595_; 
v_val_5595_ = lean_ctor_get(v_completion_x3f_5593_, 0);
if (lean_obj_tag(v_val_5595_) == 0)
{
uint8_t v___x_5596_; 
v___x_5596_ = 0;
v___y_5576_ = v___x_5596_;
goto v___jp_5575_;
}
else
{
lean_object* v_val_5597_; 
v_val_5597_ = lean_ctor_get(v_val_5595_, 0);
if (lean_obj_tag(v_val_5597_) == 0)
{
uint8_t v___x_5598_; 
v___x_5598_ = 0;
v___y_5576_ = v___x_5598_;
goto v___jp_5575_;
}
else
{
lean_object* v_val_5599_; uint8_t v___x_5600_; 
v_val_5599_ = lean_ctor_get(v_val_5597_, 0);
v___x_5600_ = lean_unbox(v_val_5599_);
v___y_5576_ = v___x_5600_;
goto v___jp_5575_;
}
}
}
}
}
v___jp_5548_:
{
lean_object* v___x_5550_; lean_object* v_items_5551_; lean_object* v___x_5552_; 
v___x_5550_ = lean_apply_3(v_mkItem_5537_, v_fst_5543_, v_snd_5544_, v___y_5549_);
v_items_5551_ = lean_array_push(v_____s_5542_, v___x_5550_);
v___x_5552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5552_, 0, v_items_5551_);
return v___x_5552_;
}
v___jp_5555_:
{
lean_object* v_toCommandContextInfo_5558_; lean_object* v___x_5560_; uint8_t v_isShared_5561_; uint8_t v_isSharedCheck_5572_; 
v_toCommandContextInfo_5558_ = lean_ctor_get(v_ctx_5538_, 0);
v_isSharedCheck_5572_ = !lean_is_exclusive(v_ctx_5538_);
if (v_isSharedCheck_5572_ == 0)
{
lean_object* v_unused_5573_; lean_object* v_unused_5574_; 
v_unused_5573_ = lean_ctor_get(v_ctx_5538_, 2);
lean_dec(v_unused_5573_);
v_unused_5574_ = lean_ctor_get(v_ctx_5538_, 1);
lean_dec(v_unused_5574_);
v___x_5560_ = v_ctx_5538_;
v_isShared_5561_ = v_isSharedCheck_5572_;
goto v_resetjp_5559_;
}
else
{
lean_inc(v_toCommandContextInfo_5558_);
lean_dec(v_ctx_5538_);
v___x_5560_ = lean_box(0);
v_isShared_5561_ = v_isSharedCheck_5572_;
goto v_resetjp_5559_;
}
v_resetjp_5559_:
{
lean_object* v_fileMap_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v_range_5566_; 
v_fileMap_5562_ = lean_ctor_get(v_toCommandContextInfo_5558_, 2);
lean_inc_ref_n(v_fileMap_5562_, 2);
lean_dec_ref(v_toCommandContextInfo_5558_);
v___x_5563_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5562_, v___y_5556_);
lean_dec(v___y_5556_);
v___x_5564_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5562_, v___y_5557_);
lean_dec(v___y_5557_);
if (v_isShared_5547_ == 0)
{
lean_ctor_set(v___x_5546_, 1, v___x_5564_);
lean_ctor_set(v___x_5546_, 0, v___x_5563_);
v_range_5566_ = v___x_5546_;
goto v_reusejp_5565_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v___x_5563_);
lean_ctor_set(v_reuseFailAlloc_5571_, 1, v___x_5564_);
v_range_5566_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5565_;
}
v_reusejp_5565_:
{
lean_object* v___x_5568_; 
lean_inc_ref(v_range_5566_);
if (v_isShared_5561_ == 0)
{
lean_ctor_set(v___x_5560_, 2, v_range_5566_);
lean_ctor_set(v___x_5560_, 1, v_range_5566_);
lean_ctor_set(v___x_5560_, 0, v___x_5554_);
v___x_5568_ = v___x_5560_;
goto v_reusejp_5567_;
}
else
{
lean_object* v_reuseFailAlloc_5570_; 
v_reuseFailAlloc_5570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5570_, 0, v___x_5554_);
lean_ctor_set(v_reuseFailAlloc_5570_, 1, v_range_5566_);
lean_ctor_set(v_reuseFailAlloc_5570_, 2, v_range_5566_);
v___x_5568_ = v_reuseFailAlloc_5570_;
goto v_reusejp_5567_;
}
v_reusejp_5567_:
{
lean_object* v___x_5569_; 
v___x_5569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5569_, 0, v___x_5568_);
v___y_5549_ = v___x_5569_;
goto v___jp_5548_;
}
}
}
}
v___jp_5575_:
{
uint8_t v___x_5577_; 
v___x_5577_ = lean_bool_not(v___y_5576_);
if (v___x_5577_ == 0)
{
lean_object* v___x_5578_; 
v___x_5578_ = l_Lean_Syntax_getRange_x3f(v_stx_5539_, v___x_5577_);
if (lean_obj_tag(v___x_5578_) == 1)
{
lean_object* v_val_5579_; 
v_val_5579_ = lean_ctor_get(v___x_5578_, 0);
lean_inc(v_val_5579_);
lean_dec_ref_known(v___x_5578_, 1);
if (v_snd_5540_ == 0)
{
lean_object* v_start_5580_; lean_object* v_stop_5581_; 
v_start_5580_ = lean_ctor_get(v_val_5579_, 0);
lean_inc(v_start_5580_);
v_stop_5581_ = lean_ctor_get(v_val_5579_, 1);
lean_inc(v_stop_5581_);
lean_dec(v_val_5579_);
v___y_5556_ = v_start_5580_;
v___y_5557_ = v_stop_5581_;
goto v___jp_5555_;
}
else
{
lean_object* v_start_5582_; lean_object* v_stop_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; 
v_start_5582_ = lean_ctor_get(v_val_5579_, 0);
lean_inc(v_start_5582_);
v_stop_5583_ = lean_ctor_get(v_val_5579_, 1);
lean_inc(v_stop_5583_);
lean_dec(v_val_5579_);
v___x_5584_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0);
v___x_5585_ = lean_nat_add(v_stop_5583_, v___x_5584_);
lean_dec(v_stop_5583_);
v___y_5556_ = v_start_5582_;
v___y_5557_ = v___x_5585_;
goto v___jp_5555_;
}
}
else
{
lean_object* v___x_5586_; 
lean_dec(v___x_5578_);
lean_dec_ref(v___x_5554_);
lean_del_object(v___x_5546_);
lean_dec_ref(v_ctx_5538_);
v___x_5586_ = lean_box(0);
v___y_5549_ = v___x_5586_;
goto v___jp_5548_;
}
}
else
{
lean_object* v___x_5587_; 
lean_dec_ref(v___x_5554_);
lean_del_object(v___x_5546_);
lean_dec_ref(v_ctx_5538_);
v___x_5587_ = lean_box(0);
v___y_5549_ = v___x_5587_;
goto v___jp_5548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___boxed(lean_object* v_fst_5602_, lean_object* v_caps_5603_, lean_object* v_mkItem_5604_, lean_object* v_ctx_5605_, lean_object* v_stx_5606_, lean_object* v_snd_5607_, lean_object* v_x_5608_, lean_object* v_____s_5609_){
_start:
{
uint8_t v_snd_1028__boxed_5610_; lean_object* v_res_5611_; 
v_snd_1028__boxed_5610_ = lean_unbox(v_snd_5607_);
v_res_5611_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0(v_fst_5602_, v_caps_5603_, v_mkItem_5604_, v_ctx_5605_, v_stx_5606_, v_snd_1028__boxed_5610_, v_x_5608_, v_____s_5609_);
lean_dec(v_stx_5606_);
lean_dec_ref(v_caps_5603_);
lean_dec_ref(v_fst_5602_);
return v_res_5611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg(lean_object* v_inst_5613_, lean_object* v_entries_5614_, lean_object* v_stx_5615_, lean_object* v_caps_5616_, lean_object* v_ctx_5617_, lean_object* v_mkItem_5618_){
_start:
{
lean_object* v_fst_5620_; uint8_t v_snd_5621_; uint8_t v___x_5626_; lean_object* v___x_5627_; 
v___x_5626_ = 0;
v___x_5627_ = l_Lean_Syntax_getSubstring_x3f(v_stx_5615_, v___x_5626_, v___x_5626_);
if (lean_obj_tag(v___x_5627_) == 0)
{
lean_object* v___x_5628_; 
v___x_5628_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_5620_ = v___x_5628_;
v_snd_5621_ = v___x_5626_;
goto v___jp_5619_;
}
else
{
lean_object* v_val_5629_; lean_object* v_str_5630_; lean_object* v_startPos_5631_; lean_object* v_stopPos_5632_; uint8_t v___y_5634_; uint8_t v___x_5639_; uint8_t v___x_5640_; 
v_val_5629_ = lean_ctor_get(v___x_5627_, 0);
lean_inc(v_val_5629_);
lean_dec_ref_known(v___x_5627_, 1);
v_str_5630_ = lean_ctor_get(v_val_5629_, 0);
lean_inc_ref(v_str_5630_);
v_startPos_5631_ = lean_ctor_get(v_val_5629_, 1);
lean_inc(v_startPos_5631_);
v_stopPos_5632_ = lean_ctor_get(v_val_5629_, 2);
lean_inc(v_stopPos_5632_);
lean_dec(v_val_5629_);
v___x_5639_ = lean_string_utf8_at_end(v_str_5630_, v_stopPos_5632_);
v___x_5640_ = lean_bool_not(v___x_5639_);
if (v___x_5640_ == 0)
{
v___y_5634_ = v___x_5640_;
goto v___jp_5633_;
}
else
{
uint32_t v___x_5641_; uint32_t v___x_5642_; uint8_t v___x_5643_; 
v___x_5641_ = lean_string_utf8_get(v_str_5630_, v_stopPos_5632_);
v___x_5642_ = 46;
v___x_5643_ = lean_uint32_dec_eq(v___x_5641_, v___x_5642_);
v___y_5634_ = v___x_5643_;
goto v___jp_5633_;
}
v___jp_5633_:
{
if (v___y_5634_ == 0)
{
lean_object* v___x_5635_; 
v___x_5635_ = lean_string_utf8_extract(v_str_5630_, v_startPos_5631_, v_stopPos_5632_);
lean_dec(v_stopPos_5632_);
lean_dec(v_startPos_5631_);
lean_dec_ref(v_str_5630_);
v_fst_5620_ = v___x_5635_;
v_snd_5621_ = v___y_5634_;
goto v___jp_5619_;
}
else
{
lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; 
v___x_5636_ = lean_string_utf8_extract(v_str_5630_, v_startPos_5631_, v_stopPos_5632_);
lean_dec(v_stopPos_5632_);
lean_dec(v_startPos_5631_);
lean_dec_ref(v_str_5630_);
v___x_5637_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_5638_ = lean_string_append(v___x_5636_, v___x_5637_);
v_fst_5620_ = v___x_5638_;
v_snd_5621_ = v___y_5634_;
goto v___jp_5619_;
}
}
}
v___jp_5619_:
{
lean_object* v___x_5622_; lean_object* v___f_5623_; lean_object* v_items_5624_; lean_object* v___x_5625_; 
v___x_5622_ = lean_box(v_snd_5621_);
v___f_5623_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_5623_, 0, v_fst_5620_);
lean_closure_set(v___f_5623_, 1, v_caps_5616_);
lean_closure_set(v___f_5623_, 2, v_mkItem_5618_);
lean_closure_set(v___f_5623_, 3, v_ctx_5617_);
lean_closure_set(v___f_5623_, 4, v_stx_5615_);
lean_closure_set(v___f_5623_, 5, v___x_5622_);
v_items_5624_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v___x_5625_ = lean_apply_4(v_inst_5613_, lean_box(0), v_entries_5614_, v_items_5624_, v___f_5623_);
return v___x_5625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion(lean_object* v_Coll_5644_, lean_object* v_00_u03b1_5645_, lean_object* v_inst_5646_, lean_object* v_entries_5647_, lean_object* v_stx_5648_, lean_object* v_caps_5649_, lean_object* v_ctx_5650_, lean_object* v_mkItem_5651_){
_start:
{
lean_object* v___x_5652_; 
v___x_5652_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg(v_inst_5646_, v_entries_5647_, v_stx_5648_, v_caps_5649_, v_ctx_5650_, v_mkItem_5651_);
return v___x_5652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__0(lean_object* v_options_5658_, lean_object* v_completionInfoPos_5659_, lean_object* v_uri_5660_, lean_object* v_pos_5661_, lean_object* v_name_5662_, lean_object* v_decl_5663_, lean_object* v_textEdit_x3f_5664_){
_start:
{
lean_object* v_defValue_5665_; lean_object* v_descr_5666_; lean_object* v_map_5667_; uint8_t v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___y_5672_; lean_object* v___x_5685_; 
v_defValue_5665_ = lean_ctor_get(v_decl_5663_, 2);
lean_inc_ref(v_defValue_5665_);
v_descr_5666_ = lean_ctor_get(v_decl_5663_, 3);
lean_inc_ref(v_descr_5666_);
lean_dec_ref(v_decl_5663_);
v_map_5667_ = lean_ctor_get(v_options_5658_, 0);
v___x_5668_ = 1;
lean_inc(v_name_5662_);
v___x_5669_ = l_Lean_Name_toString(v_name_5662_, v___x_5668_);
v___x_5670_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__0));
v___x_5685_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5667_, v_name_5662_);
lean_dec(v_name_5662_);
if (lean_obj_tag(v___x_5685_) == 0)
{
v___y_5672_ = v_defValue_5665_;
goto v___jp_5671_;
}
else
{
if (lean_obj_tag(v___x_5685_) == 0)
{
v___y_5672_ = v_defValue_5665_;
goto v___jp_5671_;
}
else
{
lean_object* v_val_5686_; 
lean_dec_ref(v_defValue_5665_);
v_val_5686_ = lean_ctor_get(v___x_5685_, 0);
lean_inc(v_val_5686_);
lean_dec_ref_known(v___x_5685_, 1);
v___y_5672_ = v_val_5686_;
goto v___jp_5671_;
}
}
v___jp_5671_:
{
lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; 
v___x_5673_ = lean_data_value_to_string(v___y_5672_);
v___x_5674_ = lean_string_append(v___x_5670_, v___x_5673_);
lean_dec_ref(v___x_5673_);
v___x_5675_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__1));
v___x_5676_ = lean_string_append(v___x_5674_, v___x_5675_);
v___x_5677_ = lean_string_append(v___x_5676_, v_descr_5666_);
lean_dec_ref(v_descr_5666_);
v___x_5678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5678_, 0, v___x_5677_);
v___x_5679_ = lean_box(0);
v___x_5680_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__2));
v___x_5681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5681_, 0, v_completionInfoPos_5659_);
v___x_5682_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5682_, 0, v_uri_5660_);
lean_ctor_set(v___x_5682_, 1, v_pos_5661_);
lean_ctor_set(v___x_5682_, 2, v___x_5681_);
lean_ctor_set(v___x_5682_, 3, v___x_5679_);
v___x_5683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5683_, 0, v___x_5682_);
v___x_5684_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5684_, 0, v___x_5669_);
lean_ctor_set(v___x_5684_, 1, v___x_5678_);
lean_ctor_set(v___x_5684_, 2, v___x_5679_);
lean_ctor_set(v___x_5684_, 3, v___x_5680_);
lean_ctor_set(v___x_5684_, 4, v_textEdit_x3f_5664_);
lean_ctor_set(v___x_5684_, 5, v___x_5679_);
lean_ctor_set(v___x_5684_, 6, v___x_5683_);
lean_ctor_set(v___x_5684_, 7, v___x_5679_);
return v___x_5684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__0___boxed(lean_object* v_options_5687_, lean_object* v_completionInfoPos_5688_, lean_object* v_uri_5689_, lean_object* v_pos_5690_, lean_object* v_name_5691_, lean_object* v_decl_5692_, lean_object* v_textEdit_x3f_5693_){
_start:
{
lean_object* v_res_5694_; 
v_res_5694_ = l_Lean_Server_Completion_optionCompletion___lam__0(v_options_5687_, v_completionInfoPos_5688_, v_uri_5689_, v_pos_5690_, v_name_5691_, v_decl_5692_, v_textEdit_x3f_5693_);
lean_dec_ref(v_options_5687_);
return v_res_5694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(lean_object* v_mkItem_5695_, lean_object* v_stx_5696_, lean_object* v_ctx_5697_, uint8_t v_snd_5698_, lean_object* v_fst_5699_, lean_object* v_caps_5700_, lean_object* v_init_5701_, lean_object* v_x_5702_){
_start:
{
if (lean_obj_tag(v_x_5702_) == 0)
{
lean_object* v_k_5703_; lean_object* v_v_5704_; lean_object* v_l_5705_; lean_object* v_r_5706_; lean_object* v___x_5707_; lean_object* v_a_5708_; lean_object* v___y_5710_; uint8_t v___x_5714_; lean_object* v___x_5715_; lean_object* v___y_5717_; lean_object* v___y_5718_; uint8_t v___y_5727_; uint8_t v___x_5739_; 
v_k_5703_ = lean_ctor_get(v_x_5702_, 1);
lean_inc_n(v_k_5703_, 2);
v_v_5704_ = lean_ctor_get(v_x_5702_, 2);
lean_inc(v_v_5704_);
v_l_5705_ = lean_ctor_get(v_x_5702_, 3);
lean_inc(v_l_5705_);
v_r_5706_ = lean_ctor_get(v_x_5702_, 4);
lean_inc(v_r_5706_);
lean_dec_ref_known(v_x_5702_, 5);
lean_inc_ref(v_ctx_5697_);
lean_inc_ref(v_mkItem_5695_);
v___x_5707_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5695_, v_stx_5696_, v_ctx_5697_, v_snd_5698_, v_fst_5699_, v_caps_5700_, v_init_5701_, v_l_5705_);
v_a_5708_ = lean_ctor_get(v___x_5707_, 0);
lean_inc(v_a_5708_);
v___x_5714_ = 1;
v___x_5715_ = l_Lean_Name_toString(v_k_5703_, v___x_5714_);
v___x_5739_ = l_String_charactersIn(v_fst_5699_, v___x_5715_);
if (v___x_5739_ == 0)
{
lean_object* v_a_5740_; 
lean_dec_ref(v___x_5715_);
lean_dec(v_a_5708_);
lean_dec(v_v_5704_);
lean_dec(v_k_5703_);
v_a_5740_ = lean_ctor_get(v___x_5707_, 0);
lean_inc(v_a_5740_);
lean_dec_ref(v___x_5707_);
v_init_5701_ = v_a_5740_;
v_x_5702_ = v_r_5706_;
goto _start;
}
else
{
lean_object* v_textDocument_x3f_5742_; 
lean_dec_ref(v___x_5707_);
v_textDocument_x3f_5742_ = lean_ctor_get(v_caps_5700_, 0);
if (lean_obj_tag(v_textDocument_x3f_5742_) == 0)
{
uint8_t v___x_5743_; 
v___x_5743_ = 0;
v___y_5727_ = v___x_5743_;
goto v___jp_5726_;
}
else
{
lean_object* v_val_5744_; lean_object* v_completion_x3f_5745_; 
v_val_5744_ = lean_ctor_get(v_textDocument_x3f_5742_, 0);
v_completion_x3f_5745_ = lean_ctor_get(v_val_5744_, 0);
if (lean_obj_tag(v_completion_x3f_5745_) == 0)
{
uint8_t v___x_5746_; 
v___x_5746_ = 0;
v___y_5727_ = v___x_5746_;
goto v___jp_5726_;
}
else
{
lean_object* v_val_5747_; 
v_val_5747_ = lean_ctor_get(v_completion_x3f_5745_, 0);
if (lean_obj_tag(v_val_5747_) == 0)
{
uint8_t v___x_5748_; 
v___x_5748_ = 0;
v___y_5727_ = v___x_5748_;
goto v___jp_5726_;
}
else
{
lean_object* v_val_5749_; 
v_val_5749_ = lean_ctor_get(v_val_5747_, 0);
if (lean_obj_tag(v_val_5749_) == 0)
{
uint8_t v___x_5750_; 
v___x_5750_ = 0;
v___y_5727_ = v___x_5750_;
goto v___jp_5726_;
}
else
{
lean_object* v_val_5751_; uint8_t v___x_5752_; 
v_val_5751_ = lean_ctor_get(v_val_5749_, 0);
v___x_5752_ = lean_unbox(v_val_5751_);
v___y_5727_ = v___x_5752_;
goto v___jp_5726_;
}
}
}
}
}
v___jp_5709_:
{
lean_object* v___x_5711_; lean_object* v_items_5712_; 
lean_inc_ref(v_mkItem_5695_);
v___x_5711_ = lean_apply_3(v_mkItem_5695_, v_k_5703_, v_v_5704_, v___y_5710_);
v_items_5712_ = lean_array_push(v_a_5708_, v___x_5711_);
v_init_5701_ = v_items_5712_;
v_x_5702_ = v_r_5706_;
goto _start;
}
v___jp_5716_:
{
lean_object* v_toCommandContextInfo_5719_; lean_object* v_fileMap_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v_range_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; 
v_toCommandContextInfo_5719_ = lean_ctor_get(v_ctx_5697_, 0);
v_fileMap_5720_ = lean_ctor_get(v_toCommandContextInfo_5719_, 2);
lean_inc_ref_n(v_fileMap_5720_, 2);
v___x_5721_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5720_, v___y_5717_);
lean_dec(v___y_5717_);
v___x_5722_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5720_, v___y_5718_);
lean_dec(v___y_5718_);
v_range_5723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_range_5723_, 0, v___x_5721_);
lean_ctor_set(v_range_5723_, 1, v___x_5722_);
lean_inc_ref(v_range_5723_);
v___x_5724_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5724_, 0, v___x_5715_);
lean_ctor_set(v___x_5724_, 1, v_range_5723_);
lean_ctor_set(v___x_5724_, 2, v_range_5723_);
v___x_5725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5725_, 0, v___x_5724_);
v___y_5710_ = v___x_5725_;
goto v___jp_5709_;
}
v___jp_5726_:
{
uint8_t v___x_5728_; 
v___x_5728_ = lean_bool_not(v___y_5727_);
if (v___x_5728_ == 0)
{
lean_object* v___x_5729_; 
v___x_5729_ = l_Lean_Syntax_getRange_x3f(v_stx_5696_, v___x_5728_);
if (lean_obj_tag(v___x_5729_) == 1)
{
lean_object* v_val_5730_; 
v_val_5730_ = lean_ctor_get(v___x_5729_, 0);
lean_inc(v_val_5730_);
lean_dec_ref_known(v___x_5729_, 1);
if (v_snd_5698_ == 0)
{
lean_object* v_start_5731_; lean_object* v_stop_5732_; 
v_start_5731_ = lean_ctor_get(v_val_5730_, 0);
lean_inc(v_start_5731_);
v_stop_5732_ = lean_ctor_get(v_val_5730_, 1);
lean_inc(v_stop_5732_);
lean_dec(v_val_5730_);
v___y_5717_ = v_start_5731_;
v___y_5718_ = v_stop_5732_;
goto v___jp_5716_;
}
else
{
lean_object* v_start_5733_; lean_object* v_stop_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; 
v_start_5733_ = lean_ctor_get(v_val_5730_, 0);
lean_inc(v_start_5733_);
v_stop_5734_ = lean_ctor_get(v_val_5730_, 1);
lean_inc(v_stop_5734_);
lean_dec(v_val_5730_);
v___x_5735_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0);
v___x_5736_ = lean_nat_add(v_stop_5734_, v___x_5735_);
lean_dec(v_stop_5734_);
v___y_5717_ = v_start_5733_;
v___y_5718_ = v___x_5736_;
goto v___jp_5716_;
}
}
else
{
lean_object* v___x_5737_; 
lean_dec(v___x_5729_);
lean_dec_ref(v___x_5715_);
v___x_5737_ = lean_box(0);
v___y_5710_ = v___x_5737_;
goto v___jp_5709_;
}
}
else
{
lean_object* v___x_5738_; 
lean_dec_ref(v___x_5715_);
v___x_5738_ = lean_box(0);
v___y_5710_ = v___x_5738_;
goto v___jp_5709_;
}
}
}
else
{
lean_object* v___x_5753_; 
lean_dec_ref(v_ctx_5697_);
lean_dec_ref(v_mkItem_5695_);
v___x_5753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5753_, 0, v_init_5701_);
return v___x_5753_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0___boxed(lean_object* v_mkItem_5754_, lean_object* v_stx_5755_, lean_object* v_ctx_5756_, lean_object* v_snd_5757_, lean_object* v_fst_5758_, lean_object* v_caps_5759_, lean_object* v_init_5760_, lean_object* v_x_5761_){
_start:
{
uint8_t v_snd_1435__boxed_5762_; lean_object* v_res_5763_; 
v_snd_1435__boxed_5762_ = lean_unbox(v_snd_5757_);
v_res_5763_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5754_, v_stx_5755_, v_ctx_5756_, v_snd_1435__boxed_5762_, v_fst_5758_, v_caps_5759_, v_init_5760_, v_x_5761_);
lean_dec_ref(v_caps_5759_);
lean_dec_ref(v_fst_5758_);
lean_dec(v_stx_5755_);
return v_res_5763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(lean_object* v_entries_5764_, lean_object* v_stx_5765_, lean_object* v_caps_5766_, lean_object* v_ctx_5767_, lean_object* v_mkItem_5768_){
_start:
{
lean_object* v_fst_5770_; uint8_t v_snd_5771_; uint8_t v___x_5775_; lean_object* v___x_5776_; 
v___x_5775_ = 0;
v___x_5776_ = l_Lean_Syntax_getSubstring_x3f(v_stx_5765_, v___x_5775_, v___x_5775_);
if (lean_obj_tag(v___x_5776_) == 0)
{
lean_object* v___x_5777_; 
v___x_5777_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_5770_ = v___x_5777_;
v_snd_5771_ = v___x_5775_;
goto v___jp_5769_;
}
else
{
lean_object* v_val_5778_; lean_object* v_str_5779_; lean_object* v_startPos_5780_; lean_object* v_stopPos_5781_; uint8_t v___y_5783_; uint8_t v___x_5788_; uint8_t v___x_5789_; 
v_val_5778_ = lean_ctor_get(v___x_5776_, 0);
lean_inc(v_val_5778_);
lean_dec_ref_known(v___x_5776_, 1);
v_str_5779_ = lean_ctor_get(v_val_5778_, 0);
lean_inc_ref(v_str_5779_);
v_startPos_5780_ = lean_ctor_get(v_val_5778_, 1);
lean_inc(v_startPos_5780_);
v_stopPos_5781_ = lean_ctor_get(v_val_5778_, 2);
lean_inc(v_stopPos_5781_);
lean_dec(v_val_5778_);
v___x_5788_ = lean_string_utf8_at_end(v_str_5779_, v_stopPos_5781_);
v___x_5789_ = lean_bool_not(v___x_5788_);
if (v___x_5789_ == 0)
{
v___y_5783_ = v___x_5789_;
goto v___jp_5782_;
}
else
{
uint32_t v___x_5790_; uint32_t v___x_5791_; uint8_t v___x_5792_; 
v___x_5790_ = lean_string_utf8_get(v_str_5779_, v_stopPos_5781_);
v___x_5791_ = 46;
v___x_5792_ = lean_uint32_dec_eq(v___x_5790_, v___x_5791_);
v___y_5783_ = v___x_5792_;
goto v___jp_5782_;
}
v___jp_5782_:
{
if (v___y_5783_ == 0)
{
lean_object* v___x_5784_; 
v___x_5784_ = lean_string_utf8_extract(v_str_5779_, v_startPos_5780_, v_stopPos_5781_);
lean_dec(v_stopPos_5781_);
lean_dec(v_startPos_5780_);
lean_dec_ref(v_str_5779_);
v_fst_5770_ = v___x_5784_;
v_snd_5771_ = v___y_5783_;
goto v___jp_5769_;
}
else
{
lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; 
v___x_5785_ = lean_string_utf8_extract(v_str_5779_, v_startPos_5780_, v_stopPos_5781_);
lean_dec(v_stopPos_5781_);
lean_dec(v_startPos_5780_);
lean_dec_ref(v_str_5779_);
v___x_5786_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_5787_ = lean_string_append(v___x_5785_, v___x_5786_);
v_fst_5770_ = v___x_5787_;
v_snd_5771_ = v___y_5783_;
goto v___jp_5769_;
}
}
}
v___jp_5769_:
{
lean_object* v_items_5772_; lean_object* v___x_5773_; lean_object* v_a_5774_; 
v_items_5772_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v___x_5773_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5768_, v_stx_5765_, v_ctx_5767_, v_snd_5771_, v_fst_5770_, v_caps_5766_, v_items_5772_, v_entries_5764_);
lean_dec_ref(v_fst_5770_);
v_a_5774_ = lean_ctor_get(v___x_5773_, 0);
lean_inc(v_a_5774_);
lean_dec_ref(v___x_5773_);
return v_a_5774_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(lean_object* v_hi_5935_, lean_object* v_pivot_5936_, lean_object* v_as_5937_, lean_object* v_i_5938_, lean_object* v_k_5939_){
_start:
{
uint8_t v___x_5940_; 
v___x_5940_ = lean_nat_dec_lt(v_k_5939_, v_hi_5935_);
if (v___x_5940_ == 0)
{
lean_object* v___x_5941_; lean_object* v___x_5942_; 
lean_dec(v_k_5939_);
lean_dec_ref(v_pivot_5936_);
v___x_5941_ = lean_array_fswap(v_as_5937_, v_i_5938_, v_hi_5935_);
v___x_5942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5942_, 0, v_i_5938_);
lean_ctor_set(v___x_5942_, 1, v___x_5941_);
return v___x_5942_;
}
else
{
lean_object* v___x_5943_; lean_object* v_fst_5944_; lean_object* v_fst_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; uint8_t v___x_5948_; 
v___x_5943_ = lean_array_fget_borrowed(v_as_5937_, v_k_5939_);
v_fst_5944_ = lean_ctor_get(v___x_5943_, 0);
v_fst_5945_ = lean_ctor_get(v_pivot_5936_, 0);
lean_inc(v_fst_5944_);
v___x_5946_ = l_Lean_Name_toString(v_fst_5944_, v___x_5940_);
lean_inc(v_fst_5945_);
v___x_5947_ = l_Lean_Name_toString(v_fst_5945_, v___x_5940_);
v___x_5948_ = lean_string_dec_lt(v___x_5946_, v___x_5947_);
lean_dec_ref(v___x_5947_);
lean_dec_ref(v___x_5946_);
if (v___x_5948_ == 0)
{
lean_object* v___x_5949_; lean_object* v___x_5950_; 
v___x_5949_ = lean_unsigned_to_nat(1u);
v___x_5950_ = lean_nat_add(v_k_5939_, v___x_5949_);
lean_dec(v_k_5939_);
v_k_5939_ = v___x_5950_;
goto _start;
}
else
{
lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; 
v___x_5952_ = lean_array_fswap(v_as_5937_, v_i_5938_, v_k_5939_);
v___x_5953_ = lean_unsigned_to_nat(1u);
v___x_5954_ = lean_nat_add(v_i_5938_, v___x_5953_);
lean_dec(v_i_5938_);
v___x_5955_ = lean_nat_add(v_k_5939_, v___x_5953_);
lean_dec(v_k_5939_);
v_as_5937_ = v___x_5952_;
v_i_5938_ = v___x_5954_;
v_k_5939_ = v___x_5955_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_hi_5957_, lean_object* v_pivot_5958_, lean_object* v_as_5959_, lean_object* v_i_5960_, lean_object* v_k_5961_){
_start:
{
lean_object* v_res_5962_; 
v_res_5962_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(v_hi_5957_, v_pivot_5958_, v_as_5959_, v_i_5960_, v_k_5961_);
lean_dec(v_hi_5957_);
return v_res_5962_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(uint8_t v___x_5963_, lean_object* v_e_5964_, lean_object* v_e_x27_5965_){
_start:
{
lean_object* v_fst_5966_; lean_object* v_fst_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; uint8_t v___x_5970_; 
v_fst_5966_ = lean_ctor_get(v_e_5964_, 0);
lean_inc(v_fst_5966_);
lean_dec_ref(v_e_5964_);
v_fst_5967_ = lean_ctor_get(v_e_x27_5965_, 0);
lean_inc(v_fst_5967_);
lean_dec_ref(v_e_x27_5965_);
v___x_5968_ = l_Lean_Name_toString(v_fst_5966_, v___x_5963_);
v___x_5969_ = l_Lean_Name_toString(v_fst_5967_, v___x_5963_);
v___x_5970_ = lean_string_dec_lt(v___x_5968_, v___x_5969_);
lean_dec_ref(v___x_5969_);
lean_dec_ref(v___x_5968_);
return v___x_5970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___x_5971_, lean_object* v_e_5972_, lean_object* v_e_x27_5973_){
_start:
{
uint8_t v___x_1619__boxed_5974_; uint8_t v_res_5975_; lean_object* v_r_5976_; 
v___x_1619__boxed_5974_ = lean_unbox(v___x_5971_);
v_res_5975_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_1619__boxed_5974_, v_e_5972_, v_e_x27_5973_);
v_r_5976_ = lean_box(v_res_5975_);
return v_r_5976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(lean_object* v_n_5977_, lean_object* v_as_5978_, lean_object* v_lo_5979_, lean_object* v_hi_5980_){
_start:
{
lean_object* v___y_5982_; uint8_t v___x_5992_; 
v___x_5992_ = lean_nat_dec_lt(v_lo_5979_, v_hi_5980_);
if (v___x_5992_ == 0)
{
lean_dec(v_lo_5979_);
return v_as_5978_;
}
else
{
lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v_mid_5995_; lean_object* v___y_5997_; lean_object* v___y_6003_; lean_object* v___x_6008_; lean_object* v___x_6009_; uint8_t v___x_6010_; 
v___x_5993_ = lean_nat_add(v_lo_5979_, v_hi_5980_);
v___x_5994_ = lean_unsigned_to_nat(1u);
v_mid_5995_ = lean_nat_shiftr(v___x_5993_, v___x_5994_);
lean_dec(v___x_5993_);
v___x_6008_ = lean_array_fget_borrowed(v_as_5978_, v_mid_5995_);
v___x_6009_ = lean_array_fget_borrowed(v_as_5978_, v_lo_5979_);
lean_inc(v___x_6009_);
lean_inc(v___x_6008_);
v___x_6010_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_5992_, v___x_6008_, v___x_6009_);
if (v___x_6010_ == 0)
{
v___y_6003_ = v_as_5978_;
goto v___jp_6002_;
}
else
{
lean_object* v___x_6011_; 
v___x_6011_ = lean_array_fswap(v_as_5978_, v_lo_5979_, v_mid_5995_);
v___y_6003_ = v___x_6011_;
goto v___jp_6002_;
}
v___jp_5996_:
{
lean_object* v___x_5998_; lean_object* v___x_5999_; uint8_t v___x_6000_; 
v___x_5998_ = lean_array_fget_borrowed(v___y_5997_, v_mid_5995_);
v___x_5999_ = lean_array_fget_borrowed(v___y_5997_, v_hi_5980_);
lean_inc(v___x_5999_);
lean_inc(v___x_5998_);
v___x_6000_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_5992_, v___x_5998_, v___x_5999_);
if (v___x_6000_ == 0)
{
lean_dec(v_mid_5995_);
v___y_5982_ = v___y_5997_;
goto v___jp_5981_;
}
else
{
lean_object* v___x_6001_; 
v___x_6001_ = lean_array_fswap(v___y_5997_, v_mid_5995_, v_hi_5980_);
lean_dec(v_mid_5995_);
v___y_5982_ = v___x_6001_;
goto v___jp_5981_;
}
}
v___jp_6002_:
{
lean_object* v___x_6004_; lean_object* v___x_6005_; uint8_t v___x_6006_; 
v___x_6004_ = lean_array_fget_borrowed(v___y_6003_, v_hi_5980_);
v___x_6005_ = lean_array_fget_borrowed(v___y_6003_, v_lo_5979_);
lean_inc(v___x_6005_);
lean_inc(v___x_6004_);
v___x_6006_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_5992_, v___x_6004_, v___x_6005_);
if (v___x_6006_ == 0)
{
v___y_5997_ = v___y_6003_;
goto v___jp_5996_;
}
else
{
lean_object* v___x_6007_; 
v___x_6007_ = lean_array_fswap(v___y_6003_, v_lo_5979_, v_hi_5980_);
v___y_5997_ = v___x_6007_;
goto v___jp_5996_;
}
}
}
v___jp_5981_:
{
lean_object* v_pivot_5983_; lean_object* v___x_5984_; lean_object* v_fst_5985_; lean_object* v_snd_5986_; uint8_t v___x_5987_; 
v_pivot_5983_ = lean_array_fget(v___y_5982_, v_hi_5980_);
lean_inc_n(v_lo_5979_, 2);
v___x_5984_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(v_hi_5980_, v_pivot_5983_, v___y_5982_, v_lo_5979_, v_lo_5979_);
v_fst_5985_ = lean_ctor_get(v___x_5984_, 0);
lean_inc(v_fst_5985_);
v_snd_5986_ = lean_ctor_get(v___x_5984_, 1);
lean_inc(v_snd_5986_);
lean_dec_ref(v___x_5984_);
v___x_5987_ = lean_nat_dec_le(v_hi_5980_, v_fst_5985_);
if (v___x_5987_ == 0)
{
lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; 
v___x_5988_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_n_5977_, v_snd_5986_, v_lo_5979_, v_fst_5985_);
v___x_5989_ = lean_unsigned_to_nat(1u);
v___x_5990_ = lean_nat_add(v_fst_5985_, v___x_5989_);
lean_dec(v_fst_5985_);
v_as_5978_ = v___x_5988_;
v_lo_5979_ = v___x_5990_;
goto _start;
}
else
{
lean_dec(v_fst_5985_);
lean_dec(v_lo_5979_);
return v_snd_5986_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___boxed(lean_object* v_n_6012_, lean_object* v_as_6013_, lean_object* v_lo_6014_, lean_object* v_hi_6015_){
_start:
{
lean_object* v_res_6016_; 
v_res_6016_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_n_6012_, v_as_6013_, v_lo_6014_, v_hi_6015_);
lean_dec(v_hi_6015_);
lean_dec(v_n_6012_);
return v_res_6016_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(lean_object* v___y_6019_){
_start:
{
lean_object* v___x_6021_; lean_object* v_env_6022_; lean_object* v___x_6023_; lean_object* v_toEnvExtension_6024_; lean_object* v_asyncMode_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___y_6034_; lean_object* v___y_6035_; uint8_t v___x_6038_; 
v___x_6021_ = lean_st_ref_get(v___y_6019_);
v_env_6022_ = lean_ctor_get(v___x_6021_, 0);
lean_inc_ref(v_env_6022_);
lean_dec(v___x_6021_);
v___x_6023_ = l_Lean_errorExplanationExt;
v_toEnvExtension_6024_ = lean_ctor_get(v___x_6023_, 0);
v_asyncMode_6025_ = lean_ctor_get(v_toEnvExtension_6024_, 2);
v___x_6026_ = lean_box(1);
v___x_6027_ = lean_box(0);
v___x_6028_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6026_, v___x_6023_, v_env_6022_, v_asyncMode_6025_, v___x_6027_);
v___x_6029_ = lean_unsigned_to_nat(0u);
v___x_6030_ = ((lean_object*)(l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg___closed__0));
v___x_6031_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v___x_6030_, v___x_6028_);
lean_dec(v___x_6028_);
v___x_6032_ = lean_array_get_size(v___x_6031_);
v___x_6038_ = lean_nat_dec_eq(v___x_6032_, v___x_6029_);
if (v___x_6038_ == 0)
{
lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___y_6042_; uint8_t v___x_6044_; 
v___x_6039_ = lean_unsigned_to_nat(1u);
v___x_6040_ = lean_nat_sub(v___x_6032_, v___x_6039_);
v___x_6044_ = lean_nat_dec_le(v___x_6029_, v___x_6040_);
if (v___x_6044_ == 0)
{
lean_inc(v___x_6040_);
v___y_6042_ = v___x_6040_;
goto v___jp_6041_;
}
else
{
v___y_6042_ = v___x_6029_;
goto v___jp_6041_;
}
v___jp_6041_:
{
uint8_t v___x_6043_; 
v___x_6043_ = lean_nat_dec_le(v___y_6042_, v___x_6040_);
if (v___x_6043_ == 0)
{
lean_dec(v___x_6040_);
lean_inc(v___y_6042_);
v___y_6034_ = v___y_6042_;
v___y_6035_ = v___y_6042_;
goto v___jp_6033_;
}
else
{
v___y_6034_ = v___y_6042_;
v___y_6035_ = v___x_6040_;
goto v___jp_6033_;
}
}
}
else
{
lean_object* v___x_6045_; 
v___x_6045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6045_, 0, v___x_6031_);
return v___x_6045_;
}
v___jp_6033_:
{
lean_object* v___x_6036_; lean_object* v___x_6037_; 
v___x_6036_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v___x_6032_, v___x_6031_, v___y_6034_, v___y_6035_);
lean_dec(v___y_6035_);
v___x_6037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6037_, 0, v___x_6036_);
return v___x_6037_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg___boxed(lean_object* v___y_6046_, lean_object* v___y_6047_){
_start:
{
lean_object* v_res_6048_; 
v_res_6048_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_6046_);
lean_dec(v___y_6046_);
return v_res_6048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(lean_object* v_mkItem_6049_, lean_object* v_stx_6050_, lean_object* v_ctx_6051_, uint8_t v_snd_6052_, lean_object* v_fst_6053_, lean_object* v_caps_6054_, lean_object* v_as_6055_, size_t v_sz_6056_, size_t v_i_6057_, lean_object* v_b_6058_){
_start:
{
lean_object* v_a_6060_; uint8_t v___x_6064_; 
v___x_6064_ = lean_usize_dec_lt(v_i_6057_, v_sz_6056_);
if (v___x_6064_ == 0)
{
lean_dec_ref(v_ctx_6051_);
lean_dec_ref(v_mkItem_6049_);
return v_b_6058_;
}
else
{
lean_object* v_a_6065_; lean_object* v_fst_6066_; lean_object* v_snd_6067_; lean_object* v___x_6069_; uint8_t v_isShared_6070_; uint8_t v_isSharedCheck_6113_; 
v_a_6065_ = lean_array_uget(v_as_6055_, v_i_6057_);
v_fst_6066_ = lean_ctor_get(v_a_6065_, 0);
v_snd_6067_ = lean_ctor_get(v_a_6065_, 1);
v_isSharedCheck_6113_ = !lean_is_exclusive(v_a_6065_);
if (v_isSharedCheck_6113_ == 0)
{
v___x_6069_ = v_a_6065_;
v_isShared_6070_ = v_isSharedCheck_6113_;
goto v_resetjp_6068_;
}
else
{
lean_inc(v_snd_6067_);
lean_inc(v_fst_6066_);
lean_dec(v_a_6065_);
v___x_6069_ = lean_box(0);
v_isShared_6070_ = v_isSharedCheck_6113_;
goto v_resetjp_6068_;
}
v_resetjp_6068_:
{
lean_object* v___y_6072_; lean_object* v___x_6075_; lean_object* v___y_6077_; lean_object* v___y_6078_; uint8_t v___y_6089_; uint8_t v___x_6101_; 
lean_inc(v_fst_6066_);
v___x_6075_ = l_Lean_Name_toString(v_fst_6066_, v___x_6064_);
v___x_6101_ = l_String_charactersIn(v_fst_6053_, v___x_6075_);
if (v___x_6101_ == 0)
{
lean_dec_ref(v___x_6075_);
lean_del_object(v___x_6069_);
lean_dec(v_snd_6067_);
lean_dec(v_fst_6066_);
v_a_6060_ = v_b_6058_;
goto v___jp_6059_;
}
else
{
lean_object* v_textDocument_x3f_6102_; 
v_textDocument_x3f_6102_ = lean_ctor_get(v_caps_6054_, 0);
if (lean_obj_tag(v_textDocument_x3f_6102_) == 0)
{
uint8_t v___x_6103_; 
v___x_6103_ = 0;
v___y_6089_ = v___x_6103_;
goto v___jp_6088_;
}
else
{
lean_object* v_val_6104_; lean_object* v_completion_x3f_6105_; 
v_val_6104_ = lean_ctor_get(v_textDocument_x3f_6102_, 0);
v_completion_x3f_6105_ = lean_ctor_get(v_val_6104_, 0);
if (lean_obj_tag(v_completion_x3f_6105_) == 0)
{
uint8_t v___x_6106_; 
v___x_6106_ = 0;
v___y_6089_ = v___x_6106_;
goto v___jp_6088_;
}
else
{
lean_object* v_val_6107_; 
v_val_6107_ = lean_ctor_get(v_completion_x3f_6105_, 0);
if (lean_obj_tag(v_val_6107_) == 0)
{
uint8_t v___x_6108_; 
v___x_6108_ = 0;
v___y_6089_ = v___x_6108_;
goto v___jp_6088_;
}
else
{
lean_object* v_val_6109_; 
v_val_6109_ = lean_ctor_get(v_val_6107_, 0);
if (lean_obj_tag(v_val_6109_) == 0)
{
uint8_t v___x_6110_; 
v___x_6110_ = 0;
v___y_6089_ = v___x_6110_;
goto v___jp_6088_;
}
else
{
lean_object* v_val_6111_; uint8_t v___x_6112_; 
v_val_6111_ = lean_ctor_get(v_val_6109_, 0);
v___x_6112_ = lean_unbox(v_val_6111_);
v___y_6089_ = v___x_6112_;
goto v___jp_6088_;
}
}
}
}
}
v___jp_6071_:
{
lean_object* v___x_6073_; lean_object* v_items_6074_; 
lean_inc_ref(v_mkItem_6049_);
v___x_6073_ = lean_apply_3(v_mkItem_6049_, v_fst_6066_, v_snd_6067_, v___y_6072_);
v_items_6074_ = lean_array_push(v_b_6058_, v___x_6073_);
v_a_6060_ = v_items_6074_;
goto v___jp_6059_;
}
v___jp_6076_:
{
lean_object* v_toCommandContextInfo_6079_; lean_object* v_fileMap_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v_range_6084_; 
v_toCommandContextInfo_6079_ = lean_ctor_get(v_ctx_6051_, 0);
v_fileMap_6080_ = lean_ctor_get(v_toCommandContextInfo_6079_, 2);
lean_inc_ref_n(v_fileMap_6080_, 2);
v___x_6081_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_6080_, v___y_6077_);
lean_dec(v___y_6077_);
v___x_6082_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_6080_, v___y_6078_);
lean_dec(v___y_6078_);
if (v_isShared_6070_ == 0)
{
lean_ctor_set(v___x_6069_, 1, v___x_6082_);
lean_ctor_set(v___x_6069_, 0, v___x_6081_);
v_range_6084_ = v___x_6069_;
goto v_reusejp_6083_;
}
else
{
lean_object* v_reuseFailAlloc_6087_; 
v_reuseFailAlloc_6087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6087_, 0, v___x_6081_);
lean_ctor_set(v_reuseFailAlloc_6087_, 1, v___x_6082_);
v_range_6084_ = v_reuseFailAlloc_6087_;
goto v_reusejp_6083_;
}
v_reusejp_6083_:
{
lean_object* v___x_6085_; lean_object* v___x_6086_; 
lean_inc_ref(v_range_6084_);
v___x_6085_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6085_, 0, v___x_6075_);
lean_ctor_set(v___x_6085_, 1, v_range_6084_);
lean_ctor_set(v___x_6085_, 2, v_range_6084_);
v___x_6086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6086_, 0, v___x_6085_);
v___y_6072_ = v___x_6086_;
goto v___jp_6071_;
}
}
v___jp_6088_:
{
uint8_t v___x_6090_; 
v___x_6090_ = lean_bool_not(v___y_6089_);
if (v___x_6090_ == 0)
{
lean_object* v___x_6091_; 
v___x_6091_ = l_Lean_Syntax_getRange_x3f(v_stx_6050_, v___x_6090_);
if (lean_obj_tag(v___x_6091_) == 1)
{
lean_object* v_val_6092_; 
v_val_6092_ = lean_ctor_get(v___x_6091_, 0);
lean_inc(v_val_6092_);
lean_dec_ref_known(v___x_6091_, 1);
if (v_snd_6052_ == 0)
{
lean_object* v_start_6093_; lean_object* v_stop_6094_; 
v_start_6093_ = lean_ctor_get(v_val_6092_, 0);
lean_inc(v_start_6093_);
v_stop_6094_ = lean_ctor_get(v_val_6092_, 1);
lean_inc(v_stop_6094_);
lean_dec(v_val_6092_);
v___y_6077_ = v_start_6093_;
v___y_6078_ = v_stop_6094_;
goto v___jp_6076_;
}
else
{
lean_object* v_start_6095_; lean_object* v_stop_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; 
v_start_6095_ = lean_ctor_get(v_val_6092_, 0);
lean_inc(v_start_6095_);
v_stop_6096_ = lean_ctor_get(v_val_6092_, 1);
lean_inc(v_stop_6096_);
lean_dec(v_val_6092_);
v___x_6097_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0);
v___x_6098_ = lean_nat_add(v_stop_6096_, v___x_6097_);
lean_dec(v_stop_6096_);
v___y_6077_ = v_start_6095_;
v___y_6078_ = v___x_6098_;
goto v___jp_6076_;
}
}
else
{
lean_object* v___x_6099_; 
lean_dec(v___x_6091_);
lean_dec_ref(v___x_6075_);
lean_del_object(v___x_6069_);
v___x_6099_ = lean_box(0);
v___y_6072_ = v___x_6099_;
goto v___jp_6071_;
}
}
else
{
lean_object* v___x_6100_; 
lean_dec_ref(v___x_6075_);
lean_del_object(v___x_6069_);
v___x_6100_ = lean_box(0);
v___y_6072_ = v___x_6100_;
goto v___jp_6071_;
}
}
}
}
v___jp_6059_:
{
size_t v___x_6061_; size_t v___x_6062_; 
v___x_6061_ = ((size_t)1ULL);
v___x_6062_ = lean_usize_add(v_i_6057_, v___x_6061_);
v_i_6057_ = v___x_6062_;
v_b_6058_ = v_a_6060_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3___boxed(lean_object* v_mkItem_6114_, lean_object* v_stx_6115_, lean_object* v_ctx_6116_, lean_object* v_snd_6117_, lean_object* v_fst_6118_, lean_object* v_caps_6119_, lean_object* v_as_6120_, lean_object* v_sz_6121_, lean_object* v_i_6122_, lean_object* v_b_6123_){
_start:
{
uint8_t v_snd_1744__boxed_6124_; size_t v_sz_boxed_6125_; size_t v_i_boxed_6126_; lean_object* v_res_6127_; 
v_snd_1744__boxed_6124_ = lean_unbox(v_snd_6117_);
v_sz_boxed_6125_ = lean_unbox_usize(v_sz_6121_);
lean_dec(v_sz_6121_);
v_i_boxed_6126_ = lean_unbox_usize(v_i_6122_);
lean_dec(v_i_6122_);
v_res_6127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(v_mkItem_6114_, v_stx_6115_, v_ctx_6116_, v_snd_1744__boxed_6124_, v_fst_6118_, v_caps_6119_, v_as_6120_, v_sz_boxed_6125_, v_i_boxed_6126_, v_b_6123_);
lean_dec_ref(v_as_6120_);
lean_dec_ref(v_caps_6119_);
lean_dec_ref(v_fst_6118_);
lean_dec(v_stx_6115_);
return v_res_6127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(lean_object* v_entries_6128_, lean_object* v_stx_6129_, lean_object* v_caps_6130_, lean_object* v_ctx_6131_, lean_object* v_mkItem_6132_){
_start:
{
lean_object* v_fst_6134_; uint8_t v_snd_6135_; uint8_t v___x_6140_; lean_object* v___x_6141_; 
v___x_6140_ = 0;
v___x_6141_ = l_Lean_Syntax_getSubstring_x3f(v_stx_6129_, v___x_6140_, v___x_6140_);
if (lean_obj_tag(v___x_6141_) == 0)
{
lean_object* v___x_6142_; 
v___x_6142_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_6134_ = v___x_6142_;
v_snd_6135_ = v___x_6140_;
goto v___jp_6133_;
}
else
{
lean_object* v_val_6143_; lean_object* v_str_6144_; lean_object* v_startPos_6145_; lean_object* v_stopPos_6146_; uint8_t v___y_6148_; uint8_t v___x_6153_; uint8_t v___x_6154_; 
v_val_6143_ = lean_ctor_get(v___x_6141_, 0);
lean_inc(v_val_6143_);
lean_dec_ref_known(v___x_6141_, 1);
v_str_6144_ = lean_ctor_get(v_val_6143_, 0);
lean_inc_ref(v_str_6144_);
v_startPos_6145_ = lean_ctor_get(v_val_6143_, 1);
lean_inc(v_startPos_6145_);
v_stopPos_6146_ = lean_ctor_get(v_val_6143_, 2);
lean_inc(v_stopPos_6146_);
lean_dec(v_val_6143_);
v___x_6153_ = lean_string_utf8_at_end(v_str_6144_, v_stopPos_6146_);
v___x_6154_ = lean_bool_not(v___x_6153_);
if (v___x_6154_ == 0)
{
v___y_6148_ = v___x_6154_;
goto v___jp_6147_;
}
else
{
uint32_t v___x_6155_; uint32_t v___x_6156_; uint8_t v___x_6157_; 
v___x_6155_ = lean_string_utf8_get(v_str_6144_, v_stopPos_6146_);
v___x_6156_ = 46;
v___x_6157_ = lean_uint32_dec_eq(v___x_6155_, v___x_6156_);
v___y_6148_ = v___x_6157_;
goto v___jp_6147_;
}
v___jp_6147_:
{
if (v___y_6148_ == 0)
{
lean_object* v___x_6149_; 
v___x_6149_ = lean_string_utf8_extract(v_str_6144_, v_startPos_6145_, v_stopPos_6146_);
lean_dec(v_stopPos_6146_);
lean_dec(v_startPos_6145_);
lean_dec_ref(v_str_6144_);
v_fst_6134_ = v___x_6149_;
v_snd_6135_ = v___y_6148_;
goto v___jp_6133_;
}
else
{
lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; 
v___x_6150_ = lean_string_utf8_extract(v_str_6144_, v_startPos_6145_, v_stopPos_6146_);
lean_dec(v_stopPos_6146_);
lean_dec(v_startPos_6145_);
lean_dec_ref(v_str_6144_);
v___x_6151_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_6152_ = lean_string_append(v___x_6150_, v___x_6151_);
v_fst_6134_ = v___x_6152_;
v_snd_6135_ = v___y_6148_;
goto v___jp_6133_;
}
}
}
v___jp_6133_:
{
lean_object* v_items_6136_; size_t v_sz_6137_; size_t v___x_6138_; lean_object* v___x_6139_; 
v_items_6136_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v_sz_6137_ = lean_array_size(v_entries_6128_);
v___x_6138_ = ((size_t)0ULL);
v___x_6139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(v_mkItem_6132_, v_stx_6129_, v_ctx_6131_, v_snd_6135_, v_fst_6134_, v_caps_6130_, v_entries_6128_, v_sz_6137_, v___x_6138_, v_items_6136_);
lean_dec_ref(v_fst_6134_);
return v___x_6139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1___boxed(lean_object* v_entries_6158_, lean_object* v_stx_6159_, lean_object* v_caps_6160_, lean_object* v_ctx_6161_, lean_object* v_mkItem_6162_){
_start:
{
lean_object* v_res_6163_; 
v_res_6163_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(v_entries_6158_, v_stx_6159_, v_caps_6160_, v_ctx_6161_, v_mkItem_6162_);
lean_dec_ref(v_caps_6160_);
lean_dec(v_stx_6159_);
lean_dec_ref(v_entries_6158_);
return v_res_6163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__1(lean_object* v_partialId_6164_, lean_object* v_caps_6165_, lean_object* v_ctx_6166_, lean_object* v___f_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_){
_start:
{
lean_object* v___x_6173_; lean_object* v_a_6174_; lean_object* v___x_6176_; uint8_t v_isShared_6177_; uint8_t v_isSharedCheck_6182_; 
v___x_6173_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_6171_);
v_a_6174_ = lean_ctor_get(v___x_6173_, 0);
v_isSharedCheck_6182_ = !lean_is_exclusive(v___x_6173_);
if (v_isSharedCheck_6182_ == 0)
{
v___x_6176_ = v___x_6173_;
v_isShared_6177_ = v_isSharedCheck_6182_;
goto v_resetjp_6175_;
}
else
{
lean_inc(v_a_6174_);
lean_dec(v___x_6173_);
v___x_6176_ = lean_box(0);
v_isShared_6177_ = v_isSharedCheck_6182_;
goto v_resetjp_6175_;
}
v_resetjp_6175_:
{
lean_object* v___x_6178_; lean_object* v___x_6180_; 
v___x_6178_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(v_a_6174_, v_partialId_6164_, v_caps_6165_, v_ctx_6166_, v___f_6167_);
lean_dec(v_a_6174_);
if (v_isShared_6177_ == 0)
{
lean_ctor_set(v___x_6176_, 0, v___x_6178_);
v___x_6180_ = v___x_6176_;
goto v_reusejp_6179_;
}
else
{
lean_object* v_reuseFailAlloc_6181_; 
v_reuseFailAlloc_6181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6181_, 0, v___x_6178_);
v___x_6180_ = v_reuseFailAlloc_6181_;
goto v_reusejp_6179_;
}
v_reusejp_6179_:
{
return v___x_6180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__1___boxed(lean_object* v_partialId_6183_, lean_object* v_caps_6184_, lean_object* v_ctx_6185_, lean_object* v___f_6186_, lean_object* v___y_6187_, lean_object* v___y_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_){
_start:
{
lean_object* v_res_6192_; 
v_res_6192_ = l_Lean_Server_Completion_errorNameCompletion___lam__1(v_partialId_6183_, v_caps_6184_, v_ctx_6185_, v___f_6186_, v___y_6187_, v___y_6188_, v___y_6189_, v___y_6190_);
lean_dec(v___y_6190_);
lean_dec_ref(v___y_6189_);
lean_dec(v___y_6188_);
lean_dec_ref(v___y_6187_);
lean_dec_ref(v_caps_6184_);
lean_dec(v_partialId_6183_);
return v_res_6192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion(lean_object* v_uri_6193_, lean_object* v_pos_6194_, lean_object* v_completionInfoPos_6195_, lean_object* v_ctx_6196_, lean_object* v_partialId_6197_, lean_object* v_caps_6198_){
_start:
{
lean_object* v___f_6200_; lean_object* v___f_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; 
v___f_6200_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_errorNameCompletion___lam__0___boxed), 6, 3);
lean_closure_set(v___f_6200_, 0, v_completionInfoPos_6195_);
lean_closure_set(v___f_6200_, 1, v_uri_6193_);
lean_closure_set(v___f_6200_, 2, v_pos_6194_);
lean_inc_ref(v_ctx_6196_);
v___f_6201_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_errorNameCompletion___lam__1___boxed), 9, 4);
lean_closure_set(v___f_6201_, 0, v_partialId_6197_);
lean_closure_set(v___f_6201_, 1, v_caps_6198_);
lean_closure_set(v___f_6201_, 2, v_ctx_6196_);
lean_closure_set(v___f_6201_, 3, v___f_6200_);
v___x_6202_ = lean_unsigned_to_nat(32u);
v___x_6203_ = lean_mk_empty_array_with_capacity(v___x_6202_);
lean_dec_ref(v___x_6203_);
v___x_6204_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__4, &l_Lean_Server_Completion_optionCompletion___closed__4_once, _init_l_Lean_Server_Completion_optionCompletion___closed__4);
v___x_6205_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_6196_, v___x_6204_, v___f_6201_);
return v___x_6205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___boxed(lean_object* v_uri_6206_, lean_object* v_pos_6207_, lean_object* v_completionInfoPos_6208_, lean_object* v_ctx_6209_, lean_object* v_partialId_6210_, lean_object* v_caps_6211_, lean_object* v_a_6212_){
_start:
{
lean_object* v_res_6213_; 
v_res_6213_ = l_Lean_Server_Completion_errorNameCompletion(v_uri_6206_, v_pos_6207_, v_completionInfoPos_6208_, v_ctx_6209_, v_partialId_6210_, v_caps_6211_);
return v_res_6213_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0(lean_object* v___y_6214_, lean_object* v___y_6215_, lean_object* v___y_6216_, lean_object* v___y_6217_){
_start:
{
lean_object* v___x_6219_; 
v___x_6219_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_6217_);
return v___x_6219_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___boxed(lean_object* v___y_6220_, lean_object* v___y_6221_, lean_object* v___y_6222_, lean_object* v___y_6223_, lean_object* v___y_6224_){
_start:
{
lean_object* v_res_6225_; 
v_res_6225_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0(v___y_6220_, v___y_6221_, v___y_6222_, v___y_6223_);
lean_dec(v___y_6223_);
lean_dec_ref(v___y_6222_);
lean_dec(v___y_6221_);
lean_dec_ref(v___y_6220_);
return v_res_6225_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0(lean_object* v_init_6226_, lean_object* v_t_6227_){
_start:
{
lean_object* v___x_6228_; 
v___x_6228_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v_init_6226_, v_t_6227_);
return v___x_6228_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0___boxed(lean_object* v_init_6229_, lean_object* v_t_6230_){
_start:
{
lean_object* v_res_6231_; 
v_res_6231_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0(v_init_6229_, v_t_6230_);
lean_dec(v_t_6230_);
return v_res_6231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1(lean_object* v_n_6232_, lean_object* v_as_6233_, lean_object* v_lo_6234_, lean_object* v_hi_6235_, lean_object* v_w_6236_, lean_object* v_hlo_6237_, lean_object* v_hhi_6238_){
_start:
{
lean_object* v___x_6239_; 
v___x_6239_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_n_6232_, v_as_6233_, v_lo_6234_, v_hi_6235_);
return v___x_6239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___boxed(lean_object* v_n_6240_, lean_object* v_as_6241_, lean_object* v_lo_6242_, lean_object* v_hi_6243_, lean_object* v_w_6244_, lean_object* v_hlo_6245_, lean_object* v_hhi_6246_){
_start:
{
lean_object* v_res_6247_; 
v_res_6247_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1(v_n_6240_, v_as_6241_, v_lo_6242_, v_hi_6243_, v_w_6244_, v_hlo_6245_, v_hhi_6246_);
lean_dec(v_hi_6243_);
lean_dec(v_n_6240_);
return v_res_6247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3(lean_object* v_n_6248_, lean_object* v_lo_6249_, lean_object* v_hi_6250_, lean_object* v_hhi_6251_, lean_object* v_pivot_6252_, lean_object* v_as_6253_, lean_object* v_i_6254_, lean_object* v_k_6255_, lean_object* v_ilo_6256_, lean_object* v_ik_6257_, lean_object* v_w_6258_){
_start:
{
lean_object* v___x_6259_; 
v___x_6259_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(v_hi_6250_, v_pivot_6252_, v_as_6253_, v_i_6254_, v_k_6255_);
return v___x_6259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___boxed(lean_object* v_n_6260_, lean_object* v_lo_6261_, lean_object* v_hi_6262_, lean_object* v_hhi_6263_, lean_object* v_pivot_6264_, lean_object* v_as_6265_, lean_object* v_i_6266_, lean_object* v_k_6267_, lean_object* v_ilo_6268_, lean_object* v_ik_6269_, lean_object* v_w_6270_){
_start:
{
lean_object* v_res_6271_; 
v_res_6271_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3(v_n_6260_, v_lo_6261_, v_hi_6262_, v_hhi_6263_, v_pivot_6264_, v_as_6265_, v_i_6266_, v_k_6267_, v_ilo_6268_, v_ik_6269_, v_w_6270_);
lean_dec(v_hi_6262_);
lean_dec(v_lo_6261_);
lean_dec(v_n_6260_);
return v_res_6271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(lean_object* v_completionInfoPos_6272_, lean_object* v_uri_6273_, lean_object* v_pos_6274_, size_t v_sz_6275_, size_t v_i_6276_, lean_object* v_bs_6277_){
_start:
{
uint8_t v___x_6278_; 
v___x_6278_ = lean_usize_dec_lt(v_i_6276_, v_sz_6275_);
if (v___x_6278_ == 0)
{
lean_dec_ref(v_pos_6274_);
lean_dec_ref(v_uri_6273_);
lean_dec(v_completionInfoPos_6272_);
return v_bs_6277_;
}
else
{
lean_object* v_v_6279_; lean_object* v_userName_6280_; lean_object* v_docString_6281_; lean_object* v___x_6282_; lean_object* v_bs_x27_6283_; lean_object* v___x_6284_; lean_object* v___y_6286_; 
v_v_6279_ = lean_array_uget_borrowed(v_bs_6277_, v_i_6276_);
v_userName_6280_ = lean_ctor_get(v_v_6279_, 1);
lean_inc_ref(v_userName_6280_);
v_docString_6281_ = lean_ctor_get(v_v_6279_, 3);
lean_inc(v_docString_6281_);
v___x_6282_ = lean_unsigned_to_nat(0u);
v_bs_x27_6283_ = lean_array_uset(v_bs_6277_, v_i_6276_, v___x_6282_);
v___x_6284_ = lean_box(0);
if (lean_obj_tag(v_docString_6281_) == 0)
{
v___y_6286_ = v___x_6284_;
goto v___jp_6285_;
}
else
{
lean_object* v_val_6296_; lean_object* v___x_6298_; uint8_t v_isShared_6299_; uint8_t v_isSharedCheck_6305_; 
v_val_6296_ = lean_ctor_get(v_docString_6281_, 0);
v_isSharedCheck_6305_ = !lean_is_exclusive(v_docString_6281_);
if (v_isSharedCheck_6305_ == 0)
{
v___x_6298_ = v_docString_6281_;
v_isShared_6299_ = v_isSharedCheck_6305_;
goto v_resetjp_6297_;
}
else
{
lean_inc(v_val_6296_);
lean_dec(v_docString_6281_);
v___x_6298_ = lean_box(0);
v_isShared_6299_ = v_isSharedCheck_6305_;
goto v_resetjp_6297_;
}
v_resetjp_6297_:
{
uint8_t v___x_6300_; lean_object* v___x_6301_; lean_object* v___x_6303_; 
v___x_6300_ = 1;
v___x_6301_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6301_, 0, v_val_6296_);
lean_ctor_set_uint8(v___x_6301_, sizeof(void*)*1, v___x_6300_);
if (v_isShared_6299_ == 0)
{
lean_ctor_set(v___x_6298_, 0, v___x_6301_);
v___x_6303_ = v___x_6298_;
goto v_reusejp_6302_;
}
else
{
lean_object* v_reuseFailAlloc_6304_; 
v_reuseFailAlloc_6304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6304_, 0, v___x_6301_);
v___x_6303_ = v_reuseFailAlloc_6304_;
goto v_reusejp_6302_;
}
v_reusejp_6302_:
{
v___y_6286_ = v___x_6303_;
goto v___jp_6285_;
}
}
}
v___jp_6285_:
{
lean_object* v___x_6287_; lean_object* v___x_6288_; lean_object* v___x_6289_; lean_object* v___x_6290_; lean_object* v___x_6291_; size_t v___x_6292_; size_t v___x_6293_; lean_object* v___x_6294_; 
v___x_6287_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__2));
lean_inc(v_completionInfoPos_6272_);
v___x_6288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6288_, 0, v_completionInfoPos_6272_);
lean_inc_ref(v_pos_6274_);
lean_inc_ref(v_uri_6273_);
v___x_6289_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6289_, 0, v_uri_6273_);
lean_ctor_set(v___x_6289_, 1, v_pos_6274_);
lean_ctor_set(v___x_6289_, 2, v___x_6288_);
lean_ctor_set(v___x_6289_, 3, v___x_6284_);
v___x_6290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6290_, 0, v___x_6289_);
v___x_6291_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6291_, 0, v_userName_6280_);
lean_ctor_set(v___x_6291_, 1, v___x_6284_);
lean_ctor_set(v___x_6291_, 2, v___y_6286_);
lean_ctor_set(v___x_6291_, 3, v___x_6287_);
lean_ctor_set(v___x_6291_, 4, v___x_6284_);
lean_ctor_set(v___x_6291_, 5, v___x_6284_);
lean_ctor_set(v___x_6291_, 6, v___x_6290_);
lean_ctor_set(v___x_6291_, 7, v___x_6284_);
v___x_6292_ = ((size_t)1ULL);
v___x_6293_ = lean_usize_add(v_i_6276_, v___x_6292_);
v___x_6294_ = lean_array_uset(v_bs_x27_6283_, v_i_6276_, v___x_6291_);
v_i_6276_ = v___x_6293_;
v_bs_6277_ = v___x_6294_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0___boxed(lean_object* v_completionInfoPos_6306_, lean_object* v_uri_6307_, lean_object* v_pos_6308_, lean_object* v_sz_6309_, lean_object* v_i_6310_, lean_object* v_bs_6311_){
_start:
{
size_t v_sz_boxed_6312_; size_t v_i_boxed_6313_; lean_object* v_res_6314_; 
v_sz_boxed_6312_ = lean_unbox_usize(v_sz_6309_);
lean_dec(v_sz_6309_);
v_i_boxed_6313_ = lean_unbox_usize(v_i_6310_);
lean_dec(v_i_6310_);
v_res_6314_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(v_completionInfoPos_6306_, v_uri_6307_, v_pos_6308_, v_sz_boxed_6312_, v_i_boxed_6313_, v_bs_6311_);
return v_res_6314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___lam__0(uint8_t v___x_6315_, lean_object* v_completionInfoPos_6316_, lean_object* v_uri_6317_, lean_object* v_pos_6318_, lean_object* v___y_6319_, lean_object* v___y_6320_, lean_object* v___y_6321_, lean_object* v___y_6322_){
_start:
{
lean_object* v___x_6324_; 
v___x_6324_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v___x_6315_, v___y_6319_, v___y_6320_, v___y_6321_, v___y_6322_);
if (lean_obj_tag(v___x_6324_) == 0)
{
lean_object* v_a_6325_; lean_object* v___x_6327_; uint8_t v_isShared_6328_; uint8_t v_isSharedCheck_6335_; 
v_a_6325_ = lean_ctor_get(v___x_6324_, 0);
v_isSharedCheck_6335_ = !lean_is_exclusive(v___x_6324_);
if (v_isSharedCheck_6335_ == 0)
{
v___x_6327_ = v___x_6324_;
v_isShared_6328_ = v_isSharedCheck_6335_;
goto v_resetjp_6326_;
}
else
{
lean_inc(v_a_6325_);
lean_dec(v___x_6324_);
v___x_6327_ = lean_box(0);
v_isShared_6328_ = v_isSharedCheck_6335_;
goto v_resetjp_6326_;
}
v_resetjp_6326_:
{
size_t v_sz_6329_; size_t v___x_6330_; lean_object* v___x_6331_; lean_object* v___x_6333_; 
v_sz_6329_ = lean_array_size(v_a_6325_);
v___x_6330_ = ((size_t)0ULL);
v___x_6331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(v_completionInfoPos_6316_, v_uri_6317_, v_pos_6318_, v_sz_6329_, v___x_6330_, v_a_6325_);
if (v_isShared_6328_ == 0)
{
lean_ctor_set(v___x_6327_, 0, v___x_6331_);
v___x_6333_ = v___x_6327_;
goto v_reusejp_6332_;
}
else
{
lean_object* v_reuseFailAlloc_6334_; 
v_reuseFailAlloc_6334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6334_, 0, v___x_6331_);
v___x_6333_ = v_reuseFailAlloc_6334_;
goto v_reusejp_6332_;
}
v_reusejp_6332_:
{
return v___x_6333_;
}
}
}
else
{
lean_object* v_a_6336_; lean_object* v___x_6338_; uint8_t v_isShared_6339_; uint8_t v_isSharedCheck_6343_; 
lean_dec_ref(v_pos_6318_);
lean_dec_ref(v_uri_6317_);
lean_dec(v_completionInfoPos_6316_);
v_a_6336_ = lean_ctor_get(v___x_6324_, 0);
v_isSharedCheck_6343_ = !lean_is_exclusive(v___x_6324_);
if (v_isSharedCheck_6343_ == 0)
{
v___x_6338_ = v___x_6324_;
v_isShared_6339_ = v_isSharedCheck_6343_;
goto v_resetjp_6337_;
}
else
{
lean_inc(v_a_6336_);
lean_dec(v___x_6324_);
v___x_6338_ = lean_box(0);
v_isShared_6339_ = v_isSharedCheck_6343_;
goto v_resetjp_6337_;
}
v_resetjp_6337_:
{
lean_object* v___x_6341_; 
if (v_isShared_6339_ == 0)
{
v___x_6341_ = v___x_6338_;
goto v_reusejp_6340_;
}
else
{
lean_object* v_reuseFailAlloc_6342_; 
v_reuseFailAlloc_6342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6342_, 0, v_a_6336_);
v___x_6341_ = v_reuseFailAlloc_6342_;
goto v_reusejp_6340_;
}
v_reusejp_6340_:
{
return v___x_6341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___lam__0___boxed(lean_object* v___x_6344_, lean_object* v_completionInfoPos_6345_, lean_object* v_uri_6346_, lean_object* v_pos_6347_, lean_object* v___y_6348_, lean_object* v___y_6349_, lean_object* v___y_6350_, lean_object* v___y_6351_, lean_object* v___y_6352_){
_start:
{
uint8_t v___x_495__boxed_6353_; lean_object* v_res_6354_; 
v___x_495__boxed_6353_ = lean_unbox(v___x_6344_);
v_res_6354_ = l_Lean_Server_Completion_tacticCompletion___lam__0(v___x_495__boxed_6353_, v_completionInfoPos_6345_, v_uri_6346_, v_pos_6347_, v___y_6348_, v___y_6349_, v___y_6350_, v___y_6351_);
lean_dec(v___y_6351_);
lean_dec_ref(v___y_6350_);
lean_dec(v___y_6349_);
lean_dec_ref(v___y_6348_);
return v_res_6354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion(lean_object* v_uri_6355_, lean_object* v_pos_6356_, lean_object* v_completionInfoPos_6357_, lean_object* v_ctx_6358_){
_start:
{
lean_object* v___x_6360_; uint8_t v___x_6361_; lean_object* v___x_6362_; lean_object* v___f_6363_; lean_object* v___x_6364_; 
v___x_6360_ = l_Lean_LocalContext_empty;
v___x_6361_ = 0;
v___x_6362_ = lean_box(v___x_6361_);
v___f_6363_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_tacticCompletion___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6363_, 0, v___x_6362_);
lean_closure_set(v___f_6363_, 1, v_completionInfoPos_6357_);
lean_closure_set(v___f_6363_, 2, v_uri_6355_);
lean_closure_set(v___f_6363_, 3, v_pos_6356_);
v___x_6364_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_6358_, v___x_6360_, v___f_6363_);
return v___x_6364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___boxed(lean_object* v_uri_6365_, lean_object* v_pos_6366_, lean_object* v_completionInfoPos_6367_, lean_object* v_ctx_6368_, lean_object* v_a_6369_){
_start:
{
lean_object* v_res_6370_; 
v_res_6370_ = l_Lean_Server_Completion_tacticCompletion(v_uri_6365_, v_pos_6366_, v_completionInfoPos_6367_, v_ctx_6368_);
return v_res_6370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(lean_object* v_a_6371_, lean_object* v_b_6372_){
_start:
{
lean_object* v_array_6373_; lean_object* v_start_6374_; lean_object* v_stop_6375_; lean_object* v___x_6377_; uint8_t v_isShared_6378_; uint8_t v_isSharedCheck_6388_; 
v_array_6373_ = lean_ctor_get(v_a_6371_, 0);
v_start_6374_ = lean_ctor_get(v_a_6371_, 1);
v_stop_6375_ = lean_ctor_get(v_a_6371_, 2);
v_isSharedCheck_6388_ = !lean_is_exclusive(v_a_6371_);
if (v_isSharedCheck_6388_ == 0)
{
v___x_6377_ = v_a_6371_;
v_isShared_6378_ = v_isSharedCheck_6388_;
goto v_resetjp_6376_;
}
else
{
lean_inc(v_stop_6375_);
lean_inc(v_start_6374_);
lean_inc(v_array_6373_);
lean_dec(v_a_6371_);
v___x_6377_ = lean_box(0);
v_isShared_6378_ = v_isSharedCheck_6388_;
goto v_resetjp_6376_;
}
v_resetjp_6376_:
{
uint8_t v___x_6379_; 
v___x_6379_ = lean_nat_dec_lt(v_start_6374_, v_stop_6375_);
if (v___x_6379_ == 0)
{
lean_del_object(v___x_6377_);
lean_dec(v_stop_6375_);
lean_dec(v_start_6374_);
lean_dec_ref(v_array_6373_);
return v_b_6372_;
}
else
{
lean_object* v___x_6380_; lean_object* v___x_6381_; lean_object* v___x_6383_; 
v___x_6380_ = lean_unsigned_to_nat(1u);
v___x_6381_ = lean_nat_add(v_start_6374_, v___x_6380_);
lean_inc_ref(v_array_6373_);
if (v_isShared_6378_ == 0)
{
lean_ctor_set(v___x_6377_, 1, v___x_6381_);
v___x_6383_ = v___x_6377_;
goto v_reusejp_6382_;
}
else
{
lean_object* v_reuseFailAlloc_6387_; 
v_reuseFailAlloc_6387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6387_, 0, v_array_6373_);
lean_ctor_set(v_reuseFailAlloc_6387_, 1, v___x_6381_);
lean_ctor_set(v_reuseFailAlloc_6387_, 2, v_stop_6375_);
v___x_6383_ = v_reuseFailAlloc_6387_;
goto v_reusejp_6382_;
}
v_reusejp_6382_:
{
lean_object* v___x_6384_; lean_object* v___x_6385_; 
v___x_6384_ = lean_array_fget(v_array_6373_, v_start_6374_);
lean_dec(v_start_6374_);
lean_dec_ref(v_array_6373_);
v___x_6385_ = lean_array_push(v_b_6372_, v___x_6384_);
v_a_6371_ = v___x_6383_;
v_b_6372_ = v___x_6385_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(lean_object* v_scopeNames_6391_, lean_object* v_idx_6392_){
_start:
{
lean_object* v___x_6393_; lean_object* v___x_6394_; lean_object* v___x_6395_; lean_object* v___x_6396_; lean_object* v___x_6397_; lean_object* v___x_6398_; lean_object* v___x_6399_; 
v___x_6393_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_6394_ = lean_array_get_size(v_scopeNames_6391_);
v___x_6395_ = l_Array_toSubarray___redArg(v_scopeNames_6391_, v_idx_6392_, v___x_6394_);
v___x_6396_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___x_6397_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(v___x_6395_, v___x_6396_);
v___x_6398_ = lean_array_to_list(v___x_6397_);
v___x_6399_ = l_String_intercalate(v___x_6393_, v___x_6398_);
return v___x_6399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0(lean_object* v_inst_6400_, lean_object* v_R_6401_, lean_object* v_a_6402_, lean_object* v_b_6403_){
_start:
{
lean_object* v___x_6404_; 
v___x_6404_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(v_a_6402_, v_b_6403_);
return v___x_6404_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(lean_object* v_upperBound_6405_, lean_object* v_next_6406_, lean_object* v_scopeNames_6407_, uint8_t v___x_6408_, lean_object* v_idComponents_6409_, lean_object* v_a_6410_, uint8_t v_b_6411_){
_start:
{
uint8_t v___x_6412_; 
v___x_6412_ = lean_nat_dec_lt(v_a_6410_, v_upperBound_6405_);
if (v___x_6412_ == 0)
{
lean_dec(v_a_6410_);
return v_b_6411_;
}
else
{
lean_object* v___x_6413_; lean_object* v___x_6414_; uint8_t v___x_6415_; 
v___x_6413_ = lean_nat_add(v_next_6406_, v_a_6410_);
v___x_6414_ = lean_array_get_size(v_scopeNames_6407_);
v___x_6415_ = lean_nat_dec_lt(v___x_6413_, v___x_6414_);
if (v___x_6415_ == 0)
{
lean_dec(v___x_6413_);
lean_dec(v_a_6410_);
return v___x_6408_;
}
else
{
lean_object* v___x_6416_; lean_object* v___x_6417_; lean_object* v___x_6418_; uint8_t v___x_6419_; uint8_t v___x_6420_; 
v___x_6416_ = lean_array_fget_borrowed(v_scopeNames_6407_, v___x_6413_);
lean_dec(v___x_6413_);
v___x_6417_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v___x_6418_ = lean_array_get_borrowed(v___x_6417_, v_idComponents_6409_, v_a_6410_);
v___x_6419_ = lean_string_dec_eq(v___x_6418_, v___x_6416_);
v___x_6420_ = lean_bool_not(v___x_6419_);
if (v___x_6420_ == 0)
{
lean_object* v___x_6421_; lean_object* v___x_6422_; 
v___x_6421_ = lean_unsigned_to_nat(1u);
v___x_6422_ = lean_nat_add(v_a_6410_, v___x_6421_);
lean_dec(v_a_6410_);
v_a_6410_ = v___x_6422_;
goto _start;
}
else
{
lean_dec(v_a_6410_);
return v___x_6408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg___boxed(lean_object* v_upperBound_6424_, lean_object* v_next_6425_, lean_object* v_scopeNames_6426_, lean_object* v___x_6427_, lean_object* v_idComponents_6428_, lean_object* v_a_6429_, lean_object* v_b_6430_){
_start:
{
uint8_t v___x_2468__boxed_6431_; uint8_t v_b_boxed_6432_; uint8_t v_res_6433_; lean_object* v_r_6434_; 
v___x_2468__boxed_6431_ = lean_unbox(v___x_6427_);
v_b_boxed_6432_ = lean_unbox(v_b_6430_);
v_res_6433_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v_upperBound_6424_, v_next_6425_, v_scopeNames_6426_, v___x_2468__boxed_6431_, v_idComponents_6428_, v_a_6429_, v_b_boxed_6432_);
lean_dec_ref(v_idComponents_6428_);
lean_dec_ref(v_scopeNames_6426_);
lean_dec(v_next_6425_);
lean_dec(v_upperBound_6424_);
v_r_6434_ = lean_box(v_res_6433_);
return v_r_6434_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(lean_object* v_upperBound_6435_, lean_object* v_idComponents_6436_, lean_object* v_scopeNames_6437_, lean_object* v_a_6438_, lean_object* v_b_6439_){
_start:
{
lean_object* v_a_6441_; uint8_t v___x_6445_; 
v___x_6445_ = lean_nat_dec_lt(v_a_6438_, v_upperBound_6435_);
if (v___x_6445_ == 0)
{
lean_dec(v_a_6438_);
lean_dec_ref(v_scopeNames_6437_);
return v_b_6439_;
}
else
{
lean_object* v___x_6446_; lean_object* v___x_6447_; lean_object* v___x_6448_; uint8_t v___x_6449_; 
v___x_6446_ = lean_array_get_size(v_idComponents_6436_);
v___x_6447_ = lean_unsigned_to_nat(1u);
v___x_6448_ = lean_nat_sub(v___x_6446_, v___x_6447_);
v___x_6449_ = lean_nat_dec_lt(v___x_6448_, v___x_6446_);
if (v___x_6449_ == 0)
{
lean_object* v___x_6450_; lean_object* v___x_6451_; 
lean_dec(v___x_6448_);
lean_inc(v_a_6438_);
lean_inc_ref(v_scopeNames_6437_);
v___x_6450_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(v_scopeNames_6437_, v_a_6438_);
v___x_6451_ = lean_array_push(v_b_6439_, v___x_6450_);
v_a_6441_ = v___x_6451_;
goto v___jp_6440_;
}
else
{
lean_object* v___x_6452_; lean_object* v___x_6453_; lean_object* v___x_6454_; uint8_t v___x_6455_; 
v___x_6452_ = lean_nat_add(v_a_6438_, v___x_6446_);
v___x_6453_ = lean_nat_sub(v___x_6452_, v___x_6447_);
lean_dec(v___x_6452_);
v___x_6454_ = lean_array_get_size(v_scopeNames_6437_);
v___x_6455_ = lean_nat_dec_lt(v___x_6453_, v___x_6454_);
if (v___x_6455_ == 0)
{
lean_dec(v___x_6453_);
lean_dec(v___x_6448_);
v_a_6441_ = v_b_6439_;
goto v___jp_6440_;
}
else
{
lean_object* v___x_6456_; lean_object* v___x_6457_; uint8_t v___x_6458_; uint8_t v___x_6459_; 
v___x_6456_ = lean_array_fget_borrowed(v_idComponents_6436_, v___x_6448_);
v___x_6457_ = lean_array_fget_borrowed(v_scopeNames_6437_, v___x_6453_);
v___x_6458_ = l_String_charactersIn(v___x_6456_, v___x_6457_);
v___x_6459_ = lean_bool_not(v___x_6458_);
if (v___x_6459_ == 0)
{
lean_object* v___x_6460_; uint8_t v___x_6461_; 
v___x_6460_ = lean_unsigned_to_nat(0u);
v___x_6461_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v___x_6448_, v_a_6438_, v_scopeNames_6437_, v___x_6459_, v_idComponents_6436_, v___x_6460_, v___x_6455_);
lean_dec(v___x_6448_);
if (v___x_6461_ == 0)
{
lean_dec(v___x_6453_);
v_a_6441_ = v_b_6439_;
goto v___jp_6440_;
}
else
{
lean_object* v___x_6462_; lean_object* v___x_6463_; 
lean_inc_ref(v_scopeNames_6437_);
v___x_6462_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(v_scopeNames_6437_, v___x_6453_);
v___x_6463_ = lean_array_push(v_b_6439_, v___x_6462_);
v_a_6441_ = v___x_6463_;
goto v___jp_6440_;
}
}
else
{
lean_dec(v___x_6453_);
lean_dec(v___x_6448_);
v_a_6441_ = v_b_6439_;
goto v___jp_6440_;
}
}
}
}
v___jp_6440_:
{
lean_object* v___x_6442_; lean_object* v___x_6443_; 
v___x_6442_ = lean_unsigned_to_nat(1u);
v___x_6443_ = lean_nat_add(v_a_6438_, v___x_6442_);
lean_dec(v_a_6438_);
v_a_6438_ = v___x_6443_;
v_b_6439_ = v_a_6441_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg___boxed(lean_object* v_upperBound_6464_, lean_object* v_idComponents_6465_, lean_object* v_scopeNames_6466_, lean_object* v_a_6467_, lean_object* v_b_6468_){
_start:
{
lean_object* v_res_6469_; 
v_res_6469_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v_upperBound_6464_, v_idComponents_6465_, v_scopeNames_6466_, v_a_6467_, v_b_6468_);
lean_dec_ref(v_idComponents_6465_);
lean_dec(v_upperBound_6464_);
return v_res_6469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(lean_object* v_idComponents_6470_, lean_object* v_scopeNames_6471_){
_start:
{
lean_object* v___x_6472_; lean_object* v___x_6473_; lean_object* v_r_6474_; lean_object* v___x_6475_; 
v___x_6472_ = lean_unsigned_to_nat(0u);
v___x_6473_ = lean_array_get_size(v_scopeNames_6471_);
v_r_6474_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___x_6475_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v___x_6473_, v_idComponents_6470_, v_scopeNames_6471_, v___x_6472_, v_r_6474_);
return v___x_6475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates___boxed(lean_object* v_idComponents_6476_, lean_object* v_scopeNames_6477_){
_start:
{
lean_object* v_res_6478_; 
v_res_6478_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(v_idComponents_6476_, v_scopeNames_6477_);
lean_dec_ref(v_idComponents_6476_);
return v_res_6478_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0(lean_object* v_upperBound_6479_, lean_object* v_next_6480_, lean_object* v_scopeNames_6481_, uint8_t v___x_6482_, lean_object* v_idComponents_6483_, lean_object* v_inst_6484_, lean_object* v_R_6485_, lean_object* v_a_6486_, uint8_t v_b_6487_, lean_object* v_c_6488_){
_start:
{
uint8_t v___x_6489_; 
v___x_6489_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v_upperBound_6479_, v_next_6480_, v_scopeNames_6481_, v___x_6482_, v_idComponents_6483_, v_a_6486_, v_b_6487_);
return v___x_6489_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___boxed(lean_object* v_upperBound_6490_, lean_object* v_next_6491_, lean_object* v_scopeNames_6492_, lean_object* v___x_6493_, lean_object* v_idComponents_6494_, lean_object* v_inst_6495_, lean_object* v_R_6496_, lean_object* v_a_6497_, lean_object* v_b_6498_, lean_object* v_c_6499_){
_start:
{
uint8_t v___x_2556__boxed_6500_; uint8_t v_b_boxed_6501_; uint8_t v_res_6502_; lean_object* v_r_6503_; 
v___x_2556__boxed_6500_ = lean_unbox(v___x_6493_);
v_b_boxed_6501_ = lean_unbox(v_b_6498_);
v_res_6502_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0(v_upperBound_6490_, v_next_6491_, v_scopeNames_6492_, v___x_2556__boxed_6500_, v_idComponents_6494_, v_inst_6495_, v_R_6496_, v_a_6497_, v_b_boxed_6501_, v_c_6499_);
lean_dec_ref(v_idComponents_6494_);
lean_dec_ref(v_scopeNames_6492_);
lean_dec(v_next_6491_);
lean_dec(v_upperBound_6490_);
v_r_6503_ = lean_box(v_res_6502_);
return v_r_6503_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1(lean_object* v_upperBound_6504_, lean_object* v_idComponents_6505_, lean_object* v_scopeNames_6506_, lean_object* v_inst_6507_, lean_object* v_R_6508_, lean_object* v_a_6509_, lean_object* v_b_6510_, lean_object* v_c_6511_){
_start:
{
lean_object* v___x_6512_; 
v___x_6512_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v_upperBound_6504_, v_idComponents_6505_, v_scopeNames_6506_, v_a_6509_, v_b_6510_);
return v___x_6512_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___boxed(lean_object* v_upperBound_6513_, lean_object* v_idComponents_6514_, lean_object* v_scopeNames_6515_, lean_object* v_inst_6516_, lean_object* v_R_6517_, lean_object* v_a_6518_, lean_object* v_b_6519_, lean_object* v_c_6520_){
_start:
{
lean_object* v_res_6521_; 
v_res_6521_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1(v_upperBound_6513_, v_idComponents_6514_, v_scopeNames_6515_, v_inst_6516_, v_R_6517_, v_a_6518_, v_b_6519_, v_c_6520_);
lean_dec_ref(v_idComponents_6514_);
lean_dec(v_upperBound_6513_);
return v_res_6521_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_Completion_endSectionCompletion___lam__0(lean_object* v_x_6522_){
_start:
{
lean_object* v___x_6523_; lean_object* v___x_6524_; uint8_t v___x_6525_; uint8_t v___x_6526_; 
v___x_6523_ = lean_string_utf8_byte_size(v_x_6522_);
v___x_6524_ = lean_unsigned_to_nat(0u);
v___x_6525_ = lean_nat_dec_eq(v___x_6523_, v___x_6524_);
v___x_6526_ = lean_bool_not(v___x_6525_);
return v___x_6526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion___lam__0___boxed(lean_object* v_x_6527_){
_start:
{
uint8_t v_res_6528_; lean_object* v_r_6529_; 
v_res_6528_ = l_Lean_Server_Completion_endSectionCompletion___lam__0(v_x_6527_);
lean_dec_ref(v_x_6527_);
v_r_6529_ = lean_box(v_res_6528_);
return v_r_6529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(size_t v_sz_6530_, size_t v_i_6531_, lean_object* v_bs_6532_){
_start:
{
uint8_t v___x_6533_; 
v___x_6533_ = lean_usize_dec_lt(v_i_6531_, v_sz_6530_);
if (v___x_6533_ == 0)
{
return v_bs_6532_;
}
else
{
lean_object* v_v_6534_; lean_object* v___x_6535_; lean_object* v_bs_x27_6536_; lean_object* v___x_6537_; size_t v___x_6538_; size_t v___x_6539_; lean_object* v___x_6540_; 
v_v_6534_ = lean_array_uget(v_bs_6532_, v_i_6531_);
v___x_6535_ = lean_unsigned_to_nat(0u);
v_bs_x27_6536_ = lean_array_uset(v_bs_6532_, v_i_6531_, v___x_6535_);
v___x_6537_ = l_Lean_Name_toString(v_v_6534_, v___x_6533_);
v___x_6538_ = ((size_t)1ULL);
v___x_6539_ = lean_usize_add(v_i_6531_, v___x_6538_);
v___x_6540_ = lean_array_uset(v_bs_x27_6536_, v_i_6531_, v___x_6537_);
v_i_6531_ = v___x_6539_;
v_bs_6532_ = v___x_6540_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1___boxed(lean_object* v_sz_6542_, lean_object* v_i_6543_, lean_object* v_bs_6544_){
_start:
{
size_t v_sz_boxed_6545_; size_t v_i_boxed_6546_; lean_object* v_res_6547_; 
v_sz_boxed_6545_ = lean_unbox_usize(v_sz_6542_);
lean_dec(v_sz_6542_);
v_i_boxed_6546_ = lean_unbox_usize(v_i_6543_);
lean_dec(v_i_6543_);
v_res_6547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(v_sz_boxed_6545_, v_i_boxed_6546_, v_bs_6544_);
return v_res_6547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(lean_object* v_completionInfoPos_6548_, lean_object* v_uri_6549_, lean_object* v_pos_6550_, size_t v_sz_6551_, size_t v_i_6552_, lean_object* v_bs_6553_){
_start:
{
uint8_t v___x_6554_; 
v___x_6554_ = lean_usize_dec_lt(v_i_6552_, v_sz_6551_);
if (v___x_6554_ == 0)
{
lean_dec_ref(v_pos_6550_);
lean_dec_ref(v_uri_6549_);
lean_dec(v_completionInfoPos_6548_);
return v_bs_6553_;
}
else
{
lean_object* v_v_6555_; lean_object* v___x_6556_; lean_object* v_bs_x27_6557_; lean_object* v___x_6558_; lean_object* v___x_6559_; lean_object* v___x_6560_; lean_object* v___x_6561_; lean_object* v___x_6562_; lean_object* v___x_6563_; size_t v___x_6564_; size_t v___x_6565_; lean_object* v___x_6566_; 
v_v_6555_ = lean_array_uget(v_bs_6553_, v_i_6552_);
v___x_6556_ = lean_unsigned_to_nat(0u);
v_bs_x27_6557_ = lean_array_uset(v_bs_6553_, v_i_6552_, v___x_6556_);
v___x_6558_ = lean_box(0);
v___x_6559_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__2));
lean_inc(v_completionInfoPos_6548_);
v___x_6560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6560_, 0, v_completionInfoPos_6548_);
lean_inc_ref(v_pos_6550_);
lean_inc_ref(v_uri_6549_);
v___x_6561_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6561_, 0, v_uri_6549_);
lean_ctor_set(v___x_6561_, 1, v_pos_6550_);
lean_ctor_set(v___x_6561_, 2, v___x_6560_);
lean_ctor_set(v___x_6561_, 3, v___x_6558_);
v___x_6562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6562_, 0, v___x_6561_);
v___x_6563_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6563_, 0, v_v_6555_);
lean_ctor_set(v___x_6563_, 1, v___x_6558_);
lean_ctor_set(v___x_6563_, 2, v___x_6558_);
lean_ctor_set(v___x_6563_, 3, v___x_6559_);
lean_ctor_set(v___x_6563_, 4, v___x_6558_);
lean_ctor_set(v___x_6563_, 5, v___x_6558_);
lean_ctor_set(v___x_6563_, 6, v___x_6562_);
lean_ctor_set(v___x_6563_, 7, v___x_6558_);
v___x_6564_ = ((size_t)1ULL);
v___x_6565_ = lean_usize_add(v_i_6552_, v___x_6564_);
v___x_6566_ = lean_array_uset(v_bs_x27_6557_, v_i_6552_, v___x_6563_);
v_i_6552_ = v___x_6565_;
v_bs_6553_ = v___x_6566_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0___boxed(lean_object* v_completionInfoPos_6568_, lean_object* v_uri_6569_, lean_object* v_pos_6570_, lean_object* v_sz_6571_, lean_object* v_i_6572_, lean_object* v_bs_6573_){
_start:
{
size_t v_sz_boxed_6574_; size_t v_i_boxed_6575_; lean_object* v_res_6576_; 
v_sz_boxed_6574_ = lean_unbox_usize(v_sz_6571_);
lean_dec(v_sz_6571_);
v_i_boxed_6575_ = lean_unbox_usize(v_i_6572_);
lean_dec(v_i_6572_);
v_res_6576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(v_completionInfoPos_6568_, v_uri_6569_, v_pos_6570_, v_sz_boxed_6574_, v_i_boxed_6575_, v_bs_6573_);
return v_res_6576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion(lean_object* v_uri_6578_, lean_object* v_pos_6579_, lean_object* v_completionInfoPos_6580_, lean_object* v_id_x3f_6581_, uint8_t v_danglingDot_6582_, lean_object* v_scopeNames_6583_){
_start:
{
lean_object* v___f_6585_; lean_object* v_idComponents_6587_; lean_object* v___y_6598_; 
v___f_6585_ = ((lean_object*)(l_Lean_Server_Completion_endSectionCompletion___closed__0));
if (lean_obj_tag(v_id_x3f_6581_) == 0)
{
lean_object* v___x_6601_; 
v___x_6601_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___y_6598_ = v___x_6601_;
goto v___jp_6597_;
}
else
{
lean_object* v_val_6602_; lean_object* v___x_6603_; lean_object* v___x_6604_; size_t v_sz_6605_; size_t v___x_6606_; lean_object* v___x_6607_; 
v_val_6602_ = lean_ctor_get(v_id_x3f_6581_, 0);
lean_inc(v_val_6602_);
lean_dec_ref_known(v_id_x3f_6581_, 1);
v___x_6603_ = l_Lean_Name_components(v_val_6602_);
v___x_6604_ = lean_array_mk(v___x_6603_);
v_sz_6605_ = lean_array_size(v___x_6604_);
v___x_6606_ = ((size_t)0ULL);
v___x_6607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(v_sz_6605_, v___x_6606_, v___x_6604_);
v___y_6598_ = v___x_6607_;
goto v___jp_6597_;
}
v___jp_6586_:
{
lean_object* v___x_6588_; lean_object* v___x_6589_; lean_object* v___x_6590_; lean_object* v_scopeNames_6591_; lean_object* v_candidates_6592_; size_t v_sz_6593_; size_t v___x_6594_; lean_object* v___x_6595_; lean_object* v___x_6596_; 
v___x_6588_ = lean_array_mk(v_scopeNames_6583_);
v___x_6589_ = lean_array_pop(v___x_6588_);
v___x_6590_ = l_Array_takeWhile___redArg(v___f_6585_, v___x_6589_);
lean_dec_ref(v___x_6589_);
v_scopeNames_6591_ = l_Array_reverse___redArg(v___x_6590_);
v_candidates_6592_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(v_idComponents_6587_, v_scopeNames_6591_);
lean_dec_ref(v_idComponents_6587_);
v_sz_6593_ = lean_array_size(v_candidates_6592_);
v___x_6594_ = ((size_t)0ULL);
v___x_6595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(v_completionInfoPos_6580_, v_uri_6578_, v_pos_6579_, v_sz_6593_, v___x_6594_, v_candidates_6592_);
v___x_6596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6596_, 0, v___x_6595_);
return v___x_6596_;
}
v___jp_6597_:
{
if (v_danglingDot_6582_ == 0)
{
v_idComponents_6587_ = v___y_6598_;
goto v___jp_6586_;
}
else
{
lean_object* v___x_6599_; lean_object* v_idComponents_6600_; 
v___x_6599_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_idComponents_6600_ = lean_array_push(v___y_6598_, v___x_6599_);
v_idComponents_6587_ = v_idComponents_6600_;
goto v___jp_6586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion___boxed(lean_object* v_uri_6608_, lean_object* v_pos_6609_, lean_object* v_completionInfoPos_6610_, lean_object* v_id_x3f_6611_, lean_object* v_danglingDot_6612_, lean_object* v_scopeNames_6613_, lean_object* v_a_6614_){
_start:
{
uint8_t v_danglingDot_boxed_6615_; lean_object* v_res_6616_; 
v_danglingDot_boxed_6615_ = lean_unbox(v_danglingDot_6612_);
v_res_6616_ = l_Lean_Server_Completion_endSectionCompletion(v_uri_6608_, v_pos_6609_, v_completionInfoPos_6610_, v_id_x3f_6611_, v_danglingDot_boxed_6615_, v_scopeNames_6613_);
return v_res_6616_;
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
