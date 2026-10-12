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
lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object*, uint8_t, uint8_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls();
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_DataValue_str(lean_object*);
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
uint8_t l_Lean_Meta_allowCompletion(lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_getCompletionKindForDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_getCompletionTagsForDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_getEligibleHeaderDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(lean_object* v_item_3_, lean_object* v_id_x3f_4_, lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
lean_object* v_uri_8_; lean_object* v_pos_9_; lean_object* v_completionInfoPos_10_; lean_object* v_label_11_; lean_object* v_detail_x3f_12_; lean_object* v_documentation_x3f_13_; lean_object* v_kind_x3f_14_; lean_object* v_textEdit_x3f_15_; lean_object* v_sortText_x3f_16_; lean_object* v_tags_x3f_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_32_; 
v_uri_8_ = lean_ctor_get(v_a_5_, 0);
v_pos_9_ = lean_ctor_get(v_a_5_, 1);
v_completionInfoPos_10_ = lean_ctor_get(v_a_5_, 2);
v_label_11_ = lean_ctor_get(v_item_3_, 0);
v_detail_x3f_12_ = lean_ctor_get(v_item_3_, 1);
v_documentation_x3f_13_ = lean_ctor_get(v_item_3_, 2);
v_kind_x3f_14_ = lean_ctor_get(v_item_3_, 3);
v_textEdit_x3f_15_ = lean_ctor_get(v_item_3_, 4);
v_sortText_x3f_16_ = lean_ctor_get(v_item_3_, 5);
v_tags_x3f_17_ = lean_ctor_get(v_item_3_, 7);
v_isSharedCheck_32_ = !lean_is_exclusive(v_item_3_);
if (v_isSharedCheck_32_ == 0)
{
lean_object* v_unused_33_; 
v_unused_33_ = lean_ctor_get(v_item_3_, 6);
lean_dec(v_unused_33_);
v___x_19_ = v_item_3_;
v_isShared_20_ = v_isSharedCheck_32_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_tags_x3f_17_);
lean_inc(v_sortText_x3f_16_);
lean_inc(v_textEdit_x3f_15_);
lean_inc(v_kind_x3f_14_);
lean_inc(v_documentation_x3f_13_);
lean_inc(v_detail_x3f_12_);
lean_inc(v_label_11_);
lean_dec(v_item_3_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_32_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_25_; 
lean_inc(v_completionInfoPos_10_);
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_completionInfoPos_10_);
lean_inc_ref(v_pos_9_);
lean_inc_ref(v_uri_8_);
v___x_22_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_22_, 0, v_uri_8_);
lean_ctor_set(v___x_22_, 1, v_pos_9_);
lean_ctor_set(v___x_22_, 2, v___x_21_);
lean_ctor_set(v___x_22_, 3, v_id_x3f_4_);
v___x_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 6, v___x_23_);
v___x_25_ = v___x_19_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_label_11_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v_detail_x3f_12_);
lean_ctor_set(v_reuseFailAlloc_31_, 2, v_documentation_x3f_13_);
lean_ctor_set(v_reuseFailAlloc_31_, 3, v_kind_x3f_14_);
lean_ctor_set(v_reuseFailAlloc_31_, 4, v_textEdit_x3f_15_);
lean_ctor_set(v_reuseFailAlloc_31_, 5, v_sortText_x3f_16_);
lean_ctor_set(v_reuseFailAlloc_31_, 6, v___x_23_);
lean_ctor_set(v_reuseFailAlloc_31_, 7, v_tags_x3f_17_);
v___x_25_ = v_reuseFailAlloc_31_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_26_ = lean_st_ref_take(v_a_6_);
v___x_27_ = lean_array_push(v___x_26_, v___x_25_);
v___x_28_ = lean_st_ref_put(v_a_6_, v___x_27_);
v___x_29_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
return v___x_30_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_item_3_ = stack[0].m_obj;
lean_object* v_id_x3f_4_ = stack[1].m_obj;
lean_object* v_a_5_ = stack[2].m_obj;
lean_object* v_a_6_ = stack[3].m_obj;
lean_object* v_res_34_;
v_res_34_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(v_item_3_, v_id_x3f_4_, v_a_5_, v_a_6_);
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___boxed(lean_object* v_item_35_, lean_object* v_id_x3f_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(v_item_35_, v_id_x3f_36_, v_a_37_, v_a_38_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
return v_res_40_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem(lean_object* v_item_41_, lean_object* v_id_x3f_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(v_item_41_, v_id_x3f_42_, v_a_43_, v_a_44_);
return v___x_51_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem_0interp(lean_interpreter_value* stack)
{
lean_object* v_item_41_ = stack[0].m_obj;
lean_object* v_id_x3f_42_ = stack[1].m_obj;
lean_object* v_a_43_ = stack[2].m_obj;
lean_object* v_a_44_ = stack[3].m_obj;
lean_object* v_a_45_ = stack[4].m_obj;
lean_object* v_a_46_ = stack[5].m_obj;
lean_object* v_a_47_ = stack[6].m_obj;
lean_object* v_a_48_ = stack[7].m_obj;
lean_object* v_a_49_ = stack[8].m_obj;
lean_object* v_res_52_;
v_res_52_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem(v_item_41_, v_id_x3f_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
stack->m_obj
 = v_res_52_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___boxed(lean_object* v_item_53_, lean_object* v_id_x3f_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem(v_item_53_, v_id_x3f_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
lean_dec(v_a_59_);
lean_dec_ref(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
return v_res_63_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(lean_object* v_label_64_, lean_object* v_id_65_, uint8_t v_kind_66_, lean_object* v_tags_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
uint8_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v_item_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_71_ = 1;
v___x_72_ = l_Lean_Name_toString(v_label_64_, v___x_71_);
v___x_73_ = lean_box(0);
v___x_74_ = lean_box(v_kind_66_);
v___x_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
v___x_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_76_, 0, v_tags_67_);
v_item_77_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_item_77_, 0, v___x_72_);
lean_ctor_set(v_item_77_, 1, v___x_73_);
lean_ctor_set(v_item_77_, 2, v___x_73_);
lean_ctor_set(v_item_77_, 3, v___x_75_);
lean_ctor_set(v_item_77_, 4, v___x_73_);
lean_ctor_set(v_item_77_, 5, v___x_73_);
lean_ctor_set(v_item_77_, 6, v___x_73_);
lean_ctor_set(v_item_77_, 7, v___x_76_);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v_id_65_);
v___x_79_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(v_item_77_, v___x_78_, v_a_68_, v_a_69_);
return v___x_79_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_label_64_ = stack[0].m_obj;
lean_object* v_id_65_ = stack[1].m_obj;
uint8_t v_kind_66_ = stack[2].m_num;
lean_object* v_tags_67_ = stack[3].m_obj;
lean_object* v_a_68_ = stack[4].m_obj;
lean_object* v_a_69_ = stack[5].m_obj;
lean_object* v_res_80_;
v_res_80_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_label_64_, v_id_65_, v_kind_66_, v_tags_67_, v_a_68_, v_a_69_);
stack->m_obj
 = v_res_80_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg___boxed(lean_object* v_label_81_, lean_object* v_id_82_, lean_object* v_kind_83_, lean_object* v_tags_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
uint8_t v_kind_boxed_88_; lean_object* v_res_89_; 
v_kind_boxed_88_ = lean_unbox(v_kind_83_);
v_res_89_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_label_81_, v_id_82_, v_kind_boxed_88_, v_tags_84_, v_a_85_, v_a_86_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
return v_res_89_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(lean_object* v_label_90_, lean_object* v_id_91_, uint8_t v_kind_92_, lean_object* v_tags_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_label_90_, v_id_91_, v_kind_92_, v_tags_93_, v_a_94_, v_a_95_);
return v___x_102_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem_0interp(lean_interpreter_value* stack)
{
lean_object* v_label_90_ = stack[0].m_obj;
lean_object* v_id_91_ = stack[1].m_obj;
uint8_t v_kind_92_ = stack[2].m_num;
lean_object* v_tags_93_ = stack[3].m_obj;
lean_object* v_a_94_ = stack[4].m_obj;
lean_object* v_a_95_ = stack[5].m_obj;
lean_object* v_a_96_ = stack[6].m_obj;
lean_object* v_a_97_ = stack[7].m_obj;
lean_object* v_a_98_ = stack[8].m_obj;
lean_object* v_a_99_ = stack[9].m_obj;
lean_object* v_a_100_ = stack[10].m_obj;
lean_object* v_res_103_;
v_res_103_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(v_label_90_, v_id_91_, v_kind_92_, v_tags_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
stack->m_obj
 = v_res_103_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___boxed(lean_object* v_label_104_, lean_object* v_id_105_, lean_object* v_kind_106_, lean_object* v_tags_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
uint8_t v_kind_boxed_116_; lean_object* v_res_117_; 
v_kind_boxed_116_ = lean_unbox(v_kind_106_);
v_res_117_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(v_label_104_, v_id_105_, v_kind_boxed_116_, v_tags_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
return v_res_117_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(lean_object* v_label_118_, lean_object* v_declName_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_127_; lean_object* v_env_128_; uint8_t v___x_129_; lean_object* v___x_130_; 
v___x_127_ = lean_st_ref_get(v_a_125_);
v_env_128_ = lean_ctor_get(v___x_127_, 0);
lean_inc_ref(v_env_128_);
lean_dec(v___x_127_);
v___x_129_ = 0;
lean_inc(v_declName_119_);
v___x_130_ = l_Lean_Environment_find_x3f(v_env_128_, v_declName_119_, v___x_129_);
if (lean_obj_tag(v___x_130_) == 1)
{
lean_object* v_val_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_160_; 
v_val_131_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_160_ == 0)
{
v___x_133_ = v___x_130_;
v_isShared_134_ = v_isSharedCheck_160_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_val_131_);
lean_dec(v___x_130_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_160_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Server_Completion_getCompletionKindForDecl(v_val_131_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
lean_dec(v_val_131_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_137_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v___x_135_, 1);
lean_inc(v_declName_119_);
v___x_137_ = l_Lean_Server_Completion_getCompletionTagsForDecl___redArg(v_declName_119_, v_a_125_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_140_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_a_138_);
lean_dec_ref_known(v___x_137_, 1);
if (v_isShared_134_ == 0)
{
lean_ctor_set_tag(v___x_133_, 0);
lean_ctor_set(v___x_133_, 0, v_declName_119_);
v___x_140_ = v___x_133_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_declName_119_);
v___x_140_ = v_reuseFailAlloc_143_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
uint8_t v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_unbox(v_a_136_);
lean_dec(v_a_136_);
v___x_142_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_label_118_, v___x_140_, v___x_141_, v_a_138_, v_a_120_, v_a_121_);
return v___x_142_;
}
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
lean_dec(v_a_136_);
lean_del_object(v___x_133_);
lean_dec(v_declName_119_);
lean_dec(v_label_118_);
v_a_144_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_137_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_137_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
lean_del_object(v___x_133_);
lean_dec(v_declName_119_);
lean_dec(v_label_118_);
v_a_152_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_135_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_135_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v___x_130_);
lean_dec(v_declName_119_);
lean_dec(v_label_118_);
v___x_161_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_label_118_ = stack[0].m_obj;
lean_object* v_declName_119_ = stack[1].m_obj;
lean_object* v_a_120_ = stack[2].m_obj;
lean_object* v_a_121_ = stack[3].m_obj;
lean_object* v_a_122_ = stack[4].m_obj;
lean_object* v_a_123_ = stack[5].m_obj;
lean_object* v_a_124_ = stack[6].m_obj;
lean_object* v_a_125_ = stack[7].m_obj;
lean_object* v_res_163_;
v_res_163_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v_label_118_, v_declName_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
stack->m_obj
 = v_res_163_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg___boxed(lean_object* v_label_164_, lean_object* v_declName_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v_label_164_, v_declName_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
return v_res_173_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl(lean_object* v_label_174_, lean_object* v_declName_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v_label_174_, v_declName_175_, v_a_176_, v_a_177_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
return v___x_184_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_label_174_ = stack[0].m_obj;
lean_object* v_declName_175_ = stack[1].m_obj;
lean_object* v_a_176_ = stack[2].m_obj;
lean_object* v_a_177_ = stack[3].m_obj;
lean_object* v_a_178_ = stack[4].m_obj;
lean_object* v_a_179_ = stack[5].m_obj;
lean_object* v_a_180_ = stack[6].m_obj;
lean_object* v_a_181_ = stack[7].m_obj;
lean_object* v_a_182_ = stack[8].m_obj;
lean_object* v_res_185_;
v_res_185_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl(v_label_174_, v_declName_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
stack->m_obj
 = v_res_185_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___boxed(lean_object* v_label_186_, lean_object* v_declName_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl(v_label_186_, v_declName_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
return v_res_196_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg(lean_object* v_keyword_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v_item_210_; lean_object* v___x_211_; 
v___x_207_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__1));
v___x_208_ = lean_box(0);
v___x_209_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__2));
v_item_210_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_item_210_, 0, v_keyword_203_);
lean_ctor_set(v_item_210_, 1, v___x_207_);
lean_ctor_set(v_item_210_, 2, v___x_208_);
lean_ctor_set(v_item_210_, 3, v___x_209_);
lean_ctor_set(v_item_210_, 4, v___x_208_);
lean_ctor_set(v_item_210_, 5, v___x_208_);
lean_ctor_set(v_item_210_, 6, v___x_208_);
lean_ctor_set(v_item_210_, 7, v___x_208_);
v___x_211_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(v_item_210_, v___x_208_, v_a_204_, v_a_205_);
return v___x_211_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keyword_203_ = stack[0].m_obj;
lean_object* v_a_204_ = stack[1].m_obj;
lean_object* v_a_205_ = stack[2].m_obj;
lean_object* v_res_212_;
v_res_212_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg(v_keyword_203_, v_a_204_, v_a_205_);
stack->m_obj
 = v_res_212_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___boxed(lean_object* v_keyword_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg(v_keyword_213_, v_a_214_, v_a_215_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
return v_res_217_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem(lean_object* v_keyword_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg(v_keyword_218_, v_a_219_, v_a_220_);
return v___x_227_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem_0interp(lean_interpreter_value* stack)
{
lean_object* v_keyword_218_ = stack[0].m_obj;
lean_object* v_a_219_ = stack[1].m_obj;
lean_object* v_a_220_ = stack[2].m_obj;
lean_object* v_a_221_ = stack[3].m_obj;
lean_object* v_a_222_ = stack[4].m_obj;
lean_object* v_a_223_ = stack[5].m_obj;
lean_object* v_a_224_ = stack[6].m_obj;
lean_object* v_a_225_ = stack[7].m_obj;
lean_object* v_res_228_;
v_res_228_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem(v_keyword_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
stack->m_obj
 = v_res_228_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___boxed(lean_object* v_keyword_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem(v_keyword_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec_ref(v_a_232_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
return v_res_238_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg(lean_object* v_ns_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
uint8_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v_item_254_; lean_object* v___x_255_; 
v___x_249_ = 1;
v___x_250_ = l_Lean_Name_toString(v_ns_245_, v___x_249_);
v___x_251_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__1));
v___x_252_ = lean_box(0);
v___x_253_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__2));
v_item_254_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_item_254_, 0, v___x_250_);
lean_ctor_set(v_item_254_, 1, v___x_251_);
lean_ctor_set(v_item_254_, 2, v___x_252_);
lean_ctor_set(v_item_254_, 3, v___x_253_);
lean_ctor_set(v_item_254_, 4, v___x_252_);
lean_ctor_set(v_item_254_, 5, v___x_252_);
lean_ctor_set(v_item_254_, 6, v___x_252_);
lean_ctor_set(v_item_254_, 7, v___x_252_);
v___x_255_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(v_item_254_, v___x_252_, v_a_246_, v_a_247_);
return v___x_255_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ns_245_ = stack[0].m_obj;
lean_object* v_a_246_ = stack[1].m_obj;
lean_object* v_a_247_ = stack[2].m_obj;
lean_object* v_res_256_;
v_res_256_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg(v_ns_245_, v_a_246_, v_a_247_);
stack->m_obj
 = v_res_256_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___boxed(lean_object* v_ns_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg(v_ns_257_, v_a_258_, v_a_259_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
return v_res_261_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem(lean_object* v_ns_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg(v_ns_262_, v_a_263_, v_a_264_);
return v___x_271_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem_0interp(lean_interpreter_value* stack)
{
lean_object* v_ns_262_ = stack[0].m_obj;
lean_object* v_a_263_ = stack[1].m_obj;
lean_object* v_a_264_ = stack[2].m_obj;
lean_object* v_a_265_ = stack[3].m_obj;
lean_object* v_a_266_ = stack[4].m_obj;
lean_object* v_a_267_ = stack[5].m_obj;
lean_object* v_a_268_ = stack[6].m_obj;
lean_object* v_a_269_ = stack[7].m_obj;
lean_object* v_res_272_;
v_res_272_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem(v_ns_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
stack->m_obj
 = v_res_272_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___boxed(lean_object* v_ns_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem(v_ns_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
return v_res_282_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___lam__0(lean_object* v___x_283_, lean_object* v_x_284_, lean_object* v___x_285_, lean_object* v_a_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_st_mk_ref(v___x_283_);
lean_inc_ref(v_a_286_);
lean_inc(v___x_292_);
v___x_293_ = lean_apply_8(v_x_284_, v___x_285_, v___x_292_, v_a_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, lean_box(0));
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_322_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_322_ == 0)
{
v___x_296_ = v___x_293_;
v_isShared_297_ = v_isSharedCheck_322_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_293_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_322_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
if (lean_obj_tag(v_a_294_) == 0)
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_308_; 
lean_dec(v___x_292_);
v_a_298_ = lean_ctor_get(v_a_294_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v_a_294_);
if (v_isSharedCheck_308_ == 0)
{
v___x_300_ = v_a_294_;
v_isShared_301_ = v_isSharedCheck_308_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v_a_294_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_308_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_307_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_305_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_303_);
v___x_305_ = v___x_296_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_303_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_321_; 
v_a_309_ = lean_ctor_get(v_a_294_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v_a_294_);
if (v_isSharedCheck_321_ == 0)
{
v___x_311_ = v_a_294_;
v_isShared_312_ = v_isSharedCheck_321_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v_a_294_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_321_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_313_ = lean_st_ref_get(v___x_292_);
lean_dec(v___x_292_);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v_a_309_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_314_);
v___x_316_ = v___x_311_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_314_);
v___x_316_ = v_reuseFailAlloc_320_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_318_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_316_);
v___x_318_ = v___x_296_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
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
}
else
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
lean_dec(v___x_292_);
v_a_323_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_293_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_293_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_283_ = stack[0].m_obj;
lean_object* v_x_284_ = stack[1].m_obj;
lean_object* v___x_285_ = stack[2].m_obj;
lean_object* v_a_286_ = stack[3].m_obj;
lean_object* v___y_287_ = stack[4].m_obj;
lean_object* v___y_288_ = stack[5].m_obj;
lean_object* v___y_289_ = stack[6].m_obj;
lean_object* v___y_290_ = stack[7].m_obj;
lean_object* v_res_331_;
v_res_331_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___lam__0(v___x_283_, v_x_284_, v___x_285_, v_a_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
stack->m_obj
 = v_res_331_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___lam__0___boxed(lean_object* v___x_332_, lean_object* v_x_333_, lean_object* v___x_334_, lean_object* v_a_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___lam__0(v___x_332_, v_x_333_, v___x_334_, v_a_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec_ref(v_a_335_);
return v_res_341_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = l_Lean_Server_RequestCancellation_requestCancelled;
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(lean_object* v_uri_346_, lean_object* v_pos_347_, lean_object* v_completionInfoPos_348_, lean_object* v_ctx_349_, lean_object* v_lctx_350_, lean_object* v_x_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___f_356_; lean_object* v___x_357_; 
v___x_354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_354_, 0, v_uri_346_);
lean_ctor_set(v___x_354_, 1, v_pos_347_);
lean_ctor_set(v___x_354_, 2, v_completionInfoPos_348_);
v___x_355_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
lean_inc_ref(v_a_352_);
v___f_356_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___lam__0___boxed), 9, 4);
lean_closure_set(v___f_356_, 0, v___x_355_);
lean_closure_set(v___f_356_, 1, v_x_351_);
lean_closure_set(v___f_356_, 2, v___x_354_);
lean_closure_set(v___f_356_, 3, v_a_352_);
v___x_357_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_349_, v_lctx_350_, v___f_356_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_378_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_378_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_378_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_378_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
if (lean_obj_tag(v_a_358_) == 0)
{
lean_object* v___x_362_; lean_object* v___x_364_; 
lean_dec_ref_known(v_a_358_, 1);
v___x_362_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_362_);
v___x_364_ = v___x_360_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_377_; 
v_a_366_ = lean_ctor_get(v_a_358_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v_a_358_);
if (v_isSharedCheck_377_ == 0)
{
v___x_368_ = v_a_358_;
v_isShared_369_ = v_isSharedCheck_377_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v_a_358_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_377_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v_snd_370_; lean_object* v___x_372_; 
v_snd_370_ = lean_ctor_get(v_a_366_, 1);
lean_inc(v_snd_370_);
lean_dec(v_a_366_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v_snd_370_);
v___x_372_ = v___x_368_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_snd_370_);
v___x_372_ = v_reuseFailAlloc_376_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_374_; 
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_372_);
v___x_374_ = v___x_360_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
v_a_379_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_357_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_357_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM_0interp(lean_interpreter_value* stack)
{
lean_object* v_uri_346_ = stack[0].m_obj;
lean_object* v_pos_347_ = stack[1].m_obj;
lean_object* v_completionInfoPos_348_ = stack[2].m_obj;
lean_object* v_ctx_349_ = stack[3].m_obj;
lean_object* v_lctx_350_ = stack[4].m_obj;
lean_object* v_x_351_ = stack[5].m_obj;
lean_object* v_a_352_ = stack[6].m_obj;
lean_object* v_res_387_;
v_res_387_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_346_, v_pos_347_, v_completionInfoPos_348_, v_ctx_349_, v_lctx_350_, v_x_351_, v_a_352_);
stack->m_obj
 = v_res_387_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___boxed(lean_object* v_uri_388_, lean_object* v_pos_389_, lean_object* v_completionInfoPos_390_, lean_object* v_ctx_391_, lean_object* v_lctx_392_, lean_object* v_x_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_388_, v_pos_389_, v_completionInfoPos_390_, v_ctx_391_, v_lctx_392_, v_x_393_, v_a_394_);
lean_dec_ref(v_a_394_);
return v_res_396_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(lean_object* v_declName_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_400_; 
lean_inc(v_declName_397_);
v___x_400_ = l_Lean_privateToUserName_x3f(v_declName_397_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_401_, 0, v_declName_397_);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
return v___x_402_;
}
else
{
lean_object* v_val_403_; lean_object* v___x_404_; lean_object* v_env_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v_val_403_ = lean_ctor_get(v___x_400_, 0);
v___x_404_ = lean_st_ref_get(v_a_398_);
v_env_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc_ref(v_env_405_);
lean_dec(v___x_404_);
lean_inc(v_val_403_);
v___x_406_ = l_Lean_mkPrivateName(v_env_405_, v_val_403_);
lean_dec_ref(v_env_405_);
v___x_407_ = lean_name_eq(v___x_406_, v_declName_397_);
lean_dec(v_declName_397_);
lean_dec(v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_415_; 
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; 
v_unused_416_ = lean_ctor_get(v___x_400_, 0);
lean_dec(v_unused_416_);
v___x_409_ = v___x_400_;
v_isShared_410_ = v_isSharedCheck_415_;
goto v_resetjp_408_;
}
else
{
lean_dec(v___x_400_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_415_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_411_ = lean_box(0);
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 0);
lean_ctor_set(v___x_409_, 0, v___x_411_);
v___x_413_ = v___x_409_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
else
{
lean_object* v___x_417_; 
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_400_);
return v___x_417_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_397_ = stack[0].m_obj;
lean_object* v_a_398_ = stack[1].m_obj;
lean_object* v_res_418_;
v_res_418_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_397_, v_a_398_);
stack->m_obj
 = v_res_418_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg___boxed(lean_object* v_declName_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_419_, v_a_420_);
lean_dec(v_a_420_);
return v_res_422_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f(lean_object* v_declName_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_423_, v_a_427_);
return v___x_429_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_423_ = stack[0].m_obj;
lean_object* v_a_424_ = stack[1].m_obj;
lean_object* v_a_425_ = stack[2].m_obj;
lean_object* v_a_426_ = stack[3].m_obj;
lean_object* v_a_427_ = stack[4].m_obj;
lean_object* v_res_430_;
v_res_430_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f(v_declName_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___boxed(lean_object* v_declName_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f(v_declName_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
return v_res_437_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(lean_object* v_ns_438_, lean_object* v_id_439_, uint8_t v_danglingDot_440_, lean_object* v_declName_441_, lean_object* v_a_442_){
_start:
{
lean_object* v___x_447_; lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_507_; 
v___x_447_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_441_, v_a_442_);
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_507_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_507_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_507_;
goto v_resetjp_449_;
}
v___jp_444_:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_box(0);
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
v_resetjp_449_:
{
if (lean_obj_tag(v_a_448_) == 1)
{
lean_object* v_val_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_502_; 
v_val_452_ = lean_ctor_get(v_a_448_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v_a_448_);
if (v_isSharedCheck_502_ == 0)
{
v___x_454_ = v_a_448_;
v_isShared_455_ = v_isSharedCheck_502_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_val_452_);
lean_dec(v_a_448_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_502_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
uint8_t v___x_456_; 
v___x_456_ = l_Lean_Name_isPrefixOf(v_ns_438_, v_val_452_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_459_; 
lean_del_object(v___x_454_);
lean_dec(v_val_452_);
v___x_457_ = lean_box(0);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_457_);
v___x_459_ = v___x_450_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_box(0);
v___x_462_ = l_Lean_Name_replacePrefix(v_val_452_, v_ns_438_, v___x_461_);
if (v_danglingDot_440_ == 0)
{
if (lean_obj_tag(v_id_439_) == 1)
{
if (lean_obj_tag(v___x_462_) == 1)
{
lean_object* v_pre_463_; lean_object* v_str_464_; lean_object* v_pre_465_; lean_object* v_str_466_; uint8_t v___x_467_; 
v_pre_463_ = lean_ctor_get(v_id_439_, 0);
v_str_464_ = lean_ctor_get(v_id_439_, 1);
v_pre_465_ = lean_ctor_get(v___x_462_, 0);
v_str_466_ = lean_ctor_get(v___x_462_, 1);
v___x_467_ = lean_name_eq(v_pre_463_, v_pre_465_);
if (v___x_467_ == 0)
{
uint8_t v___x_468_; 
v___x_468_ = l_Lean_Name_isAnonymous(v_pre_463_);
if (v___x_468_ == 0)
{
lean_dec_ref_known(v___x_462_, 2);
lean_del_object(v___x_454_);
lean_del_object(v___x_450_);
goto v___jp_444_;
}
else
{
uint8_t v___x_469_; 
v___x_469_ = l_Lean_String_charactersIn(v_str_464_, v_str_466_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_472_; 
lean_dec_ref_known(v___x_462_, 2);
lean_del_object(v___x_454_);
v___x_470_ = lean_box(0);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_470_);
v___x_472_ = v___x_450_;
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
else
{
lean_object* v___x_475_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_462_);
v___x_475_ = v___x_454_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_462_);
v___x_475_ = v_reuseFailAlloc_479_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_477_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_475_);
v___x_477_ = v___x_450_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
else
{
uint8_t v___x_480_; 
lean_inc_ref(v_str_466_);
lean_dec_ref_known(v___x_462_, 2);
v___x_480_ = l_Lean_String_charactersIn(v_str_464_, v_str_466_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_483_; 
lean_dec_ref(v_str_466_);
lean_del_object(v___x_454_);
v___x_481_ = lean_box(0);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_481_);
v___x_483_ = v___x_450_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
else
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = l_Lean_Name_str___override(v___x_461_, v_str_466_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_485_);
v___x_487_ = v___x_454_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_491_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_489_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_487_);
v___x_489_ = v___x_450_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
else
{
lean_dec(v___x_462_);
lean_del_object(v___x_454_);
lean_del_object(v___x_450_);
goto v___jp_444_;
}
}
else
{
lean_dec(v___x_462_);
lean_del_object(v___x_454_);
lean_del_object(v___x_450_);
goto v___jp_444_;
}
}
else
{
uint8_t v___x_492_; 
v___x_492_ = l_Lean_Name_isPrefixOf(v_id_439_, v___x_462_);
if (v___x_492_ == 0)
{
lean_dec(v___x_462_);
lean_del_object(v___x_454_);
lean_del_object(v___x_450_);
goto v___jp_444_;
}
else
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = l_Lean_Name_replacePrefix(v___x_462_, v_id_439_, v___x_461_);
v___x_494_ = l_Lean_Name_isAtomic(v___x_493_);
if (v___x_494_ == 0)
{
lean_dec(v___x_493_);
lean_del_object(v___x_454_);
lean_del_object(v___x_450_);
goto v___jp_444_;
}
else
{
uint8_t v___x_495_; 
v___x_495_ = l_Lean_Name_isAnonymous(v___x_493_);
if (v___x_495_ == 0)
{
if (v___x_492_ == 0)
{
lean_dec(v___x_493_);
lean_del_object(v___x_454_);
lean_del_object(v___x_450_);
goto v___jp_444_;
}
else
{
lean_object* v___x_497_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_493_);
v___x_497_ = v___x_454_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_493_);
v___x_497_ = v_reuseFailAlloc_501_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_499_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_497_);
v___x_499_ = v___x_450_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_dec(v___x_493_);
lean_del_object(v___x_454_);
lean_del_object(v___x_450_);
goto v___jp_444_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_503_; lean_object* v___x_505_; 
lean_dec(v_a_448_);
v___x_503_ = lean_box(0);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_503_);
v___x_505_ = v___x_450_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ns_438_ = stack[0].m_obj;
lean_object* v_id_439_ = stack[1].m_obj;
uint8_t v_danglingDot_440_ = stack[2].m_num;
lean_object* v_declName_441_ = stack[3].m_obj;
lean_object* v_a_442_ = stack[4].m_obj;
lean_object* v_res_508_;
v_res_508_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_438_, v_id_439_, v_danglingDot_440_, v_declName_441_, v_a_442_);
stack->m_obj
 = v_res_508_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg___boxed(lean_object* v_ns_509_, lean_object* v_id_510_, lean_object* v_danglingDot_511_, lean_object* v_declName_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
uint8_t v_danglingDot_boxed_515_; lean_object* v_res_516_; 
v_danglingDot_boxed_515_ = lean_unbox(v_danglingDot_511_);
v_res_516_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_509_, v_id_510_, v_danglingDot_boxed_515_, v_declName_512_, v_a_513_);
lean_dec(v_a_513_);
lean_dec(v_id_510_);
lean_dec(v_ns_509_);
return v_res_516_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f(lean_object* v_ns_517_, lean_object* v_id_518_, uint8_t v_danglingDot_519_, lean_object* v_declName_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_517_, v_id_518_, v_danglingDot_519_, v_declName_520_, v_a_524_);
return v___x_526_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_ns_517_ = stack[0].m_obj;
lean_object* v_id_518_ = stack[1].m_obj;
uint8_t v_danglingDot_519_ = stack[2].m_num;
lean_object* v_declName_520_ = stack[3].m_obj;
lean_object* v_a_521_ = stack[4].m_obj;
lean_object* v_a_522_ = stack[5].m_obj;
lean_object* v_a_523_ = stack[6].m_obj;
lean_object* v_a_524_ = stack[7].m_obj;
lean_object* v_res_527_;
v_res_527_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f(v_ns_517_, v_id_518_, v_danglingDot_519_, v_declName_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
stack->m_obj
 = v_res_527_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___boxed(lean_object* v_ns_528_, lean_object* v_id_529_, lean_object* v_danglingDot_530_, lean_object* v_declName_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
uint8_t v_danglingDot_boxed_537_; lean_object* v_res_538_; 
v_danglingDot_boxed_537_ = lean_unbox(v_danglingDot_530_);
v_res_538_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f(v_ns_528_, v_id_529_, v_danglingDot_boxed_537_, v_declName_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
lean_dec(v_id_529_);
lean_dec(v_ns_528_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__0(lean_object* v___y_539_, lean_object* v_toPure_540_, lean_object* v_a_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v_a_541_);
lean_ctor_set(v___x_542_, 1, v___y_539_);
v___x_543_ = lean_apply_2(v_toPure_540_, lean_box(0), v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__1(lean_object* v_f_544_, lean_object* v_decl_545_, lean_object* v_ci_546_, lean_object* v_toPure_547_, lean_object* v_toBind_548_, lean_object* v_____r_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___x_551_; lean_object* v___f_552_; lean_object* v___x_553_; 
v___x_551_ = lean_apply_2(v_f_544_, v_decl_545_, v_ci_546_);
v___f_552_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_552_, 0, v___y_550_);
lean_closure_set(v___f_552_, 1, v_toPure_547_);
v___x_553_ = lean_apply_4(v_toBind_548_, lean_box(0), lean_box(0), v___x_551_, v___f_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__2(lean_object* v___f_554_, lean_object* v_____x_555_){
_start:
{
lean_object* v_fst_556_; lean_object* v_snd_557_; lean_object* v___x_558_; 
v_fst_556_ = lean_ctor_get(v_____x_555_, 0);
lean_inc(v_fst_556_);
v_snd_557_ = lean_ctor_get(v_____x_555_, 1);
lean_inc(v_snd_557_);
lean_dec_ref(v_____x_555_);
v___x_558_ = lean_apply_2(v___f_554_, v_fst_556_, v_snd_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3(lean_object* v_toPure_562_, lean_object* v_toBind_563_, lean_object* v___f_564_, lean_object* v_____x_565_){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_566_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3___closed__0));
v___x_567_ = lean_apply_2(v_toPure_562_, lean_box(0), v___x_566_);
v___x_568_ = lean_apply_4(v_toBind_563_, lean_box(0), lean_box(0), v___x_567_, v___f_564_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3___boxed(lean_object* v_toPure_569_, lean_object* v_toBind_570_, lean_object* v___f_571_, lean_object* v_____x_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3(v_toPure_569_, v_toBind_570_, v___f_571_, v_____x_572_);
lean_dec_ref(v_____x_572_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__4(lean_object* v_snd_574_, lean_object* v_toPure_575_, lean_object* v_a_576_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v_a_576_);
lean_ctor_set(v___x_577_, 1, v_snd_574_);
v___x_578_ = lean_apply_2(v_toPure_575_, lean_box(0), v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__5(lean_object* v___f_579_, lean_object* v_toPure_580_, lean_object* v_toBind_581_, lean_object* v_inst_582_, lean_object* v___f_583_, lean_object* v_____x_584_){
_start:
{
lean_object* v_fst_585_; lean_object* v_snd_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v_fst_585_ = lean_ctor_get(v_____x_584_, 0);
lean_inc(v_fst_585_);
v_snd_586_ = lean_ctor_get(v_____x_584_, 1);
lean_inc(v_snd_586_);
lean_dec_ref(v_____x_584_);
v___x_587_ = lean_unsigned_to_nat(10000u);
v___x_588_ = lean_nat_dec_le(v___x_587_, v_fst_585_);
lean_dec(v_fst_585_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; 
lean_dec(v___f_583_);
lean_dec(v_inst_582_);
lean_dec(v_toBind_581_);
lean_dec(v_toPure_580_);
v___x_589_ = lean_box(0);
v___x_590_ = lean_apply_2(v___f_579_, v___x_589_, v_snd_586_);
return v___x_590_;
}
else
{
lean_object* v___f_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
lean_dec(v___f_579_);
v___f_591_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__4), 3, 2);
lean_closure_set(v___f_591_, 0, v_snd_586_);
lean_closure_set(v___f_591_, 1, v_toPure_580_);
lean_inc(v_toBind_581_);
v___x_592_ = lean_apply_4(v_toBind_581_, lean_box(0), lean_box(0), v_inst_582_, v___f_591_);
v___x_593_ = lean_apply_4(v_toBind_581_, lean_box(0), lean_box(0), v___x_592_, v___f_583_);
return v___x_593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__6(lean_object* v_toPure_594_, lean_object* v_toBind_595_, lean_object* v___f_596_, lean_object* v_____x_597_){
_start:
{
lean_object* v_snd_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_607_; 
v_snd_598_ = lean_ctor_get(v_____x_597_, 1);
v_isSharedCheck_607_ = !lean_is_exclusive(v_____x_597_);
if (v_isSharedCheck_607_ == 0)
{
lean_object* v_unused_608_; 
v_unused_608_ = lean_ctor_get(v_____x_597_, 0);
lean_dec(v_unused_608_);
v___x_600_ = v_____x_597_;
v_isShared_601_ = v_isSharedCheck_607_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_snd_598_);
lean_dec(v_____x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_607_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
lean_inc(v_snd_598_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v_snd_598_);
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_snd_598_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_snd_598_);
v___x_603_ = v_reuseFailAlloc_606_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_apply_2(v_toPure_594_, lean_box(0), v___x_603_);
v___x_605_ = lean_apply_4(v_toBind_595_, lean_box(0), lean_box(0), v___x_604_, v___f_596_);
return v___x_605_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__7(lean_object* v_f_609_, lean_object* v_toPure_610_, lean_object* v_toBind_611_, lean_object* v_inst_612_, lean_object* v_decl_613_, lean_object* v_ci_614_, lean_object* v___y_615_){
_start:
{
lean_object* v___f_616_; lean_object* v___f_617_; lean_object* v___f_618_; lean_object* v___f_619_; lean_object* v___f_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
lean_inc_n(v_toBind_611_, 4);
lean_inc_n(v_toPure_610_, 4);
v___f_616_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__1), 7, 5);
lean_closure_set(v___f_616_, 0, v_f_609_);
lean_closure_set(v___f_616_, 1, v_decl_613_);
lean_closure_set(v___f_616_, 2, v_ci_614_);
lean_closure_set(v___f_616_, 3, v_toPure_610_);
lean_closure_set(v___f_616_, 4, v_toBind_611_);
lean_inc_ref(v___f_616_);
v___f_617_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__2), 2, 1);
lean_closure_set(v___f_617_, 0, v___f_616_);
v___f_618_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_618_, 0, v_toPure_610_);
lean_closure_set(v___f_618_, 1, v_toBind_611_);
lean_closure_set(v___f_618_, 2, v___f_617_);
v___f_619_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__5), 6, 5);
lean_closure_set(v___f_619_, 0, v___f_616_);
lean_closure_set(v___f_619_, 1, v_toPure_610_);
lean_closure_set(v___f_619_, 2, v_toBind_611_);
lean_closure_set(v___f_619_, 3, v_inst_612_);
lean_closure_set(v___f_619_, 4, v___f_618_);
v___f_620_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__6), 4, 3);
lean_closure_set(v___f_620_, 0, v_toPure_610_);
lean_closure_set(v___f_620_, 1, v_toBind_611_);
lean_closure_set(v___f_620_, 2, v___f_619_);
v___x_621_ = lean_box(0);
v___x_622_ = lean_unsigned_to_nat(1u);
v___x_623_ = lean_nat_add(v___y_615_, v___x_622_);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_621_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = lean_apply_2(v_toPure_610_, lean_box(0), v___x_624_);
v___x_626_ = lean_apply_4(v_toBind_611_, lean_box(0), lean_box(0), v___x_625_, v___f_620_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__7___boxed(lean_object* v_f_627_, lean_object* v_toPure_628_, lean_object* v_toBind_629_, lean_object* v_inst_630_, lean_object* v_decl_631_, lean_object* v_ci_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__7(v_f_627_, v_toPure_628_, v_toBind_629_, v_inst_630_, v_decl_631_, v_ci_632_, v___y_633_);
lean_dec(v___y_633_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__8(lean_object* v_toPure_635_, lean_object* v_____x_636_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_box(0);
v___x_638_ = lean_apply_2(v_toPure_635_, lean_box(0), v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__8___boxed(lean_object* v_toPure_639_, lean_object* v_____x_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__8(v_toPure_639_, v_____x_640_);
lean_dec_ref(v_____x_640_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg(lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_f_646_){
_start:
{
lean_object* v_toApplicative_647_; lean_object* v_toBind_648_; lean_object* v___f_649_; lean_object* v___f_650_; lean_object* v___f_651_; lean_object* v___f_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v_getEnv_659_; lean_object* v_modifyEnv_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_678_; 
v_toApplicative_647_ = lean_ctor_get(v_inst_642_, 0);
lean_inc_ref(v_toApplicative_647_);
v_toBind_648_ = lean_ctor_get(v_inst_642_, 1);
lean_inc(v_toBind_648_);
lean_inc_ref_n(v_inst_642_, 7);
v___f_649_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_649_, 0, v_inst_642_);
v___f_650_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_650_, 0, v_inst_642_);
v___f_651_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_651_, 0, v_inst_642_);
v___f_652_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_652_, 0, v_inst_642_);
v___x_653_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_653_, 0, lean_box(0));
lean_closure_set(v___x_653_, 1, lean_box(0));
lean_closure_set(v___x_653_, 2, v_inst_642_);
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v___f_649_);
v___x_655_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_655_, 0, lean_box(0));
lean_closure_set(v___x_655_, 1, lean_box(0));
lean_closure_set(v___x_655_, 2, v_inst_642_);
v___x_656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
lean_ctor_set(v___x_656_, 2, v___f_650_);
lean_ctor_set(v___x_656_, 3, v___f_651_);
lean_ctor_set(v___x_656_, 4, v___f_652_);
v___x_657_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_657_, 0, lean_box(0));
lean_closure_set(v___x_657_, 1, lean_box(0));
lean_closure_set(v___x_657_, 2, v_inst_642_);
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_656_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v_getEnv_659_ = lean_ctor_get(v_inst_643_, 0);
v_modifyEnv_660_ = lean_ctor_get(v_inst_643_, 1);
v_isSharedCheck_678_ = !lean_is_exclusive(v_inst_643_);
if (v_isSharedCheck_678_ == 0)
{
v___x_662_ = v_inst_643_;
v_isShared_663_ = v_isSharedCheck_678_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_modifyEnv_660_);
lean_inc(v_getEnv_659_);
lean_dec(v_inst_643_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_678_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___f_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
lean_inc_ref(v_inst_642_);
v___x_664_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_664_, 0, lean_box(0));
lean_closure_set(v___x_664_, 1, lean_box(0));
lean_closure_set(v___x_664_, 2, v_inst_642_);
lean_inc_ref(v___x_664_);
v___f_665_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_665_, 0, v_modifyEnv_660_);
lean_closure_set(v___f_665_, 1, v___x_664_);
v___x_666_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 5);
lean_closure_set(v___x_666_, 0, lean_box(0));
lean_closure_set(v___x_666_, 1, lean_box(0));
lean_closure_set(v___x_666_, 2, v_inst_642_);
lean_closure_set(v___x_666_, 3, lean_box(0));
lean_closure_set(v___x_666_, 4, v_getEnv_659_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v___f_665_);
lean_ctor_set(v___x_662_, 0, v___x_666_);
v___x_668_ = v___x_662_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v___f_665_);
v___x_668_ = v_reuseFailAlloc_677_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v_toPure_669_; lean_object* v___f_670_; lean_object* v___f_671_; lean_object* v___f_672_; lean_object* v___x_673_; lean_object* v___x_467__overap_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v_toPure_669_ = lean_ctor_get(v_toApplicative_647_, 1);
lean_inc_n(v_toPure_669_, 2);
lean_dec_ref(v_toApplicative_647_);
lean_inc(v_toBind_648_);
v___f_670_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_670_, 0, v_f_646_);
lean_closure_set(v___f_670_, 1, v_toPure_669_);
lean_closure_set(v___f_670_, 2, v_toBind_648_);
lean_closure_set(v___f_670_, 3, v_inst_645_);
v___f_671_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_671_, 0, v_inst_644_);
lean_closure_set(v___f_671_, 1, v___x_664_);
v___f_672_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__8___boxed), 2, 1);
lean_closure_set(v___f_672_, 0, v_toPure_669_);
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_467__overap_674_ = l_Lean_Server_Completion_forEligibleDeclsM___redArg(v___x_658_, v___x_668_, v___f_671_, v___f_670_);
v___x_675_ = lean_apply_1(v___x_467__overap_674_, v___x_673_);
v___x_676_ = lean_apply_4(v_toBind_648_, lean_box(0), lean_box(0), v___x_675_, v___f_672_);
return v___x_676_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM(lean_object* v_m_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_f_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg(v_inst_680_, v_inst_681_, v_inst_682_, v_inst_683_, v_f_684_);
return v___x_685_;
}
}
uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(lean_object* v_id_686_, lean_object* v_declName_687_, uint8_t v_danglingDot_688_){
_start:
{
if (v_danglingDot_688_ == 0)
{
if (lean_obj_tag(v_id_686_) == 1)
{
lean_object* v_pre_689_; 
v_pre_689_ = lean_ctor_get(v_id_686_, 0);
if (lean_obj_tag(v_pre_689_) == 0)
{
if (lean_obj_tag(v_declName_687_) == 1)
{
lean_object* v_pre_690_; 
v_pre_690_ = lean_ctor_get(v_declName_687_, 0);
if (lean_obj_tag(v_pre_690_) == 0)
{
lean_object* v_str_691_; lean_object* v_str_692_; uint8_t v___x_693_; 
v_str_691_ = lean_ctor_get(v_id_686_, 1);
v_str_692_ = lean_ctor_get(v_declName_687_, 1);
v___x_693_ = l_Lean_String_charactersIn(v_str_691_, v_str_692_);
return v___x_693_;
}
else
{
return v_danglingDot_688_;
}
}
else
{
return v_danglingDot_688_;
}
}
else
{
return v_danglingDot_688_;
}
}
else
{
return v_danglingDot_688_;
}
}
else
{
uint8_t v___x_694_; 
v___x_694_ = 0;
return v___x_694_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_686_ = stack[0].m_obj;
lean_object* v_declName_687_ = stack[1].m_obj;
uint8_t v_danglingDot_688_ = stack[2].m_num;
uint8_t v_res_695_;
v_res_695_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_686_, v_declName_687_, v_danglingDot_688_);
stack->m_num = v_res_695_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic___boxed(lean_object* v_id_696_, lean_object* v_declName_697_, lean_object* v_danglingDot_698_){
_start:
{
uint8_t v_danglingDot_boxed_699_; uint8_t v_res_700_; lean_object* v_r_701_; 
v_danglingDot_boxed_699_ = lean_unbox(v_danglingDot_698_);
v_res_700_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_696_, v_declName_697_, v_danglingDot_boxed_699_);
lean_dec(v_declName_697_);
lean_dec(v_id_696_);
v_r_701_ = lean_box(v_res_700_);
return v_r_701_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go_spec__0(lean_object* v_msg_705_){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go_spec__0___closed__0));
v___x_707_ = lean_panic_fn_borrowed(v___x_706_, v_msg_705_);
return v___x_707_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_711_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__2));
v___x_712_ = lean_unsigned_to_nat(26u);
v___x_713_ = lean_unsigned_to_nat(177u);
v___x_714_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__1));
v___x_715_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__0));
v___x_716_ = l_mkPanicMessageWithDecl(v___x_715_, v___x_714_, v___x_713_, v___x_712_, v___x_711_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go(lean_object* v_newLen_717_, lean_object* v_id_718_){
_start:
{
switch(lean_obj_tag(v_id_718_))
{
case 0:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
lean_dec(v_newLen_717_);
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v_id_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
return v___x_720_;
}
case 1:
{
lean_object* v_pre_721_; lean_object* v_str_722_; lean_object* v___x_723_; lean_object* v_snd_724_; lean_object* v___y_726_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v_pre_721_ = lean_ctor_get(v_id_718_, 0);
v_str_722_ = lean_ctor_get(v_id_718_, 1);
lean_inc(v_pre_721_);
lean_inc(v_newLen_717_);
v___x_723_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go(v_newLen_717_, v_pre_721_);
v_snd_724_ = lean_ctor_get(v___x_723_, 1);
v___x_738_ = lean_unsigned_to_nat(1u);
v___x_739_ = lean_nat_add(v_snd_724_, v___x_738_);
v___x_740_ = lean_nat_dec_le(v_newLen_717_, v___x_739_);
lean_dec(v___x_739_);
if (v___x_740_ == 0)
{
uint8_t v___x_741_; 
lean_inc(v_snd_724_);
lean_dec_ref(v___x_723_);
v___x_741_ = l_Lean_Name_isAnonymous(v_pre_721_);
if (v___x_741_ == 0)
{
v___y_726_ = v___x_738_;
goto v___jp_725_;
}
else
{
lean_object* v___x_742_; 
v___x_742_ = lean_unsigned_to_nat(0u);
v___y_726_ = v___x_742_;
goto v___jp_725_;
}
}
else
{
lean_dec_ref_known(v_id_718_, 2);
lean_dec(v_newLen_717_);
return v___x_723_;
}
v___jp_725_:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v_len_x27_729_; uint8_t v___x_730_; 
v___x_727_ = lean_nat_add(v_snd_724_, v___y_726_);
v___x_728_ = lean_string_length(v_str_722_);
v_len_x27_729_ = lean_nat_add(v___x_727_, v___x_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_nat_dec_le(v_len_x27_729_, v_newLen_717_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
lean_inc_ref(v_str_722_);
lean_inc(v_pre_721_);
lean_dec(v_len_x27_729_);
lean_dec_ref_known(v_id_718_, 2);
v___x_731_ = lean_unsigned_to_nat(0u);
v___x_732_ = lean_nat_sub(v_newLen_717_, v___y_726_);
v___x_733_ = lean_nat_sub(v___x_732_, v_snd_724_);
lean_dec(v_snd_724_);
lean_dec(v___x_732_);
v___x_734_ = lean_string_utf8_extract(v_str_722_, v___x_731_, v___x_733_);
lean_dec(v___x_733_);
lean_dec_ref(v_str_722_);
v___x_735_ = l_Lean_Name_str___override(v_pre_721_, v___x_734_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v_newLen_717_);
return v___x_736_;
}
else
{
lean_object* v___x_737_; 
lean_dec(v_snd_724_);
lean_dec(v_newLen_717_);
v___x_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_737_, 0, v_id_718_);
lean_ctor_set(v___x_737_, 1, v_len_x27_729_);
return v___x_737_;
}
}
}
default: 
{
lean_object* v___x_743_; lean_object* v___x_744_; 
lean_dec_ref_known(v_id_718_, 2);
lean_dec(v_newLen_717_);
v___x_743_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3);
v___x_744_ = l_panic___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go_spec__0(v___x_743_);
return v___x_744_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate(lean_object* v_id_745_, lean_object* v_newLen_746_){
_start:
{
lean_object* v___x_747_; lean_object* v_fst_748_; 
v___x_747_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go(v_newLen_746_, v_id_745_);
v_fst_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_fst_748_);
lean_dec_ref(v___x_747_);
return v_fst_748_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces(lean_object* v_matchUsingNamespace_749_, lean_object* v_ns_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
if (lean_obj_tag(v_ns_750_) == 1)
{
lean_object* v_pre_760_; lean_object* v___x_761_; 
v_pre_760_ = lean_ctor_get(v_ns_750_, 0);
lean_inc(v_pre_760_);
lean_inc_ref(v_matchUsingNamespace_749_);
lean_inc(v_a_758_);
lean_inc_ref(v_a_757_);
lean_inc(v_a_756_);
lean_inc_ref(v_a_755_);
lean_inc_ref(v_a_754_);
lean_inc(v_a_753_);
lean_inc_ref(v_a_752_);
v___x_761_ = lean_apply_10(v_matchUsingNamespace_749_, v_ns_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, lean_box(0));
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
if (lean_obj_tag(v_a_762_) == 0)
{
lean_dec_ref_known(v_a_762_, 1);
lean_dec(v_pre_760_);
lean_dec_ref(v_matchUsingNamespace_749_);
return v___x_761_;
}
else
{
lean_object* v_a_763_; lean_object* v_snd_764_; 
lean_dec_ref_known(v___x_761_, 1);
v_a_763_ = lean_ctor_get(v_a_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v_a_762_, 1);
v_snd_764_ = lean_ctor_get(v_a_763_, 1);
lean_inc(v_snd_764_);
lean_dec(v_a_763_);
v_ns_750_ = v_pre_760_;
v_a_751_ = v_snd_764_;
goto _start;
}
}
else
{
lean_dec(v_pre_760_);
lean_dec_ref(v_matchUsingNamespace_749_);
return v___x_761_;
}
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
lean_dec(v_ns_750_);
lean_dec_ref(v_matchUsingNamespace_749_);
v___x_766_ = lean_box(0);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v_a_751_);
v___x_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
return v___x_769_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces_0interp(lean_interpreter_value* stack)
{
lean_object* v_matchUsingNamespace_749_ = stack[0].m_obj;
lean_object* v_ns_750_ = stack[1].m_obj;
lean_object* v_a_751_ = stack[2].m_obj;
lean_object* v_a_752_ = stack[3].m_obj;
lean_object* v_a_753_ = stack[4].m_obj;
lean_object* v_a_754_ = stack[5].m_obj;
lean_object* v_a_755_ = stack[6].m_obj;
lean_object* v_a_756_ = stack[7].m_obj;
lean_object* v_a_757_ = stack[8].m_obj;
lean_object* v_a_758_ = stack[9].m_obj;
lean_object* v_res_770_;
v_res_770_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces(v_matchUsingNamespace_749_, v_ns_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
stack->m_obj
 = v_res_770_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces___boxed(lean_object* v_matchUsingNamespace_771_, lean_object* v_ns_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces(v_matchUsingNamespace_771_, v_ns_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec_ref(v_a_776_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
return v_res_782_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0(lean_object* v_id_783_, uint8_t v_danglingDot_784_, lean_object* v_declName_785_, lean_object* v_ns_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_818_; 
v___x_796_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_786_, v_id_783_, v_danglingDot_784_, v_declName_785_, v___y_794_);
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_818_ == 0)
{
v___x_799_ = v___x_796_;
v_isShared_800_ = v_isSharedCheck_818_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_818_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
if (lean_obj_tag(v_a_797_) == 1)
{
lean_object* v_val_801_; lean_object* v___x_802_; lean_object* v___y_804_; 
v_val_801_ = lean_ctor_get(v_a_797_, 0);
v___x_802_ = lean_box(0);
if (lean_obj_tag(v___y_787_) == 0)
{
v___y_804_ = v_a_797_;
goto v___jp_803_;
}
else
{
lean_object* v_val_810_; uint8_t v___x_811_; 
v_val_810_ = lean_ctor_get(v___y_787_, 0);
v___x_811_ = l_Lean_Name_isSuffixOf(v_val_801_, v_val_810_);
if (v___x_811_ == 0)
{
lean_dec_ref_known(v_a_797_, 1);
v___y_804_ = v___y_787_;
goto v___jp_803_;
}
else
{
lean_dec_ref_known(v___y_787_, 1);
v___y_804_ = v_a_797_;
goto v___jp_803_;
}
}
v___jp_803_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_802_);
lean_ctor_set(v___x_805_, 1, v___y_804_);
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_806_);
v___x_808_ = v___x_799_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
else
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
lean_dec(v_a_797_);
v___x_812_ = lean_box(0);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v___y_787_);
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_814_);
v___x_816_ = v___x_799_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_783_ = stack[0].m_obj;
uint8_t v_danglingDot_784_ = stack[1].m_num;
lean_object* v_declName_785_ = stack[2].m_obj;
lean_object* v_ns_786_ = stack[3].m_obj;
lean_object* v___y_787_ = stack[4].m_obj;
lean_object* v___y_788_ = stack[5].m_obj;
lean_object* v___y_789_ = stack[6].m_obj;
lean_object* v___y_790_ = stack[7].m_obj;
lean_object* v___y_791_ = stack[8].m_obj;
lean_object* v___y_792_ = stack[9].m_obj;
lean_object* v___y_793_ = stack[10].m_obj;
lean_object* v___y_794_ = stack[11].m_obj;
lean_object* v_res_819_;
v_res_819_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0(v_id_783_, v_danglingDot_784_, v_declName_785_, v_ns_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
stack->m_obj
 = v_res_819_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0___boxed(lean_object* v_id_820_, lean_object* v_danglingDot_821_, lean_object* v_declName_822_, lean_object* v_ns_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
uint8_t v_danglingDot_boxed_833_; lean_object* v_res_834_; 
v_danglingDot_boxed_833_ = lean_unbox(v_danglingDot_821_);
v_res_834_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0(v_id_820_, v_danglingDot_boxed_833_, v_declName_822_, v_ns_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v_ns_823_);
lean_dec(v_id_820_);
return v_res_834_;
}
}
uint8_t l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0(lean_object* v_a_835_, lean_object* v_x_836_){
_start:
{
if (lean_obj_tag(v_x_836_) == 0)
{
uint8_t v___x_837_; 
v___x_837_ = 0;
return v___x_837_;
}
else
{
lean_object* v_head_838_; lean_object* v_tail_839_; uint8_t v___x_840_; 
v_head_838_ = lean_ctor_get(v_x_836_, 0);
v_tail_839_ = lean_ctor_get(v_x_836_, 1);
v___x_840_ = lean_name_eq(v_a_835_, v_head_838_);
if (v___x_840_ == 0)
{
v_x_836_ = v_tail_839_;
goto _start;
}
else
{
return v___x_840_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_835_ = stack[0].m_obj;
lean_object* v_x_836_ = stack[1].m_obj;
uint8_t v_res_842_;
v_res_842_ = l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0(v_a_835_, v_x_836_);
stack->m_num = v_res_842_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0___boxed(lean_object* v_a_843_, lean_object* v_x_844_){
_start:
{
uint8_t v_res_845_; lean_object* v_r_846_; 
v_res_845_ = l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0(v_a_843_, v_x_844_);
lean_dec(v_x_844_);
lean_dec(v_a_843_);
v_r_846_ = lean_box(v_res_845_);
return v_r_846_;
}
}
lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(lean_object* v_declName_847_, lean_object* v_id_848_, uint8_t v_danglingDot_849_, lean_object* v_as_x27_850_, lean_object* v_b_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
if (lean_obj_tag(v_as_x27_850_) == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
lean_dec(v_declName_847_);
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v_b_851_);
lean_ctor_set(v___x_855_, 1, v___y_852_);
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
return v___x_857_;
}
else
{
lean_object* v_head_858_; lean_object* v_tail_859_; lean_object* v___x_860_; 
v_head_858_ = lean_ctor_get(v_as_x27_850_, 0);
v_tail_859_ = lean_ctor_get(v_as_x27_850_, 1);
v___x_860_ = lean_box(0);
if (lean_obj_tag(v_head_858_) == 0)
{
lean_object* v_ns_861_; lean_object* v_except_862_; uint8_t v___x_863_; 
v_ns_861_ = lean_ctor_get(v_head_858_, 0);
v_except_862_ = lean_ctor_get(v_head_858_, 1);
v___x_863_ = l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0(v_declName_847_, v_except_862_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; lean_object* v_a_865_; 
lean_inc(v_declName_847_);
v___x_864_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_861_, v_id_848_, v_danglingDot_849_, v_declName_847_, v___y_853_);
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref(v___x_864_);
if (lean_obj_tag(v_a_865_) == 1)
{
if (lean_obj_tag(v___y_852_) == 0)
{
v_as_x27_850_ = v_tail_859_;
v_b_851_ = v___x_860_;
v___y_852_ = v_a_865_;
goto _start;
}
else
{
lean_object* v_val_867_; lean_object* v_val_868_; uint8_t v___x_869_; 
v_val_867_ = lean_ctor_get(v_a_865_, 0);
v_val_868_ = lean_ctor_get(v___y_852_, 0);
v___x_869_ = l_Lean_Name_isSuffixOf(v_val_867_, v_val_868_);
if (v___x_869_ == 0)
{
lean_dec_ref_known(v_a_865_, 1);
v_as_x27_850_ = v_tail_859_;
v_b_851_ = v___x_860_;
goto _start;
}
else
{
lean_dec_ref_known(v___y_852_, 1);
v_as_x27_850_ = v_tail_859_;
v_b_851_ = v___x_860_;
v___y_852_ = v_a_865_;
goto _start;
}
}
}
else
{
lean_dec(v_a_865_);
v_as_x27_850_ = v_tail_859_;
v_b_851_ = v___x_860_;
goto _start;
}
}
else
{
v_as_x27_850_ = v_tail_859_;
v_b_851_ = v___x_860_;
goto _start;
}
}
else
{
v_as_x27_850_ = v_tail_859_;
v_b_851_ = v___x_860_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_847_ = stack[0].m_obj;
lean_object* v_id_848_ = stack[1].m_obj;
uint8_t v_danglingDot_849_ = stack[2].m_num;
lean_object* v_as_x27_850_ = stack[3].m_obj;
lean_object* v_b_851_ = stack[4].m_obj;
lean_object* v___y_852_ = stack[5].m_obj;
lean_object* v___y_853_ = stack[6].m_obj;
lean_object* v_res_875_;
v_res_875_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_847_, v_id_848_, v_danglingDot_849_, v_as_x27_850_, v_b_851_, v___y_852_, v___y_853_);
stack->m_obj
 = v_res_875_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_declName_876_, lean_object* v_id_877_, lean_object* v_danglingDot_878_, lean_object* v_as_x27_879_, lean_object* v_b_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
uint8_t v_danglingDot_boxed_884_; lean_object* v_res_885_; 
v_danglingDot_boxed_884_ = lean_unbox(v_danglingDot_878_);
v_res_885_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_876_, v_id_877_, v_danglingDot_boxed_884_, v_as_x27_879_, v_b_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec(v_as_x27_879_);
lean_dec(v_id_877_);
return v_res_885_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg(lean_object* v_declName_886_, lean_object* v_id_887_, uint8_t v_danglingDot_888_, lean_object* v_as_889_, lean_object* v_as_x27_890_, lean_object* v_b_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
if (lean_obj_tag(v_as_x27_890_) == 0)
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
lean_dec(v_declName_886_);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v_b_891_);
lean_ctor_set(v___x_901_, 1, v___y_892_);
v___x_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
return v___x_903_;
}
else
{
lean_object* v_head_904_; lean_object* v_tail_905_; lean_object* v___x_906_; 
v_head_904_ = lean_ctor_get(v_as_x27_890_, 0);
v_tail_905_ = lean_ctor_get(v_as_x27_890_, 1);
v___x_906_ = lean_box(0);
if (lean_obj_tag(v_head_904_) == 0)
{
lean_object* v_ns_907_; lean_object* v_except_908_; uint8_t v___x_909_; 
v_ns_907_ = lean_ctor_get(v_head_904_, 0);
v_except_908_ = lean_ctor_get(v_head_904_, 1);
v___x_909_ = l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0(v_declName_886_, v_except_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v_a_911_; 
lean_inc(v_declName_886_);
v___x_910_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_907_, v_id_887_, v_danglingDot_888_, v_declName_886_, v___y_899_);
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref(v___x_910_);
if (lean_obj_tag(v_a_911_) == 1)
{
if (lean_obj_tag(v___y_892_) == 0)
{
lean_object* v___x_912_; 
v___x_912_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_886_, v_id_887_, v_danglingDot_888_, v_tail_905_, v___x_906_, v_a_911_, v___y_899_);
return v___x_912_;
}
else
{
lean_object* v_val_913_; lean_object* v_val_914_; uint8_t v___x_915_; 
v_val_913_ = lean_ctor_get(v_a_911_, 0);
v_val_914_ = lean_ctor_get(v___y_892_, 0);
v___x_915_ = l_Lean_Name_isSuffixOf(v_val_913_, v_val_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; 
lean_dec_ref_known(v_a_911_, 1);
v___x_916_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_886_, v_id_887_, v_danglingDot_888_, v_tail_905_, v___x_906_, v___y_892_, v___y_899_);
return v___x_916_;
}
else
{
lean_object* v___x_917_; 
lean_dec_ref_known(v___y_892_, 1);
v___x_917_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_886_, v_id_887_, v_danglingDot_888_, v_tail_905_, v___x_906_, v_a_911_, v___y_899_);
return v___x_917_;
}
}
}
else
{
lean_object* v___x_918_; 
lean_dec(v_a_911_);
v___x_918_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_886_, v_id_887_, v_danglingDot_888_, v_tail_905_, v___x_906_, v___y_892_, v___y_899_);
return v___x_918_;
}
}
else
{
lean_object* v___x_919_; 
v___x_919_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_886_, v_id_887_, v_danglingDot_888_, v_tail_905_, v___x_906_, v___y_892_, v___y_899_);
return v___x_919_;
}
}
else
{
lean_object* v___x_920_; 
v___x_920_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_886_, v_id_887_, v_danglingDot_888_, v_tail_905_, v___x_906_, v___y_892_, v___y_899_);
return v___x_920_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_886_ = stack[0].m_obj;
lean_object* v_id_887_ = stack[1].m_obj;
uint8_t v_danglingDot_888_ = stack[2].m_num;
lean_object* v_as_889_ = stack[3].m_obj;
lean_object* v_as_x27_890_ = stack[4].m_obj;
lean_object* v_b_891_ = stack[5].m_obj;
lean_object* v___y_892_ = stack[6].m_obj;
lean_object* v___y_893_ = stack[7].m_obj;
lean_object* v___y_894_ = stack[8].m_obj;
lean_object* v___y_895_ = stack[9].m_obj;
lean_object* v___y_896_ = stack[10].m_obj;
lean_object* v___y_897_ = stack[11].m_obj;
lean_object* v___y_898_ = stack[12].m_obj;
lean_object* v___y_899_ = stack[13].m_obj;
lean_object* v_res_921_;
v_res_921_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg(v_declName_886_, v_id_887_, v_danglingDot_888_, v_as_889_, v_as_x27_890_, v_b_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
stack->m_obj
 = v_res_921_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg___boxed(lean_object* v_declName_922_, lean_object* v_id_923_, lean_object* v_danglingDot_924_, lean_object* v_as_925_, lean_object* v_as_x27_926_, lean_object* v_b_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
uint8_t v_danglingDot_boxed_937_; lean_object* v_res_938_; 
v_danglingDot_boxed_937_ = lean_unbox(v_danglingDot_924_);
v_res_938_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg(v_declName_922_, v_id_923_, v_danglingDot_boxed_937_, v_as_925_, v_as_x27_926_, v_b_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v_as_x27_926_);
lean_dec(v_as_925_);
lean_dec(v_id_923_);
return v_res_938_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(lean_object* v_ctx_939_, lean_object* v_declName_940_, lean_object* v_id_941_, uint8_t v_danglingDot_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___y_952_; lean_object* v_toCommandContextInfo_989_; lean_object* v_currNamespace_990_; lean_object* v_openDecls_991_; lean_object* v___x_992_; lean_object* v_matchUsingNamespace_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_toCommandContextInfo_989_ = lean_ctor_get(v_ctx_939_, 0);
lean_inc_ref(v_toCommandContextInfo_989_);
lean_dec_ref(v_ctx_939_);
v_currNamespace_990_ = lean_ctor_get(v_toCommandContextInfo_989_, 5);
lean_inc(v_currNamespace_990_);
v_openDecls_991_ = lean_ctor_get(v_toCommandContextInfo_989_, 6);
lean_inc(v_openDecls_991_);
lean_dec_ref(v_toCommandContextInfo_989_);
v___x_992_ = lean_box(v_danglingDot_942_);
lean_inc(v_declName_940_);
lean_inc(v_id_941_);
v_matchUsingNamespace_993_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0___boxed), 13, 3);
lean_closure_set(v_matchUsingNamespace_993_, 0, v_id_941_);
lean_closure_set(v_matchUsingNamespace_993_, 1, v___x_992_);
lean_closure_set(v_matchUsingNamespace_993_, 2, v_declName_940_);
v___x_994_ = lean_box(0);
v___x_995_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces(v_matchUsingNamespace_993_, v_currNamespace_990_, v___x_994_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
if (lean_obj_tag(v_a_996_) == 0)
{
lean_dec(v_openDecls_991_);
lean_dec(v_id_941_);
lean_dec(v_declName_940_);
v___y_952_ = v___x_995_;
goto v___jp_951_;
}
else
{
lean_object* v_a_997_; lean_object* v_snd_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_inc_ref(v_a_996_);
lean_dec_ref_known(v___x_995_, 1);
v_a_997_ = lean_ctor_get(v_a_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v_a_996_, 1);
v_snd_998_ = lean_ctor_get(v_a_997_, 1);
lean_inc(v_snd_998_);
lean_dec(v_a_997_);
v___x_999_ = lean_box(0);
lean_inc(v_declName_940_);
v___x_1000_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg(v_declName_940_, v_id_941_, v_danglingDot_942_, v_openDecls_991_, v_openDecls_991_, v___x_999_, v_snd_998_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_openDecls_991_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v_a_1002_; lean_object* v_snd_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v_a_1002_ = lean_ctor_get(v_a_1001_, 0);
lean_inc(v_a_1002_);
lean_dec(v_a_1001_);
v_snd_1003_ = lean_ctor_get(v_a_1002_, 1);
lean_inc(v_snd_1003_);
lean_dec(v_a_1002_);
v___x_1004_ = lean_box(0);
v___x_1005_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0(v_id_941_, v_danglingDot_942_, v_declName_940_, v___x_1004_, v_snd_1003_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_id_941_);
v___y_952_ = v___x_1005_;
goto v___jp_951_;
}
else
{
lean_dec(v_id_941_);
lean_dec(v_declName_940_);
v___y_952_ = v___x_1000_;
goto v___jp_951_;
}
}
}
else
{
lean_dec(v_openDecls_991_);
lean_dec(v_id_941_);
lean_dec(v_declName_940_);
v___y_952_ = v___x_995_;
goto v___jp_951_;
}
v___jp_951_:
{
if (lean_obj_tag(v___y_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_980_; 
v_a_953_ = lean_ctor_get(v___y_952_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___y_952_);
if (v_isSharedCheck_980_ == 0)
{
v___x_955_ = v___y_952_;
v_isShared_956_ = v_isSharedCheck_980_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___y_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_980_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
if (lean_obj_tag(v_a_953_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_967_; 
v_a_957_ = lean_ctor_get(v_a_953_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v_a_953_);
if (v_isSharedCheck_967_ == 0)
{
v___x_959_ = v_a_953_;
v_isShared_960_ = v_isSharedCheck_967_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v_a_953_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_967_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_966_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_964_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_962_);
v___x_964_ = v___x_955_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
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
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_979_; 
v_a_968_ = lean_ctor_get(v_a_953_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v_a_953_);
if (v_isSharedCheck_979_ == 0)
{
v___x_970_ = v_a_953_;
v_isShared_971_ = v_isSharedCheck_979_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v_a_953_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_979_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v_snd_972_; lean_object* v___x_974_; 
v_snd_972_ = lean_ctor_get(v_a_968_, 1);
lean_inc(v_snd_972_);
lean_dec(v_a_968_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v_snd_972_);
v___x_974_ = v___x_970_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_snd_972_);
v___x_974_ = v_reuseFailAlloc_978_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_976_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_974_);
v___x_976_ = v___x_955_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
v_a_981_ = lean_ctor_get(v___y_952_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___y_952_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___y_952_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___y_952_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_939_ = stack[0].m_obj;
lean_object* v_declName_940_ = stack[1].m_obj;
lean_object* v_id_941_ = stack[2].m_obj;
uint8_t v_danglingDot_942_ = stack[3].m_num;
lean_object* v_a_943_ = stack[4].m_obj;
lean_object* v_a_944_ = stack[5].m_obj;
lean_object* v_a_945_ = stack[6].m_obj;
lean_object* v_a_946_ = stack[7].m_obj;
lean_object* v_a_947_ = stack[8].m_obj;
lean_object* v_a_948_ = stack[9].m_obj;
lean_object* v_a_949_ = stack[10].m_obj;
lean_object* v_res_1006_;
v_res_1006_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(v_ctx_939_, v_declName_940_, v_id_941_, v_danglingDot_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
stack->m_obj
 = v_res_1006_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___boxed(lean_object* v_ctx_1007_, lean_object* v_declName_1008_, lean_object* v_id_1009_, lean_object* v_danglingDot_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
uint8_t v_danglingDot_boxed_1019_; lean_object* v_res_1020_; 
v_danglingDot_boxed_1019_ = lean_unbox(v_danglingDot_1010_);
v_res_1020_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(v_ctx_1007_, v_declName_1008_, v_id_1009_, v_danglingDot_boxed_1019_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
return v_res_1020_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1(lean_object* v_declName_1021_, lean_object* v_id_1022_, uint8_t v_danglingDot_1023_, lean_object* v_as_1024_, lean_object* v_as_x27_1025_, lean_object* v_b_1026_, lean_object* v_a_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg(v_declName_1021_, v_id_1022_, v_danglingDot_1023_, v_as_1024_, v_as_x27_1025_, v_b_1026_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
return v___x_1037_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1021_ = stack[0].m_obj;
lean_object* v_id_1022_ = stack[1].m_obj;
uint8_t v_danglingDot_1023_ = stack[2].m_num;
lean_object* v_as_1024_ = stack[3].m_obj;
lean_object* v_as_x27_1025_ = stack[4].m_obj;
lean_object* v_b_1026_ = stack[5].m_obj;
lean_object* v___y_1028_ = stack[7].m_obj;
lean_object* v___y_1029_ = stack[8].m_obj;
lean_object* v___y_1030_ = stack[9].m_obj;
lean_object* v___y_1031_ = stack[10].m_obj;
lean_object* v___y_1032_ = stack[11].m_obj;
lean_object* v___y_1033_ = stack[12].m_obj;
lean_object* v___y_1034_ = stack[13].m_obj;
lean_object* v___y_1035_ = stack[14].m_obj;
lean_object* v_res_1038_;
v_res_1038_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1(v_declName_1021_, v_id_1022_, v_danglingDot_1023_, v_as_1024_, v_as_x27_1025_, v_b_1026_, lean_box(0), v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
stack->m_obj
 = v_res_1038_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___boxed(lean_object* v_declName_1039_, lean_object* v_id_1040_, lean_object* v_danglingDot_1041_, lean_object* v_as_1042_, lean_object* v_as_x27_1043_, lean_object* v_b_1044_, lean_object* v_a_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
uint8_t v_danglingDot_boxed_1055_; lean_object* v_res_1056_; 
v_danglingDot_boxed_1055_ = lean_unbox(v_danglingDot_1041_);
v_res_1056_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1(v_declName_1039_, v_id_1040_, v_danglingDot_boxed_1055_, v_as_1042_, v_as_x27_1043_, v_b_1044_, v_a_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v_as_x27_1043_);
lean_dec(v_as_1042_);
lean_dec(v_id_1040_);
return v_res_1056_;
}
}
lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1(lean_object* v_declName_1057_, lean_object* v_id_1058_, uint8_t v_danglingDot_1059_, lean_object* v_as_1060_, lean_object* v_as_x27_1061_, lean_object* v_b_1062_, lean_object* v_a_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_1057_, v_id_1058_, v_danglingDot_1059_, v_as_x27_1061_, v_b_1062_, v___y_1064_, v___y_1071_);
return v___x_1073_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1057_ = stack[0].m_obj;
lean_object* v_id_1058_ = stack[1].m_obj;
uint8_t v_danglingDot_1059_ = stack[2].m_num;
lean_object* v_as_1060_ = stack[3].m_obj;
lean_object* v_as_x27_1061_ = stack[4].m_obj;
lean_object* v_b_1062_ = stack[5].m_obj;
lean_object* v___y_1064_ = stack[7].m_obj;
lean_object* v___y_1065_ = stack[8].m_obj;
lean_object* v___y_1066_ = stack[9].m_obj;
lean_object* v___y_1067_ = stack[10].m_obj;
lean_object* v___y_1068_ = stack[11].m_obj;
lean_object* v___y_1069_ = stack[12].m_obj;
lean_object* v___y_1070_ = stack[13].m_obj;
lean_object* v___y_1071_ = stack[14].m_obj;
lean_object* v_res_1074_;
v_res_1074_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1(v_declName_1057_, v_id_1058_, v_danglingDot_1059_, v_as_1060_, v_as_x27_1061_, v_b_1062_, lean_box(0), v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
stack->m_obj
 = v_res_1074_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___boxed(lean_object* v_declName_1075_, lean_object* v_id_1076_, lean_object* v_danglingDot_1077_, lean_object* v_as_1078_, lean_object* v_as_x27_1079_, lean_object* v_b_1080_, lean_object* v_a_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
uint8_t v_danglingDot_boxed_1091_; lean_object* v_res_1092_; 
v_danglingDot_boxed_1091_ = lean_unbox(v_danglingDot_1077_);
v_res_1092_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1(v_declName_1075_, v_id_1076_, v_danglingDot_boxed_1091_, v_as_1078_, v_as_x27_1079_, v_b_1080_, v_a_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v_as_x27_1079_);
lean_dec(v_as_1078_);
lean_dec(v_id_1076_);
return v_res_1092_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(lean_object* v_ctx_1093_, lean_object* v_id_1094_, uint8_t v_danglingDot_1095_, lean_object* v___x_1096_, lean_object* v_a_1097_, lean_object* v_b_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_it_1108_; lean_object* v_a_1112_; lean_object* v___x_1115_; lean_object* v___y_1117_; lean_object* v___y_1118_; uint8_t v___y_1119_; lean_object* v_it_1140_; lean_object* v_fst_1141_; lean_object* v_it_1146_; lean_object* v_fst_1147_; 
v___x_1115_ = lean_box(0);
if (lean_obj_tag(v_a_1097_) == 0)
{
lean_object* v_a_1149_; lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1217_; 
v_a_1149_ = lean_ctor_get(v_a_1097_, 0);
v_a_1150_ = lean_ctor_get(v_a_1097_, 1);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_a_1097_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1152_ = v_a_1097_;
v_isShared_1153_ = v_isSharedCheck_1217_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_inc(v_a_1149_);
lean_dec(v_a_1097_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1217_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v_it_1155_; lean_object* v_it_u2082_1160_; 
v_it_u2082_1160_ = lean_ctor_get(v_a_1149_, 1);
lean_inc(v_it_u2082_1160_);
if (lean_obj_tag(v_it_u2082_1160_) == 0)
{
lean_object* v_it_u2081_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1185_; 
v_it_u2081_1161_ = lean_ctor_get(v_a_1149_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_a_1149_);
if (v_isSharedCheck_1185_ == 0)
{
lean_object* v_unused_1186_; 
v_unused_1186_ = lean_ctor_get(v_a_1149_, 1);
lean_dec(v_unused_1186_);
v___x_1163_ = v_a_1149_;
v_isShared_1164_ = v_isSharedCheck_1185_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_it_u2081_1161_);
lean_dec(v_a_1149_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1185_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v_array_1165_; lean_object* v_pos_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1184_; 
v_array_1165_ = lean_ctor_get(v_it_u2081_1161_, 0);
v_pos_1166_ = lean_ctor_get(v_it_u2081_1161_, 1);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_it_u2081_1161_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1168_ = v_it_u2081_1161_;
v_isShared_1169_ = v_isSharedCheck_1184_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_pos_1166_);
lean_inc(v_array_1165_);
lean_dec(v_it_u2081_1161_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1184_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = lean_array_get_size(v_array_1165_);
v___x_1171_ = lean_nat_dec_lt(v_pos_1166_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; 
lean_del_object(v___x_1168_);
lean_dec(v_pos_1166_);
lean_dec_ref(v_array_1165_);
lean_del_object(v___x_1163_);
lean_del_object(v___x_1152_);
v___x_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1172_, 0, v_a_1150_);
v_a_1097_ = v___x_1172_;
goto _start;
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1174_ = lean_unsigned_to_nat(1u);
v___x_1175_ = lean_nat_add(v_pos_1166_, v___x_1174_);
lean_inc_ref(v_array_1165_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v___x_1175_);
v___x_1177_ = v___x_1168_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_array_1165_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1178_ = lean_array_fget(v_array_1165_, v_pos_1166_);
lean_dec(v_pos_1166_);
lean_dec_ref(v_array_1165_);
v___x_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v___x_1179_);
lean_ctor_set(v___x_1163_, 0, v___x_1177_);
v___x_1181_ = v___x_1163_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
v_it_1155_ = v___x_1181_;
goto v___jp_1154_;
}
}
}
}
}
}
else
{
lean_object* v_val_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1216_; 
v_val_1187_ = lean_ctor_get(v_it_u2082_1160_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_it_u2082_1160_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1189_ = v_it_u2082_1160_;
v_isShared_1190_ = v_isSharedCheck_1216_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_val_1187_);
lean_dec(v_it_u2082_1160_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1216_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
if (lean_obj_tag(v_val_1187_) == 0)
{
lean_object* v_it_u2081_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1199_; 
lean_del_object(v___x_1189_);
v_it_u2081_1191_ = lean_ctor_get(v_a_1149_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_a_1149_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; 
v_unused_1200_ = lean_ctor_get(v_a_1149_, 1);
lean_dec(v_unused_1200_);
v___x_1193_ = v_a_1149_;
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_it_u2081_1191_);
lean_dec(v_a_1149_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1195_ = lean_box(0);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v___x_1195_);
v___x_1197_ = v___x_1193_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_it_u2081_1191_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
v_it_1155_ = v___x_1197_;
goto v___jp_1154_;
}
}
}
else
{
lean_object* v_it_u2081_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1214_; 
lean_del_object(v___x_1152_);
v_it_u2081_1201_ = lean_ctor_get(v_a_1149_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_a_1149_);
if (v_isSharedCheck_1214_ == 0)
{
lean_object* v_unused_1215_; 
v_unused_1215_ = lean_ctor_get(v_a_1149_, 1);
lean_dec(v_unused_1215_);
v___x_1203_ = v_a_1149_;
v_isShared_1204_ = v_isSharedCheck_1214_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_it_u2081_1201_);
lean_dec(v_a_1149_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1214_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_key_1205_; lean_object* v_tail_1206_; lean_object* v___x_1208_; 
v_key_1205_ = lean_ctor_get(v_val_1187_, 0);
lean_inc(v_key_1205_);
v_tail_1206_ = lean_ctor_get(v_val_1187_, 2);
lean_inc(v_tail_1206_);
lean_dec_ref_known(v_val_1187_, 3);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v_tail_1206_);
v___x_1208_ = v___x_1189_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_tail_1206_);
v___x_1208_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1210_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 1, v___x_1208_);
v___x_1210_ = v___x_1203_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_it_u2081_1201_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v_a_1150_);
v_it_1140_ = v___x_1211_;
v_fst_1141_ = v_key_1205_;
goto v___jp_1139_;
}
}
}
}
}
}
v___jp_1154_:
{
lean_object* v___x_1157_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v_it_1155_);
v___x_1157_ = v___x_1152_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_it_1155_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_a_1150_);
v___x_1157_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
v_a_1097_ = v___x_1157_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1218_; 
v_a_1218_ = lean_ctor_get(v_a_1097_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v_a_1097_, 1);
switch(lean_obj_tag(v_a_1218_))
{
case 0:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_dec_ref(v___x_1096_);
lean_dec(v_id_1094_);
lean_dec_ref(v_ctx_1093_);
v___x_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1219_, 0, v_b_1098_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
case 1:
{
lean_object* v_a_1221_; lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1240_; 
v_a_1221_ = lean_ctor_get(v_a_1218_, 0);
v_a_1222_ = lean_ctor_get(v_a_1218_, 1);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_a_1218_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1224_ = v_a_1218_;
v_isShared_1225_ = v_isSharedCheck_1240_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_inc(v_a_1221_);
lean_dec(v_a_1218_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1240_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v_start_1226_; lean_object* v_stop_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v_start_1226_ = lean_ctor_get(v_a_1221_, 1);
v_stop_1227_ = lean_ctor_get(v_a_1221_, 2);
v___x_1228_ = lean_unsigned_to_nat(0u);
v___x_1229_ = lean_nat_sub(v_stop_1227_, v_start_1226_);
v___x_1230_ = lean_nat_dec_lt(v___x_1228_, v___x_1229_);
lean_dec(v___x_1229_);
if (v___x_1230_ == 0)
{
lean_del_object(v___x_1224_);
lean_dec_ref(v_a_1221_);
v_it_1108_ = v_a_1222_;
goto v___jp_1107_;
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v_z_1234_; 
v___x_1231_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_a_1221_);
v___x_1232_ = l_Subarray_drop___redArg(v_a_1221_, v___x_1231_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1232_);
v_z_1234_ = v___x_1224_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_a_1222_);
v_z_1234_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Subarray_get___redArg(v_a_1221_, v___x_1228_);
lean_dec_ref(v_a_1221_);
switch(lean_obj_tag(v___x_1235_))
{
case 0:
{
lean_object* v_key_1236_; 
v_key_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_key_1236_);
lean_dec_ref_known(v___x_1235_, 2);
v_it_1146_ = v_z_1234_;
v_fst_1147_ = v_key_1236_;
goto v___jp_1145_;
}
case 1:
{
lean_object* v_node_1237_; lean_object* v___x_1238_; 
v_node_1237_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_node_1237_);
lean_dec_ref_known(v___x_1235_, 1);
v___x_1238_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_1237_, v_z_1234_);
v_it_1108_ = v___x_1238_;
goto v___jp_1107_;
}
default: 
{
v_it_1108_ = v_z_1234_;
goto v___jp_1107_;
}
}
}
}
}
}
default: 
{
lean_object* v_vals_1241_; lean_object* v_keys_1242_; lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1259_; 
v_vals_1241_ = lean_ctor_get(v_a_1218_, 1);
v_keys_1242_ = lean_ctor_get(v_a_1218_, 0);
v_a_1243_ = lean_ctor_get(v_a_1218_, 2);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_a_1218_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1245_ = v_a_1218_;
v_isShared_1246_ = v_isSharedCheck_1259_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_inc(v_vals_1241_);
lean_inc(v_keys_1242_);
lean_dec(v_a_1218_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1259_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v_start_1247_; lean_object* v_stop_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_start_1247_ = lean_ctor_get(v_vals_1241_, 1);
v_stop_1248_ = lean_ctor_get(v_vals_1241_, 2);
v___x_1249_ = lean_unsigned_to_nat(0u);
v___x_1250_ = lean_nat_sub(v_stop_1248_, v_start_1247_);
v___x_1251_ = lean_nat_dec_lt(v___x_1249_, v___x_1250_);
lean_dec(v___x_1250_);
if (v___x_1251_ == 0)
{
lean_del_object(v___x_1245_);
lean_dec_ref(v_keys_1242_);
lean_dec_ref(v_vals_1241_);
v_it_1108_ = v_a_1243_;
goto v___jp_1107_;
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1252_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_keys_1242_);
v___x_1253_ = l_Subarray_drop___redArg(v_keys_1242_, v___x_1252_);
v___x_1254_ = l_Subarray_drop___redArg(v_vals_1241_, v___x_1252_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v___x_1254_);
lean_ctor_set(v___x_1245_, 0, v___x_1253_);
v___x_1256_ = v___x_1245_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v_a_1243_);
v___x_1256_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Subarray_get___redArg(v_keys_1242_, v___x_1249_);
lean_dec_ref(v_keys_1242_);
v_it_1146_ = v___x_1256_;
v_fst_1147_ = v___x_1257_;
goto v___jp_1145_;
}
}
}
}
}
}
v___jp_1107_:
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1109_, 0, v_it_1108_);
v_a_1097_ = v___x_1109_;
goto _start;
}
v___jp_1111_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v_a_1112_);
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
return v___x_1114_;
}
v___jp_1116_:
{
if (v___y_1119_ == 0)
{
lean_object* v___x_1120_; 
lean_inc(v_id_1094_);
lean_inc_ref(v_ctx_1093_);
v___x_1120_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(v_ctx_1093_, v___y_1117_, v_id_1094_, v_danglingDot_1095_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
lean_dec_ref_known(v___x_1120_, 1);
if (lean_obj_tag(v_a_1121_) == 0)
{
lean_object* v_a_1122_; 
lean_dec_ref(v___y_1118_);
lean_dec_ref(v___x_1096_);
lean_dec(v_id_1094_);
lean_dec_ref(v_ctx_1093_);
v_a_1122_ = lean_ctor_get(v_a_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v_a_1121_, 1);
v_a_1112_ = v_a_1122_;
goto v___jp_1111_;
}
else
{
lean_object* v_a_1123_; 
v_a_1123_ = lean_ctor_get(v_a_1121_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v_a_1121_, 1);
if (lean_obj_tag(v_a_1123_) == 1)
{
lean_object* v_val_1124_; lean_object* v___x_1125_; 
v_val_1124_ = lean_ctor_get(v_a_1123_, 0);
lean_inc(v_val_1124_);
lean_dec_ref_known(v_a_1123_, 1);
v___x_1125_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg(v_val_1124_, v___y_1099_, v___y_1100_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
lean_dec_ref_known(v___x_1125_, 1);
if (lean_obj_tag(v_a_1126_) == 0)
{
lean_object* v_a_1127_; 
lean_dec_ref(v___y_1118_);
lean_dec_ref(v___x_1096_);
lean_dec(v_id_1094_);
lean_dec_ref(v_ctx_1093_);
v_a_1127_ = lean_ctor_get(v_a_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref_known(v_a_1126_, 1);
v_a_1112_ = v_a_1127_;
goto v___jp_1111_;
}
else
{
lean_dec_ref_known(v_a_1126_, 1);
v_a_1097_ = v___y_1118_;
v_b_1098_ = v___x_1115_;
goto _start;
}
}
else
{
lean_dec_ref(v___y_1118_);
lean_dec_ref(v___x_1096_);
lean_dec(v_id_1094_);
lean_dec_ref(v_ctx_1093_);
return v___x_1125_;
}
}
else
{
lean_dec(v_a_1123_);
v_a_1097_ = v___y_1118_;
v_b_1098_ = v___x_1115_;
goto _start;
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec_ref(v___y_1118_);
lean_dec_ref(v___x_1096_);
lean_dec(v_id_1094_);
lean_dec_ref(v_ctx_1093_);
v_a_1130_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1120_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1120_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
else
{
lean_dec(v___y_1117_);
v_a_1097_ = v___y_1118_;
v_b_1098_ = v___x_1115_;
goto _start;
}
}
v___jp_1139_:
{
uint8_t v___x_1142_; 
v___x_1142_ = l_Lean_Name_isInternal(v_fst_1141_);
if (v___x_1142_ == 0)
{
uint8_t v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = 1;
lean_inc(v_fst_1141_);
lean_inc_ref(v___x_1096_);
v___x_1144_ = l_Lean_Environment_contains(v___x_1096_, v_fst_1141_, v___x_1143_);
v___y_1117_ = v_fst_1141_;
v___y_1118_ = v_it_1140_;
v___y_1119_ = v___x_1144_;
goto v___jp_1116_;
}
else
{
v___y_1117_ = v_fst_1141_;
v___y_1118_ = v_it_1140_;
v___y_1119_ = v___x_1142_;
goto v___jp_1116_;
}
}
v___jp_1145_:
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_it_1146_);
v_it_1140_ = v___x_1148_;
v_fst_1141_ = v_fst_1147_;
goto v___jp_1139_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1093_ = stack[0].m_obj;
lean_object* v_id_1094_ = stack[1].m_obj;
uint8_t v_danglingDot_1095_ = stack[2].m_num;
lean_object* v___x_1096_ = stack[3].m_obj;
lean_object* v_a_1097_ = stack[4].m_obj;
lean_object* v_b_1098_ = stack[5].m_obj;
lean_object* v___y_1099_ = stack[6].m_obj;
lean_object* v___y_1100_ = stack[7].m_obj;
lean_object* v___y_1101_ = stack[8].m_obj;
lean_object* v___y_1102_ = stack[9].m_obj;
lean_object* v___y_1103_ = stack[10].m_obj;
lean_object* v___y_1104_ = stack[11].m_obj;
lean_object* v___y_1105_ = stack[12].m_obj;
lean_object* v_res_1260_;
v_res_1260_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v_ctx_1093_, v_id_1094_, v_danglingDot_1095_, v___x_1096_, v_a_1097_, v_b_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
stack->m_obj
 = v_res_1260_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg___boxed(lean_object* v_ctx_1261_, lean_object* v_id_1262_, lean_object* v_danglingDot_1263_, lean_object* v___x_1264_, lean_object* v_a_1265_, lean_object* v_b_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
uint8_t v_danglingDot_boxed_1275_; lean_object* v_res_1276_; 
v_danglingDot_boxed_1275_ = lean_unbox(v_danglingDot_1263_);
v_res_1276_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v_ctx_1261_, v_id_1262_, v_danglingDot_boxed_1275_, v___x_1264_, v_a_1265_, v_b_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
return v_res_1276_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(lean_object* v_ctx_1277_, lean_object* v_id_1278_, uint8_t v_danglingDot_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v___x_1288_; lean_object* v_env_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1288_ = lean_st_ref_get(v_a_1286_);
v_env_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc_ref_n(v_env_1289_, 2);
lean_dec(v___x_1288_);
v___x_1290_ = l_Lean_Environment_getNamespaces(v_env_1289_);
v___x_1291_ = lean_box(0);
v___x_1292_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v_ctx_1277_, v_id_1278_, v_danglingDot_1279_, v_env_1289_, v___x_1290_, v___x_1291_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
if (lean_obj_tag(v_a_1293_) == 0)
{
return v___x_1292_;
}
else
{
lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1301_; 
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1301_ == 0)
{
lean_object* v_unused_1302_; 
v_unused_1302_ = lean_ctor_get(v___x_1292_, 0);
lean_dec(v_unused_1302_);
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1301_;
goto v_resetjp_1294_;
}
else
{
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1301_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1297_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1297_);
v___x_1299_ = v___x_1295_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
else
{
return v___x_1292_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1277_ = stack[0].m_obj;
lean_object* v_id_1278_ = stack[1].m_obj;
uint8_t v_danglingDot_1279_ = stack[2].m_num;
lean_object* v_a_1280_ = stack[3].m_obj;
lean_object* v_a_1281_ = stack[4].m_obj;
lean_object* v_a_1282_ = stack[5].m_obj;
lean_object* v_a_1283_ = stack[6].m_obj;
lean_object* v_a_1284_ = stack[7].m_obj;
lean_object* v_a_1285_ = stack[8].m_obj;
lean_object* v_a_1286_ = stack[9].m_obj;
lean_object* v_res_1303_;
v_res_1303_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_1277_, v_id_1278_, v_danglingDot_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
stack->m_obj
 = v_res_1303_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces___boxed(lean_object* v_ctx_1304_, lean_object* v_id_1305_, lean_object* v_danglingDot_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
uint8_t v_danglingDot_boxed_1315_; lean_object* v_res_1316_; 
v_danglingDot_boxed_1315_ = lean_unbox(v_danglingDot_1306_);
v_res_1316_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_1304_, v_id_1305_, v_danglingDot_boxed_1315_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
return v_res_1316_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0(lean_object* v_ctx_1317_, lean_object* v_id_1318_, uint8_t v_danglingDot_1319_, lean_object* v___x_1320_, lean_object* v_inst_1321_, lean_object* v_R_1322_, lean_object* v_a_1323_, lean_object* v_b_1324_, lean_object* v_c_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v_ctx_1317_, v_id_1318_, v_danglingDot_1319_, v___x_1320_, v_a_1323_, v_b_1324_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
return v___x_1334_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1317_ = stack[0].m_obj;
lean_object* v_id_1318_ = stack[1].m_obj;
uint8_t v_danglingDot_1319_ = stack[2].m_num;
lean_object* v___x_1320_ = stack[3].m_obj;
lean_object* v_a_1323_ = stack[6].m_obj;
lean_object* v_b_1324_ = stack[7].m_obj;
lean_object* v___y_1326_ = stack[9].m_obj;
lean_object* v___y_1327_ = stack[10].m_obj;
lean_object* v___y_1328_ = stack[11].m_obj;
lean_object* v___y_1329_ = stack[12].m_obj;
lean_object* v___y_1330_ = stack[13].m_obj;
lean_object* v___y_1331_ = stack[14].m_obj;
lean_object* v___y_1332_ = stack[15].m_obj;
lean_object* v_res_1335_;
v_res_1335_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0(v_ctx_1317_, v_id_1318_, v_danglingDot_1319_, v___x_1320_, lean_box(0), lean_box(0), v_a_1323_, v_b_1324_, lean_box(0), v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
stack->m_obj
 = v_res_1335_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___boxed(lean_object** _args){
lean_object* v_ctx_1336_ = _args[0];
lean_object* v_id_1337_ = _args[1];
lean_object* v_danglingDot_1338_ = _args[2];
lean_object* v___x_1339_ = _args[3];
lean_object* v_inst_1340_ = _args[4];
lean_object* v_R_1341_ = _args[5];
lean_object* v_a_1342_ = _args[6];
lean_object* v_b_1343_ = _args[7];
lean_object* v_c_1344_ = _args[8];
lean_object* v___y_1345_ = _args[9];
lean_object* v___y_1346_ = _args[10];
lean_object* v___y_1347_ = _args[11];
lean_object* v___y_1348_ = _args[12];
lean_object* v___y_1349_ = _args[13];
lean_object* v___y_1350_ = _args[14];
lean_object* v___y_1351_ = _args[15];
lean_object* v___y_1352_ = _args[16];
_start:
{
uint8_t v_danglingDot_boxed_1353_; lean_object* v_res_1354_; 
v_danglingDot_boxed_1353_ = lean_unbox(v_danglingDot_1338_);
v_res_1354_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0(v_ctx_1336_, v_id_1337_, v_danglingDot_boxed_1353_, v___x_1339_, v_inst_1340_, v_R_1341_, v_a_1342_, v_b_1343_, v_c_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(lean_object* v_n_1355_){
_start:
{
if (lean_obj_tag(v_n_1355_) == 2)
{
lean_object* v_i_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v_i_1356_ = lean_ctor_get(v_n_1355_, 1);
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = lean_nat_dec_eq(v_i_1356_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_inc_ref(v_n_1355_);
return v_n_1355_;
}
else
{
uint8_t v___x_1359_; 
v___x_1359_ = l_Lean_isPrivatePrefix(v_n_1355_);
if (v___x_1359_ == 0)
{
lean_inc_ref(v_n_1355_);
return v_n_1355_;
}
else
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_box(0);
return v___x_1360_;
}
}
}
else
{
lean_inc(v_n_1355_);
return v_n_1355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix___boxed(lean_object* v_n_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(v_n_1361_);
lean_dec(v_n_1361_);
return v_res_1362_;
}
}
uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(lean_object* v_n_u2081_1363_, lean_object* v_n_u2082_1364_){
_start:
{
lean_object* v_n_u2081_1365_; lean_object* v_n_u2082_1366_; 
v_n_u2081_1365_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(v_n_u2081_1363_);
lean_dec(v_n_u2081_1363_);
v_n_u2082_1366_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(v_n_u2082_1364_);
lean_dec(v_n_u2082_1364_);
switch(lean_obj_tag(v_n_u2081_1365_))
{
case 0:
{
if (lean_obj_tag(v_n_u2082_1366_) == 0)
{
uint8_t v___x_1367_; 
v___x_1367_ = 1;
return v___x_1367_;
}
else
{
uint8_t v___x_1368_; 
lean_dec(v_n_u2082_1366_);
v___x_1368_ = 0;
return v___x_1368_;
}
}
case 1:
{
if (lean_obj_tag(v_n_u2082_1366_) == 1)
{
lean_object* v_pre_1369_; lean_object* v_str_1370_; lean_object* v_pre_1371_; lean_object* v_str_1372_; uint8_t v___x_1373_; 
v_pre_1369_ = lean_ctor_get(v_n_u2081_1365_, 0);
lean_inc(v_pre_1369_);
v_str_1370_ = lean_ctor_get(v_n_u2081_1365_, 1);
lean_inc_ref(v_str_1370_);
lean_dec_ref_known(v_n_u2081_1365_, 2);
v_pre_1371_ = lean_ctor_get(v_n_u2082_1366_, 0);
lean_inc(v_pre_1371_);
v_str_1372_ = lean_ctor_get(v_n_u2082_1366_, 1);
lean_inc_ref(v_str_1372_);
lean_dec_ref_known(v_n_u2082_1366_, 2);
v___x_1373_ = lean_string_compare(v_str_1370_, v_str_1372_);
lean_dec_ref(v_str_1372_);
lean_dec_ref(v_str_1370_);
if (v___x_1373_ == 1)
{
v_n_u2081_1363_ = v_pre_1369_;
v_n_u2082_1364_ = v_pre_1371_;
goto _start;
}
else
{
lean_dec(v_pre_1371_);
lean_dec(v_pre_1369_);
return v___x_1373_;
}
}
else
{
uint8_t v___x_1375_; 
lean_dec_ref_known(v_n_u2081_1365_, 2);
lean_dec(v_n_u2082_1366_);
v___x_1375_ = 2;
return v___x_1375_;
}
}
default: 
{
switch(lean_obj_tag(v_n_u2082_1366_))
{
case 0:
{
uint8_t v___x_1376_; 
lean_dec_ref_known(v_n_u2081_1365_, 2);
v___x_1376_ = 2;
return v___x_1376_;
}
case 1:
{
uint8_t v___x_1377_; 
lean_dec_ref_known(v_n_u2082_1366_, 2);
lean_dec_ref_known(v_n_u2081_1365_, 2);
v___x_1377_ = 0;
return v___x_1377_;
}
default: 
{
lean_object* v_pre_1378_; lean_object* v_i_1379_; lean_object* v_pre_1380_; lean_object* v_i_1381_; uint8_t v___x_1382_; 
v_pre_1378_ = lean_ctor_get(v_n_u2081_1365_, 0);
lean_inc(v_pre_1378_);
v_i_1379_ = lean_ctor_get(v_n_u2081_1365_, 1);
lean_inc(v_i_1379_);
lean_dec_ref_known(v_n_u2081_1365_, 2);
v_pre_1380_ = lean_ctor_get(v_n_u2082_1366_, 0);
lean_inc(v_pre_1380_);
v_i_1381_ = lean_ctor_get(v_n_u2082_1366_, 1);
lean_inc(v_i_1381_);
lean_dec_ref_known(v_n_u2082_1366_, 2);
v___x_1382_ = lean_nat_dec_lt(v_i_1379_, v_i_1381_);
if (v___x_1382_ == 0)
{
uint8_t v___x_1383_; 
v___x_1383_ = lean_nat_dec_eq(v_i_1379_, v_i_1381_);
lean_dec(v_i_1381_);
lean_dec(v_i_1379_);
if (v___x_1383_ == 0)
{
uint8_t v___x_1384_; 
lean_dec(v_pre_1380_);
lean_dec(v_pre_1378_);
v___x_1384_ = 2;
return v___x_1384_;
}
else
{
v_n_u2081_1363_ = v_pre_1378_;
v_n_u2082_1364_ = v_pre_1380_;
goto _start;
}
}
else
{
uint8_t v___x_1386_; 
lean_dec(v_i_1381_);
lean_dec(v_pre_1380_);
lean_dec(v_i_1379_);
lean_dec(v_pre_1378_);
v___x_1386_ = 0;
return v___x_1386_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_u2081_1363_ = stack[0].m_obj;
lean_object* v_n_u2082_1364_ = stack[1].m_obj;
uint8_t v_res_1387_;
v_res_1387_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_n_u2081_1363_, v_n_u2082_1364_);
stack->m_num = v_res_1387_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate___boxed(lean_object* v_n_u2081_1388_, lean_object* v_n_u2082_1389_){
_start:
{
uint8_t v_res_1390_; lean_object* v_r_1391_; 
v_res_1390_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_n_u2081_1388_, v_n_u2082_1389_);
v_r_1391_ = lean_box(v_res_1390_);
return v_r_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(lean_object* v_names_1393_){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray___closed__0));
v___x_1395_ = l_Std_TreeSet_ofArray___redArg(v_names_1393_, v___x_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray___boxed(lean_object* v_names_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(v_names_1396_);
lean_dec_ref(v_names_1396_);
return v_res_1397_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(lean_object* v_k_1398_, lean_object* v_t_1399_){
_start:
{
if (lean_obj_tag(v_t_1399_) == 0)
{
lean_object* v_k_1400_; lean_object* v_l_1401_; lean_object* v_r_1402_; uint8_t v___x_1403_; 
v_k_1400_ = lean_ctor_get(v_t_1399_, 1);
lean_inc(v_k_1400_);
v_l_1401_ = lean_ctor_get(v_t_1399_, 3);
lean_inc(v_l_1401_);
v_r_1402_ = lean_ctor_get(v_t_1399_, 4);
lean_inc(v_r_1402_);
lean_dec_ref_known(v_t_1399_, 5);
lean_inc(v_k_1398_);
v___x_1403_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_k_1398_, v_k_1400_);
switch(v___x_1403_)
{
case 0:
{
lean_dec(v_r_1402_);
v_t_1399_ = v_l_1401_;
goto _start;
}
case 1:
{
uint8_t v___x_1405_; 
lean_dec(v_r_1402_);
lean_dec(v_l_1401_);
lean_dec(v_k_1398_);
v___x_1405_ = 1;
return v___x_1405_;
}
default: 
{
lean_dec(v_l_1401_);
v_t_1399_ = v_r_1402_;
goto _start;
}
}
}
else
{
uint8_t v___x_1407_; 
lean_dec(v_k_1398_);
v___x_1407_ = 0;
return v___x_1407_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1398_ = stack[0].m_obj;
lean_object* v_t_1399_ = stack[1].m_obj;
uint8_t v_res_1408_;
v_res_1408_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_k_1398_, v_t_1399_);
stack->m_num = v_res_1408_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg___boxed(lean_object* v_k_1409_, lean_object* v_t_1410_){
_start:
{
uint8_t v_res_1411_; lean_object* v_r_1412_; 
v_res_1411_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_k_1409_, v_t_1410_);
v_r_1412_ = lean_box(v_res_1411_);
return v_r_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(lean_object* v_k_1413_, lean_object* v_v_1414_, lean_object* v_t_1415_){
_start:
{
if (lean_obj_tag(v_t_1415_) == 0)
{
lean_object* v_size_1416_; lean_object* v_k_1417_; lean_object* v_v_1418_; lean_object* v_l_1419_; lean_object* v_r_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1700_; 
v_size_1416_ = lean_ctor_get(v_t_1415_, 0);
v_k_1417_ = lean_ctor_get(v_t_1415_, 1);
v_v_1418_ = lean_ctor_get(v_t_1415_, 2);
v_l_1419_ = lean_ctor_get(v_t_1415_, 3);
v_r_1420_ = lean_ctor_get(v_t_1415_, 4);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_t_1415_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1422_ = v_t_1415_;
v_isShared_1423_ = v_isSharedCheck_1700_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_r_1420_);
lean_inc(v_l_1419_);
lean_inc(v_v_1418_);
lean_inc(v_k_1417_);
lean_inc(v_size_1416_);
lean_dec(v_t_1415_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1700_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
uint8_t v___x_1424_; 
lean_inc(v_k_1417_);
lean_inc(v_k_1413_);
v___x_1424_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_k_1413_, v_k_1417_);
switch(v___x_1424_)
{
case 0:
{
lean_object* v_impl_1425_; lean_object* v___x_1426_; 
lean_dec(v_size_1416_);
v_impl_1425_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1413_, v_v_1414_, v_l_1419_);
v___x_1426_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1420_) == 0)
{
lean_object* v_size_1427_; lean_object* v_size_1428_; lean_object* v_k_1429_; lean_object* v_v_1430_; lean_object* v_l_1431_; lean_object* v_r_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; uint8_t v___x_1435_; 
v_size_1427_ = lean_ctor_get(v_r_1420_, 0);
v_size_1428_ = lean_ctor_get(v_impl_1425_, 0);
v_k_1429_ = lean_ctor_get(v_impl_1425_, 1);
v_v_1430_ = lean_ctor_get(v_impl_1425_, 2);
v_l_1431_ = lean_ctor_get(v_impl_1425_, 3);
v_r_1432_ = lean_ctor_get(v_impl_1425_, 4);
lean_inc(v_r_1432_);
v___x_1433_ = lean_unsigned_to_nat(3u);
v___x_1434_ = lean_nat_mul(v___x_1433_, v_size_1427_);
v___x_1435_ = lean_nat_dec_lt(v___x_1434_, v_size_1428_);
lean_dec(v___x_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
lean_dec(v_r_1432_);
v___x_1436_ = lean_nat_add(v___x_1426_, v_size_1428_);
v___x_1437_ = lean_nat_add(v___x_1436_, v_size_1427_);
lean_dec(v___x_1436_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 3, v_impl_1425_);
lean_ctor_set(v___x_1422_, 0, v___x_1437_);
v___x_1439_ = v___x_1422_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_k_1417_);
lean_ctor_set(v_reuseFailAlloc_1440_, 2, v_v_1418_);
lean_ctor_set(v_reuseFailAlloc_1440_, 3, v_impl_1425_);
lean_ctor_set(v_reuseFailAlloc_1440_, 4, v_r_1420_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
else
{
lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1506_; 
lean_inc(v_l_1431_);
lean_inc(v_v_1430_);
lean_inc(v_k_1429_);
lean_inc(v_size_1428_);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_impl_1425_);
if (v_isSharedCheck_1506_ == 0)
{
lean_object* v_unused_1507_; lean_object* v_unused_1508_; lean_object* v_unused_1509_; lean_object* v_unused_1510_; lean_object* v_unused_1511_; 
v_unused_1507_ = lean_ctor_get(v_impl_1425_, 4);
lean_dec(v_unused_1507_);
v_unused_1508_ = lean_ctor_get(v_impl_1425_, 3);
lean_dec(v_unused_1508_);
v_unused_1509_ = lean_ctor_get(v_impl_1425_, 2);
lean_dec(v_unused_1509_);
v_unused_1510_ = lean_ctor_get(v_impl_1425_, 1);
lean_dec(v_unused_1510_);
v_unused_1511_ = lean_ctor_get(v_impl_1425_, 0);
lean_dec(v_unused_1511_);
v___x_1442_ = v_impl_1425_;
v_isShared_1443_ = v_isSharedCheck_1506_;
goto v_resetjp_1441_;
}
else
{
lean_dec(v_impl_1425_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1506_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v_size_1444_; lean_object* v_size_1445_; lean_object* v_k_1446_; lean_object* v_v_1447_; lean_object* v_l_1448_; lean_object* v_r_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v_size_1444_ = lean_ctor_get(v_l_1431_, 0);
v_size_1445_ = lean_ctor_get(v_r_1432_, 0);
v_k_1446_ = lean_ctor_get(v_r_1432_, 1);
v_v_1447_ = lean_ctor_get(v_r_1432_, 2);
v_l_1448_ = lean_ctor_get(v_r_1432_, 3);
v_r_1449_ = lean_ctor_get(v_r_1432_, 4);
v___x_1450_ = lean_unsigned_to_nat(2u);
v___x_1451_ = lean_nat_mul(v___x_1450_, v_size_1444_);
v___x_1452_ = lean_nat_dec_lt(v_size_1445_, v___x_1451_);
lean_dec(v___x_1451_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1481_; 
lean_inc(v_r_1449_);
lean_inc(v_l_1448_);
lean_inc(v_v_1447_);
lean_inc(v_k_1446_);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_r_1432_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; lean_object* v_unused_1483_; lean_object* v_unused_1484_; lean_object* v_unused_1485_; lean_object* v_unused_1486_; 
v_unused_1482_ = lean_ctor_get(v_r_1432_, 4);
lean_dec(v_unused_1482_);
v_unused_1483_ = lean_ctor_get(v_r_1432_, 3);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v_r_1432_, 2);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v_r_1432_, 1);
lean_dec(v_unused_1485_);
v_unused_1486_ = lean_ctor_get(v_r_1432_, 0);
lean_dec(v_unused_1486_);
v___x_1454_ = v_r_1432_;
v_isShared_1455_ = v_isSharedCheck_1481_;
goto v_resetjp_1453_;
}
else
{
lean_dec(v_r_1432_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1481_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___x_1469_; lean_object* v___y_1471_; 
v___x_1456_ = lean_nat_add(v___x_1426_, v_size_1428_);
lean_dec(v_size_1428_);
v___x_1457_ = lean_nat_add(v___x_1456_, v_size_1427_);
lean_dec(v___x_1456_);
v___x_1469_ = lean_nat_add(v___x_1426_, v_size_1444_);
if (lean_obj_tag(v_l_1448_) == 0)
{
lean_object* v_size_1479_; 
v_size_1479_ = lean_ctor_get(v_l_1448_, 0);
lean_inc(v_size_1479_);
v___y_1471_ = v_size_1479_;
goto v___jp_1470_;
}
else
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_unsigned_to_nat(0u);
v___y_1471_ = v___x_1480_;
goto v___jp_1470_;
}
v___jp_1458_:
{
lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1462_ = lean_nat_add(v___y_1459_, v___y_1461_);
lean_dec(v___y_1461_);
lean_dec(v___y_1459_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 4, v_r_1420_);
lean_ctor_set(v___x_1454_, 3, v_r_1449_);
lean_ctor_set(v___x_1454_, 2, v_v_1418_);
lean_ctor_set(v___x_1454_, 1, v_k_1417_);
lean_ctor_set(v___x_1454_, 0, v___x_1462_);
v___x_1464_ = v___x_1454_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_k_1417_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_v_1418_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v_r_1449_);
lean_ctor_set(v_reuseFailAlloc_1468_, 4, v_r_1420_);
v___x_1464_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1466_; 
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 4, v___x_1464_);
lean_ctor_set(v___x_1442_, 3, v___y_1460_);
lean_ctor_set(v___x_1442_, 2, v_v_1447_);
lean_ctor_set(v___x_1442_, 1, v_k_1446_);
lean_ctor_set(v___x_1442_, 0, v___x_1457_);
v___x_1466_ = v___x_1442_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_k_1446_);
lean_ctor_set(v_reuseFailAlloc_1467_, 2, v_v_1447_);
lean_ctor_set(v_reuseFailAlloc_1467_, 3, v___y_1460_);
lean_ctor_set(v_reuseFailAlloc_1467_, 4, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
v___jp_1470_:
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1472_ = lean_nat_add(v___x_1469_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec(v___x_1469_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 4, v_l_1448_);
lean_ctor_set(v___x_1422_, 3, v_l_1431_);
lean_ctor_set(v___x_1422_, 2, v_v_1430_);
lean_ctor_set(v___x_1422_, 1, v_k_1429_);
lean_ctor_set(v___x_1422_, 0, v___x_1472_);
v___x_1474_ = v___x_1422_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_k_1429_);
lean_ctor_set(v_reuseFailAlloc_1478_, 2, v_v_1430_);
lean_ctor_set(v_reuseFailAlloc_1478_, 3, v_l_1431_);
lean_ctor_set(v_reuseFailAlloc_1478_, 4, v_l_1448_);
v___x_1474_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_object* v___x_1475_; 
v___x_1475_ = lean_nat_add(v___x_1426_, v_size_1427_);
if (lean_obj_tag(v_r_1449_) == 0)
{
lean_object* v_size_1476_; 
v_size_1476_ = lean_ctor_get(v_r_1449_, 0);
lean_inc(v_size_1476_);
v___y_1459_ = v___x_1475_;
v___y_1460_ = v___x_1474_;
v___y_1461_ = v_size_1476_;
goto v___jp_1458_;
}
else
{
lean_object* v___x_1477_; 
v___x_1477_ = lean_unsigned_to_nat(0u);
v___y_1459_ = v___x_1475_;
v___y_1460_ = v___x_1474_;
v___y_1461_ = v___x_1477_;
goto v___jp_1458_;
}
}
}
}
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
lean_del_object(v___x_1422_);
v___x_1487_ = lean_nat_add(v___x_1426_, v_size_1428_);
lean_dec(v_size_1428_);
v___x_1488_ = lean_nat_add(v___x_1487_, v_size_1427_);
lean_dec(v___x_1487_);
v___x_1489_ = lean_nat_add(v___x_1426_, v_size_1427_);
v___x_1490_ = lean_nat_add(v___x_1489_, v_size_1445_);
lean_dec(v___x_1489_);
lean_inc_ref(v_r_1420_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 4, v_r_1420_);
lean_ctor_set(v___x_1442_, 3, v_r_1432_);
lean_ctor_set(v___x_1442_, 2, v_v_1418_);
lean_ctor_set(v___x_1442_, 1, v_k_1417_);
lean_ctor_set(v___x_1442_, 0, v___x_1490_);
v___x_1492_ = v___x_1442_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_k_1417_);
lean_ctor_set(v_reuseFailAlloc_1505_, 2, v_v_1418_);
lean_ctor_set(v_reuseFailAlloc_1505_, 3, v_r_1432_);
lean_ctor_set(v_reuseFailAlloc_1505_, 4, v_r_1420_);
v___x_1492_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
v_isSharedCheck_1499_ = !lean_is_exclusive(v_r_1420_);
if (v_isSharedCheck_1499_ == 0)
{
lean_object* v_unused_1500_; lean_object* v_unused_1501_; lean_object* v_unused_1502_; lean_object* v_unused_1503_; lean_object* v_unused_1504_; 
v_unused_1500_ = lean_ctor_get(v_r_1420_, 4);
lean_dec(v_unused_1500_);
v_unused_1501_ = lean_ctor_get(v_r_1420_, 3);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v_r_1420_, 2);
lean_dec(v_unused_1502_);
v_unused_1503_ = lean_ctor_get(v_r_1420_, 1);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v_r_1420_, 0);
lean_dec(v_unused_1504_);
v___x_1494_ = v_r_1420_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_dec(v_r_1420_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 4, v___x_1492_);
lean_ctor_set(v___x_1494_, 3, v_l_1431_);
lean_ctor_set(v___x_1494_, 2, v_v_1430_);
lean_ctor_set(v___x_1494_, 1, v_k_1429_);
lean_ctor_set(v___x_1494_, 0, v___x_1488_);
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_k_1429_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_v_1430_);
lean_ctor_set(v_reuseFailAlloc_1498_, 3, v_l_1431_);
lean_ctor_set(v_reuseFailAlloc_1498_, 4, v___x_1492_);
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
}
}
}
else
{
lean_object* v_l_1512_; 
v_l_1512_ = lean_ctor_get(v_impl_1425_, 3);
if (lean_obj_tag(v_l_1512_) == 0)
{
lean_object* v_r_1513_; lean_object* v_k_1514_; lean_object* v_v_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1526_; 
lean_inc_ref(v_l_1512_);
v_r_1513_ = lean_ctor_get(v_impl_1425_, 4);
v_k_1514_ = lean_ctor_get(v_impl_1425_, 1);
v_v_1515_ = lean_ctor_get(v_impl_1425_, 2);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_impl_1425_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; lean_object* v_unused_1528_; 
v_unused_1527_ = lean_ctor_get(v_impl_1425_, 3);
lean_dec(v_unused_1527_);
v_unused_1528_ = lean_ctor_get(v_impl_1425_, 0);
lean_dec(v_unused_1528_);
v___x_1517_ = v_impl_1425_;
v_isShared_1518_ = v_isSharedCheck_1526_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_r_1513_);
lean_inc(v_v_1515_);
lean_inc(v_k_1514_);
lean_dec(v_impl_1425_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1526_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1519_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1513_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 3, v_r_1513_);
lean_ctor_set(v___x_1517_, 2, v_v_1418_);
lean_ctor_set(v___x_1517_, 1, v_k_1417_);
lean_ctor_set(v___x_1517_, 0, v___x_1426_);
v___x_1521_ = v___x_1517_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_k_1417_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_v_1418_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v_r_1513_);
lean_ctor_set(v_reuseFailAlloc_1525_, 4, v_r_1513_);
v___x_1521_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1523_; 
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 4, v___x_1521_);
lean_ctor_set(v___x_1422_, 3, v_l_1512_);
lean_ctor_set(v___x_1422_, 2, v_v_1515_);
lean_ctor_set(v___x_1422_, 1, v_k_1514_);
lean_ctor_set(v___x_1422_, 0, v___x_1519_);
v___x_1523_ = v___x_1422_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1519_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_k_1514_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_v_1515_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_l_1512_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
else
{
lean_object* v_r_1529_; 
v_r_1529_ = lean_ctor_get(v_impl_1425_, 4);
lean_inc(v_r_1529_);
if (lean_obj_tag(v_r_1529_) == 0)
{
lean_object* v_k_1530_; lean_object* v_v_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1554_; 
lean_inc(v_l_1512_);
v_k_1530_ = lean_ctor_get(v_impl_1425_, 1);
v_v_1531_ = lean_ctor_get(v_impl_1425_, 2);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_impl_1425_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; lean_object* v_unused_1556_; lean_object* v_unused_1557_; 
v_unused_1555_ = lean_ctor_get(v_impl_1425_, 4);
lean_dec(v_unused_1555_);
v_unused_1556_ = lean_ctor_get(v_impl_1425_, 3);
lean_dec(v_unused_1556_);
v_unused_1557_ = lean_ctor_get(v_impl_1425_, 0);
lean_dec(v_unused_1557_);
v___x_1533_ = v_impl_1425_;
v_isShared_1534_ = v_isSharedCheck_1554_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_v_1531_);
lean_inc(v_k_1530_);
lean_dec(v_impl_1425_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1554_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v_k_1535_; lean_object* v_v_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1550_; 
v_k_1535_ = lean_ctor_get(v_r_1529_, 1);
v_v_1536_ = lean_ctor_get(v_r_1529_, 2);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_r_1529_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; lean_object* v_unused_1552_; lean_object* v_unused_1553_; 
v_unused_1551_ = lean_ctor_get(v_r_1529_, 4);
lean_dec(v_unused_1551_);
v_unused_1552_ = lean_ctor_get(v_r_1529_, 3);
lean_dec(v_unused_1552_);
v_unused_1553_ = lean_ctor_get(v_r_1529_, 0);
lean_dec(v_unused_1553_);
v___x_1538_ = v_r_1529_;
v_isShared_1539_ = v_isSharedCheck_1550_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_v_1536_);
lean_inc(v_k_1535_);
lean_dec(v_r_1529_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1550_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1540_ = lean_unsigned_to_nat(3u);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 4, v_l_1512_);
lean_ctor_set(v___x_1538_, 3, v_l_1512_);
lean_ctor_set(v___x_1538_, 2, v_v_1531_);
lean_ctor_set(v___x_1538_, 1, v_k_1530_);
lean_ctor_set(v___x_1538_, 0, v___x_1426_);
v___x_1542_ = v___x_1538_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_k_1530_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_v_1531_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v_l_1512_);
lean_ctor_set(v_reuseFailAlloc_1549_, 4, v_l_1512_);
v___x_1542_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1544_; 
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 4, v_l_1512_);
lean_ctor_set(v___x_1533_, 2, v_v_1418_);
lean_ctor_set(v___x_1533_, 1, v_k_1417_);
lean_ctor_set(v___x_1533_, 0, v___x_1426_);
v___x_1544_ = v___x_1533_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_k_1417_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_v_1418_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v_l_1512_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v_l_1512_);
v___x_1544_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1546_; 
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 4, v___x_1544_);
lean_ctor_set(v___x_1422_, 3, v___x_1542_);
lean_ctor_set(v___x_1422_, 2, v_v_1536_);
lean_ctor_set(v___x_1422_, 1, v_k_1535_);
lean_ctor_set(v___x_1422_, 0, v___x_1540_);
v___x_1546_ = v___x_1422_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_k_1535_);
lean_ctor_set(v_reuseFailAlloc_1547_, 2, v_v_1536_);
lean_ctor_set(v_reuseFailAlloc_1547_, 3, v___x_1542_);
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
}
}
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1558_ = lean_unsigned_to_nat(2u);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 4, v_r_1529_);
lean_ctor_set(v___x_1422_, 3, v_impl_1425_);
lean_ctor_set(v___x_1422_, 0, v___x_1558_);
v___x_1560_ = v___x_1422_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_k_1417_);
lean_ctor_set(v_reuseFailAlloc_1561_, 2, v_v_1418_);
lean_ctor_set(v_reuseFailAlloc_1561_, 3, v_impl_1425_);
lean_ctor_set(v_reuseFailAlloc_1561_, 4, v_r_1529_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1563_; 
lean_dec(v_v_1418_);
lean_dec(v_k_1417_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 2, v_v_1414_);
lean_ctor_set(v___x_1422_, 1, v_k_1413_);
v___x_1563_ = v___x_1422_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_size_1416_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_k_1413_);
lean_ctor_set(v_reuseFailAlloc_1564_, 2, v_v_1414_);
lean_ctor_set(v_reuseFailAlloc_1564_, 3, v_l_1419_);
lean_ctor_set(v_reuseFailAlloc_1564_, 4, v_r_1420_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
default: 
{
lean_object* v_impl_1565_; lean_object* v___x_1566_; 
lean_dec(v_size_1416_);
v_impl_1565_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1413_, v_v_1414_, v_r_1420_);
v___x_1566_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1419_) == 0)
{
lean_object* v_size_1567_; lean_object* v_size_1568_; lean_object* v_k_1569_; lean_object* v_v_1570_; lean_object* v_l_1571_; lean_object* v_r_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v_size_1567_ = lean_ctor_get(v_l_1419_, 0);
v_size_1568_ = lean_ctor_get(v_impl_1565_, 0);
v_k_1569_ = lean_ctor_get(v_impl_1565_, 1);
v_v_1570_ = lean_ctor_get(v_impl_1565_, 2);
v_l_1571_ = lean_ctor_get(v_impl_1565_, 3);
lean_inc(v_l_1571_);
v_r_1572_ = lean_ctor_get(v_impl_1565_, 4);
v___x_1573_ = lean_unsigned_to_nat(3u);
v___x_1574_ = lean_nat_mul(v___x_1573_, v_size_1567_);
v___x_1575_ = lean_nat_dec_lt(v___x_1574_, v_size_1568_);
lean_dec(v___x_1574_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1579_; 
lean_dec(v_l_1571_);
v___x_1576_ = lean_nat_add(v___x_1566_, v_size_1567_);
v___x_1577_ = lean_nat_add(v___x_1576_, v_size_1568_);
lean_dec(v___x_1576_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 4, v_impl_1565_);
lean_ctor_set(v___x_1422_, 0, v___x_1577_);
v___x_1579_ = v___x_1422_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_k_1417_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v_v_1418_);
lean_ctor_set(v_reuseFailAlloc_1580_, 3, v_l_1419_);
lean_ctor_set(v_reuseFailAlloc_1580_, 4, v_impl_1565_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
else
{
lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1644_; 
lean_inc(v_r_1572_);
lean_inc(v_v_1570_);
lean_inc(v_k_1569_);
lean_inc(v_size_1568_);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_impl_1565_);
if (v_isSharedCheck_1644_ == 0)
{
lean_object* v_unused_1645_; lean_object* v_unused_1646_; lean_object* v_unused_1647_; lean_object* v_unused_1648_; lean_object* v_unused_1649_; 
v_unused_1645_ = lean_ctor_get(v_impl_1565_, 4);
lean_dec(v_unused_1645_);
v_unused_1646_ = lean_ctor_get(v_impl_1565_, 3);
lean_dec(v_unused_1646_);
v_unused_1647_ = lean_ctor_get(v_impl_1565_, 2);
lean_dec(v_unused_1647_);
v_unused_1648_ = lean_ctor_get(v_impl_1565_, 1);
lean_dec(v_unused_1648_);
v_unused_1649_ = lean_ctor_get(v_impl_1565_, 0);
lean_dec(v_unused_1649_);
v___x_1582_ = v_impl_1565_;
v_isShared_1583_ = v_isSharedCheck_1644_;
goto v_resetjp_1581_;
}
else
{
lean_dec(v_impl_1565_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1644_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v_size_1584_; lean_object* v_k_1585_; lean_object* v_v_1586_; lean_object* v_l_1587_; lean_object* v_r_1588_; lean_object* v_size_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v_size_1584_ = lean_ctor_get(v_l_1571_, 0);
v_k_1585_ = lean_ctor_get(v_l_1571_, 1);
v_v_1586_ = lean_ctor_get(v_l_1571_, 2);
v_l_1587_ = lean_ctor_get(v_l_1571_, 3);
v_r_1588_ = lean_ctor_get(v_l_1571_, 4);
v_size_1589_ = lean_ctor_get(v_r_1572_, 0);
v___x_1590_ = lean_unsigned_to_nat(2u);
v___x_1591_ = lean_nat_mul(v___x_1590_, v_size_1589_);
v___x_1592_ = lean_nat_dec_lt(v_size_1584_, v___x_1591_);
lean_dec(v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1620_; 
lean_inc(v_r_1588_);
lean_inc(v_l_1587_);
lean_inc(v_v_1586_);
lean_inc(v_k_1585_);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_l_1571_);
if (v_isSharedCheck_1620_ == 0)
{
lean_object* v_unused_1621_; lean_object* v_unused_1622_; lean_object* v_unused_1623_; lean_object* v_unused_1624_; lean_object* v_unused_1625_; 
v_unused_1621_ = lean_ctor_get(v_l_1571_, 4);
lean_dec(v_unused_1621_);
v_unused_1622_ = lean_ctor_get(v_l_1571_, 3);
lean_dec(v_unused_1622_);
v_unused_1623_ = lean_ctor_get(v_l_1571_, 2);
lean_dec(v_unused_1623_);
v_unused_1624_ = lean_ctor_get(v_l_1571_, 1);
lean_dec(v_unused_1624_);
v_unused_1625_ = lean_ctor_get(v_l_1571_, 0);
lean_dec(v_unused_1625_);
v___x_1594_ = v_l_1571_;
v_isShared_1595_ = v_isSharedCheck_1620_;
goto v_resetjp_1593_;
}
else
{
lean_dec(v_l_1571_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1620_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1610_; 
v___x_1596_ = lean_nat_add(v___x_1566_, v_size_1567_);
v___x_1597_ = lean_nat_add(v___x_1596_, v_size_1568_);
lean_dec(v_size_1568_);
if (lean_obj_tag(v_l_1587_) == 0)
{
lean_object* v_size_1618_; 
v_size_1618_ = lean_ctor_get(v_l_1587_, 0);
lean_inc(v_size_1618_);
v___y_1610_ = v_size_1618_;
goto v___jp_1609_;
}
else
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_unsigned_to_nat(0u);
v___y_1610_ = v___x_1619_;
goto v___jp_1609_;
}
v___jp_1598_:
{
lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1602_ = lean_nat_add(v___y_1599_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec(v___y_1599_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 4, v_r_1572_);
lean_ctor_set(v___x_1594_, 3, v_r_1588_);
lean_ctor_set(v___x_1594_, 2, v_v_1570_);
lean_ctor_set(v___x_1594_, 1, v_k_1569_);
lean_ctor_set(v___x_1594_, 0, v___x_1602_);
v___x_1604_ = v___x_1594_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_k_1569_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_v_1570_);
lean_ctor_set(v_reuseFailAlloc_1608_, 3, v_r_1588_);
lean_ctor_set(v_reuseFailAlloc_1608_, 4, v_r_1572_);
v___x_1604_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1606_; 
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 4, v___x_1604_);
lean_ctor_set(v___x_1582_, 3, v___y_1600_);
lean_ctor_set(v___x_1582_, 2, v_v_1586_);
lean_ctor_set(v___x_1582_, 1, v_k_1585_);
lean_ctor_set(v___x_1582_, 0, v___x_1597_);
v___x_1606_ = v___x_1582_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_k_1585_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_v_1586_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v___y_1600_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
v___jp_1609_:
{
lean_object* v___x_1611_; lean_object* v___x_1613_; 
v___x_1611_ = lean_nat_add(v___x_1596_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec(v___x_1596_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 4, v_l_1587_);
lean_ctor_set(v___x_1422_, 0, v___x_1611_);
v___x_1613_ = v___x_1422_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_k_1417_);
lean_ctor_set(v_reuseFailAlloc_1617_, 2, v_v_1418_);
lean_ctor_set(v_reuseFailAlloc_1617_, 3, v_l_1419_);
lean_ctor_set(v_reuseFailAlloc_1617_, 4, v_l_1587_);
v___x_1613_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_nat_add(v___x_1566_, v_size_1589_);
if (lean_obj_tag(v_r_1588_) == 0)
{
lean_object* v_size_1615_; 
v_size_1615_ = lean_ctor_get(v_r_1588_, 0);
lean_inc(v_size_1615_);
v___y_1599_ = v___x_1614_;
v___y_1600_ = v___x_1613_;
v___y_1601_ = v_size_1615_;
goto v___jp_1598_;
}
else
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_unsigned_to_nat(0u);
v___y_1599_ = v___x_1614_;
v___y_1600_ = v___x_1613_;
v___y_1601_ = v___x_1616_;
goto v___jp_1598_;
}
}
}
}
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1630_; 
lean_del_object(v___x_1422_);
v___x_1626_ = lean_nat_add(v___x_1566_, v_size_1567_);
v___x_1627_ = lean_nat_add(v___x_1626_, v_size_1568_);
lean_dec(v_size_1568_);
v___x_1628_ = lean_nat_add(v___x_1626_, v_size_1584_);
lean_dec(v___x_1626_);
lean_inc_ref(v_l_1419_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 4, v_l_1571_);
lean_ctor_set(v___x_1582_, 3, v_l_1419_);
lean_ctor_set(v___x_1582_, 2, v_v_1418_);
lean_ctor_set(v___x_1582_, 1, v_k_1417_);
lean_ctor_set(v___x_1582_, 0, v___x_1628_);
v___x_1630_ = v___x_1582_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_k_1417_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_v_1418_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v_l_1419_);
lean_ctor_set(v_reuseFailAlloc_1643_, 4, v_l_1571_);
v___x_1630_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
v_isSharedCheck_1637_ = !lean_is_exclusive(v_l_1419_);
if (v_isSharedCheck_1637_ == 0)
{
lean_object* v_unused_1638_; lean_object* v_unused_1639_; lean_object* v_unused_1640_; lean_object* v_unused_1641_; lean_object* v_unused_1642_; 
v_unused_1638_ = lean_ctor_get(v_l_1419_, 4);
lean_dec(v_unused_1638_);
v_unused_1639_ = lean_ctor_get(v_l_1419_, 3);
lean_dec(v_unused_1639_);
v_unused_1640_ = lean_ctor_get(v_l_1419_, 2);
lean_dec(v_unused_1640_);
v_unused_1641_ = lean_ctor_get(v_l_1419_, 1);
lean_dec(v_unused_1641_);
v_unused_1642_ = lean_ctor_get(v_l_1419_, 0);
lean_dec(v_unused_1642_);
v___x_1632_ = v_l_1419_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_dec(v_l_1419_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 4, v_r_1572_);
lean_ctor_set(v___x_1632_, 3, v___x_1630_);
lean_ctor_set(v___x_1632_, 2, v_v_1570_);
lean_ctor_set(v___x_1632_, 1, v_k_1569_);
lean_ctor_set(v___x_1632_, 0, v___x_1627_);
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_k_1569_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_v_1570_);
lean_ctor_set(v_reuseFailAlloc_1636_, 3, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1636_, 4, v_r_1572_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1650_; 
v_l_1650_ = lean_ctor_get(v_impl_1565_, 3);
lean_inc(v_l_1650_);
if (lean_obj_tag(v_l_1650_) == 0)
{
lean_object* v_r_1651_; lean_object* v_k_1652_; lean_object* v_v_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1676_; 
v_r_1651_ = lean_ctor_get(v_impl_1565_, 4);
v_k_1652_ = lean_ctor_get(v_impl_1565_, 1);
v_v_1653_ = lean_ctor_get(v_impl_1565_, 2);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_impl_1565_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; lean_object* v_unused_1678_; 
v_unused_1677_ = lean_ctor_get(v_impl_1565_, 3);
lean_dec(v_unused_1677_);
v_unused_1678_ = lean_ctor_get(v_impl_1565_, 0);
lean_dec(v_unused_1678_);
v___x_1655_ = v_impl_1565_;
v_isShared_1656_ = v_isSharedCheck_1676_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_r_1651_);
lean_inc(v_v_1653_);
lean_inc(v_k_1652_);
lean_dec(v_impl_1565_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1676_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v_k_1657_; lean_object* v_v_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1672_; 
v_k_1657_ = lean_ctor_get(v_l_1650_, 1);
v_v_1658_ = lean_ctor_get(v_l_1650_, 2);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_l_1650_);
if (v_isSharedCheck_1672_ == 0)
{
lean_object* v_unused_1673_; lean_object* v_unused_1674_; lean_object* v_unused_1675_; 
v_unused_1673_ = lean_ctor_get(v_l_1650_, 4);
lean_dec(v_unused_1673_);
v_unused_1674_ = lean_ctor_get(v_l_1650_, 3);
lean_dec(v_unused_1674_);
v_unused_1675_ = lean_ctor_get(v_l_1650_, 0);
lean_dec(v_unused_1675_);
v___x_1660_ = v_l_1650_;
v_isShared_1661_ = v_isSharedCheck_1672_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_v_1658_);
lean_inc(v_k_1657_);
lean_dec(v_l_1650_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1672_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1662_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1651_, 2);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 4, v_r_1651_);
lean_ctor_set(v___x_1660_, 3, v_r_1651_);
lean_ctor_set(v___x_1660_, 2, v_v_1418_);
lean_ctor_set(v___x_1660_, 1, v_k_1417_);
lean_ctor_set(v___x_1660_, 0, v___x_1566_);
v___x_1664_ = v___x_1660_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_k_1417_);
lean_ctor_set(v_reuseFailAlloc_1671_, 2, v_v_1418_);
lean_ctor_set(v_reuseFailAlloc_1671_, 3, v_r_1651_);
lean_ctor_set(v_reuseFailAlloc_1671_, 4, v_r_1651_);
v___x_1664_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1666_; 
lean_inc(v_r_1651_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 3, v_r_1651_);
lean_ctor_set(v___x_1655_, 0, v___x_1566_);
v___x_1666_ = v___x_1655_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_k_1652_);
lean_ctor_set(v_reuseFailAlloc_1670_, 2, v_v_1653_);
lean_ctor_set(v_reuseFailAlloc_1670_, 3, v_r_1651_);
lean_ctor_set(v_reuseFailAlloc_1670_, 4, v_r_1651_);
v___x_1666_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1668_; 
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 4, v___x_1666_);
lean_ctor_set(v___x_1422_, 3, v___x_1664_);
lean_ctor_set(v___x_1422_, 2, v_v_1658_);
lean_ctor_set(v___x_1422_, 1, v_k_1657_);
lean_ctor_set(v___x_1422_, 0, v___x_1662_);
v___x_1668_ = v___x_1422_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_k_1657_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v_v_1658_);
lean_ctor_set(v_reuseFailAlloc_1669_, 3, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1669_, 4, v___x_1666_);
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
else
{
lean_object* v_r_1679_; 
v_r_1679_ = lean_ctor_get(v_impl_1565_, 4);
lean_inc(v_r_1679_);
if (lean_obj_tag(v_r_1679_) == 0)
{
lean_object* v_k_1680_; lean_object* v_v_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1692_; 
v_k_1680_ = lean_ctor_get(v_impl_1565_, 1);
v_v_1681_ = lean_ctor_get(v_impl_1565_, 2);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_impl_1565_);
if (v_isSharedCheck_1692_ == 0)
{
lean_object* v_unused_1693_; lean_object* v_unused_1694_; lean_object* v_unused_1695_; 
v_unused_1693_ = lean_ctor_get(v_impl_1565_, 4);
lean_dec(v_unused_1693_);
v_unused_1694_ = lean_ctor_get(v_impl_1565_, 3);
lean_dec(v_unused_1694_);
v_unused_1695_ = lean_ctor_get(v_impl_1565_, 0);
lean_dec(v_unused_1695_);
v___x_1683_ = v_impl_1565_;
v_isShared_1684_ = v_isSharedCheck_1692_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_v_1681_);
lean_inc(v_k_1680_);
lean_dec(v_impl_1565_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1692_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1685_ = lean_unsigned_to_nat(3u);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 4, v_l_1650_);
lean_ctor_set(v___x_1683_, 2, v_v_1418_);
lean_ctor_set(v___x_1683_, 1, v_k_1417_);
lean_ctor_set(v___x_1683_, 0, v___x_1566_);
v___x_1687_ = v___x_1683_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_k_1417_);
lean_ctor_set(v_reuseFailAlloc_1691_, 2, v_v_1418_);
lean_ctor_set(v_reuseFailAlloc_1691_, 3, v_l_1650_);
lean_ctor_set(v_reuseFailAlloc_1691_, 4, v_l_1650_);
v___x_1687_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1689_; 
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 4, v_r_1679_);
lean_ctor_set(v___x_1422_, 3, v___x_1687_);
lean_ctor_set(v___x_1422_, 2, v_v_1681_);
lean_ctor_set(v___x_1422_, 1, v_k_1680_);
lean_ctor_set(v___x_1422_, 0, v___x_1685_);
v___x_1689_ = v___x_1422_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_k_1680_);
lean_ctor_set(v_reuseFailAlloc_1690_, 2, v_v_1681_);
lean_ctor_set(v_reuseFailAlloc_1690_, 3, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1690_, 4, v_r_1679_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1696_ = lean_unsigned_to_nat(2u);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 4, v_impl_1565_);
lean_ctor_set(v___x_1422_, 3, v_r_1679_);
lean_ctor_set(v___x_1422_, 0, v___x_1696_);
v___x_1698_ = v___x_1422_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_k_1417_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_v_1418_);
lean_ctor_set(v_reuseFailAlloc_1699_, 3, v_r_1679_);
lean_ctor_set(v_reuseFailAlloc_1699_, 4, v_impl_1565_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
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
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = lean_unsigned_to_nat(1u);
v___x_1702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
lean_ctor_set(v___x_1702_, 1, v_k_1413_);
lean_ctor_set(v___x_1702_, 2, v_v_1414_);
lean_ctor_set(v___x_1702_, 3, v_t_1415_);
lean_ctor_set(v___x_1702_, 4, v_t_1415_);
return v___x_1702_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(lean_object* v_as_1703_, size_t v_sz_1704_, size_t v_i_1705_, lean_object* v_b_1706_){
_start:
{
lean_object* v___y_1709_; uint8_t v___x_1713_; 
v___x_1713_ = lean_usize_dec_lt(v_i_1705_, v_sz_1704_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1714_, 0, v_b_1706_);
return v___x_1714_;
}
else
{
lean_object* v_a_1715_; uint8_t v___x_1716_; 
v_a_1715_ = lean_array_uget_borrowed(v_as_1703_, v_i_1705_);
lean_inc(v_b_1706_);
lean_inc(v_a_1715_);
v___x_1716_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_a_1715_, v_b_1706_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = lean_box(0);
lean_inc(v_a_1715_);
v___x_1718_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_a_1715_, v___x_1717_, v_b_1706_);
v___y_1709_ = v___x_1718_;
goto v___jp_1708_;
}
else
{
v___y_1709_ = v_b_1706_;
goto v___jp_1708_;
}
}
v___jp_1708_:
{
size_t v___x_1710_; size_t v___x_1711_; 
v___x_1710_ = ((size_t)1ULL);
v___x_1711_ = lean_usize_add(v_i_1705_, v___x_1710_);
v_i_1705_ = v___x_1711_;
v_b_1706_ = v___y_1709_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1703_ = stack[0].m_obj;
size_t v_sz_1704_ = stack[1].m_num;
size_t v_i_1705_ = stack[2].m_num;
lean_object* v_b_1706_ = stack[3].m_obj;
lean_object* v_res_1719_;
v_res_1719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_as_1703_, v_sz_1704_, v_i_1705_, v_b_1706_);
stack->m_obj
 = v_res_1719_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg___boxed(lean_object* v_as_1720_, lean_object* v_sz_1721_, lean_object* v_i_1722_, lean_object* v_b_1723_, lean_object* v___y_1724_){
_start:
{
size_t v_sz_boxed_1725_; size_t v_i_boxed_1726_; lean_object* v_res_1727_; 
v_sz_boxed_1725_ = lean_unbox_usize(v_sz_1721_);
lean_dec(v_sz_1721_);
v_i_boxed_1726_ = lean_unbox_usize(v_i_1722_);
lean_dec(v_i_1722_);
v_res_1727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_as_1720_, v_sz_boxed_1725_, v_i_boxed_1726_, v_b_1723_);
lean_dec_ref(v_as_1720_);
return v_res_1727_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(lean_object* v_type_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v_set_1734_; lean_object* v___x_1735_; 
v_set_1734_ = lean_box(1);
v___x_1735_ = l_Lean_Server_Completion_getDotCompletionTypeNames(v_type_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; size_t v_sz_1737_; size_t v___x_1738_; lean_object* v___x_1739_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1735_, 1);
v_sz_1737_ = lean_array_size(v_a_1736_);
v___x_1738_ = ((size_t)0ULL);
v___x_1739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_a_1736_, v_sz_1737_, v___x_1738_, v_set_1734_);
lean_dec(v_a_1736_);
return v___x_1739_;
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
v_a_1740_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1735_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1735_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1728_ = stack[0].m_obj;
lean_object* v_a_1729_ = stack[1].m_obj;
lean_object* v_a_1730_ = stack[2].m_obj;
lean_object* v_a_1731_ = stack[3].m_obj;
lean_object* v_a_1732_ = stack[4].m_obj;
lean_object* v_res_1748_;
v_res_1748_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(v_type_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
stack->m_obj
 = v_res_1748_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet___boxed(lean_object* v_type_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(v_type_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
return v_res_1755_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0(lean_object* v_00_u03b2_1756_, lean_object* v_k_1757_, lean_object* v_t_1758_){
_start:
{
uint8_t v___x_1759_; 
v___x_1759_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_k_1757_, v_t_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1757_ = stack[1].m_obj;
lean_object* v_t_1758_ = stack[2].m_obj;
uint8_t v_res_1760_;
v_res_1760_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0(lean_box(0), v_k_1757_, v_t_1758_);
stack->m_num = v_res_1760_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___boxed(lean_object* v_00_u03b2_1761_, lean_object* v_k_1762_, lean_object* v_t_1763_){
_start:
{
uint8_t v_res_1764_; lean_object* v_r_1765_; 
v_res_1764_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0(v_00_u03b2_1761_, v_k_1762_, v_t_1763_);
v_r_1765_ = lean_box(v_res_1764_);
return v_r_1765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1(lean_object* v_00_u03b2_1766_, lean_object* v_k_1767_, lean_object* v_v_1768_, lean_object* v_t_1769_, lean_object* v_hl_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1767_, v_v_1768_, v_t_1769_);
return v___x_1771_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2(lean_object* v_as_1772_, size_t v_sz_1773_, size_t v_i_1774_, lean_object* v_b_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_as_1772_, v_sz_1773_, v_i_1774_, v_b_1775_);
return v___x_1781_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1772_ = stack[0].m_obj;
size_t v_sz_1773_ = stack[1].m_num;
size_t v_i_1774_ = stack[2].m_num;
lean_object* v_b_1775_ = stack[3].m_obj;
lean_object* v___y_1776_ = stack[4].m_obj;
lean_object* v___y_1777_ = stack[5].m_obj;
lean_object* v___y_1778_ = stack[6].m_obj;
lean_object* v___y_1779_ = stack[7].m_obj;
lean_object* v_res_1782_;
v_res_1782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2(v_as_1772_, v_sz_1773_, v_i_1774_, v_b_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
stack->m_obj
 = v_res_1782_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___boxed(lean_object* v_as_1783_, lean_object* v_sz_1784_, lean_object* v_i_1785_, lean_object* v_b_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
size_t v_sz_boxed_1792_; size_t v_i_boxed_1793_; lean_object* v_res_1794_; 
v_sz_boxed_1792_ = lean_unbox_usize(v_sz_1784_);
lean_dec(v_sz_1784_);
v_i_boxed_1793_ = lean_unbox_usize(v_i_1785_);
lean_dec(v_i_1785_);
v_res_1794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2(v_as_1783_, v_sz_boxed_1792_, v_i_boxed_1793_, v_b_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec_ref(v_as_1783_);
return v_res_1794_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(lean_object* v_e_1795_, lean_object* v_declName_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_){
_start:
{
uint8_t v___y_1803_; uint8_t v___y_1825_; lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_Expr_getAppFn(v_e_1795_);
if (lean_obj_tag(v___x_1828_) == 4)
{
lean_object* v_declName_1829_; lean_object* v___x_1830_; 
v_declName_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc_n(v_declName_1829_, 2);
lean_dec_ref_known(v___x_1828_, 2);
v___x_1830_ = l_Lean_privateToUserName_x3f(v_declName_1829_);
if (lean_obj_tag(v___x_1830_) == 0)
{
uint8_t v___x_1831_; 
v___x_1831_ = lean_name_eq(v_declName_1829_, v_declName_1796_);
lean_dec(v_declName_1829_);
v___y_1825_ = v___x_1831_;
goto v___jp_1824_;
}
else
{
lean_object* v_val_1832_; uint8_t v___x_1833_; 
lean_dec(v_declName_1829_);
v_val_1832_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_val_1832_);
lean_dec_ref_known(v___x_1830_, 1);
v___x_1833_ = lean_name_eq(v_val_1832_, v_declName_1796_);
lean_dec(v_val_1832_);
v___y_1825_ = v___x_1833_;
goto v___jp_1824_;
}
}
else
{
uint8_t v___x_1834_; 
lean_dec_ref(v___x_1828_);
v___x_1834_ = 0;
v___y_1803_ = v___x_1834_;
goto v___jp_1802_;
}
v___jp_1802_:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f(v_e_1795_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1815_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1815_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1815_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
if (lean_obj_tag(v_a_1805_) == 1)
{
lean_object* v_val_1809_; 
lean_del_object(v___x_1807_);
v_val_1809_ = lean_ctor_get(v_a_1805_, 0);
lean_inc(v_val_1809_);
lean_dec_ref_known(v_a_1805_, 1);
v_e_1795_ = v_val_1809_;
goto _start;
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
lean_dec(v_a_1805_);
v___x_1811_ = lean_box(v___y_1803_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1811_);
v___x_1813_ = v___x_1807_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
v_a_1816_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1804_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1804_);
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
v___jp_1824_:
{
if (v___y_1825_ == 0)
{
v___y_1803_ = v___y_1825_;
goto v___jp_1802_;
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_dec_ref(v_e_1795_);
v___x_1826_ = lean_box(v___y_1825_);
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
return v___x_1827_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1795_ = stack[0].m_obj;
lean_object* v_declName_1796_ = stack[1].m_obj;
lean_object* v_a_1797_ = stack[2].m_obj;
lean_object* v_a_1798_ = stack[3].m_obj;
lean_object* v_a_1799_ = stack[4].m_obj;
lean_object* v_a_1800_ = stack[5].m_obj;
lean_object* v_res_1835_;
v_res_1835_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(v_e_1795_, v_declName_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_);
stack->m_obj
 = v_res_1835_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf___boxed(lean_object* v_e_1836_, lean_object* v_declName_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(v_e_1836_, v_declName_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec(v_declName_1837_);
return v_res_1843_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0(lean_object* v_k_1844_, lean_object* v_b_1845_, lean_object* v_c_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___x_1852_; 
lean_inc(v___y_1850_);
lean_inc_ref(v___y_1849_);
lean_inc(v___y_1848_);
lean_inc_ref(v___y_1847_);
v___x_1852_ = lean_apply_7(v_k_1844_, v_b_1845_, v_c_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, lean_box(0));
return v___x_1852_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1844_ = stack[0].m_obj;
lean_object* v_b_1845_ = stack[1].m_obj;
lean_object* v_c_1846_ = stack[2].m_obj;
lean_object* v___y_1847_ = stack[3].m_obj;
lean_object* v___y_1848_ = stack[4].m_obj;
lean_object* v___y_1849_ = stack[5].m_obj;
lean_object* v___y_1850_ = stack[6].m_obj;
lean_object* v_res_1853_;
v_res_1853_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0(v_k_1844_, v_b_1845_, v_c_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
stack->m_obj
 = v_res_1853_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed(lean_object* v_k_1854_, lean_object* v_b_1855_, lean_object* v_c_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0(v_k_1854_, v_b_1855_, v_c_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
return v_res_1862_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(lean_object* v_type_1863_, lean_object* v_k_1864_, uint8_t v_cleanupAnnotations_1865_, uint8_t v_whnfType_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v___f_1872_; lean_object* v___x_1873_; 
v___f_1872_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1872_, 0, v_k_1864_);
v___x_1873_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1863_, v___f_1872_, v_cleanupAnnotations_1865_, v_whnfType_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
v_a_1882_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1873_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1873_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1863_ = stack[0].m_obj;
lean_object* v_k_1864_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_1865_ = stack[2].m_num;
uint8_t v_whnfType_1866_ = stack[3].m_num;
lean_object* v___y_1867_ = stack[4].m_obj;
lean_object* v___y_1868_ = stack[5].m_obj;
lean_object* v___y_1869_ = stack[6].m_obj;
lean_object* v___y_1870_ = stack[7].m_obj;
lean_object* v_res_1890_;
v_res_1890_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v_type_1863_, v_k_1864_, v_cleanupAnnotations_1865_, v_whnfType_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
stack->m_obj
 = v_res_1890_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___boxed(lean_object* v_type_1891_, lean_object* v_k_1892_, lean_object* v_cleanupAnnotations_1893_, lean_object* v_whnfType_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1900_; uint8_t v_whnfType_boxed_1901_; lean_object* v_res_1902_; 
v_cleanupAnnotations_boxed_1900_ = lean_unbox(v_cleanupAnnotations_1893_);
v_whnfType_boxed_1901_ = lean_unbox(v_whnfType_1894_);
v_res_1902_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v_type_1891_, v_k_1892_, v_cleanupAnnotations_boxed_1900_, v_whnfType_boxed_1901_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
return v_res_1902_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1(lean_object* v_00_u03b1_1903_, lean_object* v_type_1904_, lean_object* v_k_1905_, uint8_t v_cleanupAnnotations_1906_, uint8_t v_whnfType_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v_type_1904_, v_k_1905_, v_cleanupAnnotations_1906_, v_whnfType_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
return v___x_1913_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1904_ = stack[1].m_obj;
lean_object* v_k_1905_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_1906_ = stack[3].m_num;
uint8_t v_whnfType_1907_ = stack[4].m_num;
lean_object* v___y_1908_ = stack[5].m_obj;
lean_object* v___y_1909_ = stack[6].m_obj;
lean_object* v___y_1910_ = stack[7].m_obj;
lean_object* v___y_1911_ = stack[8].m_obj;
lean_object* v_res_1914_;
v_res_1914_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1(lean_box(0), v_type_1904_, v_k_1905_, v_cleanupAnnotations_1906_, v_whnfType_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
stack->m_obj
 = v_res_1914_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___boxed(lean_object* v_00_u03b1_1915_, lean_object* v_type_1916_, lean_object* v_k_1917_, lean_object* v_cleanupAnnotations_1918_, lean_object* v_whnfType_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1925_; uint8_t v_whnfType_boxed_1926_; lean_object* v_res_1927_; 
v_cleanupAnnotations_boxed_1925_ = lean_unbox(v_cleanupAnnotations_1918_);
v_whnfType_boxed_1926_ = lean_unbox(v_whnfType_1919_);
v_res_1927_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1(v_00_u03b1_1915_, v_type_1916_, v_k_1917_, v_cleanupAnnotations_boxed_1925_, v_whnfType_boxed_1926_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
return v_res_1927_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(lean_object* v_typeName_1931_, lean_object* v_as_1932_, size_t v_sz_1933_, size_t v_i_1934_, lean_object* v_b_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_usize_dec_lt(v_i_1934_, v_sz_1933_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; 
v___x_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1942_, 0, v_b_1935_);
return v___x_1942_;
}
else
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v_a_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
lean_dec_ref(v_b_1935_);
v___x_1943_ = lean_box(0);
v___x_1944_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___closed__0));
v_a_1945_ = lean_array_uget_borrowed(v_as_1932_, v_i_1934_);
v___x_1946_ = l_Lean_Expr_fvarId_x21(v_a_1945_);
v___x_1947_ = l_Lean_FVarId_getDecl___redArg(v___x_1946_, v___y_1936_, v___y_1938_, v___y_1939_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1947_, 1);
v___x_1949_ = l_Lean_LocalDecl_type(v_a_1948_);
lean_dec(v_a_1948_);
v___x_1950_ = l_Lean_Expr_consumeMData(v___x_1949_);
lean_dec_ref(v___x_1949_);
v___x_1951_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(v___x_1950_, v_typeName_1931_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1965_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1954_ = v___x_1951_;
v_isShared_1955_ = v_isSharedCheck_1965_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1965_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
uint8_t v___x_1956_; 
v___x_1956_ = lean_unbox(v_a_1952_);
if (v___x_1956_ == 0)
{
size_t v___x_1957_; size_t v___x_1958_; 
lean_del_object(v___x_1954_);
lean_dec(v_a_1952_);
v___x_1957_ = ((size_t)1ULL);
v___x_1958_ = lean_usize_add(v_i_1934_, v___x_1957_);
v_i_1934_ = v___x_1958_;
v_b_1935_ = v___x_1944_;
goto _start;
}
else
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1963_; 
v___x_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1960_, 0, v_a_1952_);
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
lean_ctor_set(v___x_1961_, 1, v___x_1943_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1961_);
v___x_1963_ = v___x_1954_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
v_a_1966_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1951_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1951_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
v_a_1974_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1947_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1947_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_typeName_1931_ = stack[0].m_obj;
lean_object* v_as_1932_ = stack[1].m_obj;
size_t v_sz_1933_ = stack[2].m_num;
size_t v_i_1934_ = stack[3].m_num;
lean_object* v_b_1935_ = stack[4].m_obj;
lean_object* v___y_1936_ = stack[5].m_obj;
lean_object* v___y_1937_ = stack[6].m_obj;
lean_object* v___y_1938_ = stack[7].m_obj;
lean_object* v___y_1939_ = stack[8].m_obj;
lean_object* v_res_1982_;
v_res_1982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(v_typeName_1931_, v_as_1932_, v_sz_1933_, v_i_1934_, v_b_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
stack->m_obj
 = v_res_1982_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___boxed(lean_object* v_typeName_1983_, lean_object* v_as_1984_, lean_object* v_sz_1985_, lean_object* v_i_1986_, lean_object* v_b_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
size_t v_sz_boxed_1993_; size_t v_i_boxed_1994_; lean_object* v_res_1995_; 
v_sz_boxed_1993_ = lean_unbox_usize(v_sz_1985_);
lean_dec(v_sz_1985_);
v_i_boxed_1994_ = lean_unbox_usize(v_i_1986_);
lean_dec(v_i_1986_);
v_res_1995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(v_typeName_1983_, v_as_1984_, v_sz_boxed_1993_, v_i_boxed_1994_, v_b_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec_ref(v_as_1984_);
lean_dec(v_typeName_1983_);
return v_res_1995_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0(lean_object* v_typeName_1996_, lean_object* v_xs_1997_, lean_object* v_x_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___x_2004_; size_t v_sz_2005_; size_t v___x_2006_; lean_object* v___x_2007_; 
v___x_2004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___closed__0));
v_sz_2005_ = lean_array_size(v_xs_1997_);
v___x_2006_ = ((size_t)0ULL);
v___x_2007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(v_typeName_1996_, v_xs_1997_, v_sz_2005_, v___x_2006_, v___x_2004_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2022_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2022_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2022_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v_fst_2012_; 
v_fst_2012_ = lean_ctor_get(v_a_2008_, 0);
lean_inc(v_fst_2012_);
lean_dec(v_a_2008_);
if (lean_obj_tag(v_fst_2012_) == 0)
{
uint8_t v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2016_; 
v___x_2013_ = 0;
v___x_2014_ = lean_box(v___x_2013_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2014_);
v___x_2016_ = v___x_2010_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
else
{
lean_object* v_val_2018_; lean_object* v___x_2020_; 
v_val_2018_ = lean_ctor_get(v_fst_2012_, 0);
lean_inc(v_val_2018_);
lean_dec_ref_known(v_fst_2012_, 1);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v_val_2018_);
v___x_2020_ = v___x_2010_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_val_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
v_a_2023_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_2007_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2007_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_typeName_1996_ = stack[0].m_obj;
lean_object* v_xs_1997_ = stack[1].m_obj;
lean_object* v_x_1998_ = stack[2].m_obj;
lean_object* v___y_1999_ = stack[3].m_obj;
lean_object* v___y_2000_ = stack[4].m_obj;
lean_object* v___y_2001_ = stack[5].m_obj;
lean_object* v___y_2002_ = stack[6].m_obj;
lean_object* v_res_2031_;
v_res_2031_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0(v_typeName_1996_, v_xs_1997_, v_x_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
stack->m_obj
 = v_res_2031_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0___boxed(lean_object* v_typeName_2032_, lean_object* v_xs_2033_, lean_object* v_x_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0(v_typeName_2032_, v_xs_2033_, v_x_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec_ref(v_x_2034_);
lean_dec_ref(v_xs_2033_);
lean_dec(v_typeName_2032_);
return v_res_2040_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(lean_object* v_typeName_2041_, lean_object* v_info_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v___f_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; lean_object* v___x_2051_; 
v___f_2048_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2048_, 0, v_typeName_2041_);
v___x_2049_ = l_Lean_ConstantInfo_type(v_info_2042_);
v___x_2050_ = 0;
v___x_2051_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v___x_2049_, v___f_2048_, v___x_2050_, v___x_2050_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_);
return v___x_2051_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_0interp(lean_interpreter_value* stack)
{
lean_object* v_typeName_2041_ = stack[0].m_obj;
lean_object* v_info_2042_ = stack[1].m_obj;
lean_object* v_a_2043_ = stack[2].m_obj;
lean_object* v_a_2044_ = stack[3].m_obj;
lean_object* v_a_2045_ = stack[4].m_obj;
lean_object* v_a_2046_ = stack[5].m_obj;
lean_object* v_res_2052_;
v_res_2052_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(v_typeName_2041_, v_info_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_);
stack->m_obj
 = v_res_2052_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___boxed(lean_object* v_typeName_2053_, lean_object* v_info_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(v_typeName_2053_, v_info_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec_ref(v_info_2054_);
return v_res_2060_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(lean_object* v_e_2061_, lean_object* v___y_2062_){
_start:
{
uint8_t v___x_2064_; 
v___x_2064_ = l_Lean_Expr_hasMVar(v_e_2061_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; 
v___x_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2065_, 0, v_e_2061_);
return v___x_2065_;
}
else
{
lean_object* v___x_2066_; lean_object* v_mctx_2067_; lean_object* v___x_2068_; lean_object* v_fst_2069_; lean_object* v_snd_2070_; lean_object* v___x_2071_; lean_object* v_cache_2072_; lean_object* v_zetaDeltaFVarIds_2073_; lean_object* v_postponed_2074_; lean_object* v_diag_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2084_; 
v___x_2066_ = lean_st_ref_get(v___y_2062_);
v_mctx_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc_ref(v_mctx_2067_);
lean_dec(v___x_2066_);
v___x_2068_ = l_Lean_instantiateMVarsCore(v_mctx_2067_, v_e_2061_);
v_fst_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_fst_2069_);
v_snd_2070_ = lean_ctor_get(v___x_2068_, 1);
lean_inc(v_snd_2070_);
lean_dec_ref(v___x_2068_);
v___x_2071_ = lean_st_ref_take(v___y_2062_);
v_cache_2072_ = lean_ctor_get(v___x_2071_, 1);
v_zetaDeltaFVarIds_2073_ = lean_ctor_get(v___x_2071_, 2);
v_postponed_2074_ = lean_ctor_get(v___x_2071_, 3);
v_diag_2075_ = lean_ctor_get(v___x_2071_, 4);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2084_ == 0)
{
lean_object* v_unused_2085_; 
v_unused_2085_ = lean_ctor_get(v___x_2071_, 0);
lean_dec(v_unused_2085_);
v___x_2077_ = v___x_2071_;
v_isShared_2078_ = v_isSharedCheck_2084_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_diag_2075_);
lean_inc(v_postponed_2074_);
lean_inc(v_zetaDeltaFVarIds_2073_);
lean_inc(v_cache_2072_);
lean_dec(v___x_2071_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2084_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v_snd_2070_);
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_snd_2070_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_cache_2072_);
lean_ctor_set(v_reuseFailAlloc_2083_, 2, v_zetaDeltaFVarIds_2073_);
lean_ctor_set(v_reuseFailAlloc_2083_, 3, v_postponed_2074_);
lean_ctor_set(v_reuseFailAlloc_2083_, 4, v_diag_2075_);
v___x_2080_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = lean_st_ref_put(v___y_2062_, v___x_2080_);
v___x_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2082_, 0, v_fst_2069_);
return v___x_2082_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2061_ = stack[0].m_obj;
lean_object* v___y_2062_ = stack[1].m_obj;
lean_object* v_res_2086_;
v_res_2086_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(v_e_2061_, v___y_2062_);
stack->m_obj
 = v_res_2086_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg___boxed(lean_object* v_e_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(v_e_2087_, v___y_2088_);
lean_dec(v___y_2088_);
return v_res_2090_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0(lean_object* v_e_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v___x_2097_; 
v___x_2097_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(v_e_2091_, v___y_2093_);
return v___x_2097_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2091_ = stack[0].m_obj;
lean_object* v___y_2092_ = stack[1].m_obj;
lean_object* v___y_2093_ = stack[2].m_obj;
lean_object* v___y_2094_ = stack[3].m_obj;
lean_object* v___y_2095_ = stack[4].m_obj;
lean_object* v_res_2098_;
v_res_2098_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0(v_e_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
stack->m_obj
 = v_res_2098_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___boxed(lean_object* v_e_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0(v_e_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
return v_res_2105_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(lean_object* v_type_2106_, lean_object* v_k_2107_, uint8_t v_cleanupAnnotations_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___f_2114_; uint8_t v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___f_2114_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2114_, 0, v_k_2107_);
v___x_2115_ = 0;
v___x_2116_ = lean_box(0);
v___x_2117_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2115_, v___x_2116_, v_type_2106_, v___f_2114_, v_cleanupAnnotations_2108_, v___x_2115_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2117_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
v_a_2126_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2117_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2117_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2106_ = stack[0].m_obj;
lean_object* v_k_2107_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_2108_ = stack[2].m_num;
lean_object* v___y_2109_ = stack[3].m_obj;
lean_object* v___y_2110_ = stack[4].m_obj;
lean_object* v___y_2111_ = stack[5].m_obj;
lean_object* v___y_2112_ = stack[6].m_obj;
lean_object* v_res_2134_;
v_res_2134_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(v_type_2106_, v_k_2107_, v_cleanupAnnotations_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
stack->m_obj
 = v_res_2134_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg___boxed(lean_object* v_type_2135_, lean_object* v_k_2136_, lean_object* v_cleanupAnnotations_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2143_; lean_object* v_res_2144_; 
v_cleanupAnnotations_boxed_2143_ = lean_unbox(v_cleanupAnnotations_2137_);
v_res_2144_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(v_type_2135_, v_k_2136_, v_cleanupAnnotations_boxed_2143_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
return v_res_2144_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1(lean_object* v_00_u03b1_2145_, lean_object* v_type_2146_, lean_object* v_k_2147_, uint8_t v_cleanupAnnotations_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(v_type_2146_, v_k_2147_, v_cleanupAnnotations_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
return v___x_2154_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2146_ = stack[1].m_obj;
lean_object* v_k_2147_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_2148_ = stack[3].m_num;
lean_object* v___y_2149_ = stack[4].m_obj;
lean_object* v___y_2150_ = stack[5].m_obj;
lean_object* v___y_2151_ = stack[6].m_obj;
lean_object* v___y_2152_ = stack[7].m_obj;
lean_object* v_res_2155_;
v_res_2155_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1(lean_box(0), v_type_2146_, v_k_2147_, v_cleanupAnnotations_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
stack->m_obj
 = v_res_2155_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___boxed(lean_object* v_00_u03b1_2156_, lean_object* v_type_2157_, lean_object* v_k_2158_, lean_object* v_cleanupAnnotations_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2165_; lean_object* v_res_2166_; 
v_cleanupAnnotations_boxed_2165_ = lean_unbox(v_cleanupAnnotations_2159_);
v_res_2166_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1(v_00_u03b1_2156_, v_type_2157_, v_k_2158_, v_cleanupAnnotations_boxed_2165_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0___boxed(lean_object* v_typeNameSet_2167_, lean_object* v_x_2168_, lean_object* v_type_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0(v_typeNameSet_2167_, v_x_2168_, v_type_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec_ref(v_x_2168_);
return v_res_2175_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(lean_object* v_typeNameSet_2176_, lean_object* v_type_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v___f_2183_; lean_object* v_a_2185_; lean_object* v___y_2236_; lean_object* v___x_2246_; 
lean_inc(v_typeNameSet_2176_);
v___f_2183_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2183_, 0, v_typeNameSet_2176_);
lean_inc_ref(v_type_2177_);
v___x_2246_ = l_Lean_Meta_whnfCoreUnfoldingAnnotations(v_type_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_dec_ref(v_type_2177_);
v___y_2236_ = v___x_2246_;
goto v___jp_2235_;
}
else
{
lean_object* v_a_2247_; uint8_t v___y_2249_; uint8_t v___x_2250_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
v___x_2250_ = l_Lean_Exception_isInterrupt(v_a_2247_);
if (v___x_2250_ == 0)
{
uint8_t v___x_2251_; 
lean_inc(v_a_2247_);
v___x_2251_ = l_Lean_Exception_isRuntime(v_a_2247_);
v___y_2249_ = v___x_2251_;
goto v___jp_2248_;
}
else
{
v___y_2249_ = v___x_2250_;
goto v___jp_2248_;
}
v___jp_2248_:
{
if (v___y_2249_ == 0)
{
lean_dec_ref_known(v___x_2246_, 1);
v_a_2185_ = v_type_2177_;
goto v___jp_2184_;
}
else
{
lean_dec_ref(v_type_2177_);
v___y_2236_ = v___x_2246_;
goto v___jp_2235_;
}
}
}
v___jp_2184_:
{
uint8_t v___x_2186_; 
v___x_2186_ = l_Lean_Expr_isForall(v_a_2185_);
if (v___x_2186_ == 0)
{
uint8_t v___x_2187_; lean_object* v___x_2188_; 
lean_dec_ref(v___f_2183_);
v___x_2187_ = 1;
v___x_2188_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(v_a_2185_, v_a_2179_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2224_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2191_ = v___x_2188_;
v_isShared_2192_ = v_isSharedCheck_2224_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2188_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2224_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_Expr_getAppFn(v_a_2189_);
if (lean_obj_tag(v___x_2193_) == 4)
{
lean_object* v_declName_2194_; uint8_t v___x_2195_; 
v_declName_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_declName_2194_);
lean_dec_ref_known(v___x_2193_, 2);
lean_inc(v_typeNameSet_2176_);
v___x_2195_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_declName_2194_, v_typeNameSet_2176_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; 
lean_del_object(v___x_2191_);
v___x_2196_ = l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f(v_a_2189_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2207_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2199_ = v___x_2196_;
v_isShared_2200_ = v_isSharedCheck_2207_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2196_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2207_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
if (lean_obj_tag(v_a_2197_) == 1)
{
lean_object* v_val_2201_; 
lean_del_object(v___x_2199_);
v_val_2201_ = lean_ctor_get(v_a_2197_, 0);
lean_inc(v_val_2201_);
lean_dec_ref_known(v_a_2197_, 1);
v_type_2177_ = v_val_2201_;
goto _start;
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2205_; 
lean_dec(v_a_2197_);
lean_dec(v_typeNameSet_2176_);
v___x_2203_ = lean_box(v___x_2195_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v___x_2203_);
v___x_2205_ = v___x_2199_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2203_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_dec(v_typeNameSet_2176_);
v_a_2208_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2196_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2196_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
else
{
lean_object* v___x_2216_; lean_object* v___x_2218_; 
lean_dec(v_a_2189_);
lean_dec(v_typeNameSet_2176_);
v___x_2216_ = lean_box(v___x_2187_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 0, v___x_2216_);
v___x_2218_ = v___x_2191_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
else
{
lean_object* v___x_2220_; lean_object* v___x_2222_; 
lean_dec_ref(v___x_2193_);
lean_dec(v_a_2189_);
lean_dec(v_typeNameSet_2176_);
v___x_2220_ = lean_box(v___x_2186_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 0, v___x_2220_);
v___x_2222_ = v___x_2191_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2220_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v_typeNameSet_2176_);
v_a_2225_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2188_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2188_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
else
{
uint8_t v___x_2233_; lean_object* v___x_2234_; 
lean_dec(v_typeNameSet_2176_);
v___x_2233_ = 0;
v___x_2234_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(v_a_2185_, v___f_2183_, v___x_2233_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
return v___x_2234_;
}
}
v___jp_2235_:
{
if (lean_obj_tag(v___y_2236_) == 0)
{
lean_object* v_a_2237_; 
v_a_2237_ = lean_ctor_get(v___y_2236_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___y_2236_, 1);
v_a_2185_ = v_a_2237_;
goto v___jp_2184_;
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec_ref(v___f_2183_);
lean_dec(v_typeNameSet_2176_);
v_a_2238_ = lean_ctor_get(v___y_2236_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___y_2236_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___y_2236_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___y_2236_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_typeNameSet_2176_ = stack[0].m_obj;
lean_object* v_type_2177_ = stack[1].m_obj;
lean_object* v_a_2178_ = stack[2].m_obj;
lean_object* v_a_2179_ = stack[3].m_obj;
lean_object* v_a_2180_ = stack[4].m_obj;
lean_object* v_a_2181_ = stack[5].m_obj;
lean_object* v_res_2252_;
v_res_2252_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(v_typeNameSet_2176_, v_type_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
stack->m_obj
 = v_res_2252_;
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0(lean_object* v_typeNameSet_2253_, lean_object* v_x_2254_, lean_object* v_type_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(v_typeNameSet_2253_, v_type_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
return v___x_2261_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_typeNameSet_2253_ = stack[0].m_obj;
lean_object* v_x_2254_ = stack[1].m_obj;
lean_object* v_type_2255_ = stack[2].m_obj;
lean_object* v___y_2256_ = stack[3].m_obj;
lean_object* v___y_2257_ = stack[4].m_obj;
lean_object* v___y_2258_ = stack[5].m_obj;
lean_object* v___y_2259_ = stack[6].m_obj;
lean_object* v_res_2262_;
v_res_2262_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0(v_typeNameSet_2253_, v_x_2254_, v_type_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
stack->m_obj
 = v_res_2262_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___boxed(lean_object* v_typeNameSet_2263_, lean_object* v_type_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(v_typeNameSet_2263_, v_type_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_);
lean_dec(v_a_2268_);
lean_dec_ref(v_a_2267_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
return v_res_2270_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(lean_object* v_typeNameSet_2271_, lean_object* v_info_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = l_Lean_ConstantInfo_type(v_info_2272_);
v___x_2279_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(v_typeNameSet_2271_, v___x_2278_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
return v___x_2279_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_0interp(lean_interpreter_value* stack)
{
lean_object* v_typeNameSet_2271_ = stack[0].m_obj;
lean_object* v_info_2272_ = stack[1].m_obj;
lean_object* v_a_2273_ = stack[2].m_obj;
lean_object* v_a_2274_ = stack[3].m_obj;
lean_object* v_a_2275_ = stack[4].m_obj;
lean_object* v_a_2276_ = stack[5].m_obj;
lean_object* v_res_2280_;
v_res_2280_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(v_typeNameSet_2271_, v_info_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
stack->m_obj
 = v_res_2280_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod___boxed(lean_object* v_typeNameSet_2281_, lean_object* v_info_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(v_typeNameSet_2281_, v_info_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
lean_dec_ref(v_info_2282_);
return v_res_2288_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(lean_object* v_matchAlias_2289_, lean_object* v_addAlias_2290_, lean_object* v_alias_2291_, lean_object* v_declNames_2292_, lean_object* v_ns_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v___x_2302_; uint8_t v___x_2303_; 
lean_inc_ref(v_matchAlias_2289_);
lean_inc(v_alias_2291_);
lean_inc(v_ns_2293_);
v___x_2302_ = lean_apply_2(v_matchAlias_2289_, v_ns_2293_, v_alias_2291_);
v___x_2303_ = lean_unbox(v___x_2302_);
if (v___x_2303_ == 0)
{
if (lean_obj_tag(v_ns_2293_) == 1)
{
lean_object* v_pre_2304_; 
v_pre_2304_ = lean_ctor_get(v_ns_2293_, 0);
lean_inc(v_pre_2304_);
lean_dec_ref_known(v_ns_2293_, 2);
v_ns_2293_ = v_pre_2304_;
goto _start;
}
else
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
lean_dec(v_ns_2293_);
lean_dec(v_declNames_2292_);
lean_dec(v_alias_2291_);
lean_dec_ref(v_addAlias_2290_);
lean_dec_ref(v_matchAlias_2289_);
v___x_2306_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
return v___x_2307_;
}
}
else
{
lean_object* v___x_2308_; 
lean_dec(v_ns_2293_);
lean_dec_ref(v_matchAlias_2289_);
lean_inc(v_a_2300_);
lean_inc_ref(v_a_2299_);
lean_inc(v_a_2298_);
lean_inc_ref(v_a_2297_);
lean_inc_ref(v_a_2296_);
lean_inc(v_a_2295_);
lean_inc_ref(v_a_2294_);
v___x_2308_ = lean_apply_10(v_addAlias_2290_, v_alias_2291_, v_declNames_2292_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, lean_box(0));
return v___x_2308_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias_0interp(lean_interpreter_value* stack)
{
lean_object* v_matchAlias_2289_ = stack[0].m_obj;
lean_object* v_addAlias_2290_ = stack[1].m_obj;
lean_object* v_alias_2291_ = stack[2].m_obj;
lean_object* v_declNames_2292_ = stack[3].m_obj;
lean_object* v_ns_2293_ = stack[4].m_obj;
lean_object* v_a_2294_ = stack[5].m_obj;
lean_object* v_a_2295_ = stack[6].m_obj;
lean_object* v_a_2296_ = stack[7].m_obj;
lean_object* v_a_2297_ = stack[8].m_obj;
lean_object* v_a_2298_ = stack[9].m_obj;
lean_object* v_a_2299_ = stack[10].m_obj;
lean_object* v_a_2300_ = stack[11].m_obj;
lean_object* v_res_2309_;
v_res_2309_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(v_matchAlias_2289_, v_addAlias_2290_, v_alias_2291_, v_declNames_2292_, v_ns_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
stack->m_obj
 = v_res_2309_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias___boxed(lean_object* v_matchAlias_2310_, lean_object* v_addAlias_2311_, lean_object* v_alias_2312_, lean_object* v_declNames_2313_, lean_object* v_ns_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(v_matchAlias_2310_, v_addAlias_2311_, v_alias_2312_, v_declNames_2313_, v_ns_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
lean_dec(v_a_2321_);
lean_dec_ref(v_a_2320_);
lean_dec(v_a_2319_);
lean_dec_ref(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
return v_res_2323_;
}
}
lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(lean_object* v_a_2326_){
_start:
{
uint8_t v___x_2328_; 
v___x_2328_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_a_2326_);
if (v___x_2328_ == 0)
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2329_);
return v___x_2330_;
}
else
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = ((lean_object*)(l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg___closed__0));
v___x_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
return v___x_2332_;
}
}
}
LEAN_EXPORT void l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2326_ = stack[0].m_obj;
lean_object* v_res_2333_;
v_res_2333_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v_a_2326_);
stack->m_obj
 = v_res_2333_;
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg___boxed(lean_object* v_a_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v_a_2334_);
lean_dec_ref(v_a_2334_);
return v_res_2336_;
}
}
lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1(lean_object* v_a_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v_a_2337_);
return v___x_2343_;
}
}
LEAN_EXPORT void l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2337_ = stack[0].m_obj;
lean_object* v___y_2338_ = stack[1].m_obj;
lean_object* v___y_2339_ = stack[2].m_obj;
lean_object* v___y_2340_ = stack[3].m_obj;
lean_object* v___y_2341_ = stack[4].m_obj;
lean_object* v_res_2344_;
v_res_2344_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1(v_a_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
stack->m_obj
 = v_res_2344_;
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___boxed(lean_object* v_a_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1(v_a_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec_ref(v_a_2345_);
return v_res_2351_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0(lean_object* v_ctx_2352_, lean_object* v_id_2353_, uint8_t v_danglingDot_2354_, lean_object* v_declName_2355_, lean_object* v_decl_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v___x_2365_; 
lean_inc(v_declName_2355_);
v___x_2365_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(v_ctx_2352_, v_declName_2355_, v_id_2353_, v_danglingDot_2354_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2418_; 
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2368_ = v___x_2365_;
v_isShared_2369_ = v_isSharedCheck_2418_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2365_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2418_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
if (lean_obj_tag(v_a_2366_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2380_; 
lean_dec_ref(v_decl_2356_);
lean_dec(v_declName_2355_);
v_a_2370_ = lean_ctor_get(v_a_2366_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_a_2366_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2372_ = v_a_2366_;
v_isShared_2373_ = v_isSharedCheck_2380_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v_a_2366_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2380_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2377_; 
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v___x_2375_);
v___x_2377_ = v___x_2368_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2375_);
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
else
{
lean_object* v_a_2381_; 
v_a_2381_ = lean_ctor_get(v_a_2366_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v_a_2366_, 1);
if (lean_obj_tag(v_a_2381_) == 1)
{
lean_object* v_val_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2413_; 
lean_del_object(v___x_2368_);
v_val_2382_ = lean_ctor_get(v_a_2381_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_a_2381_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2384_ = v_a_2381_;
v_isShared_2385_ = v_isSharedCheck_2413_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_val_2382_);
lean_dec(v_a_2381_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2413_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v_kind_2386_; lean_object* v_tags_2387_; lean_object* v___x_2388_; 
v_kind_2386_ = lean_ctor_get(v_decl_2356_, 1);
lean_inc_ref(v_kind_2386_);
v_tags_2387_ = lean_ctor_get(v_decl_2356_, 2);
lean_inc_ref(v_tags_2387_);
lean_dec_ref(v_decl_2356_);
lean_inc(v___y_2363_);
lean_inc_ref(v___y_2362_);
lean_inc(v___y_2361_);
lean_inc_ref(v___y_2360_);
v___x_2388_ = lean_apply_5(v_kind_2386_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, lean_box(0));
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2390_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2388_, 1);
lean_inc(v___y_2363_);
lean_inc_ref(v___y_2362_);
lean_inc(v___y_2361_);
lean_inc_ref(v___y_2360_);
v___x_2390_ = lean_apply_5(v_tags_2387_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, lean_box(0));
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2393_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2390_, 1);
if (v_isShared_2385_ == 0)
{
lean_ctor_set_tag(v___x_2384_, 0);
lean_ctor_set(v___x_2384_, 0, v_declName_2355_);
v___x_2393_ = v___x_2384_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_declName_2355_);
v___x_2393_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
uint8_t v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = lean_unbox(v_a_2389_);
lean_dec(v_a_2389_);
v___x_2395_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_val_2382_, v___x_2393_, v___x_2394_, v_a_2391_, v___y_2357_, v___y_2358_);
return v___x_2395_;
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec(v_a_2389_);
lean_del_object(v___x_2384_);
lean_dec(v_val_2382_);
lean_dec(v_declName_2355_);
v_a_2397_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2390_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2390_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec_ref(v_tags_2387_);
lean_del_object(v___x_2384_);
lean_dec(v_val_2382_);
lean_dec(v_declName_2355_);
v_a_2405_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2388_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2388_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
else
{
lean_object* v___x_2414_; lean_object* v___x_2416_; 
lean_dec(v_a_2381_);
lean_dec_ref(v_decl_2356_);
lean_dec(v_declName_2355_);
v___x_2414_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v___x_2414_);
v___x_2416_ = v___x_2368_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_dec_ref(v_decl_2356_);
lean_dec(v_declName_2355_);
v_a_2419_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2365_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2365_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_2352_ = stack[0].m_obj;
lean_object* v_id_2353_ = stack[1].m_obj;
uint8_t v_danglingDot_2354_ = stack[2].m_num;
lean_object* v_declName_2355_ = stack[3].m_obj;
lean_object* v_decl_2356_ = stack[4].m_obj;
lean_object* v___y_2357_ = stack[5].m_obj;
lean_object* v___y_2358_ = stack[6].m_obj;
lean_object* v___y_2359_ = stack[7].m_obj;
lean_object* v___y_2360_ = stack[8].m_obj;
lean_object* v___y_2361_ = stack[9].m_obj;
lean_object* v___y_2362_ = stack[10].m_obj;
lean_object* v___y_2363_ = stack[11].m_obj;
lean_object* v_res_2427_;
v_res_2427_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0(v_ctx_2352_, v_id_2353_, v_danglingDot_2354_, v_declName_2355_, v_decl_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
stack->m_obj
 = v_res_2427_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0___boxed(lean_object* v_ctx_2428_, lean_object* v_id_2429_, lean_object* v_danglingDot_2430_, lean_object* v_declName_2431_, lean_object* v_decl_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
uint8_t v_danglingDot_boxed_2441_; lean_object* v_res_2442_; 
v_danglingDot_boxed_2441_ = lean_unbox(v_danglingDot_2430_);
v_res_2442_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0(v_ctx_2428_, v_id_2429_, v_danglingDot_boxed_2441_, v_declName_2431_, v_decl_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
return v_res_2442_;
}
}
uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1(lean_object* v_id_2443_, uint8_t v_danglingDot_2444_, lean_object* v_ns_2445_, lean_object* v_alias_2446_){
_start:
{
uint8_t v___x_2447_; 
v___x_2447_ = l_Lean_Name_isPrefixOf(v_ns_2445_, v_alias_2446_);
if (v___x_2447_ == 0)
{
lean_dec(v_alias_2446_);
return v___x_2447_;
}
else
{
lean_object* v___x_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; 
v___x_2448_ = lean_box(0);
v___x_2449_ = l_Lean_Name_replacePrefix(v_alias_2446_, v_ns_2445_, v___x_2448_);
v___x_2450_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_2443_, v___x_2449_, v_danglingDot_2444_);
lean_dec(v___x_2449_);
return v___x_2450_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_2443_ = stack[0].m_obj;
uint8_t v_danglingDot_2444_ = stack[1].m_num;
lean_object* v_ns_2445_ = stack[2].m_obj;
lean_object* v_alias_2446_ = stack[3].m_obj;
uint8_t v_res_2451_;
v_res_2451_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1(v_id_2443_, v_danglingDot_2444_, v_ns_2445_, v_alias_2446_);
stack->m_num = v_res_2451_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1___boxed(lean_object* v_id_2452_, lean_object* v_danglingDot_2453_, lean_object* v_ns_2454_, lean_object* v_alias_2455_){
_start:
{
uint8_t v_danglingDot_boxed_2456_; uint8_t v_res_2457_; lean_object* v_r_2458_; 
v_danglingDot_boxed_2456_ = lean_unbox(v_danglingDot_2453_);
v_res_2457_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1(v_id_2452_, v_danglingDot_boxed_2456_, v_ns_2454_, v_alias_2455_);
lean_dec(v_ns_2454_);
lean_dec(v_id_2452_);
v_r_2458_ = lean_box(v_res_2457_);
return v_r_2458_;
}
}
lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(lean_object* v_a_2459_, lean_object* v___x_2460_, lean_object* v_alias_2461_, lean_object* v_as_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
if (lean_obj_tag(v_as_2462_) == 0)
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
lean_dec_ref(v___x_2460_);
v___x_2470_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
return v___x_2471_;
}
else
{
lean_object* v_head_2472_; lean_object* v_tail_2473_; uint8_t v___x_2474_; 
v_head_2472_ = lean_ctor_get(v_as_2462_, 0);
lean_inc_n(v_head_2472_, 2);
v_tail_2473_ = lean_ctor_get(v_as_2462_, 1);
lean_inc(v_tail_2473_);
lean_dec_ref_known(v_as_2462_, 2);
lean_inc_ref(v___x_2460_);
v___x_2474_ = l_Lean_Server_Completion_allowCompletion(v_a_2459_, v___x_2460_, v_head_2472_);
if (v___x_2474_ == 0)
{
lean_dec(v_head_2472_);
v_as_2462_ = v_tail_2473_;
goto _start;
}
else
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2476_ = l_Lean_Name_getString_x21(v_alias_2461_);
v___x_2477_ = lean_box(0);
v___x_2478_ = l_Lean_Name_str___override(v___x_2477_, v___x_2476_);
v___x_2479_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_2478_, v_head_2472_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_dec_ref_known(v___x_2479_, 1);
v_as_2462_ = v_tail_2473_;
goto _start;
}
else
{
lean_dec(v_tail_2473_);
lean_dec_ref(v___x_2460_);
return v___x_2479_;
}
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2459_ = stack[0].m_obj;
lean_object* v___x_2460_ = stack[1].m_obj;
lean_object* v_alias_2461_ = stack[2].m_obj;
lean_object* v_as_2462_ = stack[3].m_obj;
lean_object* v___y_2463_ = stack[4].m_obj;
lean_object* v___y_2464_ = stack[5].m_obj;
lean_object* v___y_2465_ = stack[6].m_obj;
lean_object* v___y_2466_ = stack[7].m_obj;
lean_object* v___y_2467_ = stack[8].m_obj;
lean_object* v___y_2468_ = stack[9].m_obj;
lean_object* v_res_2481_;
v_res_2481_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_2459_, v___x_2460_, v_alias_2461_, v_as_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
stack->m_obj
 = v_res_2481_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg___boxed(lean_object* v_a_2482_, lean_object* v___x_2483_, lean_object* v_alias_2484_, lean_object* v_as_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_2482_, v___x_2483_, v_alias_2484_, v_as_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v_alias_2484_);
lean_dec_ref(v_a_2482_);
return v_res_2493_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2(lean_object* v_a_2494_, lean_object* v_env_2495_, lean_object* v_alias_2496_, lean_object* v_declNames_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v___x_2506_; 
v___x_2506_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_2494_, v_env_2495_, v_alias_2496_, v_declNames_2497_, v___y_2498_, v___y_2499_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2506_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2494_ = stack[0].m_obj;
lean_object* v_env_2495_ = stack[1].m_obj;
lean_object* v_alias_2496_ = stack[2].m_obj;
lean_object* v_declNames_2497_ = stack[3].m_obj;
lean_object* v___y_2498_ = stack[4].m_obj;
lean_object* v___y_2499_ = stack[5].m_obj;
lean_object* v___y_2500_ = stack[6].m_obj;
lean_object* v___y_2501_ = stack[7].m_obj;
lean_object* v___y_2502_ = stack[8].m_obj;
lean_object* v___y_2503_ = stack[9].m_obj;
lean_object* v___y_2504_ = stack[10].m_obj;
lean_object* v_res_2507_;
v_res_2507_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2(v_a_2494_, v_env_2495_, v_alias_2496_, v_declNames_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
stack->m_obj
 = v_res_2507_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2___boxed(lean_object* v_a_2508_, lean_object* v_env_2509_, lean_object* v_alias_2510_, lean_object* v_declNames_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2(v_a_2508_, v_env_2509_, v_alias_2510_, v_declNames_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v_alias_2510_);
lean_dec_ref(v_a_2508_);
return v_res_2520_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3(lean_object* v___f_2521_, lean_object* v___f_2522_, lean_object* v_currNamespace_2523_, lean_object* v_alias_2524_, lean_object* v_declNames_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v___x_2534_; 
v___x_2534_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(v___f_2521_, v___f_2522_, v_alias_2524_, v_declNames_2525_, v_currNamespace_2523_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
return v___x_2534_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2521_ = stack[0].m_obj;
lean_object* v___f_2522_ = stack[1].m_obj;
lean_object* v_currNamespace_2523_ = stack[2].m_obj;
lean_object* v_alias_2524_ = stack[3].m_obj;
lean_object* v_declNames_2525_ = stack[4].m_obj;
lean_object* v___y_2526_ = stack[5].m_obj;
lean_object* v___y_2527_ = stack[6].m_obj;
lean_object* v___y_2528_ = stack[7].m_obj;
lean_object* v___y_2529_ = stack[8].m_obj;
lean_object* v___y_2530_ = stack[9].m_obj;
lean_object* v___y_2531_ = stack[10].m_obj;
lean_object* v___y_2532_ = stack[11].m_obj;
lean_object* v_res_2535_;
v_res_2535_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3(v___f_2521_, v___f_2522_, v_currNamespace_2523_, v_alias_2524_, v_declNames_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
stack->m_obj
 = v_res_2535_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3___boxed(lean_object* v___f_2536_, lean_object* v___f_2537_, lean_object* v_currNamespace_2538_, lean_object* v_alias_2539_, lean_object* v_declNames_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3(v___f_2536_, v___f_2537_, v_currNamespace_2538_, v_alias_2539_, v_declNames_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
return v_res_2549_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(lean_object* v_f_2550_, lean_object* v_x_2551_, lean_object* v_x_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
if (lean_obj_tag(v_x_2552_) == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
lean_dec_ref(v_f_2550_);
v___x_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2561_, 0, v_x_2551_);
v___x_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
return v___x_2562_;
}
else
{
lean_object* v_key_2563_; lean_object* v_value_2564_; lean_object* v_tail_2565_; lean_object* v___x_2566_; 
v_key_2563_ = lean_ctor_get(v_x_2552_, 0);
lean_inc(v_key_2563_);
v_value_2564_ = lean_ctor_get(v_x_2552_, 1);
lean_inc(v_value_2564_);
v_tail_2565_ = lean_ctor_get(v_x_2552_, 2);
lean_inc(v_tail_2565_);
lean_dec_ref_known(v_x_2552_, 3);
lean_inc_ref(v_f_2550_);
lean_inc(v___y_2559_);
lean_inc_ref(v___y_2558_);
lean_inc(v___y_2557_);
lean_inc_ref(v___y_2556_);
lean_inc_ref(v___y_2555_);
lean_inc(v___y_2554_);
lean_inc_ref(v___y_2553_);
v___x_2566_ = lean_apply_10(v_f_2550_, v_key_2563_, v_value_2564_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, lean_box(0));
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
if (lean_obj_tag(v_a_2567_) == 0)
{
lean_dec_ref_known(v_a_2567_, 1);
lean_dec(v_tail_2565_);
lean_dec_ref(v_f_2550_);
return v___x_2566_;
}
else
{
lean_object* v_a_2568_; 
lean_dec_ref_known(v___x_2566_, 1);
v_a_2568_ = lean_ctor_get(v_a_2567_, 0);
lean_inc(v_a_2568_);
lean_dec_ref_known(v_a_2567_, 1);
v_x_2551_ = v_a_2568_;
v_x_2552_ = v_tail_2565_;
goto _start;
}
}
else
{
lean_dec(v_tail_2565_);
lean_dec_ref(v_f_2550_);
return v___x_2566_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2550_ = stack[0].m_obj;
lean_object* v_x_2551_ = stack[1].m_obj;
lean_object* v_x_2552_ = stack[2].m_obj;
lean_object* v___y_2553_ = stack[3].m_obj;
lean_object* v___y_2554_ = stack[4].m_obj;
lean_object* v___y_2555_ = stack[5].m_obj;
lean_object* v___y_2556_ = stack[6].m_obj;
lean_object* v___y_2557_ = stack[7].m_obj;
lean_object* v___y_2558_ = stack[8].m_obj;
lean_object* v___y_2559_ = stack[9].m_obj;
lean_object* v_res_2570_;
v_res_2570_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_f_2550_, v_x_2551_, v_x_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
stack->m_obj
 = v_res_2570_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg___boxed(lean_object* v_f_2571_, lean_object* v_x_2572_, lean_object* v_x_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_f_2571_, v_x_2572_, v_x_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
return v_res_2582_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(lean_object* v_f_2583_, lean_object* v_as_2584_, size_t v_i_2585_, size_t v_stop_2586_, lean_object* v_b_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
uint8_t v___x_2596_; 
v___x_2596_ = lean_usize_dec_eq(v_i_2585_, v_stop_2586_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2597_ = lean_array_uget_borrowed(v_as_2584_, v_i_2585_);
v___x_2598_ = lean_box(0);
lean_inc(v___x_2597_);
lean_inc_ref(v_f_2583_);
v___x_2599_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_f_2583_, v___x_2598_, v___x_2597_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
if (lean_obj_tag(v_a_2600_) == 0)
{
lean_dec_ref(v_f_2583_);
return v___x_2599_;
}
else
{
lean_object* v_a_2601_; size_t v___x_2602_; size_t v___x_2603_; 
lean_inc_ref(v_a_2600_);
lean_dec_ref_known(v___x_2599_, 1);
v_a_2601_ = lean_ctor_get(v_a_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v_a_2600_, 1);
v___x_2602_ = ((size_t)1ULL);
v___x_2603_ = lean_usize_add(v_i_2585_, v___x_2602_);
v_i_2585_ = v___x_2603_;
v_b_2587_ = v_a_2601_;
goto _start;
}
}
else
{
lean_dec_ref(v_f_2583_);
return v___x_2599_;
}
}
else
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
lean_dec_ref(v_f_2583_);
v___x_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2605_, 0, v_b_2587_);
v___x_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
return v___x_2606_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2583_ = stack[0].m_obj;
lean_object* v_as_2584_ = stack[1].m_obj;
size_t v_i_2585_ = stack[2].m_num;
size_t v_stop_2586_ = stack[3].m_num;
lean_object* v_b_2587_ = stack[4].m_obj;
lean_object* v___y_2588_ = stack[5].m_obj;
lean_object* v___y_2589_ = stack[6].m_obj;
lean_object* v___y_2590_ = stack[7].m_obj;
lean_object* v___y_2591_ = stack[8].m_obj;
lean_object* v___y_2592_ = stack[9].m_obj;
lean_object* v___y_2593_ = stack[10].m_obj;
lean_object* v___y_2594_ = stack[11].m_obj;
lean_object* v_res_2607_;
v_res_2607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(v_f_2583_, v_as_2584_, v_i_2585_, v_stop_2586_, v_b_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
stack->m_obj
 = v_res_2607_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg___boxed(lean_object* v_f_2608_, lean_object* v_as_2609_, lean_object* v_i_2610_, lean_object* v_stop_2611_, lean_object* v_b_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
size_t v_i_boxed_2621_; size_t v_stop_boxed_2622_; lean_object* v_res_2623_; 
v_i_boxed_2621_ = lean_unbox_usize(v_i_2610_);
lean_dec(v_i_2610_);
v_stop_boxed_2622_ = lean_unbox_usize(v_stop_2611_);
lean_dec(v_stop_2611_);
v_res_2623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(v_f_2608_, v_as_2609_, v_i_boxed_2621_, v_stop_boxed_2622_, v_b_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec_ref(v_as_2609_);
return v_res_2623_;
}
}
lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0(lean_object* v_f_2624_, lean_object* v_x_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v___x_2636_; 
lean_inc(v___y_2634_);
lean_inc_ref(v___y_2633_);
lean_inc(v___y_2632_);
lean_inc_ref(v___y_2631_);
lean_inc_ref(v___y_2630_);
lean_inc(v___y_2629_);
lean_inc_ref(v___y_2628_);
v___x_2636_ = lean_apply_10(v_f_2624_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, lean_box(0));
return v___x_2636_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2624_ = stack[0].m_obj;
lean_object* v_x_2625_ = stack[1].m_obj;
lean_object* v___y_2626_ = stack[2].m_obj;
lean_object* v___y_2627_ = stack[3].m_obj;
lean_object* v___y_2628_ = stack[4].m_obj;
lean_object* v___y_2629_ = stack[5].m_obj;
lean_object* v___y_2630_ = stack[6].m_obj;
lean_object* v___y_2631_ = stack[7].m_obj;
lean_object* v___y_2632_ = stack[8].m_obj;
lean_object* v___y_2633_ = stack[9].m_obj;
lean_object* v___y_2634_ = stack[10].m_obj;
lean_object* v_res_2637_;
v_res_2637_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0(v_f_2624_, v_x_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
stack->m_obj
 = v_res_2637_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v_f_2638_, lean_object* v_x_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0(v_f_2638_, v_x_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
return v_res_2650_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(lean_object* v_f_2651_, lean_object* v_keys_2652_, lean_object* v_vals_2653_, lean_object* v_i_2654_, lean_object* v_acc_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v___x_2664_; uint8_t v___x_2665_; 
v___x_2664_ = lean_array_get_size(v_keys_2652_);
v___x_2665_ = lean_nat_dec_lt(v_i_2654_, v___x_2664_);
if (v___x_2665_ == 0)
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
lean_dec(v_i_2654_);
lean_dec_ref(v_f_2651_);
v___x_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2666_, 0, v_acc_2655_);
v___x_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2666_);
return v___x_2667_;
}
else
{
lean_object* v_k_2668_; lean_object* v_v_2669_; lean_object* v___x_2670_; 
v_k_2668_ = lean_array_fget_borrowed(v_keys_2652_, v_i_2654_);
v_v_2669_ = lean_array_fget_borrowed(v_vals_2653_, v_i_2654_);
lean_inc_ref(v_f_2651_);
lean_inc(v___y_2662_);
lean_inc_ref(v___y_2661_);
lean_inc(v___y_2660_);
lean_inc_ref(v___y_2659_);
lean_inc_ref(v___y_2658_);
lean_inc(v___y_2657_);
lean_inc_ref(v___y_2656_);
lean_inc(v_v_2669_);
lean_inc(v_k_2668_);
v___x_2670_ = lean_apply_11(v_f_2651_, v_acc_2655_, v_k_2668_, v_v_2669_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, lean_box(0));
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
if (lean_obj_tag(v_a_2671_) == 0)
{
lean_dec_ref_known(v_a_2671_, 1);
lean_dec(v_i_2654_);
lean_dec_ref(v_f_2651_);
return v___x_2670_;
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
lean_dec_ref_known(v___x_2670_, 1);
v_a_2672_ = lean_ctor_get(v_a_2671_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v_a_2671_, 1);
v___x_2673_ = lean_unsigned_to_nat(1u);
v___x_2674_ = lean_nat_add(v_i_2654_, v___x_2673_);
lean_dec(v_i_2654_);
v_i_2654_ = v___x_2674_;
v_acc_2655_ = v_a_2672_;
goto _start;
}
}
else
{
lean_dec(v_i_2654_);
lean_dec_ref(v_f_2651_);
return v___x_2670_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2651_ = stack[0].m_obj;
lean_object* v_keys_2652_ = stack[1].m_obj;
lean_object* v_vals_2653_ = stack[2].m_obj;
lean_object* v_i_2654_ = stack[3].m_obj;
lean_object* v_acc_2655_ = stack[4].m_obj;
lean_object* v___y_2656_ = stack[5].m_obj;
lean_object* v___y_2657_ = stack[6].m_obj;
lean_object* v___y_2658_ = stack[7].m_obj;
lean_object* v___y_2659_ = stack[8].m_obj;
lean_object* v___y_2660_ = stack[9].m_obj;
lean_object* v___y_2661_ = stack[10].m_obj;
lean_object* v___y_2662_ = stack[11].m_obj;
lean_object* v_res_2676_;
v_res_2676_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(v_f_2651_, v_keys_2652_, v_vals_2653_, v_i_2654_, v_acc_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
stack->m_obj
 = v_res_2676_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg___boxed(lean_object* v_f_2677_, lean_object* v_keys_2678_, lean_object* v_vals_2679_, lean_object* v_i_2680_, lean_object* v_acc_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(v_f_2677_, v_keys_2678_, v_vals_2679_, v_i_2680_, v_acc_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec_ref(v_vals_2679_);
lean_dec_ref(v_keys_2678_);
return v_res_2690_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(lean_object* v_f_2691_, lean_object* v_as_2692_, size_t v_i_2693_, size_t v_stop_2694_, lean_object* v_b_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v_a_2705_; lean_object* v___y_2710_; uint8_t v___x_2713_; 
v___x_2713_ = lean_usize_dec_eq(v_i_2693_, v_stop_2694_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; 
v___x_2714_ = lean_array_uget_borrowed(v_as_2692_, v_i_2693_);
switch(lean_obj_tag(v___x_2714_))
{
case 0:
{
lean_object* v_key_2715_; lean_object* v_val_2716_; lean_object* v___x_2717_; 
v_key_2715_ = lean_ctor_get(v___x_2714_, 0);
v_val_2716_ = lean_ctor_get(v___x_2714_, 1);
lean_inc_ref(v_f_2691_);
lean_inc(v___y_2702_);
lean_inc_ref(v___y_2701_);
lean_inc(v___y_2700_);
lean_inc_ref(v___y_2699_);
lean_inc_ref(v___y_2698_);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v_val_2716_);
lean_inc(v_key_2715_);
v___x_2717_ = lean_apply_11(v_f_2691_, v_b_2695_, v_key_2715_, v_val_2716_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, lean_box(0));
v___y_2710_ = v___x_2717_;
goto v___jp_2709_;
}
case 1:
{
lean_object* v_node_2718_; lean_object* v___x_2719_; 
v_node_2718_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_node_2718_);
lean_inc_ref(v_f_2691_);
v___x_2719_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_2691_, v_node_2718_, v_b_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
v___y_2710_ = v___x_2719_;
goto v___jp_2709_;
}
default: 
{
v_a_2705_ = v_b_2695_;
goto v___jp_2704_;
}
}
}
else
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
lean_dec_ref(v_f_2691_);
v___x_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2720_, 0, v_b_2695_);
v___x_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2720_);
return v___x_2721_;
}
v___jp_2704_:
{
size_t v___x_2706_; size_t v___x_2707_; 
v___x_2706_ = ((size_t)1ULL);
v___x_2707_ = lean_usize_add(v_i_2693_, v___x_2706_);
v_i_2693_ = v___x_2707_;
v_b_2695_ = v_a_2705_;
goto _start;
}
v___jp_2709_:
{
if (lean_obj_tag(v___y_2710_) == 0)
{
lean_object* v_a_2711_; 
v_a_2711_ = lean_ctor_get(v___y_2710_, 0);
if (lean_obj_tag(v_a_2711_) == 0)
{
lean_dec_ref(v_f_2691_);
return v___y_2710_;
}
else
{
lean_object* v_a_2712_; 
lean_inc_ref(v_a_2711_);
lean_dec_ref_known(v___y_2710_, 1);
v_a_2712_ = lean_ctor_get(v_a_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v_a_2711_, 1);
v_a_2705_ = v_a_2712_;
goto v___jp_2704_;
}
}
else
{
lean_dec_ref(v_f_2691_);
return v___y_2710_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2691_ = stack[0].m_obj;
lean_object* v_as_2692_ = stack[1].m_obj;
size_t v_i_2693_ = stack[2].m_num;
size_t v_stop_2694_ = stack[3].m_num;
lean_object* v_b_2695_ = stack[4].m_obj;
lean_object* v___y_2696_ = stack[5].m_obj;
lean_object* v___y_2697_ = stack[6].m_obj;
lean_object* v___y_2698_ = stack[7].m_obj;
lean_object* v___y_2699_ = stack[8].m_obj;
lean_object* v___y_2700_ = stack[9].m_obj;
lean_object* v___y_2701_ = stack[10].m_obj;
lean_object* v___y_2702_ = stack[11].m_obj;
lean_object* v_res_2722_;
v_res_2722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(v_f_2691_, v_as_2692_, v_i_2693_, v_stop_2694_, v_b_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
stack->m_obj
 = v_res_2722_;
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(lean_object* v_f_2723_, lean_object* v_x_2724_, lean_object* v_x_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
if (lean_obj_tag(v_x_2724_) == 0)
{
lean_object* v_es_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2748_; 
v_es_2734_ = lean_ctor_get(v_x_2724_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v_x_2724_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2736_ = v_x_2724_;
v_isShared_2737_ = v_isSharedCheck_2748_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_es_2734_);
lean_dec(v_x_2724_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2748_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2738_ = lean_unsigned_to_nat(0u);
v___x_2739_ = lean_array_get_size(v_es_2734_);
v___x_2740_ = lean_nat_dec_lt(v___x_2738_, v___x_2739_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2742_; 
lean_dec_ref(v_es_2734_);
lean_dec_ref(v_f_2723_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set_tag(v___x_2736_, 1);
lean_ctor_set(v___x_2736_, 0, v_x_2725_);
v___x_2742_ = v___x_2736_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_x_2725_);
v___x_2742_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_object* v___x_2743_; 
v___x_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2742_);
return v___x_2743_;
}
}
else
{
size_t v___x_2745_; size_t v___x_2746_; lean_object* v___x_2747_; 
lean_del_object(v___x_2736_);
v___x_2745_ = ((size_t)0ULL);
v___x_2746_ = lean_usize_of_nat(v___x_2739_);
v___x_2747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(v_f_2723_, v_es_2734_, v___x_2745_, v___x_2746_, v_x_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec_ref(v_es_2734_);
return v___x_2747_;
}
}
}
else
{
lean_object* v_ks_2749_; lean_object* v_vs_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v_ks_2749_ = lean_ctor_get(v_x_2724_, 0);
lean_inc_ref(v_ks_2749_);
v_vs_2750_ = lean_ctor_get(v_x_2724_, 1);
lean_inc_ref(v_vs_2750_);
lean_dec_ref_known(v_x_2724_, 2);
v___x_2751_ = lean_unsigned_to_nat(0u);
v___x_2752_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(v_f_2723_, v_ks_2749_, v_vs_2750_, v___x_2751_, v_x_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec_ref(v_vs_2750_);
lean_dec_ref(v_ks_2749_);
return v___x_2752_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2723_ = stack[0].m_obj;
lean_object* v_x_2724_ = stack[1].m_obj;
lean_object* v_x_2725_ = stack[2].m_obj;
lean_object* v___y_2726_ = stack[3].m_obj;
lean_object* v___y_2727_ = stack[4].m_obj;
lean_object* v___y_2728_ = stack[5].m_obj;
lean_object* v___y_2729_ = stack[6].m_obj;
lean_object* v___y_2730_ = stack[7].m_obj;
lean_object* v___y_2731_ = stack[8].m_obj;
lean_object* v___y_2732_ = stack[9].m_obj;
lean_object* v_res_2753_;
v_res_2753_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_2723_, v_x_2724_, v_x_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
stack->m_obj
 = v_res_2753_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg___boxed(lean_object* v_f_2754_, lean_object* v_x_2755_, lean_object* v_x_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_2754_, v_x_2755_, v_x_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg___boxed(lean_object* v_f_2766_, lean_object* v_as_2767_, lean_object* v_i_2768_, lean_object* v_stop_2769_, lean_object* v_b_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
size_t v_i_boxed_2779_; size_t v_stop_boxed_2780_; lean_object* v_res_2781_; 
v_i_boxed_2779_ = lean_unbox_usize(v_i_2768_);
lean_dec(v_i_2768_);
v_stop_boxed_2780_ = lean_unbox_usize(v_stop_2769_);
lean_dec(v_stop_2769_);
v_res_2781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(v_f_2766_, v_as_2767_, v_i_boxed_2779_, v_stop_boxed_2780_, v_b_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec_ref(v_as_2767_);
return v_res_2781_;
}
}
lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(lean_object* v_map_2782_, lean_object* v_f_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v___f_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___f_2792_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2792_, 0, v_f_2783_);
v___x_2793_ = lean_box(0);
v___x_2794_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v___f_2792_, v_map_2782_, v___x_2793_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
return v___x_2794_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_2782_ = stack[0].m_obj;
lean_object* v_f_2783_ = stack[1].m_obj;
lean_object* v___y_2784_ = stack[2].m_obj;
lean_object* v___y_2785_ = stack[3].m_obj;
lean_object* v___y_2786_ = stack[4].m_obj;
lean_object* v___y_2787_ = stack[5].m_obj;
lean_object* v___y_2788_ = stack[6].m_obj;
lean_object* v___y_2789_ = stack[7].m_obj;
lean_object* v___y_2790_ = stack[8].m_obj;
lean_object* v_res_2795_;
v_res_2795_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_2782_, v_f_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
stack->m_obj
 = v_res_2795_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___boxed(lean_object* v_map_2796_, lean_object* v_f_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_2796_, v_f_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
return v_res_2806_;
}
}
lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(lean_object* v_s_2807_, lean_object* v_f_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_map_u2081_2817_; lean_object* v_map_u2082_2818_; lean_object* v_buckets_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; 
v_map_u2081_2817_ = lean_ctor_get(v_s_2807_, 0);
lean_inc_ref(v_map_u2081_2817_);
v_map_u2082_2818_ = lean_ctor_get(v_s_2807_, 1);
lean_inc_ref(v_map_u2082_2818_);
lean_dec_ref(v_s_2807_);
v_buckets_2819_ = lean_ctor_get(v_map_u2081_2817_, 1);
lean_inc_ref(v_buckets_2819_);
lean_dec_ref(v_map_u2081_2817_);
v___x_2820_ = lean_unsigned_to_nat(0u);
v___x_2821_ = lean_array_get_size(v_buckets_2819_);
v___x_2822_ = lean_nat_dec_lt(v___x_2820_, v___x_2821_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; 
lean_dec_ref(v_buckets_2819_);
v___x_2823_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_u2082_2818_, v_f_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
return v___x_2823_;
}
else
{
lean_object* v___x_2824_; size_t v___x_2825_; size_t v___x_2826_; lean_object* v___x_2827_; 
v___x_2824_ = lean_box(0);
v___x_2825_ = ((size_t)0ULL);
v___x_2826_ = lean_usize_of_nat(v___x_2821_);
lean_inc_ref(v_f_2808_);
v___x_2827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(v_f_2808_, v_buckets_2819_, v___x_2825_, v___x_2826_, v___x_2824_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
lean_dec_ref(v_buckets_2819_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
if (lean_obj_tag(v_a_2828_) == 0)
{
lean_dec_ref(v_map_u2082_2818_);
lean_dec_ref(v_f_2808_);
return v___x_2827_;
}
else
{
lean_object* v___x_2829_; 
lean_dec_ref_known(v___x_2827_, 1);
v___x_2829_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_u2082_2818_, v_f_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
return v___x_2829_;
}
}
else
{
lean_dec_ref(v_map_u2082_2818_);
lean_dec_ref(v_f_2808_);
return v___x_2827_;
}
}
}
}
LEAN_EXPORT void l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2807_ = stack[0].m_obj;
lean_object* v_f_2808_ = stack[1].m_obj;
lean_object* v___y_2809_ = stack[2].m_obj;
lean_object* v___y_2810_ = stack[3].m_obj;
lean_object* v___y_2811_ = stack[4].m_obj;
lean_object* v___y_2812_ = stack[5].m_obj;
lean_object* v___y_2813_ = stack[6].m_obj;
lean_object* v___y_2814_ = stack[7].m_obj;
lean_object* v___y_2815_ = stack[8].m_obj;
lean_object* v_res_2830_;
v_res_2830_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v_s_2807_, v_f_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
stack->m_obj
 = v_res_2830_;
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg___boxed(lean_object* v_s_2831_, lean_object* v_f_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v_s_2831_, v_f_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
return v_res_2841_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0(lean_object* v_f_2842_, lean_object* v_decl_2843_, lean_object* v_ci_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v___y_2855_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; uint8_t v___x_2896_; 
v___x_2893_ = lean_unsigned_to_nat(1u);
v___x_2894_ = lean_nat_add(v___y_2845_, v___x_2893_);
v___x_2895_ = lean_unsigned_to_nat(10000u);
v___x_2896_ = lean_nat_dec_le(v___x_2895_, v___x_2894_);
if (v___x_2896_ == 0)
{
v___y_2855_ = v___x_2894_;
goto v___jp_2854_;
}
else
{
lean_object* v___x_2897_; lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2914_; 
lean_dec(v___x_2894_);
v___x_2897_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v___y_2848_);
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2900_ = v___x_2897_;
v_isShared_2901_ = v_isSharedCheck_2914_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2897_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2914_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
if (lean_obj_tag(v_a_2898_) == 0)
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2912_; 
lean_dec_ref(v_ci_2844_);
lean_dec(v_decl_2843_);
lean_dec_ref(v_f_2842_);
v_a_2902_ = lean_ctor_get(v_a_2898_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v_a_2898_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2904_ = v_a_2898_;
v_isShared_2905_ = v_isSharedCheck_2912_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v_a_2898_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2912_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2902_);
v___x_2907_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
lean_object* v___x_2909_; 
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 0, v___x_2907_);
v___x_2909_ = v___x_2900_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2907_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
else
{
lean_object* v___x_2913_; 
lean_dec_ref_known(v_a_2898_, 1);
lean_del_object(v___x_2900_);
v___x_2913_ = lean_unsigned_to_nat(0u);
v___y_2855_ = v___x_2913_;
goto v___jp_2854_;
}
}
}
v___jp_2854_:
{
lean_object* v___x_2856_; 
lean_inc(v___y_2852_);
lean_inc_ref(v___y_2851_);
lean_inc(v___y_2850_);
lean_inc_ref(v___y_2849_);
lean_inc_ref(v___y_2848_);
lean_inc(v___y_2847_);
lean_inc_ref(v___y_2846_);
v___x_2856_ = lean_apply_10(v_f_2842_, v_decl_2843_, v_ci_2844_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, lean_box(0));
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2884_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2859_ = v___x_2856_;
v_isShared_2860_ = v_isSharedCheck_2884_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2856_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2884_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
if (lean_obj_tag(v_a_2857_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2871_; 
lean_dec(v___y_2855_);
v_a_2861_ = lean_ctor_get(v_a_2857_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_a_2857_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2863_ = v_a_2857_;
v_isShared_2864_ = v_isSharedCheck_2871_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v_a_2857_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2871_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v___x_2868_; 
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v___x_2866_);
v___x_2868_ = v___x_2859_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2866_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2883_; 
v_a_2872_ = lean_ctor_get(v_a_2857_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v_a_2857_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2874_ = v_a_2857_;
v_isShared_2875_ = v_isSharedCheck_2883_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v_a_2857_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2883_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2876_; lean_object* v___x_2878_; 
v___x_2876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2876_, 0, v_a_2872_);
lean_ctor_set(v___x_2876_, 1, v___y_2855_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v___x_2876_);
v___x_2878_ = v___x_2874_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
lean_object* v___x_2880_; 
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v___x_2878_);
v___x_2880_ = v___x_2859_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2878_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
}
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
lean_dec(v___y_2855_);
v_a_2885_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2856_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2856_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2842_ = stack[0].m_obj;
lean_object* v_decl_2843_ = stack[1].m_obj;
lean_object* v_ci_2844_ = stack[2].m_obj;
lean_object* v___y_2845_ = stack[3].m_obj;
lean_object* v___y_2846_ = stack[4].m_obj;
lean_object* v___y_2847_ = stack[5].m_obj;
lean_object* v___y_2848_ = stack[6].m_obj;
lean_object* v___y_2849_ = stack[7].m_obj;
lean_object* v___y_2850_ = stack[8].m_obj;
lean_object* v___y_2851_ = stack[9].m_obj;
lean_object* v___y_2852_ = stack[10].m_obj;
lean_object* v_res_2915_;
v_res_2915_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0(v_f_2842_, v_decl_2843_, v_ci_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
stack->m_obj
 = v_res_2915_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0___boxed(lean_object* v_f_2916_, lean_object* v_decl_2917_, lean_object* v_ci_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0(v_f_2916_, v_decl_2917_, v_ci_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
return v_res_2928_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(lean_object* v_f_2929_, lean_object* v_keys_2930_, lean_object* v_vals_2931_, lean_object* v_i_2932_, lean_object* v_acc_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v___x_2943_; uint8_t v___x_2944_; 
v___x_2943_ = lean_array_get_size(v_keys_2930_);
v___x_2944_ = lean_nat_dec_lt(v_i_2932_, v___x_2943_);
if (v___x_2944_ == 0)
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
lean_dec(v_i_2932_);
lean_dec_ref(v_f_2929_);
v___x_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2945_, 0, v_acc_2933_);
lean_ctor_set(v___x_2945_, 1, v___y_2934_);
v___x_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
v___x_2947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
return v___x_2947_;
}
else
{
lean_object* v_k_2948_; lean_object* v_v_2949_; lean_object* v___x_2950_; 
v_k_2948_ = lean_array_fget_borrowed(v_keys_2930_, v_i_2932_);
v_v_2949_ = lean_array_fget_borrowed(v_vals_2931_, v_i_2932_);
lean_inc_ref(v_f_2929_);
lean_inc(v___y_2941_);
lean_inc_ref(v___y_2940_);
lean_inc(v___y_2939_);
lean_inc_ref(v___y_2938_);
lean_inc_ref(v___y_2937_);
lean_inc(v___y_2936_);
lean_inc_ref(v___y_2935_);
lean_inc(v_v_2949_);
lean_inc(v_k_2948_);
v___x_2950_ = lean_apply_12(v_f_2929_, v_acc_2933_, v_k_2948_, v_v_2949_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, lean_box(0));
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_a_2951_);
if (lean_obj_tag(v_a_2951_) == 0)
{
lean_dec_ref_known(v_a_2951_, 1);
lean_dec(v_i_2932_);
lean_dec_ref(v_f_2929_);
return v___x_2950_;
}
else
{
lean_object* v_a_2952_; lean_object* v_fst_2953_; lean_object* v_snd_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
lean_dec_ref_known(v___x_2950_, 1);
v_a_2952_ = lean_ctor_get(v_a_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref_known(v_a_2951_, 1);
v_fst_2953_ = lean_ctor_get(v_a_2952_, 0);
lean_inc(v_fst_2953_);
v_snd_2954_ = lean_ctor_get(v_a_2952_, 1);
lean_inc(v_snd_2954_);
lean_dec(v_a_2952_);
v___x_2955_ = lean_unsigned_to_nat(1u);
v___x_2956_ = lean_nat_add(v_i_2932_, v___x_2955_);
lean_dec(v_i_2932_);
v_i_2932_ = v___x_2956_;
v_acc_2933_ = v_fst_2953_;
v___y_2934_ = v_snd_2954_;
goto _start;
}
}
else
{
lean_dec(v_i_2932_);
lean_dec_ref(v_f_2929_);
return v___x_2950_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2929_ = stack[0].m_obj;
lean_object* v_keys_2930_ = stack[1].m_obj;
lean_object* v_vals_2931_ = stack[2].m_obj;
lean_object* v_i_2932_ = stack[3].m_obj;
lean_object* v_acc_2933_ = stack[4].m_obj;
lean_object* v___y_2934_ = stack[5].m_obj;
lean_object* v___y_2935_ = stack[6].m_obj;
lean_object* v___y_2936_ = stack[7].m_obj;
lean_object* v___y_2937_ = stack[8].m_obj;
lean_object* v___y_2938_ = stack[9].m_obj;
lean_object* v___y_2939_ = stack[10].m_obj;
lean_object* v___y_2940_ = stack[11].m_obj;
lean_object* v___y_2941_ = stack[12].m_obj;
lean_object* v_res_2958_;
v_res_2958_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(v_f_2929_, v_keys_2930_, v_vals_2931_, v_i_2932_, v_acc_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
stack->m_obj
 = v_res_2958_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg___boxed(lean_object* v_f_2959_, lean_object* v_keys_2960_, lean_object* v_vals_2961_, lean_object* v_i_2962_, lean_object* v_acc_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(v_f_2959_, v_keys_2960_, v_vals_2961_, v_i_2962_, v_acc_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec_ref(v_vals_2961_);
lean_dec_ref(v_keys_2960_);
return v_res_2973_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(lean_object* v_f_2974_, lean_object* v_as_2975_, size_t v_i_2976_, size_t v_stop_2977_, lean_object* v_b_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v_fst_2989_; lean_object* v_snd_2990_; lean_object* v___y_2995_; uint8_t v___x_3000_; 
v___x_3000_ = lean_usize_dec_eq(v_i_2976_, v_stop_2977_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; 
v___x_3001_ = lean_array_uget_borrowed(v_as_2975_, v_i_2976_);
switch(lean_obj_tag(v___x_3001_))
{
case 0:
{
lean_object* v_key_3002_; lean_object* v_val_3003_; lean_object* v___x_3004_; 
v_key_3002_ = lean_ctor_get(v___x_3001_, 0);
v_val_3003_ = lean_ctor_get(v___x_3001_, 1);
lean_inc_ref(v_f_2974_);
lean_inc(v___y_2986_);
lean_inc_ref(v___y_2985_);
lean_inc(v___y_2984_);
lean_inc_ref(v___y_2983_);
lean_inc_ref(v___y_2982_);
lean_inc(v___y_2981_);
lean_inc_ref(v___y_2980_);
lean_inc(v_val_3003_);
lean_inc(v_key_3002_);
v___x_3004_ = lean_apply_12(v_f_2974_, v_b_2978_, v_key_3002_, v_val_3003_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, lean_box(0));
v___y_2995_ = v___x_3004_;
goto v___jp_2994_;
}
case 1:
{
lean_object* v_node_3005_; lean_object* v___x_3006_; 
v_node_3005_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_node_3005_);
lean_inc_ref(v_f_2974_);
v___x_3006_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_2974_, v_node_3005_, v_b_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
v___y_2995_ = v___x_3006_;
goto v___jp_2994_;
}
default: 
{
v_fst_2989_ = v_b_2978_;
v_snd_2990_ = v___y_2979_;
goto v___jp_2988_;
}
}
}
else
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
lean_dec_ref(v_f_2974_);
v___x_3007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3007_, 0, v_b_2978_);
lean_ctor_set(v___x_3007_, 1, v___y_2979_);
v___x_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
v___x_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3008_);
return v___x_3009_;
}
v___jp_2988_:
{
size_t v___x_2991_; size_t v___x_2992_; 
v___x_2991_ = ((size_t)1ULL);
v___x_2992_ = lean_usize_add(v_i_2976_, v___x_2991_);
v_i_2976_ = v___x_2992_;
v_b_2978_ = v_fst_2989_;
v___y_2979_ = v_snd_2990_;
goto _start;
}
v___jp_2994_:
{
if (lean_obj_tag(v___y_2995_) == 0)
{
lean_object* v_a_2996_; 
v_a_2996_ = lean_ctor_get(v___y_2995_, 0);
if (lean_obj_tag(v_a_2996_) == 0)
{
lean_dec_ref(v_f_2974_);
return v___y_2995_;
}
else
{
lean_object* v_a_2997_; lean_object* v_fst_2998_; lean_object* v_snd_2999_; 
lean_inc_ref(v_a_2996_);
lean_dec_ref_known(v___y_2995_, 1);
v_a_2997_ = lean_ctor_get(v_a_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v_a_2996_, 1);
v_fst_2998_ = lean_ctor_get(v_a_2997_, 0);
lean_inc(v_fst_2998_);
v_snd_2999_ = lean_ctor_get(v_a_2997_, 1);
lean_inc(v_snd_2999_);
lean_dec(v_a_2997_);
v_fst_2989_ = v_fst_2998_;
v_snd_2990_ = v_snd_2999_;
goto v___jp_2988_;
}
}
else
{
lean_dec_ref(v_f_2974_);
return v___y_2995_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2974_ = stack[0].m_obj;
lean_object* v_as_2975_ = stack[1].m_obj;
size_t v_i_2976_ = stack[2].m_num;
size_t v_stop_2977_ = stack[3].m_num;
lean_object* v_b_2978_ = stack[4].m_obj;
lean_object* v___y_2979_ = stack[5].m_obj;
lean_object* v___y_2980_ = stack[6].m_obj;
lean_object* v___y_2981_ = stack[7].m_obj;
lean_object* v___y_2982_ = stack[8].m_obj;
lean_object* v___y_2983_ = stack[9].m_obj;
lean_object* v___y_2984_ = stack[10].m_obj;
lean_object* v___y_2985_ = stack[11].m_obj;
lean_object* v___y_2986_ = stack[12].m_obj;
lean_object* v_res_3010_;
v_res_3010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(v_f_2974_, v_as_2975_, v_i_2976_, v_stop_2977_, v_b_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
stack->m_obj
 = v_res_3010_;
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(lean_object* v_f_3011_, lean_object* v_x_3012_, lean_object* v_x_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
if (lean_obj_tag(v_x_3012_) == 0)
{
lean_object* v_es_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3038_; 
v_es_3023_ = lean_ctor_get(v_x_3012_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v_x_3012_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3025_ = v_x_3012_;
v_isShared_3026_ = v_isSharedCheck_3038_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_es_3023_);
lean_dec(v_x_3012_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3038_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; uint8_t v___x_3029_; 
v___x_3027_ = lean_unsigned_to_nat(0u);
v___x_3028_ = lean_array_get_size(v_es_3023_);
v___x_3029_ = lean_nat_dec_lt(v___x_3027_, v___x_3028_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; lean_object* v___x_3032_; 
lean_dec_ref(v_es_3023_);
lean_dec_ref(v_f_3011_);
v___x_3030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3030_, 0, v_x_3013_);
lean_ctor_set(v___x_3030_, 1, v___y_3014_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set_tag(v___x_3025_, 1);
lean_ctor_set(v___x_3025_, 0, v___x_3030_);
v___x_3032_ = v___x_3025_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3030_);
v___x_3032_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
lean_object* v___x_3033_; 
v___x_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
return v___x_3033_;
}
}
else
{
size_t v___x_3035_; size_t v___x_3036_; lean_object* v___x_3037_; 
lean_del_object(v___x_3025_);
v___x_3035_ = ((size_t)0ULL);
v___x_3036_ = lean_usize_of_nat(v___x_3028_);
v___x_3037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(v_f_3011_, v_es_3023_, v___x_3035_, v___x_3036_, v_x_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
lean_dec_ref(v_es_3023_);
return v___x_3037_;
}
}
}
else
{
lean_object* v_ks_3039_; lean_object* v_vs_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v_ks_3039_ = lean_ctor_get(v_x_3012_, 0);
lean_inc_ref(v_ks_3039_);
v_vs_3040_ = lean_ctor_get(v_x_3012_, 1);
lean_inc_ref(v_vs_3040_);
lean_dec_ref_known(v_x_3012_, 2);
v___x_3041_ = lean_unsigned_to_nat(0u);
v___x_3042_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(v_f_3011_, v_ks_3039_, v_vs_3040_, v___x_3041_, v_x_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
lean_dec_ref(v_vs_3040_);
lean_dec_ref(v_ks_3039_);
return v___x_3042_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3011_ = stack[0].m_obj;
lean_object* v_x_3012_ = stack[1].m_obj;
lean_object* v_x_3013_ = stack[2].m_obj;
lean_object* v___y_3014_ = stack[3].m_obj;
lean_object* v___y_3015_ = stack[4].m_obj;
lean_object* v___y_3016_ = stack[5].m_obj;
lean_object* v___y_3017_ = stack[6].m_obj;
lean_object* v___y_3018_ = stack[7].m_obj;
lean_object* v___y_3019_ = stack[8].m_obj;
lean_object* v___y_3020_ = stack[9].m_obj;
lean_object* v___y_3021_ = stack[10].m_obj;
lean_object* v_res_3043_;
v_res_3043_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_3011_, v_x_3012_, v_x_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
stack->m_obj
 = v_res_3043_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg___boxed(lean_object* v_f_3044_, lean_object* v_x_3045_, lean_object* v_x_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_3044_, v_x_3045_, v_x_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg___boxed(lean_object* v_f_3057_, lean_object* v_as_3058_, lean_object* v_i_3059_, lean_object* v_stop_3060_, lean_object* v_b_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
size_t v_i_boxed_3071_; size_t v_stop_boxed_3072_; lean_object* v_res_3073_; 
v_i_boxed_3071_ = lean_unbox_usize(v_i_3059_);
lean_dec(v_i_3059_);
v_stop_boxed_3072_ = lean_unbox_usize(v_stop_3060_);
lean_dec(v_stop_3060_);
v_res_3073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(v_f_3057_, v_as_3058_, v_i_boxed_3071_, v_stop_boxed_3072_, v_b_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec_ref(v_as_3058_);
return v_res_3073_;
}
}
lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_f_3074_, lean_object* v_x_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v___x_3087_; 
lean_inc(v___y_3085_);
lean_inc_ref(v___y_3084_);
lean_inc(v___y_3083_);
lean_inc_ref(v___y_3082_);
lean_inc_ref(v___y_3081_);
lean_inc(v___y_3080_);
lean_inc_ref(v___y_3079_);
v___x_3087_ = lean_apply_11(v_f_3074_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, lean_box(0));
return v___x_3087_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3074_ = stack[0].m_obj;
lean_object* v_x_3075_ = stack[1].m_obj;
lean_object* v___y_3076_ = stack[2].m_obj;
lean_object* v___y_3077_ = stack[3].m_obj;
lean_object* v___y_3078_ = stack[4].m_obj;
lean_object* v___y_3079_ = stack[5].m_obj;
lean_object* v___y_3080_ = stack[6].m_obj;
lean_object* v___y_3081_ = stack[7].m_obj;
lean_object* v___y_3082_ = stack[8].m_obj;
lean_object* v___y_3083_ = stack[9].m_obj;
lean_object* v___y_3084_ = stack[10].m_obj;
lean_object* v___y_3085_ = stack[11].m_obj;
lean_object* v_res_3088_;
v_res_3088_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0(v_f_3074_, v_x_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
stack->m_obj
 = v_res_3088_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_f_3089_, lean_object* v_x_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0(v_f_3089_, v_x_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
return v_res_3102_;
}
}
lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(lean_object* v_map_3103_, lean_object* v_f_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v___f_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___f_3114_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3114_, 0, v_f_3104_);
v___x_3115_ = lean_box(0);
v___x_3116_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v___f_3114_, v_map_3103_, v___x_3115_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
return v___x_3116_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_3103_ = stack[0].m_obj;
lean_object* v_f_3104_ = stack[1].m_obj;
lean_object* v___y_3105_ = stack[2].m_obj;
lean_object* v___y_3106_ = stack[3].m_obj;
lean_object* v___y_3107_ = stack[4].m_obj;
lean_object* v___y_3108_ = stack[5].m_obj;
lean_object* v___y_3109_ = stack[6].m_obj;
lean_object* v___y_3110_ = stack[7].m_obj;
lean_object* v___y_3111_ = stack[8].m_obj;
lean_object* v___y_3112_ = stack[9].m_obj;
lean_object* v_res_3117_;
v_res_3117_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_3103_, v_f_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
stack->m_obj
 = v_res_3117_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_map_3118_, lean_object* v_f_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_3118_, v_f_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
return v_res_3129_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(lean_object* v_f_3130_, lean_object* v_x_3131_, lean_object* v_x_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
if (lean_obj_tag(v_x_3132_) == 0)
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
lean_dec_ref(v_f_3130_);
v___x_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3142_, 0, v_x_3131_);
lean_ctor_set(v___x_3142_, 1, v___y_3133_);
v___x_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
v___x_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
return v___x_3144_;
}
else
{
lean_object* v_key_3145_; lean_object* v_value_3146_; lean_object* v_tail_3147_; lean_object* v___x_3148_; 
v_key_3145_ = lean_ctor_get(v_x_3132_, 0);
lean_inc(v_key_3145_);
v_value_3146_ = lean_ctor_get(v_x_3132_, 1);
lean_inc(v_value_3146_);
v_tail_3147_ = lean_ctor_get(v_x_3132_, 2);
lean_inc(v_tail_3147_);
lean_dec_ref_known(v_x_3132_, 3);
lean_inc_ref(v_f_3130_);
lean_inc(v___y_3140_);
lean_inc_ref(v___y_3139_);
lean_inc(v___y_3138_);
lean_inc_ref(v___y_3137_);
lean_inc_ref(v___y_3136_);
lean_inc(v___y_3135_);
lean_inc_ref(v___y_3134_);
v___x_3148_ = lean_apply_11(v_f_3130_, v_key_3145_, v_value_3146_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, lean_box(0));
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; 
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_a_3149_);
if (lean_obj_tag(v_a_3149_) == 0)
{
lean_dec_ref_known(v_a_3149_, 1);
lean_dec(v_tail_3147_);
lean_dec_ref(v_f_3130_);
return v___x_3148_;
}
else
{
lean_object* v_a_3150_; lean_object* v_fst_3151_; lean_object* v_snd_3152_; 
lean_dec_ref_known(v___x_3148_, 1);
v_a_3150_ = lean_ctor_get(v_a_3149_, 0);
lean_inc(v_a_3150_);
lean_dec_ref_known(v_a_3149_, 1);
v_fst_3151_ = lean_ctor_get(v_a_3150_, 0);
lean_inc(v_fst_3151_);
v_snd_3152_ = lean_ctor_get(v_a_3150_, 1);
lean_inc(v_snd_3152_);
lean_dec(v_a_3150_);
v_x_3131_ = v_fst_3151_;
v_x_3132_ = v_tail_3147_;
v___y_3133_ = v_snd_3152_;
goto _start;
}
}
else
{
lean_dec(v_tail_3147_);
lean_dec_ref(v_f_3130_);
return v___x_3148_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3130_ = stack[0].m_obj;
lean_object* v_x_3131_ = stack[1].m_obj;
lean_object* v_x_3132_ = stack[2].m_obj;
lean_object* v___y_3133_ = stack[3].m_obj;
lean_object* v___y_3134_ = stack[4].m_obj;
lean_object* v___y_3135_ = stack[5].m_obj;
lean_object* v___y_3136_ = stack[6].m_obj;
lean_object* v___y_3137_ = stack[7].m_obj;
lean_object* v___y_3138_ = stack[8].m_obj;
lean_object* v___y_3139_ = stack[9].m_obj;
lean_object* v___y_3140_ = stack[10].m_obj;
lean_object* v_res_3154_;
v_res_3154_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(v_f_3130_, v_x_3131_, v_x_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
stack->m_obj
 = v_res_3154_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_f_3155_, lean_object* v_x_3156_, lean_object* v_x_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(v_f_3155_, v_x_3156_, v_x_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
return v_res_3167_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(lean_object* v_f_3168_, lean_object* v_as_3169_, size_t v_i_3170_, size_t v_stop_3171_, lean_object* v_b_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
uint8_t v___x_3182_; 
v___x_3182_ = lean_usize_dec_eq(v_i_3170_, v_stop_3171_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3183_ = lean_array_uget_borrowed(v_as_3169_, v_i_3170_);
v___x_3184_ = lean_box(0);
lean_inc(v___x_3183_);
lean_inc_ref(v_f_3168_);
v___x_3185_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(v_f_3168_, v___x_3184_, v___x_3183_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
if (lean_obj_tag(v_a_3186_) == 0)
{
lean_dec_ref(v_f_3168_);
return v___x_3185_;
}
else
{
lean_object* v_a_3187_; lean_object* v_fst_3188_; lean_object* v_snd_3189_; size_t v___x_3190_; size_t v___x_3191_; 
lean_inc_ref(v_a_3186_);
lean_dec_ref_known(v___x_3185_, 1);
v_a_3187_ = lean_ctor_get(v_a_3186_, 0);
lean_inc(v_a_3187_);
lean_dec_ref_known(v_a_3186_, 1);
v_fst_3188_ = lean_ctor_get(v_a_3187_, 0);
lean_inc(v_fst_3188_);
v_snd_3189_ = lean_ctor_get(v_a_3187_, 1);
lean_inc(v_snd_3189_);
lean_dec(v_a_3187_);
v___x_3190_ = ((size_t)1ULL);
v___x_3191_ = lean_usize_add(v_i_3170_, v___x_3190_);
v_i_3170_ = v___x_3191_;
v_b_3172_ = v_fst_3188_;
v___y_3173_ = v_snd_3189_;
goto _start;
}
}
else
{
lean_dec_ref(v_f_3168_);
return v___x_3185_;
}
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
lean_dec_ref(v_f_3168_);
v___x_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3193_, 0, v_b_3172_);
lean_ctor_set(v___x_3193_, 1, v___y_3173_);
v___x_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3193_);
v___x_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3194_);
return v___x_3195_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3168_ = stack[0].m_obj;
lean_object* v_as_3169_ = stack[1].m_obj;
size_t v_i_3170_ = stack[2].m_num;
size_t v_stop_3171_ = stack[3].m_num;
lean_object* v_b_3172_ = stack[4].m_obj;
lean_object* v___y_3173_ = stack[5].m_obj;
lean_object* v___y_3174_ = stack[6].m_obj;
lean_object* v___y_3175_ = stack[7].m_obj;
lean_object* v___y_3176_ = stack[8].m_obj;
lean_object* v___y_3177_ = stack[9].m_obj;
lean_object* v___y_3178_ = stack[10].m_obj;
lean_object* v___y_3179_ = stack[11].m_obj;
lean_object* v___y_3180_ = stack[12].m_obj;
lean_object* v_res_3196_;
v_res_3196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(v_f_3168_, v_as_3169_, v_i_3170_, v_stop_3171_, v_b_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
stack->m_obj
 = v_res_3196_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4___boxed(lean_object* v_f_3197_, lean_object* v_as_3198_, lean_object* v_i_3199_, lean_object* v_stop_3200_, lean_object* v_b_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
size_t v_i_boxed_3211_; size_t v_stop_boxed_3212_; lean_object* v_res_3213_; 
v_i_boxed_3211_ = lean_unbox_usize(v_i_3199_);
lean_dec(v_i_3199_);
v_stop_boxed_3212_ = lean_unbox_usize(v_stop_3200_);
lean_dec(v_stop_3200_);
v_res_3213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(v_f_3197_, v_as_3198_, v_i_boxed_3211_, v_stop_boxed_3212_, v_b_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec_ref(v_as_3198_);
return v_res_3213_;
}
}
lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0(lean_object* v_env_3214_, lean_object* v_f_3215_, lean_object* v_name_3216_, lean_object* v_c_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
uint8_t v___x_3227_; 
lean_inc(v_name_3216_);
v___x_3227_ = l_Lean_Meta_allowCompletion(v_env_3214_, v_name_3216_);
if (v___x_3227_ == 0)
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
lean_dec_ref(v_c_3217_);
lean_dec(v_name_3216_);
lean_dec_ref(v_f_3215_);
v___x_3228_ = lean_box(0);
v___x_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
lean_ctor_set(v___x_3229_, 1, v___y_3218_);
v___x_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
v___x_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
return v___x_3231_;
}
else
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
lean_inc_ref(v_c_3217_);
v___x_3232_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_getCompletionKindForDecl___boxed), 6, 1);
lean_closure_set(v___x_3232_, 0, v_c_3217_);
lean_inc(v_name_3216_);
v___x_3233_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_getCompletionTagsForDecl___boxed), 6, 1);
lean_closure_set(v___x_3233_, 0, v_name_3216_);
v___x_3234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3234_, 0, v_c_3217_);
lean_ctor_set(v___x_3234_, 1, v___x_3232_);
lean_ctor_set(v___x_3234_, 2, v___x_3233_);
lean_inc(v___y_3225_);
lean_inc_ref(v___y_3224_);
lean_inc(v___y_3223_);
lean_inc_ref(v___y_3222_);
lean_inc_ref(v___y_3221_);
lean_inc(v___y_3220_);
lean_inc_ref(v___y_3219_);
v___x_3235_ = lean_apply_11(v_f_3215_, v_name_3216_, v___x_3234_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, lean_box(0));
return v___x_3235_;
}
}
}
LEAN_EXPORT void l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_3214_ = stack[0].m_obj;
lean_object* v_f_3215_ = stack[1].m_obj;
lean_object* v_name_3216_ = stack[2].m_obj;
lean_object* v_c_3217_ = stack[3].m_obj;
lean_object* v___y_3218_ = stack[4].m_obj;
lean_object* v___y_3219_ = stack[5].m_obj;
lean_object* v___y_3220_ = stack[6].m_obj;
lean_object* v___y_3221_ = stack[7].m_obj;
lean_object* v___y_3222_ = stack[8].m_obj;
lean_object* v___y_3223_ = stack[9].m_obj;
lean_object* v___y_3224_ = stack[10].m_obj;
lean_object* v___y_3225_ = stack[11].m_obj;
lean_object* v_res_3236_;
v_res_3236_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0(v_env_3214_, v_f_3215_, v_name_3216_, v_c_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
stack->m_obj
 = v_res_3236_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0___boxed(lean_object* v_env_3237_, lean_object* v_f_3238_, lean_object* v_name_3239_, lean_object* v_c_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0(v_env_3237_, v_f_3238_, v_name_3239_, v_c_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
return v_res_3250_;
}
}
lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(lean_object* v_f_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
lean_object* v___x_3261_; lean_object* v_env_3262_; lean_object* v___f_3263_; lean_object* v___x_3264_; 
v___x_3261_ = lean_st_ref_get(v___y_3259_);
v_env_3262_ = lean_ctor_get(v___x_3261_, 0);
lean_inc_ref_n(v_env_3262_, 3);
lean_dec(v___x_3261_);
lean_inc_ref(v_f_3251_);
v___f_3263_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0___boxed), 13, 2);
lean_closure_set(v___f_3263_, 0, v_env_3262_);
lean_closure_set(v___f_3263_, 1, v_f_3251_);
v___x_3264_ = l_Lean_Server_Completion_getEligibleHeaderDecls(v_env_3262_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v_a_3265_; lean_object* v_buckets_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; uint8_t v___x_3269_; 
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_a_3265_);
lean_dec_ref_known(v___x_3264_, 1);
v_buckets_3266_ = lean_ctor_get(v_a_3265_, 1);
lean_inc_ref(v_buckets_3266_);
lean_dec(v_a_3265_);
v___x_3267_ = lean_unsigned_to_nat(0u);
v___x_3268_ = lean_array_get_size(v_buckets_3266_);
v___x_3269_ = lean_nat_dec_lt(v___x_3267_, v___x_3268_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; lean_object* v_map_u2082_3271_; lean_object* v___x_3272_; 
lean_dec_ref(v_buckets_3266_);
lean_dec_ref(v_f_3251_);
v___x_3270_ = l_Lean_Environment_constants(v_env_3262_);
v_map_u2082_3271_ = lean_ctor_get(v___x_3270_, 1);
lean_inc_ref(v_map_u2082_3271_);
lean_dec_ref(v___x_3270_);
v___x_3272_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_u2082_3271_, v___f_3263_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
return v___x_3272_;
}
else
{
lean_object* v___x_3273_; size_t v___x_3274_; size_t v___x_3275_; lean_object* v___x_3276_; 
v___x_3273_ = lean_box(0);
v___x_3274_ = ((size_t)0ULL);
v___x_3275_ = lean_usize_of_nat(v___x_3268_);
v___x_3276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(v_f_3251_, v_buckets_3266_, v___x_3274_, v___x_3275_, v___x_3273_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
lean_dec_ref(v_buckets_3266_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
if (lean_obj_tag(v_a_3277_) == 0)
{
lean_dec_ref(v___f_3263_);
lean_dec_ref(v_env_3262_);
return v___x_3276_;
}
else
{
lean_object* v_a_3278_; lean_object* v_snd_3279_; lean_object* v___x_3280_; lean_object* v_map_u2082_3281_; lean_object* v___x_3282_; 
lean_inc_ref(v_a_3277_);
lean_dec_ref_known(v___x_3276_, 1);
v_a_3278_ = lean_ctor_get(v_a_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref_known(v_a_3277_, 1);
v_snd_3279_ = lean_ctor_get(v_a_3278_, 1);
lean_inc(v_snd_3279_);
lean_dec(v_a_3278_);
v___x_3280_ = l_Lean_Environment_constants(v_env_3262_);
v_map_u2082_3281_ = lean_ctor_get(v___x_3280_, 1);
lean_inc_ref(v_map_u2082_3281_);
lean_dec_ref(v___x_3280_);
v___x_3282_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_u2082_3281_, v___f_3263_, v_snd_3279_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
return v___x_3282_;
}
}
else
{
lean_dec_ref(v___f_3263_);
lean_dec_ref(v_env_3262_);
return v___x_3276_;
}
}
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec_ref(v___f_3263_);
lean_dec_ref(v_env_3262_);
lean_dec(v___y_3252_);
lean_dec_ref(v_f_3251_);
v_a_3283_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3264_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3264_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3251_ = stack[0].m_obj;
lean_object* v___y_3252_ = stack[1].m_obj;
lean_object* v___y_3253_ = stack[2].m_obj;
lean_object* v___y_3254_ = stack[3].m_obj;
lean_object* v___y_3255_ = stack[4].m_obj;
lean_object* v___y_3256_ = stack[5].m_obj;
lean_object* v___y_3257_ = stack[6].m_obj;
lean_object* v___y_3258_ = stack[7].m_obj;
lean_object* v___y_3259_ = stack[8].m_obj;
lean_object* v_res_3291_;
v_res_3291_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(v_f_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
stack->m_obj
 = v_res_3291_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___boxed(lean_object* v_f_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(v_f_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
return v_res_3302_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(lean_object* v_f_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v___f_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___f_3312_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0___boxed), 12, 1);
lean_closure_set(v___f_3312_, 0, v_f_3303_);
v___x_3313_ = lean_unsigned_to_nat(0u);
v___x_3314_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(v___f_3312_, v___x_3313_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3334_; 
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3317_ = v___x_3314_;
v_isShared_3318_ = v_isSharedCheck_3334_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3314_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3334_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
if (lean_obj_tag(v_a_3315_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3329_; 
v_a_3319_ = lean_ctor_get(v_a_3315_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v_a_3315_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3321_ = v_a_3315_;
v_isShared_3322_ = v_isSharedCheck_3329_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v_a_3315_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3329_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
lean_object* v___x_3326_; 
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 0, v___x_3324_);
v___x_3326_ = v___x_3317_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3324_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
else
{
lean_object* v___x_3330_; lean_object* v___x_3332_; 
lean_dec_ref_known(v_a_3315_, 1);
v___x_3330_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 0, v___x_3330_);
v___x_3332_ = v___x_3317_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3330_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
v_a_3335_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3314_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3314_);
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
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3303_ = stack[0].m_obj;
lean_object* v___y_3304_ = stack[1].m_obj;
lean_object* v___y_3305_ = stack[2].m_obj;
lean_object* v___y_3306_ = stack[3].m_obj;
lean_object* v___y_3307_ = stack[4].m_obj;
lean_object* v___y_3308_ = stack[5].m_obj;
lean_object* v___y_3309_ = stack[6].m_obj;
lean_object* v___y_3310_ = stack[7].m_obj;
lean_object* v_res_3343_;
v_res_3343_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v_f_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
stack->m_obj
 = v_res_3343_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___boxed(lean_object* v_f_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v_f_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
return v_res_3353_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg(lean_object* v_id_3356_, uint8_t v_danglingDot_3357_, lean_object* v_as_3358_, size_t v_sz_3359_, size_t v_i_3360_, lean_object* v_b_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
uint8_t v___x_3365_; 
v___x_3365_ = lean_usize_dec_lt(v_i_3360_, v_sz_3359_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3366_, 0, v_b_3361_);
v___x_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3366_);
return v___x_3367_;
}
else
{
lean_object* v_snd_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3421_; 
v_snd_3368_ = lean_ctor_get(v_b_3361_, 1);
v_isSharedCheck_3421_ = !lean_is_exclusive(v_b_3361_);
if (v_isSharedCheck_3421_ == 0)
{
lean_object* v_unused_3422_; 
v_unused_3422_ = lean_ctor_get(v_b_3361_, 0);
lean_dec(v_unused_3422_);
v___x_3370_ = v_b_3361_;
v_isShared_3371_ = v_isSharedCheck_3421_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_snd_3368_);
lean_dec(v_b_3361_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3421_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3372_; lean_object* v_a_3374_; lean_object* v_a_3381_; 
v___x_3372_ = lean_box(0);
v_a_3381_ = lean_array_uget(v_as_3358_, v_i_3360_);
if (lean_obj_tag(v_a_3381_) == 0)
{
v_a_3374_ = v_snd_3368_;
goto v___jp_3373_;
}
else
{
lean_object* v_val_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3420_; 
lean_dec(v_snd_3368_);
v_val_3382_ = lean_ctor_get(v_a_3381_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v_a_3381_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3384_ = v_a_3381_;
v_isShared_3385_ = v_isSharedCheck_3420_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_val_3382_);
lean_dec(v_a_3381_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3420_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; uint8_t v___x_3388_; 
v___x_3386_ = lean_box(0);
v___x_3387_ = l_Lean_LocalDecl_userName(v_val_3382_);
v___x_3388_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3356_, v___x_3387_, v_danglingDot_3357_);
if (v___x_3388_ == 0)
{
lean_dec(v___x_3387_);
lean_del_object(v___x_3384_);
lean_dec(v_val_3382_);
v_a_3374_ = v___x_3386_;
goto v___jp_3373_;
}
else
{
lean_object* v___x_3389_; lean_object* v___x_3391_; 
v___x_3389_ = l_Lean_LocalDecl_fvarId(v_val_3382_);
lean_dec(v_val_3382_);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 0, v___x_3389_);
v___x_3391_ = v___x_3384_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3389_);
v___x_3391_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
uint8_t v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3392_ = 5;
v___x_3393_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_3394_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3387_, v___x_3391_, v___x_3392_, v___x_3393_, v___y_3362_, v___y_3363_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3410_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3397_ = v___x_3394_;
v_isShared_3398_ = v_isSharedCheck_3410_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3394_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3410_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
if (lean_obj_tag(v_a_3395_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3409_; 
lean_del_object(v___x_3370_);
v_a_3399_ = lean_ctor_get(v_a_3395_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v_a_3395_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3401_ = v_a_3395_;
v_isShared_3402_ = v_isSharedCheck_3409_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v_a_3395_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3409_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
lean_object* v___x_3406_; 
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v___x_3404_);
v___x_3406_ = v___x_3397_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3404_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3395_, 1);
lean_del_object(v___x_3397_);
v_a_3374_ = v___x_3386_;
goto v___jp_3373_;
}
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_del_object(v___x_3370_);
v_a_3411_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3394_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3394_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
}
}
}
v___jp_3373_:
{
lean_object* v___x_3376_; 
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 1, v_a_3374_);
lean_ctor_set(v___x_3370_, 0, v___x_3372_);
v___x_3376_ = v___x_3370_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3380_, 1, v_a_3374_);
v___x_3376_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
size_t v___x_3377_; size_t v___x_3378_; 
v___x_3377_ = ((size_t)1ULL);
v___x_3378_ = lean_usize_add(v_i_3360_, v___x_3377_);
v_i_3360_ = v___x_3378_;
v_b_3361_ = v___x_3376_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_3356_ = stack[0].m_obj;
uint8_t v_danglingDot_3357_ = stack[1].m_num;
lean_object* v_as_3358_ = stack[2].m_obj;
size_t v_sz_3359_ = stack[3].m_num;
size_t v_i_3360_ = stack[4].m_num;
lean_object* v_b_3361_ = stack[5].m_obj;
lean_object* v___y_3362_ = stack[6].m_obj;
lean_object* v___y_3363_ = stack[7].m_obj;
lean_object* v_res_3423_;
v_res_3423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg(v_id_3356_, v_danglingDot_3357_, v_as_3358_, v_sz_3359_, v_i_3360_, v_b_3361_, v___y_3362_, v___y_3363_);
stack->m_obj
 = v_res_3423_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___boxed(lean_object* v_id_3424_, lean_object* v_danglingDot_3425_, lean_object* v_as_3426_, lean_object* v_sz_3427_, lean_object* v_i_3428_, lean_object* v_b_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
uint8_t v_danglingDot_boxed_3433_; size_t v_sz_boxed_3434_; size_t v_i_boxed_3435_; lean_object* v_res_3436_; 
v_danglingDot_boxed_3433_ = lean_unbox(v_danglingDot_3425_);
v_sz_boxed_3434_ = lean_unbox_usize(v_sz_3427_);
lean_dec(v_sz_3427_);
v_i_boxed_3435_ = lean_unbox_usize(v_i_3428_);
lean_dec(v_i_3428_);
v_res_3436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg(v_id_3424_, v_danglingDot_boxed_3433_, v_as_3426_, v_sz_boxed_3434_, v_i_boxed_3435_, v_b_3429_, v___y_3430_, v___y_3431_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec_ref(v_as_3426_);
lean_dec(v_id_3424_);
return v_res_3436_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17(lean_object* v_id_3437_, uint8_t v_danglingDot_3438_, lean_object* v_as_3439_, size_t v_sz_3440_, size_t v_i_3441_, lean_object* v_b_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
uint8_t v___x_3451_; 
v___x_3451_ = lean_usize_dec_lt(v_i_3441_, v_sz_3440_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3452_, 0, v_b_3442_);
v___x_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
return v___x_3453_;
}
else
{
lean_object* v_snd_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3507_; 
v_snd_3454_ = lean_ctor_get(v_b_3442_, 1);
v_isSharedCheck_3507_ = !lean_is_exclusive(v_b_3442_);
if (v_isSharedCheck_3507_ == 0)
{
lean_object* v_unused_3508_; 
v_unused_3508_ = lean_ctor_get(v_b_3442_, 0);
lean_dec(v_unused_3508_);
v___x_3456_ = v_b_3442_;
v_isShared_3457_ = v_isSharedCheck_3507_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_snd_3454_);
lean_dec(v_b_3442_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3507_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3458_; lean_object* v_a_3460_; lean_object* v_a_3467_; 
v___x_3458_ = lean_box(0);
v_a_3467_ = lean_array_uget(v_as_3439_, v_i_3441_);
if (lean_obj_tag(v_a_3467_) == 0)
{
v_a_3460_ = v_snd_3454_;
goto v___jp_3459_;
}
else
{
lean_object* v_val_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3506_; 
lean_dec(v_snd_3454_);
v_val_3468_ = lean_ctor_get(v_a_3467_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v_a_3467_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3470_ = v_a_3467_;
v_isShared_3471_ = v_isSharedCheck_3506_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_val_3468_);
lean_dec(v_a_3467_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3506_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; uint8_t v___x_3474_; 
v___x_3472_ = lean_box(0);
v___x_3473_ = l_Lean_LocalDecl_userName(v_val_3468_);
v___x_3474_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3437_, v___x_3473_, v_danglingDot_3438_);
if (v___x_3474_ == 0)
{
lean_dec(v___x_3473_);
lean_del_object(v___x_3470_);
lean_dec(v_val_3468_);
v_a_3460_ = v___x_3472_;
goto v___jp_3459_;
}
else
{
lean_object* v___x_3475_; lean_object* v___x_3477_; 
v___x_3475_ = l_Lean_LocalDecl_fvarId(v_val_3468_);
lean_dec(v_val_3468_);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v___x_3475_);
v___x_3477_ = v___x_3470_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3475_);
v___x_3477_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
uint8_t v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3478_ = 5;
v___x_3479_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_3480_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3473_, v___x_3477_, v___x_3478_, v___x_3479_, v___y_3443_, v___y_3444_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3496_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3483_ = v___x_3480_;
v_isShared_3484_ = v_isSharedCheck_3496_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3480_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3496_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
if (lean_obj_tag(v_a_3481_) == 0)
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3495_; 
lean_del_object(v___x_3456_);
v_a_3485_ = lean_ctor_get(v_a_3481_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v_a_3481_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3487_ = v_a_3481_;
v_isShared_3488_ = v_isSharedCheck_3495_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v_a_3481_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3495_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
lean_object* v___x_3492_; 
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 0, v___x_3490_);
v___x_3492_ = v___x_3483_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3481_, 1);
lean_del_object(v___x_3483_);
v_a_3460_ = v___x_3472_;
goto v___jp_3459_;
}
}
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_del_object(v___x_3456_);
v_a_3497_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3480_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3480_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
}
}
}
v___jp_3459_:
{
lean_object* v___x_3462_; 
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 1, v_a_3460_);
lean_ctor_set(v___x_3456_, 0, v___x_3458_);
v___x_3462_ = v___x_3456_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3458_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v_a_3460_);
v___x_3462_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
size_t v___x_3463_; size_t v___x_3464_; lean_object* v___x_3465_; 
v___x_3463_ = ((size_t)1ULL);
v___x_3464_ = lean_usize_add(v_i_3441_, v___x_3463_);
v___x_3465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg(v_id_3437_, v_danglingDot_3438_, v_as_3439_, v_sz_3440_, v___x_3464_, v___x_3462_, v___y_3443_, v___y_3444_);
return v___x_3465_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_3437_ = stack[0].m_obj;
uint8_t v_danglingDot_3438_ = stack[1].m_num;
lean_object* v_as_3439_ = stack[2].m_obj;
size_t v_sz_3440_ = stack[3].m_num;
size_t v_i_3441_ = stack[4].m_num;
lean_object* v_b_3442_ = stack[5].m_obj;
lean_object* v___y_3443_ = stack[6].m_obj;
lean_object* v___y_3444_ = stack[7].m_obj;
lean_object* v___y_3445_ = stack[8].m_obj;
lean_object* v___y_3446_ = stack[9].m_obj;
lean_object* v___y_3447_ = stack[10].m_obj;
lean_object* v___y_3448_ = stack[11].m_obj;
lean_object* v___y_3449_ = stack[12].m_obj;
lean_object* v_res_3509_;
v_res_3509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17(v_id_3437_, v_danglingDot_3438_, v_as_3439_, v_sz_3440_, v_i_3441_, v_b_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
stack->m_obj
 = v_res_3509_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17___boxed(lean_object* v_id_3510_, lean_object* v_danglingDot_3511_, lean_object* v_as_3512_, lean_object* v_sz_3513_, lean_object* v_i_3514_, lean_object* v_b_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
uint8_t v_danglingDot_boxed_3524_; size_t v_sz_boxed_3525_; size_t v_i_boxed_3526_; lean_object* v_res_3527_; 
v_danglingDot_boxed_3524_ = lean_unbox(v_danglingDot_3511_);
v_sz_boxed_3525_ = lean_unbox_usize(v_sz_3513_);
lean_dec(v_sz_3513_);
v_i_boxed_3526_ = lean_unbox_usize(v_i_3514_);
lean_dec(v_i_3514_);
v_res_3527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17(v_id_3510_, v_danglingDot_boxed_3524_, v_as_3512_, v_sz_boxed_3525_, v_i_boxed_3526_, v_b_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v_as_3512_);
lean_dec(v_id_3510_);
return v_res_3527_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(lean_object* v_init_3528_, lean_object* v_id_3529_, uint8_t v_danglingDot_3530_, lean_object* v_n_3531_, lean_object* v_b_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
if (lean_obj_tag(v_n_3531_) == 0)
{
lean_object* v_cs_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; size_t v_sz_3544_; size_t v___x_3545_; lean_object* v___x_3546_; 
v_cs_3541_ = lean_ctor_get(v_n_3531_, 0);
v___x_3542_ = lean_box(0);
v___x_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3542_);
lean_ctor_set(v___x_3543_, 1, v_b_3532_);
v_sz_3544_ = lean_array_size(v_cs_3541_);
v___x_3545_ = ((size_t)0ULL);
v___x_3546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16(v_init_3528_, v_id_3529_, v_danglingDot_3530_, v_cs_3541_, v_sz_3544_, v___x_3545_, v___x_3543_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3583_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3549_ = v___x_3546_;
v_isShared_3550_ = v_isSharedCheck_3583_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3546_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3583_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
if (lean_obj_tag(v_a_3547_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3561_; 
v_a_3551_ = lean_ctor_get(v_a_3547_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v_a_3547_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3553_ = v_a_3547_;
v_isShared_3554_ = v_isSharedCheck_3561_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v_a_3547_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3561_;
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
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3558_; 
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v___x_3556_);
v___x_3558_ = v___x_3549_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3556_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3582_; 
v_a_3562_ = lean_ctor_get(v_a_3547_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v_a_3547_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3564_ = v_a_3547_;
v_isShared_3565_ = v_isSharedCheck_3582_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v_a_3547_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3582_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v_fst_3566_; 
v_fst_3566_ = lean_ctor_get(v_a_3562_, 0);
if (lean_obj_tag(v_fst_3566_) == 0)
{
lean_object* v_snd_3567_; lean_object* v___x_3568_; lean_object* v___x_3570_; 
v_snd_3567_ = lean_ctor_get(v_a_3562_, 1);
lean_inc(v_snd_3567_);
lean_dec(v_a_3562_);
v___x_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3568_, 0, v_snd_3567_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 0, v___x_3568_);
v___x_3570_ = v___x_3564_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
lean_object* v___x_3572_; 
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v___x_3570_);
v___x_3572_ = v___x_3549_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3570_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
else
{
lean_object* v_val_3575_; lean_object* v___x_3577_; 
lean_inc_ref(v_fst_3566_);
lean_dec(v_a_3562_);
v_val_3575_ = lean_ctor_get(v_fst_3566_, 0);
lean_inc(v_val_3575_);
lean_dec_ref_known(v_fst_3566_, 1);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 0, v_val_3575_);
v___x_3577_ = v___x_3564_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_val_3575_);
v___x_3577_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
lean_object* v___x_3579_; 
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v___x_3577_);
v___x_3579_ = v___x_3549_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
v_a_3584_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3546_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3546_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
else
{
lean_object* v_vs_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; size_t v_sz_3595_; size_t v___x_3596_; lean_object* v___x_3597_; 
v_vs_3592_ = lean_ctor_get(v_n_3531_, 0);
v___x_3593_ = lean_box(0);
v___x_3594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3593_);
lean_ctor_set(v___x_3594_, 1, v_b_3532_);
v_sz_3595_ = lean_array_size(v_vs_3592_);
v___x_3596_ = ((size_t)0ULL);
v___x_3597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17(v_id_3529_, v_danglingDot_3530_, v_vs_3592_, v_sz_3595_, v___x_3596_, v___x_3594_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3634_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3600_ = v___x_3597_;
v_isShared_3601_ = v_isSharedCheck_3634_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3597_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3634_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
if (lean_obj_tag(v_a_3598_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3612_; 
v_a_3602_ = lean_ctor_get(v_a_3598_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v_a_3598_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3604_ = v_a_3598_;
v_isShared_3605_ = v_isSharedCheck_3612_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v_a_3598_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3612_;
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
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v___x_3609_; 
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v___x_3607_);
v___x_3609_ = v___x_3600_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3607_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
else
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3633_; 
v_a_3613_ = lean_ctor_get(v_a_3598_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v_a_3598_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3615_ = v_a_3598_;
v_isShared_3616_ = v_isSharedCheck_3633_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v_a_3598_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3633_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v_fst_3617_; 
v_fst_3617_ = lean_ctor_get(v_a_3613_, 0);
if (lean_obj_tag(v_fst_3617_) == 0)
{
lean_object* v_snd_3618_; lean_object* v___x_3619_; lean_object* v___x_3621_; 
v_snd_3618_ = lean_ctor_get(v_a_3613_, 1);
lean_inc(v_snd_3618_);
lean_dec(v_a_3613_);
v___x_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3619_, 0, v_snd_3618_);
if (v_isShared_3616_ == 0)
{
lean_ctor_set(v___x_3615_, 0, v___x_3619_);
v___x_3621_ = v___x_3615_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3619_);
v___x_3621_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
lean_object* v___x_3623_; 
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v___x_3621_);
v___x_3623_ = v___x_3600_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3621_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
else
{
lean_object* v_val_3626_; lean_object* v___x_3628_; 
lean_inc_ref(v_fst_3617_);
lean_dec(v_a_3613_);
v_val_3626_ = lean_ctor_get(v_fst_3617_, 0);
lean_inc(v_val_3626_);
lean_dec_ref_known(v_fst_3617_, 1);
if (v_isShared_3616_ == 0)
{
lean_ctor_set(v___x_3615_, 0, v_val_3626_);
v___x_3628_ = v___x_3615_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_val_3626_);
v___x_3628_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
lean_object* v___x_3630_; 
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v___x_3628_);
v___x_3630_ = v___x_3600_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v___x_3628_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
v_a_3635_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3597_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3597_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
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
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3528_ = stack[0].m_obj;
lean_object* v_id_3529_ = stack[1].m_obj;
uint8_t v_danglingDot_3530_ = stack[2].m_num;
lean_object* v_n_3531_ = stack[3].m_obj;
lean_object* v_b_3532_ = stack[4].m_obj;
lean_object* v___y_3533_ = stack[5].m_obj;
lean_object* v___y_3534_ = stack[6].m_obj;
lean_object* v___y_3535_ = stack[7].m_obj;
lean_object* v___y_3536_ = stack[8].m_obj;
lean_object* v___y_3537_ = stack[9].m_obj;
lean_object* v___y_3538_ = stack[10].m_obj;
lean_object* v___y_3539_ = stack[11].m_obj;
lean_object* v_res_3643_;
v_res_3643_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(v_init_3528_, v_id_3529_, v_danglingDot_3530_, v_n_3531_, v_b_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
stack->m_obj
 = v_res_3643_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16(lean_object* v_init_3644_, lean_object* v_id_3645_, uint8_t v_danglingDot_3646_, lean_object* v_as_3647_, size_t v_sz_3648_, size_t v_i_3649_, lean_object* v_b_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
uint8_t v___x_3659_; 
v___x_3659_ = lean_usize_dec_lt(v_i_3649_, v_sz_3648_);
if (v___x_3659_ == 0)
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3660_, 0, v_b_3650_);
v___x_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
return v___x_3661_;
}
else
{
lean_object* v_snd_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3715_; 
v_snd_3662_ = lean_ctor_get(v_b_3650_, 1);
v_isSharedCheck_3715_ = !lean_is_exclusive(v_b_3650_);
if (v_isSharedCheck_3715_ == 0)
{
lean_object* v_unused_3716_; 
v_unused_3716_ = lean_ctor_get(v_b_3650_, 0);
lean_dec(v_unused_3716_);
v___x_3664_ = v_b_3650_;
v_isShared_3665_ = v_isSharedCheck_3715_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_snd_3662_);
lean_dec(v_b_3650_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3715_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3666_; lean_object* v_a_3667_; lean_object* v___x_3668_; 
v___x_3666_ = lean_box(0);
v_a_3667_ = lean_array_uget_borrowed(v_as_3647_, v_i_3649_);
lean_inc(v_snd_3662_);
v___x_3668_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(v_init_3644_, v_id_3645_, v_danglingDot_3646_, v_a_3667_, v_snd_3662_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3706_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3671_ = v___x_3668_;
v_isShared_3672_ = v_isSharedCheck_3706_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3668_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3706_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
if (lean_obj_tag(v_a_3669_) == 0)
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3683_; 
lean_del_object(v___x_3664_);
lean_dec(v_snd_3662_);
v_a_3673_ = lean_ctor_get(v_a_3669_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v_a_3669_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3675_ = v_a_3669_;
v_isShared_3676_ = v_isSharedCheck_3683_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v_a_3669_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3683_;
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
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
lean_object* v___x_3680_; 
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v___x_3678_);
v___x_3680_ = v___x_3671_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v___x_3678_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
else
{
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3705_; 
v_a_3684_ = lean_ctor_get(v_a_3669_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v_a_3669_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3686_ = v_a_3669_;
v_isShared_3687_ = v_isSharedCheck_3705_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v_a_3669_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3705_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
if (lean_obj_tag(v_a_3684_) == 0)
{
lean_object* v___x_3688_; lean_object* v___x_3690_; 
v___x_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3688_, 0, v_a_3684_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 0, v___x_3688_);
v___x_3690_ = v___x_3664_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3688_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v_snd_3662_);
v___x_3690_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
lean_object* v___x_3692_; 
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 0, v___x_3690_);
v___x_3692_ = v___x_3686_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3690_);
v___x_3692_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
lean_object* v___x_3694_; 
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v___x_3692_);
v___x_3694_ = v___x_3671_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3692_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
else
{
lean_object* v_a_3698_; lean_object* v___x_3700_; 
lean_del_object(v___x_3686_);
lean_del_object(v___x_3671_);
lean_dec(v_snd_3662_);
v_a_3698_ = lean_ctor_get(v_a_3684_, 0);
lean_inc(v_a_3698_);
lean_dec_ref_known(v_a_3684_, 1);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 1, v_a_3698_);
lean_ctor_set(v___x_3664_, 0, v___x_3666_);
v___x_3700_ = v___x_3664_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3666_);
lean_ctor_set(v_reuseFailAlloc_3704_, 1, v_a_3698_);
v___x_3700_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
size_t v___x_3701_; size_t v___x_3702_; 
v___x_3701_ = ((size_t)1ULL);
v___x_3702_ = lean_usize_add(v_i_3649_, v___x_3701_);
v_i_3649_ = v___x_3702_;
v_b_3650_ = v___x_3700_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3714_; 
lean_del_object(v___x_3664_);
lean_dec(v_snd_3662_);
v_a_3707_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3709_ = v___x_3668_;
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3668_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3712_; 
if (v_isShared_3710_ == 0)
{
v___x_3712_ = v___x_3709_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3707_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3644_ = stack[0].m_obj;
lean_object* v_id_3645_ = stack[1].m_obj;
uint8_t v_danglingDot_3646_ = stack[2].m_num;
lean_object* v_as_3647_ = stack[3].m_obj;
size_t v_sz_3648_ = stack[4].m_num;
size_t v_i_3649_ = stack[5].m_num;
lean_object* v_b_3650_ = stack[6].m_obj;
lean_object* v___y_3651_ = stack[7].m_obj;
lean_object* v___y_3652_ = stack[8].m_obj;
lean_object* v___y_3653_ = stack[9].m_obj;
lean_object* v___y_3654_ = stack[10].m_obj;
lean_object* v___y_3655_ = stack[11].m_obj;
lean_object* v___y_3656_ = stack[12].m_obj;
lean_object* v___y_3657_ = stack[13].m_obj;
lean_object* v_res_3717_;
v_res_3717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16(v_init_3644_, v_id_3645_, v_danglingDot_3646_, v_as_3647_, v_sz_3648_, v_i_3649_, v_b_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
stack->m_obj
 = v_res_3717_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16___boxed(lean_object* v_init_3718_, lean_object* v_id_3719_, lean_object* v_danglingDot_3720_, lean_object* v_as_3721_, lean_object* v_sz_3722_, lean_object* v_i_3723_, lean_object* v_b_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_){
_start:
{
uint8_t v_danglingDot_boxed_3733_; size_t v_sz_boxed_3734_; size_t v_i_boxed_3735_; lean_object* v_res_3736_; 
v_danglingDot_boxed_3733_ = lean_unbox(v_danglingDot_3720_);
v_sz_boxed_3734_ = lean_unbox_usize(v_sz_3722_);
lean_dec(v_sz_3722_);
v_i_boxed_3735_ = lean_unbox_usize(v_i_3723_);
lean_dec(v_i_3723_);
v_res_3736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16(v_init_3718_, v_id_3719_, v_danglingDot_boxed_3733_, v_as_3721_, v_sz_boxed_3734_, v_i_boxed_3735_, v_b_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
lean_dec(v___y_3731_);
lean_dec_ref(v___y_3730_);
lean_dec(v___y_3729_);
lean_dec_ref(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec_ref(v_as_3721_);
lean_dec(v_id_3719_);
return v_res_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11___boxed(lean_object* v_init_3737_, lean_object* v_id_3738_, lean_object* v_danglingDot_3739_, lean_object* v_n_3740_, lean_object* v_b_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
uint8_t v_danglingDot_boxed_3750_; lean_object* v_res_3751_; 
v_danglingDot_boxed_3750_ = lean_unbox(v_danglingDot_3739_);
v_res_3751_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(v_init_3737_, v_id_3738_, v_danglingDot_boxed_3750_, v_n_3740_, v_b_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
lean_dec(v___y_3748_);
lean_dec_ref(v___y_3747_);
lean_dec(v___y_3746_);
lean_dec_ref(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec_ref(v_n_3740_);
lean_dec(v_id_3738_);
return v_res_3751_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(lean_object* v_id_3752_, uint8_t v_danglingDot_3753_, lean_object* v_as_3754_, size_t v_sz_3755_, size_t v_i_3756_, lean_object* v_b_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
uint8_t v___x_3761_; 
v___x_3761_ = lean_usize_dec_lt(v_i_3756_, v_sz_3755_);
if (v___x_3761_ == 0)
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3762_, 0, v_b_3757_);
v___x_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3762_);
return v___x_3763_;
}
else
{
lean_object* v_snd_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3817_; 
v_snd_3764_ = lean_ctor_get(v_b_3757_, 1);
v_isSharedCheck_3817_ = !lean_is_exclusive(v_b_3757_);
if (v_isSharedCheck_3817_ == 0)
{
lean_object* v_unused_3818_; 
v_unused_3818_ = lean_ctor_get(v_b_3757_, 0);
lean_dec(v_unused_3818_);
v___x_3766_ = v_b_3757_;
v_isShared_3767_ = v_isSharedCheck_3817_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_snd_3764_);
lean_dec(v_b_3757_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3817_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3768_; lean_object* v_a_3770_; lean_object* v_a_3777_; 
v___x_3768_ = lean_box(0);
v_a_3777_ = lean_array_uget(v_as_3754_, v_i_3756_);
if (lean_obj_tag(v_a_3777_) == 0)
{
v_a_3770_ = v_snd_3764_;
goto v___jp_3769_;
}
else
{
lean_object* v_val_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3816_; 
lean_dec(v_snd_3764_);
v_val_3778_ = lean_ctor_get(v_a_3777_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v_a_3777_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3780_ = v_a_3777_;
v_isShared_3781_ = v_isSharedCheck_3816_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_val_3778_);
lean_dec(v_a_3777_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3816_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; uint8_t v___x_3784_; 
v___x_3782_ = lean_box(0);
v___x_3783_ = l_Lean_LocalDecl_userName(v_val_3778_);
v___x_3784_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3752_, v___x_3783_, v_danglingDot_3753_);
if (v___x_3784_ == 0)
{
lean_dec(v___x_3783_);
lean_del_object(v___x_3780_);
lean_dec(v_val_3778_);
v_a_3770_ = v___x_3782_;
goto v___jp_3769_;
}
else
{
lean_object* v___x_3785_; lean_object* v___x_3787_; 
v___x_3785_ = l_Lean_LocalDecl_fvarId(v_val_3778_);
lean_dec(v_val_3778_);
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 0, v___x_3785_);
v___x_3787_ = v___x_3780_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3785_);
v___x_3787_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
uint8_t v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3788_ = 5;
v___x_3789_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_3790_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3783_, v___x_3787_, v___x_3788_, v___x_3789_, v___y_3758_, v___y_3759_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3806_; 
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3793_ = v___x_3790_;
v_isShared_3794_ = v_isSharedCheck_3806_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3790_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3806_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
if (lean_obj_tag(v_a_3791_) == 0)
{
lean_object* v_a_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3805_; 
lean_del_object(v___x_3766_);
v_a_3795_ = lean_ctor_get(v_a_3791_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v_a_3791_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3797_ = v_a_3791_;
v_isShared_3798_ = v_isSharedCheck_3805_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_a_3795_);
lean_dec(v_a_3791_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3805_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3800_; 
if (v_isShared_3798_ == 0)
{
v___x_3800_ = v___x_3797_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3795_);
v___x_3800_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
lean_object* v___x_3802_; 
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 0, v___x_3800_);
v___x_3802_ = v___x_3793_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v___x_3800_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3791_, 1);
lean_del_object(v___x_3793_);
v_a_3770_ = v___x_3782_;
goto v___jp_3769_;
}
}
}
else
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3814_; 
lean_del_object(v___x_3766_);
v_a_3807_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3809_ = v___x_3790_;
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3790_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3810_ == 0)
{
v___x_3812_ = v___x_3809_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
}
}
}
v___jp_3769_:
{
lean_object* v___x_3772_; 
if (v_isShared_3767_ == 0)
{
lean_ctor_set(v___x_3766_, 1, v_a_3770_);
lean_ctor_set(v___x_3766_, 0, v___x_3768_);
v___x_3772_ = v___x_3766_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3768_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v_a_3770_);
v___x_3772_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
size_t v___x_3773_; size_t v___x_3774_; 
v___x_3773_ = ((size_t)1ULL);
v___x_3774_ = lean_usize_add(v_i_3756_, v___x_3773_);
v_i_3756_ = v___x_3774_;
v_b_3757_ = v___x_3772_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_3752_ = stack[0].m_obj;
uint8_t v_danglingDot_3753_ = stack[1].m_num;
lean_object* v_as_3754_ = stack[2].m_obj;
size_t v_sz_3755_ = stack[3].m_num;
size_t v_i_3756_ = stack[4].m_num;
lean_object* v_b_3757_ = stack[5].m_obj;
lean_object* v___y_3758_ = stack[6].m_obj;
lean_object* v___y_3759_ = stack[7].m_obj;
lean_object* v_res_3819_;
v_res_3819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(v_id_3752_, v_danglingDot_3753_, v_as_3754_, v_sz_3755_, v_i_3756_, v_b_3757_, v___y_3758_, v___y_3759_);
stack->m_obj
 = v_res_3819_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg___boxed(lean_object* v_id_3820_, lean_object* v_danglingDot_3821_, lean_object* v_as_3822_, lean_object* v_sz_3823_, lean_object* v_i_3824_, lean_object* v_b_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
uint8_t v_danglingDot_boxed_3829_; size_t v_sz_boxed_3830_; size_t v_i_boxed_3831_; lean_object* v_res_3832_; 
v_danglingDot_boxed_3829_ = lean_unbox(v_danglingDot_3821_);
v_sz_boxed_3830_ = lean_unbox_usize(v_sz_3823_);
lean_dec(v_sz_3823_);
v_i_boxed_3831_ = lean_unbox_usize(v_i_3824_);
lean_dec(v_i_3824_);
v_res_3832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(v_id_3820_, v_danglingDot_boxed_3829_, v_as_3822_, v_sz_boxed_3830_, v_i_boxed_3831_, v_b_3825_, v___y_3826_, v___y_3827_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec_ref(v_as_3822_);
lean_dec(v_id_3820_);
return v_res_3832_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12(lean_object* v_id_3833_, uint8_t v_danglingDot_3834_, lean_object* v_as_3835_, size_t v_sz_3836_, size_t v_i_3837_, lean_object* v_b_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
uint8_t v___x_3847_; 
v___x_3847_ = lean_usize_dec_lt(v_i_3837_, v_sz_3836_);
if (v___x_3847_ == 0)
{
lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3848_, 0, v_b_3838_);
v___x_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3848_);
return v___x_3849_;
}
else
{
lean_object* v_snd_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3903_; 
v_snd_3850_ = lean_ctor_get(v_b_3838_, 1);
v_isSharedCheck_3903_ = !lean_is_exclusive(v_b_3838_);
if (v_isSharedCheck_3903_ == 0)
{
lean_object* v_unused_3904_; 
v_unused_3904_ = lean_ctor_get(v_b_3838_, 0);
lean_dec(v_unused_3904_);
v___x_3852_ = v_b_3838_;
v_isShared_3853_ = v_isSharedCheck_3903_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_snd_3850_);
lean_dec(v_b_3838_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3903_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3854_; lean_object* v_a_3856_; lean_object* v_a_3863_; 
v___x_3854_ = lean_box(0);
v_a_3863_ = lean_array_uget(v_as_3835_, v_i_3837_);
if (lean_obj_tag(v_a_3863_) == 0)
{
v_a_3856_ = v_snd_3850_;
goto v___jp_3855_;
}
else
{
lean_object* v_val_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3902_; 
lean_dec(v_snd_3850_);
v_val_3864_ = lean_ctor_get(v_a_3863_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v_a_3863_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3866_ = v_a_3863_;
v_isShared_3867_ = v_isSharedCheck_3902_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_val_3864_);
lean_dec(v_a_3863_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3902_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; uint8_t v___x_3870_; 
v___x_3868_ = lean_box(0);
v___x_3869_ = l_Lean_LocalDecl_userName(v_val_3864_);
v___x_3870_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3833_, v___x_3869_, v_danglingDot_3834_);
if (v___x_3870_ == 0)
{
lean_dec(v___x_3869_);
lean_del_object(v___x_3866_);
lean_dec(v_val_3864_);
v_a_3856_ = v___x_3868_;
goto v___jp_3855_;
}
else
{
lean_object* v___x_3871_; lean_object* v___x_3873_; 
v___x_3871_ = l_Lean_LocalDecl_fvarId(v_val_3864_);
lean_dec(v_val_3864_);
if (v_isShared_3867_ == 0)
{
lean_ctor_set(v___x_3866_, 0, v___x_3871_);
v___x_3873_ = v___x_3866_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3871_);
v___x_3873_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
uint8_t v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3874_ = 5;
v___x_3875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_3876_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3869_, v___x_3873_, v___x_3874_, v___x_3875_, v___y_3839_, v___y_3840_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3892_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3879_ = v___x_3876_;
v_isShared_3880_ = v_isSharedCheck_3892_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3876_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3892_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
if (lean_obj_tag(v_a_3877_) == 0)
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3891_; 
lean_del_object(v___x_3852_);
v_a_3881_ = lean_ctor_get(v_a_3877_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v_a_3877_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3883_ = v_a_3877_;
v_isShared_3884_ = v_isSharedCheck_3891_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v_a_3877_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3891_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3886_; 
if (v_isShared_3884_ == 0)
{
v___x_3886_ = v___x_3883_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3881_);
v___x_3886_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
lean_object* v___x_3888_; 
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 0, v___x_3886_);
v___x_3888_ = v___x_3879_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3886_);
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
else
{
lean_dec_ref_known(v_a_3877_, 1);
lean_del_object(v___x_3879_);
v_a_3856_ = v___x_3868_;
goto v___jp_3855_;
}
}
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
lean_del_object(v___x_3852_);
v_a_3893_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3876_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3876_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3893_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
}
}
}
v___jp_3855_:
{
lean_object* v___x_3858_; 
if (v_isShared_3853_ == 0)
{
lean_ctor_set(v___x_3852_, 1, v_a_3856_);
lean_ctor_set(v___x_3852_, 0, v___x_3854_);
v___x_3858_ = v___x_3852_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3854_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_a_3856_);
v___x_3858_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
size_t v___x_3859_; size_t v___x_3860_; lean_object* v___x_3861_; 
v___x_3859_ = ((size_t)1ULL);
v___x_3860_ = lean_usize_add(v_i_3837_, v___x_3859_);
v___x_3861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(v_id_3833_, v_danglingDot_3834_, v_as_3835_, v_sz_3836_, v___x_3860_, v___x_3858_, v___y_3839_, v___y_3840_);
return v___x_3861_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_3833_ = stack[0].m_obj;
uint8_t v_danglingDot_3834_ = stack[1].m_num;
lean_object* v_as_3835_ = stack[2].m_obj;
size_t v_sz_3836_ = stack[3].m_num;
size_t v_i_3837_ = stack[4].m_num;
lean_object* v_b_3838_ = stack[5].m_obj;
lean_object* v___y_3839_ = stack[6].m_obj;
lean_object* v___y_3840_ = stack[7].m_obj;
lean_object* v___y_3841_ = stack[8].m_obj;
lean_object* v___y_3842_ = stack[9].m_obj;
lean_object* v___y_3843_ = stack[10].m_obj;
lean_object* v___y_3844_ = stack[11].m_obj;
lean_object* v___y_3845_ = stack[12].m_obj;
lean_object* v_res_3905_;
v_res_3905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12(v_id_3833_, v_danglingDot_3834_, v_as_3835_, v_sz_3836_, v_i_3837_, v_b_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
stack->m_obj
 = v_res_3905_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12___boxed(lean_object* v_id_3906_, lean_object* v_danglingDot_3907_, lean_object* v_as_3908_, lean_object* v_sz_3909_, lean_object* v_i_3910_, lean_object* v_b_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_){
_start:
{
uint8_t v_danglingDot_boxed_3920_; size_t v_sz_boxed_3921_; size_t v_i_boxed_3922_; lean_object* v_res_3923_; 
v_danglingDot_boxed_3920_ = lean_unbox(v_danglingDot_3907_);
v_sz_boxed_3921_ = lean_unbox_usize(v_sz_3909_);
lean_dec(v_sz_3909_);
v_i_boxed_3922_ = lean_unbox_usize(v_i_3910_);
lean_dec(v_i_3910_);
v_res_3923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12(v_id_3906_, v_danglingDot_boxed_3920_, v_as_3908_, v_sz_boxed_3921_, v_i_boxed_3922_, v_b_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec_ref(v___y_3914_);
lean_dec(v___y_3913_);
lean_dec_ref(v___y_3912_);
lean_dec_ref(v_as_3908_);
lean_dec(v_id_3906_);
return v_res_3923_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(lean_object* v_id_3924_, uint8_t v_danglingDot_3925_, lean_object* v_t_3926_, lean_object* v_init_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
lean_object* v_b_3937_; lean_object* v_root_3940_; lean_object* v_tail_3941_; lean_object* v___x_3942_; 
v_root_3940_ = lean_ctor_get(v_t_3926_, 0);
v_tail_3941_ = lean_ctor_get(v_t_3926_, 1);
v___x_3942_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(v_init_3927_, v_id_3924_, v_danglingDot_3925_, v_root_3940_, v_init_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_4004_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3945_ = v___x_3942_;
v_isShared_3946_ = v_isSharedCheck_4004_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3942_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_4004_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
if (lean_obj_tag(v_a_3943_) == 0)
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3957_; 
v_a_3947_ = lean_ctor_get(v_a_3943_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v_a_3943_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3949_ = v_a_3943_;
v_isShared_3950_ = v_isSharedCheck_3957_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v_a_3943_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3957_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_a_3947_);
v___x_3952_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
lean_object* v___x_3954_; 
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 0, v___x_3952_);
v___x_3954_ = v___x_3945_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v___x_3952_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
}
else
{
lean_object* v_a_3958_; 
lean_del_object(v___x_3945_);
v_a_3958_ = lean_ctor_get(v_a_3943_, 0);
lean_inc(v_a_3958_);
lean_dec_ref_known(v_a_3943_, 1);
if (lean_obj_tag(v_a_3958_) == 0)
{
lean_object* v_a_3959_; 
v_a_3959_ = lean_ctor_get(v_a_3958_, 0);
lean_inc(v_a_3959_);
lean_dec_ref_known(v_a_3958_, 1);
v_b_3937_ = v_a_3959_;
goto v___jp_3936_;
}
else
{
lean_object* v_a_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; size_t v_sz_3963_; size_t v___x_3964_; lean_object* v___x_3965_; 
v_a_3960_ = lean_ctor_get(v_a_3958_, 0);
lean_inc(v_a_3960_);
lean_dec_ref_known(v_a_3958_, 1);
v___x_3961_ = lean_box(0);
v___x_3962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
lean_ctor_set(v___x_3962_, 1, v_a_3960_);
v_sz_3963_ = lean_array_size(v_tail_3941_);
v___x_3964_ = ((size_t)0ULL);
v___x_3965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12(v_id_3924_, v_danglingDot_3925_, v_tail_3941_, v_sz_3963_, v___x_3964_, v___x_3962_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3995_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3968_ = v___x_3965_;
v_isShared_3969_ = v_isSharedCheck_3995_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3965_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3995_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
if (lean_obj_tag(v_a_3966_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3980_; 
v_a_3970_ = lean_ctor_get(v_a_3966_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v_a_3966_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3972_ = v_a_3966_;
v_isShared_3973_ = v_isSharedCheck_3980_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v_a_3966_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3980_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3975_; 
if (v_isShared_3973_ == 0)
{
v___x_3975_ = v___x_3972_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3970_);
v___x_3975_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
lean_object* v___x_3977_; 
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 0, v___x_3975_);
v___x_3977_ = v___x_3968_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v___x_3975_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3994_; 
v_a_3981_ = lean_ctor_get(v_a_3966_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v_a_3966_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3983_ = v_a_3966_;
v_isShared_3984_ = v_isSharedCheck_3994_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v_a_3966_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3994_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v_fst_3985_; 
v_fst_3985_ = lean_ctor_get(v_a_3981_, 0);
if (lean_obj_tag(v_fst_3985_) == 0)
{
lean_object* v_snd_3986_; lean_object* v___x_3988_; 
v_snd_3986_ = lean_ctor_get(v_a_3981_, 1);
lean_inc(v_snd_3986_);
lean_dec(v_a_3981_);
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 0, v_snd_3986_);
v___x_3988_ = v___x_3983_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_snd_3986_);
v___x_3988_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
lean_object* v___x_3990_; 
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 0, v___x_3988_);
v___x_3990_ = v___x_3968_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v___x_3988_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
return v___x_3990_;
}
}
}
else
{
lean_object* v_val_3993_; 
lean_inc_ref(v_fst_3985_);
lean_del_object(v___x_3983_);
lean_dec(v_a_3981_);
lean_del_object(v___x_3968_);
v_val_3993_ = lean_ctor_get(v_fst_3985_, 0);
lean_inc(v_val_3993_);
lean_dec_ref_known(v_fst_3985_, 1);
v_b_3937_ = v_val_3993_;
goto v___jp_3936_;
}
}
}
}
}
else
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
v_a_3996_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3965_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3965_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
v_a_4005_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___x_3942_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_3942_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
v___jp_3936_:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3938_, 0, v_b_3937_);
v___x_3939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3938_);
return v___x_3939_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_3924_ = stack[0].m_obj;
uint8_t v_danglingDot_3925_ = stack[1].m_num;
lean_object* v_t_3926_ = stack[2].m_obj;
lean_object* v_init_3927_ = stack[3].m_obj;
lean_object* v___y_3928_ = stack[4].m_obj;
lean_object* v___y_3929_ = stack[5].m_obj;
lean_object* v___y_3930_ = stack[6].m_obj;
lean_object* v___y_3931_ = stack[7].m_obj;
lean_object* v___y_3932_ = stack[8].m_obj;
lean_object* v___y_3933_ = stack[9].m_obj;
lean_object* v___y_3934_ = stack[10].m_obj;
lean_object* v_res_4013_;
v_res_4013_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(v_id_3924_, v_danglingDot_3925_, v_t_3926_, v_init_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
stack->m_obj
 = v_res_4013_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6___boxed(lean_object* v_id_4014_, lean_object* v_danglingDot_4015_, lean_object* v_t_4016_, lean_object* v_init_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
uint8_t v_danglingDot_boxed_4026_; lean_object* v_res_4027_; 
v_danglingDot_boxed_4026_ = lean_unbox(v_danglingDot_4015_);
v_res_4027_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(v_id_4014_, v_danglingDot_boxed_4026_, v_t_4016_, v_init_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec_ref(v_t_4016_);
lean_dec(v_id_4014_);
return v_res_4027_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(lean_object* v_as_4028_, size_t v_sz_4029_, size_t v_i_4030_, lean_object* v_b_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
uint8_t v___x_4035_; 
v___x_4035_ = lean_usize_dec_lt(v_i_4030_, v_sz_4029_);
if (v___x_4035_ == 0)
{
lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4036_, 0, v_b_4031_);
v___x_4037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4036_);
return v___x_4037_;
}
else
{
lean_object* v___x_4038_; lean_object* v_a_4039_; lean_object* v___x_4040_; 
v___x_4038_ = lean_box(0);
v_a_4039_ = lean_array_uget_borrowed(v_as_4028_, v_i_4030_);
lean_inc(v_a_4039_);
v___x_4040_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg(v_a_4039_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_a_4041_; 
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
if (lean_obj_tag(v_a_4041_) == 0)
{
return v___x_4040_;
}
else
{
size_t v___x_4042_; size_t v___x_4043_; 
lean_dec_ref_known(v___x_4040_, 1);
v___x_4042_ = ((size_t)1ULL);
v___x_4043_ = lean_usize_add(v_i_4030_, v___x_4042_);
v_i_4030_ = v___x_4043_;
v_b_4031_ = v___x_4038_;
goto _start;
}
}
else
{
return v___x_4040_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4028_ = stack[0].m_obj;
size_t v_sz_4029_ = stack[1].m_num;
size_t v_i_4030_ = stack[2].m_num;
lean_object* v_b_4031_ = stack[3].m_obj;
lean_object* v___y_4032_ = stack[4].m_obj;
lean_object* v___y_4033_ = stack[5].m_obj;
lean_object* v_res_4045_;
v_res_4045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(v_as_4028_, v_sz_4029_, v_i_4030_, v_b_4031_, v___y_4032_, v___y_4033_);
stack->m_obj
 = v_res_4045_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg___boxed(lean_object* v_as_4046_, lean_object* v_sz_4047_, lean_object* v_i_4048_, lean_object* v_b_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
size_t v_sz_boxed_4053_; size_t v_i_boxed_4054_; lean_object* v_res_4055_; 
v_sz_boxed_4053_ = lean_unbox_usize(v_sz_4047_);
lean_dec(v_sz_4047_);
v_i_boxed_4054_ = lean_unbox_usize(v_i_4048_);
lean_dec(v_i_4048_);
v_res_4055_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(v_as_4046_, v_sz_boxed_4053_, v_i_boxed_4054_, v_b_4049_, v___y_4050_, v___y_4051_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec_ref(v_as_4046_);
return v_res_4055_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0(lean_object* v___x_4056_, lean_object* v_a_4057_, lean_object* v___x_4058_, lean_object* v_ns_4059_, lean_object* v_id_4060_, uint8_t v_danglingDot_4061_, lean_object* v_alias_4062_, lean_object* v_declNames_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
uint8_t v___y_4073_; uint8_t v___x_4077_; 
v___x_4077_ = l_Lean_Name_isPrefixOf(v_ns_4059_, v_alias_4062_);
if (v___x_4077_ == 0)
{
v___y_4073_ = v___x_4077_;
goto v___jp_4072_;
}
else
{
lean_object* v___x_4078_; lean_object* v___x_4079_; uint8_t v___x_4080_; 
v___x_4078_ = lean_box(0);
lean_inc(v_alias_4062_);
v___x_4079_ = l_Lean_Name_replacePrefix(v_alias_4062_, v_ns_4059_, v___x_4078_);
v___x_4080_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_4060_, v___x_4079_, v_danglingDot_4061_);
lean_dec(v___x_4079_);
v___y_4073_ = v___x_4080_;
goto v___jp_4072_;
}
v___jp_4072_:
{
if (v___y_4073_ == 0)
{
lean_object* v___x_4074_; lean_object* v___x_4075_; 
lean_dec(v_declNames_4063_);
lean_dec(v_alias_4062_);
lean_dec_ref(v___x_4058_);
v___x_4074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4056_);
v___x_4075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4074_);
return v___x_4075_;
}
else
{
lean_object* v___x_4076_; 
v___x_4076_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_4057_, v___x_4058_, v_alias_4062_, v_declNames_4063_, v___y_4064_, v___y_4065_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
lean_dec(v_alias_4062_);
return v___x_4076_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4056_ = stack[0].m_obj;
lean_object* v_a_4057_ = stack[1].m_obj;
lean_object* v___x_4058_ = stack[2].m_obj;
lean_object* v_ns_4059_ = stack[3].m_obj;
lean_object* v_id_4060_ = stack[4].m_obj;
uint8_t v_danglingDot_4061_ = stack[5].m_num;
lean_object* v_alias_4062_ = stack[6].m_obj;
lean_object* v_declNames_4063_ = stack[7].m_obj;
lean_object* v___y_4064_ = stack[8].m_obj;
lean_object* v___y_4065_ = stack[9].m_obj;
lean_object* v___y_4066_ = stack[10].m_obj;
lean_object* v___y_4067_ = stack[11].m_obj;
lean_object* v___y_4068_ = stack[12].m_obj;
lean_object* v___y_4069_ = stack[13].m_obj;
lean_object* v___y_4070_ = stack[14].m_obj;
lean_object* v_res_4081_;
v_res_4081_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0(v___x_4056_, v_a_4057_, v___x_4058_, v_ns_4059_, v_id_4060_, v_danglingDot_4061_, v_alias_4062_, v_declNames_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
stack->m_obj
 = v_res_4081_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed(lean_object* v___x_4082_, lean_object* v_a_4083_, lean_object* v___x_4084_, lean_object* v_ns_4085_, lean_object* v_id_4086_, lean_object* v_danglingDot_4087_, lean_object* v_alias_4088_, lean_object* v_declNames_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_){
_start:
{
uint8_t v_danglingDot_boxed_4098_; lean_object* v_res_4099_; 
v_danglingDot_boxed_4098_ = lean_unbox(v_danglingDot_4087_);
v_res_4099_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0(v___x_4082_, v_a_4083_, v___x_4084_, v_ns_4085_, v_id_4086_, v_danglingDot_boxed_4098_, v_alias_4088_, v_declNames_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec(v_id_4086_);
lean_dec(v_ns_4085_);
lean_dec_ref(v_a_4083_);
return v_res_4099_;
}
}
lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(lean_object* v_a_4100_, lean_object* v___x_4101_, lean_object* v_id_4102_, uint8_t v_danglingDot_4103_, lean_object* v_as_x27_4104_, lean_object* v_b_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v_a_4115_; 
if (lean_obj_tag(v_as_x27_4104_) == 0)
{
lean_object* v___x_4118_; lean_object* v___x_4119_; 
lean_dec(v_id_4102_);
lean_dec_ref(v___x_4101_);
lean_dec_ref(v_a_4100_);
v___x_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4118_, 0, v_b_4105_);
v___x_4119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4118_);
return v___x_4119_;
}
else
{
lean_object* v_head_4120_; lean_object* v_tail_4121_; lean_object* v___x_4122_; 
v_head_4120_ = lean_ctor_get(v_as_x27_4104_, 0);
v_tail_4121_ = lean_ctor_get(v_as_x27_4104_, 1);
v___x_4122_ = lean_box(0);
if (lean_obj_tag(v_head_4120_) == 0)
{
lean_object* v_ns_4123_; lean_object* v___x_4124_; lean_object* v___f_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v_ns_4123_ = lean_ctor_get(v_head_4120_, 0);
v___x_4124_ = lean_box(v_danglingDot_4103_);
lean_inc(v_id_4102_);
lean_inc(v_ns_4123_);
lean_inc_ref_n(v___x_4101_, 2);
lean_inc_ref(v_a_4100_);
v___f_4125_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed), 16, 6);
lean_closure_set(v___f_4125_, 0, v___x_4122_);
lean_closure_set(v___f_4125_, 1, v_a_4100_);
lean_closure_set(v___f_4125_, 2, v___x_4101_);
lean_closure_set(v___f_4125_, 3, v_ns_4123_);
lean_closure_set(v___f_4125_, 4, v_id_4102_);
lean_closure_set(v___f_4125_, 5, v___x_4124_);
v___x_4126_ = l_Lean_getAliasState(v___x_4101_);
v___x_4127_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v___x_4126_, v___f_4125_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4128_);
lean_dec_ref_known(v___x_4127_, 1);
if (lean_obj_tag(v_a_4128_) == 0)
{
lean_object* v_a_4129_; 
lean_dec(v_id_4102_);
lean_dec_ref(v___x_4101_);
lean_dec_ref(v_a_4100_);
v_a_4129_ = lean_ctor_get(v_a_4128_, 0);
lean_inc(v_a_4129_);
lean_dec_ref_known(v_a_4128_, 1);
v_a_4115_ = v_a_4129_;
goto v___jp_4114_;
}
else
{
lean_dec_ref_known(v_a_4128_, 1);
v_as_x27_4104_ = v_tail_4121_;
v_b_4105_ = v___x_4122_;
goto _start;
}
}
else
{
lean_dec(v_id_4102_);
lean_dec_ref(v___x_4101_);
lean_dec_ref(v_a_4100_);
return v___x_4127_;
}
}
else
{
lean_object* v_id_4131_; lean_object* v_declName_4132_; uint8_t v___x_4133_; 
v_id_4131_ = lean_ctor_get(v_head_4120_, 0);
v_declName_4132_ = lean_ctor_get(v_head_4120_, 1);
lean_inc(v_declName_4132_);
lean_inc_ref(v___x_4101_);
v___x_4133_ = l_Lean_Server_Completion_allowCompletion(v_a_4100_, v___x_4101_, v_declName_4132_);
if (v___x_4133_ == 0)
{
v_as_x27_4104_ = v_tail_4121_;
v_b_4105_ = v___x_4122_;
goto _start;
}
else
{
uint8_t v___x_4135_; 
v___x_4135_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_4102_, v_id_4131_, v_danglingDot_4103_);
if (v___x_4135_ == 0)
{
v_as_x27_4104_ = v_tail_4121_;
v_b_4105_ = v___x_4122_;
goto _start;
}
else
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4137_ = l_Lean_Name_getString_x21(v_id_4131_);
v___x_4138_ = lean_box(0);
v___x_4139_ = l_Lean_Name_str___override(v___x_4138_, v___x_4137_);
lean_inc(v_declName_4132_);
v___x_4140_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_4139_, v_declName_4132_, v___y_4106_, v___y_4107_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_dec_ref_known(v___x_4140_, 1);
v_as_x27_4104_ = v_tail_4121_;
v_b_4105_ = v___x_4122_;
goto _start;
}
else
{
lean_dec(v_id_4102_);
lean_dec_ref(v___x_4101_);
lean_dec_ref(v_a_4100_);
return v___x_4140_;
}
}
}
}
}
v___jp_4114_:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4116_, 0, v_a_4115_);
v___x_4117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4116_);
return v___x_4117_;
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4100_ = stack[0].m_obj;
lean_object* v___x_4101_ = stack[1].m_obj;
lean_object* v_id_4102_ = stack[2].m_obj;
uint8_t v_danglingDot_4103_ = stack[3].m_num;
lean_object* v_as_x27_4104_ = stack[4].m_obj;
lean_object* v_b_4105_ = stack[5].m_obj;
lean_object* v___y_4106_ = stack[6].m_obj;
lean_object* v___y_4107_ = stack[7].m_obj;
lean_object* v___y_4108_ = stack[8].m_obj;
lean_object* v___y_4109_ = stack[9].m_obj;
lean_object* v___y_4110_ = stack[10].m_obj;
lean_object* v___y_4111_ = stack[11].m_obj;
lean_object* v___y_4112_ = stack[12].m_obj;
lean_object* v_res_4142_;
v_res_4142_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4100_, v___x_4101_, v_id_4102_, v_danglingDot_4103_, v_as_x27_4104_, v_b_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
stack->m_obj
 = v_res_4142_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg___boxed(lean_object* v_a_4143_, lean_object* v___x_4144_, lean_object* v_id_4145_, lean_object* v_danglingDot_4146_, lean_object* v_as_x27_4147_, lean_object* v_b_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
uint8_t v_danglingDot_boxed_4157_; lean_object* v_res_4158_; 
v_danglingDot_boxed_4157_ = lean_unbox(v_danglingDot_4146_);
v_res_4158_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4143_, v___x_4144_, v_id_4145_, v_danglingDot_boxed_4157_, v_as_x27_4147_, v_b_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v_as_x27_4147_);
return v_res_4158_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(lean_object* v_id_4159_, uint8_t v_danglingDot_4160_, lean_object* v_a_4161_, lean_object* v___x_4162_, lean_object* v_as_4163_, lean_object* v_as_x27_4164_, lean_object* v_b_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_){
_start:
{
lean_object* v_a_4175_; 
if (lean_obj_tag(v_as_x27_4164_) == 0)
{
lean_object* v___x_4178_; lean_object* v___x_4179_; 
lean_dec_ref(v___x_4162_);
lean_dec_ref(v_a_4161_);
lean_dec(v_id_4159_);
v___x_4178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4178_, 0, v_b_4165_);
v___x_4179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4178_);
return v___x_4179_;
}
else
{
lean_object* v_head_4180_; lean_object* v_tail_4181_; lean_object* v___x_4182_; 
v_head_4180_ = lean_ctor_get(v_as_x27_4164_, 0);
v_tail_4181_ = lean_ctor_get(v_as_x27_4164_, 1);
v___x_4182_ = lean_box(0);
if (lean_obj_tag(v_head_4180_) == 0)
{
lean_object* v_ns_4183_; lean_object* v___x_4184_; lean_object* v___f_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
v_ns_4183_ = lean_ctor_get(v_head_4180_, 0);
v___x_4184_ = lean_box(v_danglingDot_4160_);
lean_inc(v_id_4159_);
lean_inc(v_ns_4183_);
lean_inc_ref_n(v___x_4162_, 2);
lean_inc_ref(v_a_4161_);
v___f_4185_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed), 16, 6);
lean_closure_set(v___f_4185_, 0, v___x_4182_);
lean_closure_set(v___f_4185_, 1, v_a_4161_);
lean_closure_set(v___f_4185_, 2, v___x_4162_);
lean_closure_set(v___f_4185_, 3, v_ns_4183_);
lean_closure_set(v___f_4185_, 4, v_id_4159_);
lean_closure_set(v___f_4185_, 5, v___x_4184_);
v___x_4186_ = l_Lean_getAliasState(v___x_4162_);
v___x_4187_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v___x_4186_, v___f_4185_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_object* v_a_4188_; 
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
lean_inc(v_a_4188_);
lean_dec_ref_known(v___x_4187_, 1);
if (lean_obj_tag(v_a_4188_) == 0)
{
lean_object* v_a_4189_; 
lean_dec_ref(v___x_4162_);
lean_dec_ref(v_a_4161_);
lean_dec(v_id_4159_);
v_a_4189_ = lean_ctor_get(v_a_4188_, 0);
lean_inc(v_a_4189_);
lean_dec_ref_known(v_a_4188_, 1);
v_a_4175_ = v_a_4189_;
goto v___jp_4174_;
}
else
{
lean_object* v___x_4190_; 
lean_dec_ref_known(v_a_4188_, 1);
v___x_4190_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4161_, v___x_4162_, v_id_4159_, v_danglingDot_4160_, v_tail_4181_, v___x_4182_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
return v___x_4190_;
}
}
else
{
lean_dec_ref(v___x_4162_);
lean_dec_ref(v_a_4161_);
lean_dec(v_id_4159_);
return v___x_4187_;
}
}
else
{
lean_object* v_id_4191_; lean_object* v_declName_4192_; uint8_t v___x_4193_; 
v_id_4191_ = lean_ctor_get(v_head_4180_, 0);
v_declName_4192_ = lean_ctor_get(v_head_4180_, 1);
lean_inc(v_declName_4192_);
lean_inc_ref(v___x_4162_);
v___x_4193_ = l_Lean_Server_Completion_allowCompletion(v_a_4161_, v___x_4162_, v_declName_4192_);
if (v___x_4193_ == 0)
{
lean_object* v___x_4194_; 
v___x_4194_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4161_, v___x_4162_, v_id_4159_, v_danglingDot_4160_, v_tail_4181_, v___x_4182_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
return v___x_4194_;
}
else
{
uint8_t v___x_4195_; 
v___x_4195_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_4159_, v_id_4191_, v_danglingDot_4160_);
if (v___x_4195_ == 0)
{
lean_object* v___x_4196_; 
v___x_4196_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4161_, v___x_4162_, v_id_4159_, v_danglingDot_4160_, v_tail_4181_, v___x_4182_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
return v___x_4196_;
}
else
{
lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4197_ = l_Lean_Name_getString_x21(v_id_4191_);
v___x_4198_ = lean_box(0);
v___x_4199_ = l_Lean_Name_str___override(v___x_4198_, v___x_4197_);
lean_inc(v_declName_4192_);
v___x_4200_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_4199_, v_declName_4192_, v___y_4166_, v___y_4167_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v___x_4201_; 
lean_dec_ref_known(v___x_4200_, 1);
v___x_4201_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4161_, v___x_4162_, v_id_4159_, v_danglingDot_4160_, v_tail_4181_, v___x_4182_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
return v___x_4201_;
}
else
{
lean_dec_ref(v___x_4162_);
lean_dec_ref(v_a_4161_);
lean_dec(v_id_4159_);
return v___x_4200_;
}
}
}
}
}
v___jp_4174_:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4176_, 0, v_a_4175_);
v___x_4177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4176_);
return v___x_4177_;
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_4159_ = stack[0].m_obj;
uint8_t v_danglingDot_4160_ = stack[1].m_num;
lean_object* v_a_4161_ = stack[2].m_obj;
lean_object* v___x_4162_ = stack[3].m_obj;
lean_object* v_as_4163_ = stack[4].m_obj;
lean_object* v_as_x27_4164_ = stack[5].m_obj;
lean_object* v_b_4165_ = stack[6].m_obj;
lean_object* v___y_4166_ = stack[7].m_obj;
lean_object* v___y_4167_ = stack[8].m_obj;
lean_object* v___y_4168_ = stack[9].m_obj;
lean_object* v___y_4169_ = stack[10].m_obj;
lean_object* v___y_4170_ = stack[11].m_obj;
lean_object* v___y_4171_ = stack[12].m_obj;
lean_object* v___y_4172_ = stack[13].m_obj;
lean_object* v_res_4202_;
v_res_4202_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v_id_4159_, v_danglingDot_4160_, v_a_4161_, v___x_4162_, v_as_4163_, v_as_x27_4164_, v_b_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
stack->m_obj
 = v_res_4202_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___boxed(lean_object* v_id_4203_, lean_object* v_danglingDot_4204_, lean_object* v_a_4205_, lean_object* v___x_4206_, lean_object* v_as_4207_, lean_object* v_as_x27_4208_, lean_object* v_b_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
uint8_t v_danglingDot_boxed_4218_; lean_object* v_res_4219_; 
v_danglingDot_boxed_4218_ = lean_unbox(v_danglingDot_4204_);
v_res_4219_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v_id_4203_, v_danglingDot_boxed_4218_, v_a_4205_, v___x_4206_, v_as_4207_, v_as_x27_4208_, v_b_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec(v_as_x27_4208_);
lean_dec(v_as_4207_);
return v_res_4219_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(lean_object* v_ctx_4220_, lean_object* v_stx_4221_, lean_object* v_id_4222_, lean_object* v_hoverInfo_4223_, uint8_t v_danglingDot_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_){
_start:
{
lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; uint8_t v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v_id_4285_; uint8_t v_danglingDot_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v_id_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; uint8_t v___x_4316_; 
v___x_4316_ = l_Lean_Name_hasMacroScopes(v_id_4222_);
if (v___x_4316_ == 0)
{
v_id_4305_ = v_id_4222_;
v___y_4306_ = v_a_4225_;
v___y_4307_ = v_a_4226_;
v___y_4308_ = v_a_4227_;
v___y_4309_ = v_a_4228_;
v___y_4310_ = v_a_4229_;
v___y_4311_ = v_a_4230_;
v___y_4312_ = v_a_4231_;
goto v___jp_4304_;
}
else
{
lean_object* v___x_4317_; 
v___x_4317_ = l_Lean_Syntax_getHeadInfo(v_stx_4221_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v_id_4318_; 
lean_dec_ref_known(v___x_4317_, 4);
v_id_4318_ = l_Lean_Name_eraseMacroScopes(v_id_4222_);
lean_dec(v_id_4222_);
v_id_4305_ = v_id_4318_;
v___y_4306_ = v_a_4225_;
v___y_4307_ = v_a_4226_;
v___y_4308_ = v_a_4227_;
v___y_4309_ = v_a_4228_;
v___y_4310_ = v_a_4229_;
v___y_4311_ = v_a_4230_;
v___y_4312_ = v_a_4231_;
goto v___jp_4304_;
}
else
{
lean_object* v___x_4319_; lean_object* v___x_4320_; 
lean_dec(v___x_4317_);
lean_dec(v_hoverInfo_4223_);
lean_dec(v_id_4222_);
lean_dec_ref(v_ctx_4220_);
v___x_4319_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4319_);
return v___x_4320_;
}
}
v___jp_4233_:
{
lean_object* v___x_4245_; lean_object* v_env_4246_; lean_object* v___x_4247_; 
v___x_4245_ = lean_st_ref_get(v___y_4236_);
v_env_4246_ = lean_ctor_get(v___x_4245_, 0);
lean_inc_ref(v_env_4246_);
lean_dec(v___x_4245_);
v___x_4247_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___y_4234_, v___y_4244_, v___y_4241_, v___y_4240_, v___y_4235_, v___y_4239_, v___y_4238_, v___y_4236_);
if (lean_obj_tag(v___x_4247_) == 0)
{
lean_object* v_a_4248_; 
v_a_4248_ = lean_ctor_get(v___x_4247_, 0);
if (lean_obj_tag(v_a_4248_) == 0)
{
lean_dec_ref(v_env_4246_);
lean_dec_ref(v___y_4243_);
lean_dec(v___y_4237_);
lean_dec_ref(v_ctx_4220_);
return v___x_4247_;
}
else
{
lean_object* v___x_4249_; lean_object* v_a_4250_; 
lean_dec_ref_known(v___x_4247_, 1);
v___x_4249_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v___y_4240_);
v_a_4250_ = lean_ctor_get(v___x_4249_, 0);
if (lean_obj_tag(v_a_4250_) == 0)
{
lean_dec_ref(v_env_4246_);
lean_dec_ref(v___y_4243_);
lean_dec(v___y_4237_);
lean_dec_ref(v_ctx_4220_);
return v___x_4249_;
}
else
{
lean_object* v___x_4251_; 
lean_dec_ref(v___x_4249_);
lean_inc_ref(v_env_4246_);
v___x_4251_ = l_Lean_Server_Completion_getEligibleHeaderDecls(v_env_4246_, v___y_4235_, v___y_4239_, v___y_4238_, v___y_4236_);
if (lean_obj_tag(v___x_4251_) == 0)
{
lean_object* v_toCommandContextInfo_4252_; lean_object* v_a_4253_; lean_object* v_currNamespace_4254_; lean_object* v_openDecls_4255_; lean_object* v___f_4256_; lean_object* v___f_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
v_toCommandContextInfo_4252_ = lean_ctor_get(v_ctx_4220_, 0);
v_a_4253_ = lean_ctor_get(v___x_4251_, 0);
lean_inc_n(v_a_4253_, 2);
lean_dec_ref_known(v___x_4251_, 1);
v_currNamespace_4254_ = lean_ctor_get(v_toCommandContextInfo_4252_, 5);
v_openDecls_4255_ = lean_ctor_get(v_toCommandContextInfo_4252_, 6);
lean_inc_ref_n(v_env_4246_, 2);
v___f_4256_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2___boxed), 12, 2);
lean_closure_set(v___f_4256_, 0, v_a_4253_);
lean_closure_set(v___f_4256_, 1, v_env_4246_);
lean_inc(v_currNamespace_4254_);
v___f_4257_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3___boxed), 13, 3);
lean_closure_set(v___f_4257_, 0, v___y_4243_);
lean_closure_set(v___f_4257_, 1, v___f_4256_);
lean_closure_set(v___f_4257_, 2, v_currNamespace_4254_);
v___x_4258_ = lean_box(0);
lean_inc(v___y_4237_);
v___x_4259_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v___y_4237_, v___y_4242_, v_a_4253_, v_env_4246_, v_openDecls_4255_, v_openDecls_4255_, v___x_4258_, v___y_4244_, v___y_4241_, v___y_4240_, v___y_4235_, v___y_4239_, v___y_4238_, v___y_4236_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
if (lean_obj_tag(v_a_4260_) == 0)
{
lean_dec_ref(v___f_4257_);
lean_dec_ref(v_env_4246_);
lean_dec(v___y_4237_);
lean_dec_ref(v_ctx_4220_);
return v___x_4259_;
}
else
{
lean_object* v___x_4261_; lean_object* v___x_4262_; 
lean_dec_ref_known(v___x_4259_, 1);
lean_inc_ref(v_env_4246_);
v___x_4261_ = l_Lean_getAliasState(v_env_4246_);
v___x_4262_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v___x_4261_, v___f_4257_, v___y_4244_, v___y_4241_, v___y_4240_, v___y_4235_, v___y_4239_, v___y_4238_, v___y_4236_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
if (lean_obj_tag(v_a_4263_) == 0)
{
lean_dec_ref(v_env_4246_);
lean_dec(v___y_4237_);
lean_dec_ref(v_ctx_4220_);
return v___x_4262_;
}
else
{
lean_dec_ref_known(v___x_4262_, 1);
if (v___y_4242_ == 0)
{
if (lean_obj_tag(v___y_4237_) == 1)
{
lean_object* v_pre_4264_; 
v_pre_4264_ = lean_ctor_get(v___y_4237_, 0);
if (lean_obj_tag(v_pre_4264_) == 0)
{
lean_object* v_str_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; size_t v_sz_4268_; size_t v___x_4269_; lean_object* v___x_4270_; 
v_str_4265_ = lean_ctor_get(v___y_4237_, 1);
v___x_4266_ = l_Lean_Parser_getTokenTable(v_env_4246_);
v___x_4267_ = l_Lean_Data_Trie_findPrefix___redArg(v___x_4266_, v_str_4265_);
lean_dec_ref(v___x_4266_);
v_sz_4268_ = lean_array_size(v___x_4267_);
v___x_4269_ = ((size_t)0ULL);
v___x_4270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(v___x_4267_, v_sz_4268_, v___x_4269_, v___x_4258_, v___y_4244_, v___y_4241_);
lean_dec_ref(v___x_4267_);
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_object* v_a_4271_; 
v_a_4271_ = lean_ctor_get(v___x_4270_, 0);
if (lean_obj_tag(v_a_4271_) == 0)
{
lean_dec_ref_known(v___y_4237_, 2);
lean_dec_ref(v_ctx_4220_);
return v___x_4270_;
}
else
{
lean_object* v___x_4272_; 
lean_dec_ref_known(v___x_4270_, 1);
v___x_4272_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4220_, v___y_4237_, v___y_4242_, v___y_4244_, v___y_4241_, v___y_4240_, v___y_4235_, v___y_4239_, v___y_4238_, v___y_4236_);
return v___x_4272_;
}
}
else
{
lean_dec_ref_known(v___y_4237_, 2);
lean_dec_ref(v_ctx_4220_);
return v___x_4270_;
}
}
else
{
lean_object* v___x_4273_; 
lean_dec_ref(v_env_4246_);
v___x_4273_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4220_, v___y_4237_, v___y_4242_, v___y_4244_, v___y_4241_, v___y_4240_, v___y_4235_, v___y_4239_, v___y_4238_, v___y_4236_);
return v___x_4273_;
}
}
else
{
lean_object* v___x_4274_; 
lean_dec_ref(v_env_4246_);
v___x_4274_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4220_, v___y_4237_, v___y_4242_, v___y_4244_, v___y_4241_, v___y_4240_, v___y_4235_, v___y_4239_, v___y_4238_, v___y_4236_);
return v___x_4274_;
}
}
else
{
lean_object* v___x_4275_; 
lean_dec_ref(v_env_4246_);
v___x_4275_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4220_, v___y_4237_, v___y_4242_, v___y_4244_, v___y_4241_, v___y_4240_, v___y_4235_, v___y_4239_, v___y_4238_, v___y_4236_);
return v___x_4275_;
}
}
}
else
{
lean_dec_ref(v_env_4246_);
lean_dec(v___y_4237_);
lean_dec_ref(v_ctx_4220_);
return v___x_4262_;
}
}
}
else
{
lean_dec_ref(v___f_4257_);
lean_dec_ref(v_env_4246_);
lean_dec(v___y_4237_);
lean_dec_ref(v_ctx_4220_);
return v___x_4259_;
}
}
else
{
lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4283_; 
lean_dec_ref(v_env_4246_);
lean_dec_ref(v___y_4243_);
lean_dec(v___y_4237_);
lean_dec_ref(v_ctx_4220_);
v_a_4276_ = lean_ctor_get(v___x_4251_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4251_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4278_ = v___x_4251_;
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_dec(v___x_4251_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4281_; 
if (v_isShared_4279_ == 0)
{
v___x_4281_ = v___x_4278_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4276_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
return v___x_4281_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_env_4246_);
lean_dec_ref(v___y_4243_);
lean_dec(v___y_4237_);
lean_dec_ref(v_ctx_4220_);
return v___x_4247_;
}
}
v___jp_4284_:
{
lean_object* v___x_4294_; lean_object* v___f_4295_; lean_object* v___x_4296_; lean_object* v___f_4297_; uint8_t v___x_4298_; 
v___x_4294_ = lean_box(v_danglingDot_4286_);
lean_inc_n(v_id_4285_, 2);
lean_inc_ref(v_ctx_4220_);
v___f_4295_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0___boxed), 13, 3);
lean_closure_set(v___f_4295_, 0, v_ctx_4220_);
lean_closure_set(v___f_4295_, 1, v_id_4285_);
lean_closure_set(v___f_4295_, 2, v___x_4294_);
v___x_4296_ = lean_box(v_danglingDot_4286_);
v___f_4297_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4297_, 0, v_id_4285_);
lean_closure_set(v___f_4297_, 1, v___x_4296_);
v___x_4298_ = l_Lean_Name_isAtomic(v_id_4285_);
if (v___x_4298_ == 0)
{
v___y_4234_ = v___f_4295_;
v___y_4235_ = v___y_4290_;
v___y_4236_ = v___y_4293_;
v___y_4237_ = v_id_4285_;
v___y_4238_ = v___y_4292_;
v___y_4239_ = v___y_4291_;
v___y_4240_ = v___y_4289_;
v___y_4241_ = v___y_4288_;
v___y_4242_ = v_danglingDot_4286_;
v___y_4243_ = v___f_4297_;
v___y_4244_ = v___y_4287_;
goto v___jp_4233_;
}
else
{
lean_object* v_lctx_4299_; lean_object* v_decls_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v_lctx_4299_ = lean_ctor_get(v___y_4290_, 2);
v_decls_4300_ = lean_ctor_get(v_lctx_4299_, 1);
v___x_4301_ = lean_box(0);
v___x_4302_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(v_id_4285_, v_danglingDot_4286_, v_decls_4300_, v___x_4301_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; 
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
if (lean_obj_tag(v_a_4303_) == 0)
{
lean_dec_ref(v___f_4297_);
lean_dec_ref(v___f_4295_);
lean_dec(v_id_4285_);
lean_dec_ref(v_ctx_4220_);
return v___x_4302_;
}
else
{
lean_dec_ref_known(v___x_4302_, 1);
v___y_4234_ = v___f_4295_;
v___y_4235_ = v___y_4290_;
v___y_4236_ = v___y_4293_;
v___y_4237_ = v_id_4285_;
v___y_4238_ = v___y_4292_;
v___y_4239_ = v___y_4291_;
v___y_4240_ = v___y_4289_;
v___y_4241_ = v___y_4288_;
v___y_4242_ = v_danglingDot_4286_;
v___y_4243_ = v___f_4297_;
v___y_4244_ = v___y_4287_;
goto v___jp_4233_;
}
}
else
{
lean_dec_ref(v___f_4297_);
lean_dec_ref(v___f_4295_);
lean_dec(v_id_4285_);
lean_dec_ref(v_ctx_4220_);
return v___x_4302_;
}
}
}
v___jp_4304_:
{
if (lean_obj_tag(v_hoverInfo_4223_) == 1)
{
lean_object* v_delta_4313_; lean_object* v_id_4314_; uint8_t v_danglingDot_4315_; 
v_delta_4313_ = lean_ctor_get(v_hoverInfo_4223_, 0);
lean_inc(v_delta_4313_);
lean_dec_ref_known(v_hoverInfo_4223_, 1);
v_id_4314_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate(v_id_4305_, v_delta_4313_);
v_danglingDot_4315_ = 0;
v_id_4285_ = v_id_4314_;
v_danglingDot_4286_ = v_danglingDot_4315_;
v___y_4287_ = v___y_4306_;
v___y_4288_ = v___y_4307_;
v___y_4289_ = v___y_4308_;
v___y_4290_ = v___y_4309_;
v___y_4291_ = v___y_4310_;
v___y_4292_ = v___y_4311_;
v___y_4293_ = v___y_4312_;
goto v___jp_4284_;
}
else
{
lean_dec(v_hoverInfo_4223_);
v_id_4285_ = v_id_4305_;
v_danglingDot_4286_ = v_danglingDot_4224_;
v___y_4287_ = v___y_4306_;
v___y_4288_ = v___y_4307_;
v___y_4289_ = v___y_4308_;
v___y_4290_ = v___y_4309_;
v___y_4291_ = v___y_4310_;
v___y_4292_ = v___y_4311_;
v___y_4293_ = v___y_4312_;
goto v___jp_4284_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_4220_ = stack[0].m_obj;
lean_object* v_stx_4221_ = stack[1].m_obj;
lean_object* v_id_4222_ = stack[2].m_obj;
lean_object* v_hoverInfo_4223_ = stack[3].m_obj;
uint8_t v_danglingDot_4224_ = stack[4].m_num;
lean_object* v_a_4225_ = stack[5].m_obj;
lean_object* v_a_4226_ = stack[6].m_obj;
lean_object* v_a_4227_ = stack[7].m_obj;
lean_object* v_a_4228_ = stack[8].m_obj;
lean_object* v_a_4229_ = stack[9].m_obj;
lean_object* v_a_4230_ = stack[10].m_obj;
lean_object* v_a_4231_ = stack[11].m_obj;
lean_object* v_res_4321_;
v_res_4321_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(v_ctx_4220_, v_stx_4221_, v_id_4222_, v_hoverInfo_4223_, v_danglingDot_4224_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_);
stack->m_obj
 = v_res_4321_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___boxed(lean_object* v_ctx_4322_, lean_object* v_stx_4323_, lean_object* v_id_4324_, lean_object* v_hoverInfo_4325_, lean_object* v_danglingDot_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_){
_start:
{
uint8_t v_danglingDot_boxed_4335_; lean_object* v_res_4336_; 
v_danglingDot_boxed_4335_ = lean_unbox(v_danglingDot_4326_);
v_res_4336_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(v_ctx_4322_, v_stx_4323_, v_id_4324_, v_hoverInfo_4325_, v_danglingDot_boxed_4335_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_);
lean_dec(v_a_4333_);
lean_dec_ref(v_a_4332_);
lean_dec(v_a_4331_);
lean_dec_ref(v_a_4330_);
lean_dec_ref(v_a_4329_);
lean_dec(v_a_4328_);
lean_dec_ref(v_a_4327_);
lean_dec(v_stx_4323_);
return v_res_4336_;
}
}
lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2(lean_object* v_a_4337_, lean_object* v___x_4338_, lean_object* v_alias_4339_, lean_object* v_as_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_){
_start:
{
lean_object* v___x_4349_; 
v___x_4349_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_4337_, v___x_4338_, v_alias_4339_, v_as_4340_, v___y_4341_, v___y_4342_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
return v___x_4349_;
}
}
LEAN_EXPORT void l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4337_ = stack[0].m_obj;
lean_object* v___x_4338_ = stack[1].m_obj;
lean_object* v_alias_4339_ = stack[2].m_obj;
lean_object* v_as_4340_ = stack[3].m_obj;
lean_object* v___y_4341_ = stack[4].m_obj;
lean_object* v___y_4342_ = stack[5].m_obj;
lean_object* v___y_4343_ = stack[6].m_obj;
lean_object* v___y_4344_ = stack[7].m_obj;
lean_object* v___y_4345_ = stack[8].m_obj;
lean_object* v___y_4346_ = stack[9].m_obj;
lean_object* v___y_4347_ = stack[10].m_obj;
lean_object* v_res_4350_;
v_res_4350_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2(v_a_4337_, v___x_4338_, v_alias_4339_, v_as_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
stack->m_obj
 = v_res_4350_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___boxed(lean_object* v_a_4351_, lean_object* v___x_4352_, lean_object* v_alias_4353_, lean_object* v_as_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2(v_a_4351_, v___x_4352_, v_alias_4353_, v_as_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
lean_dec_ref(v___y_4357_);
lean_dec(v___y_4356_);
lean_dec_ref(v___y_4355_);
lean_dec(v_alias_4353_);
lean_dec_ref(v_a_4351_);
return v_res_4363_;
}
}
lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3(lean_object* v_00_u03b2_4364_, lean_object* v_s_4365_, lean_object* v_f_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_){
_start:
{
lean_object* v___x_4375_; 
v___x_4375_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v_s_4365_, v_f_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_);
return v___x_4375_;
}
}
LEAN_EXPORT void l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4365_ = stack[1].m_obj;
lean_object* v_f_4366_ = stack[2].m_obj;
lean_object* v___y_4367_ = stack[3].m_obj;
lean_object* v___y_4368_ = stack[4].m_obj;
lean_object* v___y_4369_ = stack[5].m_obj;
lean_object* v___y_4370_ = stack[6].m_obj;
lean_object* v___y_4371_ = stack[7].m_obj;
lean_object* v___y_4372_ = stack[8].m_obj;
lean_object* v___y_4373_ = stack[9].m_obj;
lean_object* v_res_4376_;
v_res_4376_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3(lean_box(0), v_s_4365_, v_f_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_);
stack->m_obj
 = v_res_4376_;
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___boxed(lean_object* v_00_u03b2_4377_, lean_object* v_s_4378_, lean_object* v_f_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_){
_start:
{
lean_object* v_res_4388_; 
v_res_4388_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3(v_00_u03b2_4377_, v_s_4378_, v_f_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
lean_dec(v___y_4386_);
lean_dec_ref(v___y_4385_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
lean_dec_ref(v___y_4382_);
lean_dec(v___y_4381_);
lean_dec_ref(v___y_4380_);
return v_res_4388_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4(lean_object* v_id_4389_, uint8_t v_danglingDot_4390_, lean_object* v_a_4391_, lean_object* v___x_4392_, lean_object* v_as_4393_, lean_object* v_as_x27_4394_, lean_object* v_b_4395_, lean_object* v_a_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_){
_start:
{
lean_object* v___x_4405_; 
v___x_4405_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v_id_4389_, v_danglingDot_4390_, v_a_4391_, v___x_4392_, v_as_4393_, v_as_x27_4394_, v_b_4395_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_);
return v___x_4405_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_4389_ = stack[0].m_obj;
uint8_t v_danglingDot_4390_ = stack[1].m_num;
lean_object* v_a_4391_ = stack[2].m_obj;
lean_object* v___x_4392_ = stack[3].m_obj;
lean_object* v_as_4393_ = stack[4].m_obj;
lean_object* v_as_x27_4394_ = stack[5].m_obj;
lean_object* v_b_4395_ = stack[6].m_obj;
lean_object* v___y_4397_ = stack[8].m_obj;
lean_object* v___y_4398_ = stack[9].m_obj;
lean_object* v___y_4399_ = stack[10].m_obj;
lean_object* v___y_4400_ = stack[11].m_obj;
lean_object* v___y_4401_ = stack[12].m_obj;
lean_object* v___y_4402_ = stack[13].m_obj;
lean_object* v___y_4403_ = stack[14].m_obj;
lean_object* v_res_4406_;
v_res_4406_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4(v_id_4389_, v_danglingDot_4390_, v_a_4391_, v___x_4392_, v_as_4393_, v_as_x27_4394_, v_b_4395_, lean_box(0), v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_);
stack->m_obj
 = v_res_4406_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___boxed(lean_object* v_id_4407_, lean_object* v_danglingDot_4408_, lean_object* v_a_4409_, lean_object* v___x_4410_, lean_object* v_as_4411_, lean_object* v_as_x27_4412_, lean_object* v_b_4413_, lean_object* v_a_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_){
_start:
{
uint8_t v_danglingDot_boxed_4423_; lean_object* v_res_4424_; 
v_danglingDot_boxed_4423_ = lean_unbox(v_danglingDot_4408_);
v_res_4424_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4(v_id_4407_, v_danglingDot_boxed_4423_, v_a_4409_, v___x_4410_, v_as_4411_, v_as_x27_4412_, v_b_4413_, v_a_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec(v___y_4419_);
lean_dec_ref(v___y_4418_);
lean_dec_ref(v___y_4417_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v_as_x27_4412_);
lean_dec(v_as_4411_);
return v_res_4424_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5(lean_object* v_as_4425_, size_t v_sz_4426_, size_t v_i_4427_, lean_object* v_b_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
lean_object* v___x_4437_; 
v___x_4437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(v_as_4425_, v_sz_4426_, v_i_4427_, v_b_4428_, v___y_4429_, v___y_4430_);
return v___x_4437_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4425_ = stack[0].m_obj;
size_t v_sz_4426_ = stack[1].m_num;
size_t v_i_4427_ = stack[2].m_num;
lean_object* v_b_4428_ = stack[3].m_obj;
lean_object* v___y_4429_ = stack[4].m_obj;
lean_object* v___y_4430_ = stack[5].m_obj;
lean_object* v___y_4431_ = stack[6].m_obj;
lean_object* v___y_4432_ = stack[7].m_obj;
lean_object* v___y_4433_ = stack[8].m_obj;
lean_object* v___y_4434_ = stack[9].m_obj;
lean_object* v___y_4435_ = stack[10].m_obj;
lean_object* v_res_4438_;
v_res_4438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5(v_as_4425_, v_sz_4426_, v_i_4427_, v_b_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
stack->m_obj
 = v_res_4438_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___boxed(lean_object* v_as_4439_, lean_object* v_sz_4440_, lean_object* v_i_4441_, lean_object* v_b_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
size_t v_sz_boxed_4451_; size_t v_i_boxed_4452_; lean_object* v_res_4453_; 
v_sz_boxed_4451_ = lean_unbox_usize(v_sz_4440_);
lean_dec(v_sz_4440_);
v_i_boxed_4452_ = lean_unbox_usize(v_i_4441_);
lean_dec(v_i_4441_);
v_res_4453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5(v_as_4439_, v_sz_boxed_4451_, v_i_boxed_4452_, v_b_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec_ref(v___y_4445_);
lean_dec(v___y_4444_);
lean_dec_ref(v___y_4443_);
lean_dec_ref(v_as_4439_);
return v_res_4453_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4(lean_object* v_00_u03b2_4454_, lean_object* v_f_4455_, lean_object* v_x_4456_, lean_object* v_x_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_){
_start:
{
lean_object* v___x_4466_; 
v___x_4466_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_f_4455_, v_x_4456_, v_x_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_);
return v___x_4466_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4455_ = stack[1].m_obj;
lean_object* v_x_4456_ = stack[2].m_obj;
lean_object* v_x_4457_ = stack[3].m_obj;
lean_object* v___y_4458_ = stack[4].m_obj;
lean_object* v___y_4459_ = stack[5].m_obj;
lean_object* v___y_4460_ = stack[6].m_obj;
lean_object* v___y_4461_ = stack[7].m_obj;
lean_object* v___y_4462_ = stack[8].m_obj;
lean_object* v___y_4463_ = stack[9].m_obj;
lean_object* v___y_4464_ = stack[10].m_obj;
lean_object* v_res_4467_;
v_res_4467_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4(lean_box(0), v_f_4455_, v_x_4456_, v_x_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_);
stack->m_obj
 = v_res_4467_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4468_, lean_object* v_f_4469_, lean_object* v_x_4470_, lean_object* v_x_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_){
_start:
{
lean_object* v_res_4480_; 
v_res_4480_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4(v_00_u03b2_4468_, v_f_4469_, v_x_4470_, v_x_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
return v_res_4480_;
}
}
lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5(lean_object* v_00_u03b2_4481_, lean_object* v_map_4482_, lean_object* v_f_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_){
_start:
{
lean_object* v___x_4492_; 
v___x_4492_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_4482_, v_f_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
return v___x_4492_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_4482_ = stack[1].m_obj;
lean_object* v_f_4483_ = stack[2].m_obj;
lean_object* v___y_4484_ = stack[3].m_obj;
lean_object* v___y_4485_ = stack[4].m_obj;
lean_object* v___y_4486_ = stack[5].m_obj;
lean_object* v___y_4487_ = stack[6].m_obj;
lean_object* v___y_4488_ = stack[7].m_obj;
lean_object* v___y_4489_ = stack[8].m_obj;
lean_object* v___y_4490_ = stack[9].m_obj;
lean_object* v_res_4493_;
v_res_4493_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5(lean_box(0), v_map_4482_, v_f_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
stack->m_obj
 = v_res_4493_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4494_, lean_object* v_map_4495_, lean_object* v_f_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
lean_object* v_res_4505_; 
v_res_4505_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5(v_00_u03b2_4494_, v_map_4495_, v_f_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
return v_res_4505_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6(lean_object* v_00_u03b2_4506_, lean_object* v_f_4507_, lean_object* v_as_4508_, size_t v_i_4509_, size_t v_stop_4510_, lean_object* v_b_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
lean_object* v___x_4520_; 
v___x_4520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(v_f_4507_, v_as_4508_, v_i_4509_, v_stop_4510_, v_b_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
return v___x_4520_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4507_ = stack[1].m_obj;
lean_object* v_as_4508_ = stack[2].m_obj;
size_t v_i_4509_ = stack[3].m_num;
size_t v_stop_4510_ = stack[4].m_num;
lean_object* v_b_4511_ = stack[5].m_obj;
lean_object* v___y_4512_ = stack[6].m_obj;
lean_object* v___y_4513_ = stack[7].m_obj;
lean_object* v___y_4514_ = stack[8].m_obj;
lean_object* v___y_4515_ = stack[9].m_obj;
lean_object* v___y_4516_ = stack[10].m_obj;
lean_object* v___y_4517_ = stack[11].m_obj;
lean_object* v___y_4518_ = stack[12].m_obj;
lean_object* v_res_4521_;
v_res_4521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6(lean_box(0), v_f_4507_, v_as_4508_, v_i_4509_, v_stop_4510_, v_b_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
stack->m_obj
 = v_res_4521_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___boxed(lean_object* v_00_u03b2_4522_, lean_object* v_f_4523_, lean_object* v_as_4524_, lean_object* v_i_4525_, lean_object* v_stop_4526_, lean_object* v_b_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_){
_start:
{
size_t v_i_boxed_4536_; size_t v_stop_boxed_4537_; lean_object* v_res_4538_; 
v_i_boxed_4536_ = lean_unbox_usize(v_i_4525_);
lean_dec(v_i_4525_);
v_stop_boxed_4537_ = lean_unbox_usize(v_stop_4526_);
lean_dec(v_stop_4526_);
v_res_4538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6(v_00_u03b2_4522_, v_f_4523_, v_as_4524_, v_i_boxed_4536_, v_stop_boxed_4537_, v_b_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
lean_dec(v___y_4534_);
lean_dec_ref(v___y_4533_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
lean_dec_ref(v_as_4524_);
return v_res_4538_;
}
}
lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8(lean_object* v_a_4539_, lean_object* v___x_4540_, lean_object* v_id_4541_, uint8_t v_danglingDot_4542_, lean_object* v_as_4543_, lean_object* v_as_x27_4544_, lean_object* v_b_4545_, lean_object* v_a_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_){
_start:
{
lean_object* v___x_4555_; 
v___x_4555_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4539_, v___x_4540_, v_id_4541_, v_danglingDot_4542_, v_as_x27_4544_, v_b_4545_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_);
return v___x_4555_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4539_ = stack[0].m_obj;
lean_object* v___x_4540_ = stack[1].m_obj;
lean_object* v_id_4541_ = stack[2].m_obj;
uint8_t v_danglingDot_4542_ = stack[3].m_num;
lean_object* v_as_4543_ = stack[4].m_obj;
lean_object* v_as_x27_4544_ = stack[5].m_obj;
lean_object* v_b_4545_ = stack[6].m_obj;
lean_object* v___y_4547_ = stack[8].m_obj;
lean_object* v___y_4548_ = stack[9].m_obj;
lean_object* v___y_4549_ = stack[10].m_obj;
lean_object* v___y_4550_ = stack[11].m_obj;
lean_object* v___y_4551_ = stack[12].m_obj;
lean_object* v___y_4552_ = stack[13].m_obj;
lean_object* v___y_4553_ = stack[14].m_obj;
lean_object* v_res_4556_;
v_res_4556_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8(v_a_4539_, v___x_4540_, v_id_4541_, v_danglingDot_4542_, v_as_4543_, v_as_x27_4544_, v_b_4545_, lean_box(0), v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_);
stack->m_obj
 = v_res_4556_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___boxed(lean_object* v_a_4557_, lean_object* v___x_4558_, lean_object* v_id_4559_, lean_object* v_danglingDot_4560_, lean_object* v_as_4561_, lean_object* v_as_x27_4562_, lean_object* v_b_4563_, lean_object* v_a_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_){
_start:
{
uint8_t v_danglingDot_boxed_4573_; lean_object* v_res_4574_; 
v_danglingDot_boxed_4573_ = lean_unbox(v_danglingDot_4560_);
v_res_4574_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8(v_a_4557_, v___x_4558_, v_id_4559_, v_danglingDot_boxed_4573_, v_as_4561_, v_as_x27_4562_, v_b_4563_, v_a_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_);
lean_dec(v___y_4571_);
lean_dec_ref(v___y_4570_);
lean_dec(v___y_4569_);
lean_dec_ref(v___y_4568_);
lean_dec_ref(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
lean_dec(v_as_x27_4562_);
lean_dec(v_as_4561_);
return v_res_4574_;
}
}
lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_4575_, lean_object* v_map_4576_, lean_object* v_f_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_){
_start:
{
lean_object* v___x_4587_; 
v___x_4587_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_4576_, v_f_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_);
return v___x_4587_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_4576_ = stack[1].m_obj;
lean_object* v_f_4577_ = stack[2].m_obj;
lean_object* v___y_4578_ = stack[3].m_obj;
lean_object* v___y_4579_ = stack[4].m_obj;
lean_object* v___y_4580_ = stack[5].m_obj;
lean_object* v___y_4581_ = stack[6].m_obj;
lean_object* v___y_4582_ = stack[7].m_obj;
lean_object* v___y_4583_ = stack[8].m_obj;
lean_object* v___y_4584_ = stack[9].m_obj;
lean_object* v___y_4585_ = stack[10].m_obj;
lean_object* v_res_4588_;
v_res_4588_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3(lean_box(0), v_map_4576_, v_f_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_);
stack->m_obj
 = v_res_4588_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_4589_, lean_object* v_map_4590_, lean_object* v_f_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_){
_start:
{
lean_object* v_res_4601_; 
v_res_4601_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3(v_00_u03b2_4589_, v_map_4590_, v_f_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_);
lean_dec(v___y_4599_);
lean_dec_ref(v___y_4598_);
lean_dec(v___y_4597_);
lean_dec_ref(v___y_4596_);
lean_dec_ref(v___y_4595_);
lean_dec(v___y_4594_);
lean_dec_ref(v___y_4593_);
return v_res_4601_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg(lean_object* v_map_4602_, lean_object* v_f_4603_, lean_object* v_init_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
lean_object* v___x_4613_; 
v___x_4613_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_4603_, v_map_4602_, v_init_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_);
return v___x_4613_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_4602_ = stack[0].m_obj;
lean_object* v_f_4603_ = stack[1].m_obj;
lean_object* v_init_4604_ = stack[2].m_obj;
lean_object* v___y_4605_ = stack[3].m_obj;
lean_object* v___y_4606_ = stack[4].m_obj;
lean_object* v___y_4607_ = stack[5].m_obj;
lean_object* v___y_4608_ = stack[6].m_obj;
lean_object* v___y_4609_ = stack[7].m_obj;
lean_object* v___y_4610_ = stack[8].m_obj;
lean_object* v___y_4611_ = stack[9].m_obj;
lean_object* v_res_4614_;
v_res_4614_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg(v_map_4602_, v_f_4603_, v_init_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_);
stack->m_obj
 = v_res_4614_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_map_4615_, lean_object* v_f_4616_, lean_object* v_init_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_){
_start:
{
lean_object* v_res_4626_; 
v_res_4626_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg(v_map_4615_, v_f_4616_, v_init_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
lean_dec(v___y_4624_);
lean_dec_ref(v___y_4623_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
lean_dec_ref(v___y_4620_);
lean_dec(v___y_4619_);
lean_dec_ref(v___y_4618_);
return v_res_4626_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_4627_, lean_object* v_00_u03b2_4628_, lean_object* v_map_4629_, lean_object* v_f_4630_, lean_object* v_init_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_){
_start:
{
lean_object* v___x_4640_; 
v___x_4640_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_4630_, v_map_4629_, v_init_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_);
return v___x_4640_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_4629_ = stack[2].m_obj;
lean_object* v_f_4630_ = stack[3].m_obj;
lean_object* v_init_4631_ = stack[4].m_obj;
lean_object* v___y_4632_ = stack[5].m_obj;
lean_object* v___y_4633_ = stack[6].m_obj;
lean_object* v___y_4634_ = stack[7].m_obj;
lean_object* v___y_4635_ = stack[8].m_obj;
lean_object* v___y_4636_ = stack[9].m_obj;
lean_object* v___y_4637_ = stack[10].m_obj;
lean_object* v___y_4638_ = stack[11].m_obj;
lean_object* v_res_4641_;
v_res_4641_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9(lean_box(0), lean_box(0), v_map_4629_, v_f_4630_, v_init_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_);
stack->m_obj
 = v_res_4641_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_4642_, lean_object* v_00_u03b2_4643_, lean_object* v_map_4644_, lean_object* v_f_4645_, lean_object* v_init_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_){
_start:
{
lean_object* v_res_4655_; 
v_res_4655_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9(v_00_u03c3_4642_, v_00_u03b2_4643_, v_map_4644_, v_f_4645_, v_init_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
lean_dec_ref(v___y_4649_);
lean_dec(v___y_4648_);
lean_dec_ref(v___y_4647_);
return v_res_4655_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19(lean_object* v_id_4656_, uint8_t v_danglingDot_4657_, lean_object* v_as_4658_, size_t v_sz_4659_, size_t v_i_4660_, lean_object* v_b_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_){
_start:
{
lean_object* v___x_4670_; 
v___x_4670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(v_id_4656_, v_danglingDot_4657_, v_as_4658_, v_sz_4659_, v_i_4660_, v_b_4661_, v___y_4662_, v___y_4663_);
return v___x_4670_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_4656_ = stack[0].m_obj;
uint8_t v_danglingDot_4657_ = stack[1].m_num;
lean_object* v_as_4658_ = stack[2].m_obj;
size_t v_sz_4659_ = stack[3].m_num;
size_t v_i_4660_ = stack[4].m_num;
lean_object* v_b_4661_ = stack[5].m_obj;
lean_object* v___y_4662_ = stack[6].m_obj;
lean_object* v___y_4663_ = stack[7].m_obj;
lean_object* v___y_4664_ = stack[8].m_obj;
lean_object* v___y_4665_ = stack[9].m_obj;
lean_object* v___y_4666_ = stack[10].m_obj;
lean_object* v___y_4667_ = stack[11].m_obj;
lean_object* v___y_4668_ = stack[12].m_obj;
lean_object* v_res_4671_;
v_res_4671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19(v_id_4656_, v_danglingDot_4657_, v_as_4658_, v_sz_4659_, v_i_4660_, v_b_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_);
stack->m_obj
 = v_res_4671_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___boxed(lean_object* v_id_4672_, lean_object* v_danglingDot_4673_, lean_object* v_as_4674_, lean_object* v_sz_4675_, lean_object* v_i_4676_, lean_object* v_b_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_){
_start:
{
uint8_t v_danglingDot_boxed_4686_; size_t v_sz_boxed_4687_; size_t v_i_boxed_4688_; lean_object* v_res_4689_; 
v_danglingDot_boxed_4686_ = lean_unbox(v_danglingDot_4673_);
v_sz_boxed_4687_ = lean_unbox_usize(v_sz_4675_);
lean_dec(v_sz_4675_);
v_i_boxed_4688_ = lean_unbox_usize(v_i_4676_);
lean_dec(v_i_4676_);
v_res_4689_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19(v_id_4672_, v_danglingDot_boxed_4686_, v_as_4674_, v_sz_boxed_4687_, v_i_boxed_4688_, v_b_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_);
lean_dec(v___y_4684_);
lean_dec_ref(v___y_4683_);
lean_dec(v___y_4682_);
lean_dec_ref(v___y_4681_);
lean_dec_ref(v___y_4680_);
lean_dec(v___y_4679_);
lean_dec_ref(v___y_4678_);
lean_dec_ref(v_as_4674_);
lean_dec(v_id_4672_);
return v_res_4689_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___redArg(lean_object* v_map_4690_, lean_object* v_f_4691_, lean_object* v_init_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v___x_4702_; 
v___x_4702_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_4691_, v_map_4690_, v_init_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_);
return v___x_4702_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_4690_ = stack[0].m_obj;
lean_object* v_f_4691_ = stack[1].m_obj;
lean_object* v_init_4692_ = stack[2].m_obj;
lean_object* v___y_4693_ = stack[3].m_obj;
lean_object* v___y_4694_ = stack[4].m_obj;
lean_object* v___y_4695_ = stack[5].m_obj;
lean_object* v___y_4696_ = stack[6].m_obj;
lean_object* v___y_4697_ = stack[7].m_obj;
lean_object* v___y_4698_ = stack[8].m_obj;
lean_object* v___y_4699_ = stack[9].m_obj;
lean_object* v___y_4700_ = stack[10].m_obj;
lean_object* v_res_4703_;
v_res_4703_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___redArg(v_map_4690_, v_f_4691_, v_init_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_);
stack->m_obj
 = v_res_4703_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___redArg___boxed(lean_object* v_map_4704_, lean_object* v_f_4705_, lean_object* v_init_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_){
_start:
{
lean_object* v_res_4716_; 
v_res_4716_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___redArg(v_map_4704_, v_f_4705_, v_init_4706_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_);
lean_dec(v___y_4714_);
lean_dec_ref(v___y_4713_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec_ref(v___y_4710_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
return v_res_4716_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9(lean_object* v_00_u03c3_4717_, lean_object* v_00_u03b2_4718_, lean_object* v_map_4719_, lean_object* v_f_4720_, lean_object* v_init_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_){
_start:
{
lean_object* v___x_4731_; 
v___x_4731_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_4720_, v_map_4719_, v_init_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
return v___x_4731_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_4719_ = stack[2].m_obj;
lean_object* v_f_4720_ = stack[3].m_obj;
lean_object* v_init_4721_ = stack[4].m_obj;
lean_object* v___y_4722_ = stack[5].m_obj;
lean_object* v___y_4723_ = stack[6].m_obj;
lean_object* v___y_4724_ = stack[7].m_obj;
lean_object* v___y_4725_ = stack[8].m_obj;
lean_object* v___y_4726_ = stack[9].m_obj;
lean_object* v___y_4727_ = stack[10].m_obj;
lean_object* v___y_4728_ = stack[11].m_obj;
lean_object* v___y_4729_ = stack[12].m_obj;
lean_object* v_res_4732_;
v_res_4732_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9(lean_box(0), lean_box(0), v_map_4719_, v_f_4720_, v_init_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
stack->m_obj
 = v_res_4732_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___boxed(lean_object* v_00_u03c3_4733_, lean_object* v_00_u03b2_4734_, lean_object* v_map_4735_, lean_object* v_f_4736_, lean_object* v_init_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_){
_start:
{
lean_object* v_res_4747_; 
v_res_4747_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9(v_00_u03c3_4733_, v_00_u03b2_4734_, v_map_4735_, v_f_4736_, v_init_4737_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
lean_dec_ref(v___y_4741_);
lean_dec(v___y_4740_);
lean_dec_ref(v___y_4739_);
return v_res_4747_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14(lean_object* v_00_u03c3_4748_, lean_object* v_00_u03b1_4749_, lean_object* v_00_u03b2_4750_, lean_object* v_f_4751_, lean_object* v_x_4752_, lean_object* v_x_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_){
_start:
{
lean_object* v___x_4762_; 
v___x_4762_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_4751_, v_x_4752_, v_x_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_);
return v___x_4762_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4751_ = stack[3].m_obj;
lean_object* v_x_4752_ = stack[4].m_obj;
lean_object* v_x_4753_ = stack[5].m_obj;
lean_object* v___y_4754_ = stack[6].m_obj;
lean_object* v___y_4755_ = stack[7].m_obj;
lean_object* v___y_4756_ = stack[8].m_obj;
lean_object* v___y_4757_ = stack[9].m_obj;
lean_object* v___y_4758_ = stack[10].m_obj;
lean_object* v___y_4759_ = stack[11].m_obj;
lean_object* v___y_4760_ = stack[12].m_obj;
lean_object* v_res_4763_;
v_res_4763_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14(lean_box(0), lean_box(0), lean_box(0), v_f_4751_, v_x_4752_, v_x_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_);
stack->m_obj
 = v_res_4763_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___boxed(lean_object* v_00_u03c3_4764_, lean_object* v_00_u03b1_4765_, lean_object* v_00_u03b2_4766_, lean_object* v_f_4767_, lean_object* v_x_4768_, lean_object* v_x_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_){
_start:
{
lean_object* v_res_4778_; 
v_res_4778_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14(v_00_u03c3_4764_, v_00_u03b1_4765_, v_00_u03b2_4766_, v_f_4767_, v_x_4768_, v_x_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
lean_dec(v___y_4774_);
lean_dec_ref(v___y_4773_);
lean_dec_ref(v___y_4772_);
lean_dec(v___y_4771_);
lean_dec_ref(v___y_4770_);
return v_res_4778_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20(lean_object* v_id_4779_, uint8_t v_danglingDot_4780_, lean_object* v_as_4781_, size_t v_sz_4782_, size_t v_i_4783_, lean_object* v_b_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_){
_start:
{
lean_object* v___x_4793_; 
v___x_4793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg(v_id_4779_, v_danglingDot_4780_, v_as_4781_, v_sz_4782_, v_i_4783_, v_b_4784_, v___y_4785_, v___y_4786_);
return v___x_4793_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_4779_ = stack[0].m_obj;
uint8_t v_danglingDot_4780_ = stack[1].m_num;
lean_object* v_as_4781_ = stack[2].m_obj;
size_t v_sz_4782_ = stack[3].m_num;
size_t v_i_4783_ = stack[4].m_num;
lean_object* v_b_4784_ = stack[5].m_obj;
lean_object* v___y_4785_ = stack[6].m_obj;
lean_object* v___y_4786_ = stack[7].m_obj;
lean_object* v___y_4787_ = stack[8].m_obj;
lean_object* v___y_4788_ = stack[9].m_obj;
lean_object* v___y_4789_ = stack[10].m_obj;
lean_object* v___y_4790_ = stack[11].m_obj;
lean_object* v___y_4791_ = stack[12].m_obj;
lean_object* v_res_4794_;
v_res_4794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20(v_id_4779_, v_danglingDot_4780_, v_as_4781_, v_sz_4782_, v_i_4783_, v_b_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_);
stack->m_obj
 = v_res_4794_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___boxed(lean_object* v_id_4795_, lean_object* v_danglingDot_4796_, lean_object* v_as_4797_, lean_object* v_sz_4798_, lean_object* v_i_4799_, lean_object* v_b_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_){
_start:
{
uint8_t v_danglingDot_boxed_4809_; size_t v_sz_boxed_4810_; size_t v_i_boxed_4811_; lean_object* v_res_4812_; 
v_danglingDot_boxed_4809_ = lean_unbox(v_danglingDot_4796_);
v_sz_boxed_4810_ = lean_unbox_usize(v_sz_4798_);
lean_dec(v_sz_4798_);
v_i_boxed_4811_ = lean_unbox_usize(v_i_4799_);
lean_dec(v_i_4799_);
v_res_4812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20(v_id_4795_, v_danglingDot_boxed_4809_, v_as_4797_, v_sz_boxed_4810_, v_i_boxed_4811_, v_b_4800_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_, v___y_4807_);
lean_dec(v___y_4807_);
lean_dec_ref(v___y_4806_);
lean_dec(v___y_4805_);
lean_dec_ref(v___y_4804_);
lean_dec_ref(v___y_4803_);
lean_dec(v___y_4802_);
lean_dec_ref(v___y_4801_);
lean_dec_ref(v_as_4797_);
lean_dec(v_id_4795_);
return v_res_4812_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16(lean_object* v_00_u03c3_4813_, lean_object* v_00_u03b1_4814_, lean_object* v_00_u03b2_4815_, lean_object* v_f_4816_, lean_object* v_x_4817_, lean_object* v_x_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_){
_start:
{
lean_object* v___x_4828_; 
v___x_4828_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_4816_, v_x_4817_, v_x_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_);
return v___x_4828_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4816_ = stack[3].m_obj;
lean_object* v_x_4817_ = stack[4].m_obj;
lean_object* v_x_4818_ = stack[5].m_obj;
lean_object* v___y_4819_ = stack[6].m_obj;
lean_object* v___y_4820_ = stack[7].m_obj;
lean_object* v___y_4821_ = stack[8].m_obj;
lean_object* v___y_4822_ = stack[9].m_obj;
lean_object* v___y_4823_ = stack[10].m_obj;
lean_object* v___y_4824_ = stack[11].m_obj;
lean_object* v___y_4825_ = stack[12].m_obj;
lean_object* v___y_4826_ = stack[13].m_obj;
lean_object* v_res_4829_;
v_res_4829_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16(lean_box(0), lean_box(0), lean_box(0), v_f_4816_, v_x_4817_, v_x_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_);
stack->m_obj
 = v_res_4829_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___boxed(lean_object* v_00_u03c3_4830_, lean_object* v_00_u03b1_4831_, lean_object* v_00_u03b2_4832_, lean_object* v_f_4833_, lean_object* v_x_4834_, lean_object* v_x_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_){
_start:
{
lean_object* v_res_4845_; 
v_res_4845_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16(v_00_u03c3_4830_, v_00_u03b1_4831_, v_00_u03b2_4832_, v_f_4833_, v_x_4834_, v_x_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___y_4841_);
lean_dec_ref(v___y_4840_);
lean_dec_ref(v___y_4839_);
lean_dec(v___y_4838_);
lean_dec_ref(v___y_4837_);
return v_res_4845_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20(lean_object* v_00_u03b1_4846_, lean_object* v_00_u03b2_4847_, lean_object* v_00_u03c3_4848_, lean_object* v_f_4849_, lean_object* v_as_4850_, size_t v_i_4851_, size_t v_stop_4852_, lean_object* v_b_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_){
_start:
{
lean_object* v___x_4862_; 
v___x_4862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(v_f_4849_, v_as_4850_, v_i_4851_, v_stop_4852_, v_b_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_);
return v___x_4862_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4849_ = stack[3].m_obj;
lean_object* v_as_4850_ = stack[4].m_obj;
size_t v_i_4851_ = stack[5].m_num;
size_t v_stop_4852_ = stack[6].m_num;
lean_object* v_b_4853_ = stack[7].m_obj;
lean_object* v___y_4854_ = stack[8].m_obj;
lean_object* v___y_4855_ = stack[9].m_obj;
lean_object* v___y_4856_ = stack[10].m_obj;
lean_object* v___y_4857_ = stack[11].m_obj;
lean_object* v___y_4858_ = stack[12].m_obj;
lean_object* v___y_4859_ = stack[13].m_obj;
lean_object* v___y_4860_ = stack[14].m_obj;
lean_object* v_res_4863_;
v_res_4863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20(lean_box(0), lean_box(0), lean_box(0), v_f_4849_, v_as_4850_, v_i_4851_, v_stop_4852_, v_b_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_);
stack->m_obj
 = v_res_4863_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___boxed(lean_object* v_00_u03b1_4864_, lean_object* v_00_u03b2_4865_, lean_object* v_00_u03c3_4866_, lean_object* v_f_4867_, lean_object* v_as_4868_, lean_object* v_i_4869_, lean_object* v_stop_4870_, lean_object* v_b_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_){
_start:
{
size_t v_i_boxed_4880_; size_t v_stop_boxed_4881_; lean_object* v_res_4882_; 
v_i_boxed_4880_ = lean_unbox_usize(v_i_4869_);
lean_dec(v_i_4869_);
v_stop_boxed_4881_ = lean_unbox_usize(v_stop_4870_);
lean_dec(v_stop_4870_);
v_res_4882_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20(v_00_u03b1_4864_, v_00_u03b2_4865_, v_00_u03c3_4866_, v_f_4867_, v_as_4868_, v_i_boxed_4880_, v_stop_boxed_4881_, v_b_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_, v___y_4878_);
lean_dec(v___y_4878_);
lean_dec_ref(v___y_4877_);
lean_dec(v___y_4876_);
lean_dec_ref(v___y_4875_);
lean_dec_ref(v___y_4874_);
lean_dec(v___y_4873_);
lean_dec_ref(v___y_4872_);
lean_dec_ref(v_as_4868_);
return v_res_4882_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21(lean_object* v_00_u03c3_4883_, lean_object* v_00_u03b1_4884_, lean_object* v_00_u03b2_4885_, lean_object* v_f_4886_, lean_object* v_keys_4887_, lean_object* v_vals_4888_, lean_object* v_heq_4889_, lean_object* v_i_4890_, lean_object* v_acc_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_){
_start:
{
lean_object* v___x_4900_; 
v___x_4900_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(v_f_4886_, v_keys_4887_, v_vals_4888_, v_i_4890_, v_acc_4891_, v___y_4892_, v___y_4893_, v___y_4894_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_);
return v___x_4900_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4886_ = stack[3].m_obj;
lean_object* v_keys_4887_ = stack[4].m_obj;
lean_object* v_vals_4888_ = stack[5].m_obj;
lean_object* v_i_4890_ = stack[7].m_obj;
lean_object* v_acc_4891_ = stack[8].m_obj;
lean_object* v___y_4892_ = stack[9].m_obj;
lean_object* v___y_4893_ = stack[10].m_obj;
lean_object* v___y_4894_ = stack[11].m_obj;
lean_object* v___y_4895_ = stack[12].m_obj;
lean_object* v___y_4896_ = stack[13].m_obj;
lean_object* v___y_4897_ = stack[14].m_obj;
lean_object* v___y_4898_ = stack[15].m_obj;
lean_object* v_res_4901_;
v_res_4901_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21(lean_box(0), lean_box(0), lean_box(0), v_f_4886_, v_keys_4887_, v_vals_4888_, lean_box(0), v_i_4890_, v_acc_4891_, v___y_4892_, v___y_4893_, v___y_4894_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_);
stack->m_obj
 = v_res_4901_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___boxed(lean_object** _args){
lean_object* v_00_u03c3_4902_ = _args[0];
lean_object* v_00_u03b1_4903_ = _args[1];
lean_object* v_00_u03b2_4904_ = _args[2];
lean_object* v_f_4905_ = _args[3];
lean_object* v_keys_4906_ = _args[4];
lean_object* v_vals_4907_ = _args[5];
lean_object* v_heq_4908_ = _args[6];
lean_object* v_i_4909_ = _args[7];
lean_object* v_acc_4910_ = _args[8];
lean_object* v___y_4911_ = _args[9];
lean_object* v___y_4912_ = _args[10];
lean_object* v___y_4913_ = _args[11];
lean_object* v___y_4914_ = _args[12];
lean_object* v___y_4915_ = _args[13];
lean_object* v___y_4916_ = _args[14];
lean_object* v___y_4917_ = _args[15];
lean_object* v___y_4918_ = _args[16];
_start:
{
lean_object* v_res_4919_; 
v_res_4919_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21(v_00_u03c3_4902_, v_00_u03b1_4903_, v_00_u03b2_4904_, v_f_4905_, v_keys_4906_, v_vals_4907_, v_heq_4908_, v_i_4909_, v_acc_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_, v___y_4917_);
lean_dec(v___y_4917_);
lean_dec_ref(v___y_4916_);
lean_dec(v___y_4915_);
lean_dec_ref(v___y_4914_);
lean_dec_ref(v___y_4913_);
lean_dec(v___y_4912_);
lean_dec_ref(v___y_4911_);
lean_dec_ref(v_vals_4907_);
lean_dec_ref(v_keys_4906_);
return v_res_4919_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22(lean_object* v_00_u03b1_4920_, lean_object* v_00_u03b2_4921_, lean_object* v_00_u03c3_4922_, lean_object* v_f_4923_, lean_object* v_as_4924_, size_t v_i_4925_, size_t v_stop_4926_, lean_object* v_b_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_){
_start:
{
lean_object* v___x_4937_; 
v___x_4937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(v_f_4923_, v_as_4924_, v_i_4925_, v_stop_4926_, v_b_4927_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_);
return v___x_4937_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4923_ = stack[3].m_obj;
lean_object* v_as_4924_ = stack[4].m_obj;
size_t v_i_4925_ = stack[5].m_num;
size_t v_stop_4926_ = stack[6].m_num;
lean_object* v_b_4927_ = stack[7].m_obj;
lean_object* v___y_4928_ = stack[8].m_obj;
lean_object* v___y_4929_ = stack[9].m_obj;
lean_object* v___y_4930_ = stack[10].m_obj;
lean_object* v___y_4931_ = stack[11].m_obj;
lean_object* v___y_4932_ = stack[12].m_obj;
lean_object* v___y_4933_ = stack[13].m_obj;
lean_object* v___y_4934_ = stack[14].m_obj;
lean_object* v___y_4935_ = stack[15].m_obj;
lean_object* v_res_4938_;
v_res_4938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22(lean_box(0), lean_box(0), lean_box(0), v_f_4923_, v_as_4924_, v_i_4925_, v_stop_4926_, v_b_4927_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_);
stack->m_obj
 = v_res_4938_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___boxed(lean_object** _args){
lean_object* v_00_u03b1_4939_ = _args[0];
lean_object* v_00_u03b2_4940_ = _args[1];
lean_object* v_00_u03c3_4941_ = _args[2];
lean_object* v_f_4942_ = _args[3];
lean_object* v_as_4943_ = _args[4];
lean_object* v_i_4944_ = _args[5];
lean_object* v_stop_4945_ = _args[6];
lean_object* v_b_4946_ = _args[7];
lean_object* v___y_4947_ = _args[8];
lean_object* v___y_4948_ = _args[9];
lean_object* v___y_4949_ = _args[10];
lean_object* v___y_4950_ = _args[11];
lean_object* v___y_4951_ = _args[12];
lean_object* v___y_4952_ = _args[13];
lean_object* v___y_4953_ = _args[14];
lean_object* v___y_4954_ = _args[15];
lean_object* v___y_4955_ = _args[16];
_start:
{
size_t v_i_boxed_4956_; size_t v_stop_boxed_4957_; lean_object* v_res_4958_; 
v_i_boxed_4956_ = lean_unbox_usize(v_i_4944_);
lean_dec(v_i_4944_);
v_stop_boxed_4957_ = lean_unbox_usize(v_stop_4945_);
lean_dec(v_stop_4945_);
v_res_4958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22(v_00_u03b1_4939_, v_00_u03b2_4940_, v_00_u03c3_4941_, v_f_4942_, v_as_4943_, v_i_boxed_4956_, v_stop_boxed_4957_, v_b_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_);
lean_dec(v___y_4954_);
lean_dec_ref(v___y_4953_);
lean_dec(v___y_4952_);
lean_dec_ref(v___y_4951_);
lean_dec_ref(v___y_4950_);
lean_dec(v___y_4949_);
lean_dec_ref(v___y_4948_);
lean_dec_ref(v_as_4943_);
return v_res_4958_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23(lean_object* v_00_u03c3_4959_, lean_object* v_00_u03b1_4960_, lean_object* v_00_u03b2_4961_, lean_object* v_f_4962_, lean_object* v_keys_4963_, lean_object* v_vals_4964_, lean_object* v_heq_4965_, lean_object* v_i_4966_, lean_object* v_acc_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_){
_start:
{
lean_object* v___x_4977_; 
v___x_4977_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(v_f_4962_, v_keys_4963_, v_vals_4964_, v_i_4966_, v_acc_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_);
return v___x_4977_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4962_ = stack[3].m_obj;
lean_object* v_keys_4963_ = stack[4].m_obj;
lean_object* v_vals_4964_ = stack[5].m_obj;
lean_object* v_i_4966_ = stack[7].m_obj;
lean_object* v_acc_4967_ = stack[8].m_obj;
lean_object* v___y_4968_ = stack[9].m_obj;
lean_object* v___y_4969_ = stack[10].m_obj;
lean_object* v___y_4970_ = stack[11].m_obj;
lean_object* v___y_4971_ = stack[12].m_obj;
lean_object* v___y_4972_ = stack[13].m_obj;
lean_object* v___y_4973_ = stack[14].m_obj;
lean_object* v___y_4974_ = stack[15].m_obj;
lean_object* v___y_4975_ = stack[16].m_obj;
lean_object* v_res_4978_;
v_res_4978_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23(lean_box(0), lean_box(0), lean_box(0), v_f_4962_, v_keys_4963_, v_vals_4964_, lean_box(0), v_i_4966_, v_acc_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_);
stack->m_obj
 = v_res_4978_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___boxed(lean_object** _args){
lean_object* v_00_u03c3_4979_ = _args[0];
lean_object* v_00_u03b1_4980_ = _args[1];
lean_object* v_00_u03b2_4981_ = _args[2];
lean_object* v_f_4982_ = _args[3];
lean_object* v_keys_4983_ = _args[4];
lean_object* v_vals_4984_ = _args[5];
lean_object* v_heq_4985_ = _args[6];
lean_object* v_i_4986_ = _args[7];
lean_object* v_acc_4987_ = _args[8];
lean_object* v___y_4988_ = _args[9];
lean_object* v___y_4989_ = _args[10];
lean_object* v___y_4990_ = _args[11];
lean_object* v___y_4991_ = _args[12];
lean_object* v___y_4992_ = _args[13];
lean_object* v___y_4993_ = _args[14];
lean_object* v___y_4994_ = _args[15];
lean_object* v___y_4995_ = _args[16];
lean_object* v___y_4996_ = _args[17];
_start:
{
lean_object* v_res_4997_; 
v_res_4997_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23(v_00_u03c3_4979_, v_00_u03b1_4980_, v_00_u03b2_4981_, v_f_4982_, v_keys_4983_, v_vals_4984_, v_heq_4985_, v_i_4986_, v_acc_4987_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_);
lean_dec(v___y_4995_);
lean_dec_ref(v___y_4994_);
lean_dec(v___y_4993_);
lean_dec_ref(v___y_4992_);
lean_dec_ref(v___y_4991_);
lean_dec(v___y_4990_);
lean_dec_ref(v___y_4989_);
lean_dec_ref(v_vals_4984_);
lean_dec_ref(v_keys_4983_);
return v_res_4997_;
}
}
lean_object* l_Lean_Server_Completion_idCompletion(lean_object* v_uri_4998_, lean_object* v_pos_4999_, lean_object* v_completionInfoPos_5000_, lean_object* v_ctx_5001_, lean_object* v_lctx_5002_, lean_object* v_stx_5003_, lean_object* v_id_5004_, lean_object* v_hoverInfo_5005_, uint8_t v_danglingDot_5006_, lean_object* v_a_5007_){
_start:
{
lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; 
v___x_5009_ = lean_box(v_danglingDot_5006_);
lean_inc_ref(v_ctx_5001_);
v___x_5010_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___boxed), 13, 5);
lean_closure_set(v___x_5010_, 0, v_ctx_5001_);
lean_closure_set(v___x_5010_, 1, v_stx_5003_);
lean_closure_set(v___x_5010_, 2, v_id_5004_);
lean_closure_set(v___x_5010_, 3, v_hoverInfo_5005_);
lean_closure_set(v___x_5010_, 4, v___x_5009_);
v___x_5011_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_4998_, v_pos_4999_, v_completionInfoPos_5000_, v_ctx_5001_, v_lctx_5002_, v___x_5010_, v_a_5007_);
return v___x_5011_;
}
}
LEAN_EXPORT void l_Lean_Server_Completion_idCompletion_0interp(lean_interpreter_value* stack)
{
lean_object* v_uri_4998_ = stack[0].m_obj;
lean_object* v_pos_4999_ = stack[1].m_obj;
lean_object* v_completionInfoPos_5000_ = stack[2].m_obj;
lean_object* v_ctx_5001_ = stack[3].m_obj;
lean_object* v_lctx_5002_ = stack[4].m_obj;
lean_object* v_stx_5003_ = stack[5].m_obj;
lean_object* v_id_5004_ = stack[6].m_obj;
lean_object* v_hoverInfo_5005_ = stack[7].m_obj;
uint8_t v_danglingDot_5006_ = stack[8].m_num;
lean_object* v_a_5007_ = stack[9].m_obj;
lean_object* v_res_5012_;
v_res_5012_ = l_Lean_Server_Completion_idCompletion(v_uri_4998_, v_pos_4999_, v_completionInfoPos_5000_, v_ctx_5001_, v_lctx_5002_, v_stx_5003_, v_id_5004_, v_hoverInfo_5005_, v_danglingDot_5006_, v_a_5007_);
stack->m_obj
 = v_res_5012_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_idCompletion___boxed(lean_object* v_uri_5013_, lean_object* v_pos_5014_, lean_object* v_completionInfoPos_5015_, lean_object* v_ctx_5016_, lean_object* v_lctx_5017_, lean_object* v_stx_5018_, lean_object* v_id_5019_, lean_object* v_hoverInfo_5020_, lean_object* v_danglingDot_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_){
_start:
{
uint8_t v_danglingDot_boxed_5024_; lean_object* v_res_5025_; 
v_danglingDot_boxed_5024_ = lean_unbox(v_danglingDot_5021_);
v_res_5025_ = l_Lean_Server_Completion_idCompletion(v_uri_5013_, v_pos_5014_, v_completionInfoPos_5015_, v_ctx_5016_, v_lctx_5017_, v_stx_5018_, v_id_5019_, v_hoverInfo_5020_, v_danglingDot_boxed_5024_, v_a_5022_);
lean_dec_ref(v_a_5022_);
return v_res_5025_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(lean_object* v_e_5026_, lean_object* v___y_5027_){
_start:
{
uint8_t v___x_5029_; 
v___x_5029_ = l_Lean_Expr_hasMVar(v_e_5026_);
if (v___x_5029_ == 0)
{
lean_object* v___x_5030_; lean_object* v___x_5031_; 
v___x_5030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5030_, 0, v_e_5026_);
v___x_5031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5031_, 0, v___x_5030_);
return v___x_5031_;
}
else
{
lean_object* v___x_5032_; lean_object* v_mctx_5033_; lean_object* v___x_5034_; lean_object* v_fst_5035_; lean_object* v_snd_5036_; lean_object* v___x_5037_; lean_object* v_cache_5038_; lean_object* v_zetaDeltaFVarIds_5039_; lean_object* v_postponed_5040_; lean_object* v_diag_5041_; lean_object* v___x_5043_; uint8_t v_isShared_5044_; uint8_t v_isSharedCheck_5051_; 
v___x_5032_ = lean_st_ref_get(v___y_5027_);
v_mctx_5033_ = lean_ctor_get(v___x_5032_, 0);
lean_inc_ref(v_mctx_5033_);
lean_dec(v___x_5032_);
v___x_5034_ = l_Lean_instantiateMVarsCore(v_mctx_5033_, v_e_5026_);
v_fst_5035_ = lean_ctor_get(v___x_5034_, 0);
lean_inc(v_fst_5035_);
v_snd_5036_ = lean_ctor_get(v___x_5034_, 1);
lean_inc(v_snd_5036_);
lean_dec_ref(v___x_5034_);
v___x_5037_ = lean_st_ref_take(v___y_5027_);
v_cache_5038_ = lean_ctor_get(v___x_5037_, 1);
v_zetaDeltaFVarIds_5039_ = lean_ctor_get(v___x_5037_, 2);
v_postponed_5040_ = lean_ctor_get(v___x_5037_, 3);
v_diag_5041_ = lean_ctor_get(v___x_5037_, 4);
v_isSharedCheck_5051_ = !lean_is_exclusive(v___x_5037_);
if (v_isSharedCheck_5051_ == 0)
{
lean_object* v_unused_5052_; 
v_unused_5052_ = lean_ctor_get(v___x_5037_, 0);
lean_dec(v_unused_5052_);
v___x_5043_ = v___x_5037_;
v_isShared_5044_ = v_isSharedCheck_5051_;
goto v_resetjp_5042_;
}
else
{
lean_inc(v_diag_5041_);
lean_inc(v_postponed_5040_);
lean_inc(v_zetaDeltaFVarIds_5039_);
lean_inc(v_cache_5038_);
lean_dec(v___x_5037_);
v___x_5043_ = lean_box(0);
v_isShared_5044_ = v_isSharedCheck_5051_;
goto v_resetjp_5042_;
}
v_resetjp_5042_:
{
lean_object* v___x_5046_; 
if (v_isShared_5044_ == 0)
{
lean_ctor_set(v___x_5043_, 0, v_snd_5036_);
v___x_5046_ = v___x_5043_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v_snd_5036_);
lean_ctor_set(v_reuseFailAlloc_5050_, 1, v_cache_5038_);
lean_ctor_set(v_reuseFailAlloc_5050_, 2, v_zetaDeltaFVarIds_5039_);
lean_ctor_set(v_reuseFailAlloc_5050_, 3, v_postponed_5040_);
lean_ctor_set(v_reuseFailAlloc_5050_, 4, v_diag_5041_);
v___x_5046_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; 
v___x_5047_ = lean_st_ref_put(v___y_5027_, v___x_5046_);
v___x_5048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5048_, 0, v_fst_5035_);
v___x_5049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5049_, 0, v___x_5048_);
return v___x_5049_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5026_ = stack[0].m_obj;
lean_object* v___y_5027_ = stack[1].m_obj;
lean_object* v_res_5053_;
v_res_5053_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_e_5026_, v___y_5027_);
stack->m_obj
 = v_res_5053_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg___boxed(lean_object* v_e_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_){
_start:
{
lean_object* v_res_5057_; 
v_res_5057_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_e_5054_, v___y_5055_);
lean_dec(v___y_5055_);
return v_res_5057_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0(lean_object* v_e_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_){
_start:
{
lean_object* v___x_5067_; 
v___x_5067_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_e_5058_, v___y_5063_);
return v___x_5067_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5058_ = stack[0].m_obj;
lean_object* v___y_5059_ = stack[1].m_obj;
lean_object* v___y_5060_ = stack[2].m_obj;
lean_object* v___y_5061_ = stack[3].m_obj;
lean_object* v___y_5062_ = stack[4].m_obj;
lean_object* v___y_5063_ = stack[5].m_obj;
lean_object* v___y_5064_ = stack[6].m_obj;
lean_object* v___y_5065_ = stack[7].m_obj;
lean_object* v_res_5068_;
v_res_5068_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0(v_e_5058_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_);
stack->m_obj
 = v_res_5068_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___boxed(lean_object* v_e_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_){
_start:
{
lean_object* v_res_5078_; 
v_res_5078_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0(v_e_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_);
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
lean_dec(v___y_5074_);
lean_dec_ref(v___y_5073_);
lean_dec_ref(v___y_5072_);
lean_dec(v___y_5071_);
lean_dec_ref(v___y_5070_);
return v_res_5078_;
}
}
lean_object* l_Lean_Server_Completion_dotCompletion___lam__0(lean_object* v_a_5079_, lean_object* v_declName_5080_, lean_object* v_decl_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_){
_start:
{
lean_object* v_unnormedTypeName_5090_; uint8_t v___x_5091_; 
v_unnormedTypeName_5090_ = l_Lean_Name_getPrefix(v_declName_5080_);
v___x_5091_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_unnormedTypeName_5090_, v_a_5079_);
if (v___x_5091_ == 0)
{
lean_object* v___x_5092_; lean_object* v___x_5093_; 
lean_dec_ref(v_decl_5081_);
lean_dec(v_declName_5080_);
v___x_5092_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5093_, 0, v___x_5092_);
return v___x_5093_;
}
else
{
lean_object* v___x_5094_; lean_object* v_a_5095_; lean_object* v___x_5097_; uint8_t v_isShared_5098_; uint8_t v_isSharedCheck_5160_; 
v___x_5094_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_5080_, v___y_5088_);
v_a_5095_ = lean_ctor_get(v___x_5094_, 0);
v_isSharedCheck_5160_ = !lean_is_exclusive(v___x_5094_);
if (v_isSharedCheck_5160_ == 0)
{
v___x_5097_ = v___x_5094_;
v_isShared_5098_ = v_isSharedCheck_5160_;
goto v_resetjp_5096_;
}
else
{
lean_inc(v_a_5095_);
lean_dec(v___x_5094_);
v___x_5097_ = lean_box(0);
v_isShared_5098_ = v_isSharedCheck_5160_;
goto v_resetjp_5096_;
}
v_resetjp_5096_:
{
if (lean_obj_tag(v_a_5095_) == 1)
{
lean_object* v_val_5099_; lean_object* v___x_5101_; uint8_t v_isShared_5102_; uint8_t v_isSharedCheck_5155_; 
lean_del_object(v___x_5097_);
v_val_5099_ = lean_ctor_get(v_a_5095_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v_a_5095_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5101_ = v_a_5095_;
v_isShared_5102_ = v_isSharedCheck_5155_;
goto v_resetjp_5100_;
}
else
{
lean_inc(v_val_5099_);
lean_dec(v_a_5095_);
v___x_5101_ = lean_box(0);
v_isShared_5102_ = v_isSharedCheck_5155_;
goto v_resetjp_5100_;
}
v_resetjp_5100_:
{
lean_object* v_info_5103_; lean_object* v_kind_5104_; lean_object* v_tags_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; 
v_info_5103_ = lean_ctor_get(v_decl_5081_, 0);
lean_inc_ref(v_info_5103_);
v_kind_5104_ = lean_ctor_get(v_decl_5081_, 1);
lean_inc_ref(v_kind_5104_);
v_tags_5105_ = lean_ctor_get(v_decl_5081_, 2);
lean_inc_ref(v_tags_5105_);
lean_dec_ref(v_decl_5081_);
v___x_5106_ = l_Lean_Name_getPrefix(v_val_5099_);
lean_dec(v_val_5099_);
v___x_5107_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(v___x_5106_, v_info_5103_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_);
if (lean_obj_tag(v___x_5107_) == 0)
{
lean_object* v_a_5108_; lean_object* v___x_5110_; uint8_t v_isShared_5111_; uint8_t v_isSharedCheck_5146_; 
v_a_5108_ = lean_ctor_get(v___x_5107_, 0);
v_isSharedCheck_5146_ = !lean_is_exclusive(v___x_5107_);
if (v_isSharedCheck_5146_ == 0)
{
v___x_5110_ = v___x_5107_;
v_isShared_5111_ = v_isSharedCheck_5146_;
goto v_resetjp_5109_;
}
else
{
lean_inc(v_a_5108_);
lean_dec(v___x_5107_);
v___x_5110_ = lean_box(0);
v_isShared_5111_ = v_isSharedCheck_5146_;
goto v_resetjp_5109_;
}
v_resetjp_5109_:
{
uint8_t v___x_5112_; 
v___x_5112_ = lean_unbox(v_a_5108_);
lean_dec(v_a_5108_);
if (v___x_5112_ == 0)
{
lean_object* v___x_5113_; lean_object* v___x_5115_; 
lean_dec_ref(v_tags_5105_);
lean_dec_ref(v_kind_5104_);
lean_dec_ref(v_info_5103_);
lean_del_object(v___x_5101_);
v___x_5113_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5111_ == 0)
{
lean_ctor_set(v___x_5110_, 0, v___x_5113_);
v___x_5115_ = v___x_5110_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v___x_5113_);
v___x_5115_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
return v___x_5115_;
}
}
else
{
lean_object* v___x_5117_; 
lean_del_object(v___x_5110_);
lean_inc(v___y_5088_);
lean_inc_ref(v___y_5087_);
lean_inc(v___y_5086_);
lean_inc_ref(v___y_5085_);
v___x_5117_ = lean_apply_5(v_kind_5104_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_, lean_box(0));
if (lean_obj_tag(v___x_5117_) == 0)
{
lean_object* v_a_5118_; lean_object* v___x_5119_; 
v_a_5118_ = lean_ctor_get(v___x_5117_, 0);
lean_inc(v_a_5118_);
lean_dec_ref_known(v___x_5117_, 1);
lean_inc(v___y_5088_);
lean_inc_ref(v___y_5087_);
lean_inc(v___y_5086_);
lean_inc_ref(v___y_5085_);
v___x_5119_ = lean_apply_5(v_tags_5105_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_, lean_box(0));
if (lean_obj_tag(v___x_5119_) == 0)
{
lean_object* v_a_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5126_; 
v_a_5120_ = lean_ctor_get(v___x_5119_, 0);
lean_inc(v_a_5120_);
lean_dec_ref_known(v___x_5119_, 1);
v___x_5121_ = l_Lean_ConstantInfo_name(v_info_5103_);
lean_dec_ref(v_info_5103_);
v___x_5122_ = l_Lean_Name_getString_x21(v___x_5121_);
v___x_5123_ = lean_box(0);
v___x_5124_ = l_Lean_Name_str___override(v___x_5123_, v___x_5122_);
if (v_isShared_5102_ == 0)
{
lean_ctor_set_tag(v___x_5101_, 0);
lean_ctor_set(v___x_5101_, 0, v___x_5121_);
v___x_5126_ = v___x_5101_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v___x_5121_);
v___x_5126_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
uint8_t v___x_5127_; lean_object* v___x_5128_; 
v___x_5127_ = lean_unbox(v_a_5118_);
lean_dec(v_a_5118_);
v___x_5128_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_5124_, v___x_5126_, v___x_5127_, v_a_5120_, v___y_5082_, v___y_5083_);
return v___x_5128_;
}
}
else
{
lean_object* v_a_5130_; lean_object* v___x_5132_; uint8_t v_isShared_5133_; uint8_t v_isSharedCheck_5137_; 
lean_dec(v_a_5118_);
lean_dec_ref(v_info_5103_);
lean_del_object(v___x_5101_);
v_a_5130_ = lean_ctor_get(v___x_5119_, 0);
v_isSharedCheck_5137_ = !lean_is_exclusive(v___x_5119_);
if (v_isSharedCheck_5137_ == 0)
{
v___x_5132_ = v___x_5119_;
v_isShared_5133_ = v_isSharedCheck_5137_;
goto v_resetjp_5131_;
}
else
{
lean_inc(v_a_5130_);
lean_dec(v___x_5119_);
v___x_5132_ = lean_box(0);
v_isShared_5133_ = v_isSharedCheck_5137_;
goto v_resetjp_5131_;
}
v_resetjp_5131_:
{
lean_object* v___x_5135_; 
if (v_isShared_5133_ == 0)
{
v___x_5135_ = v___x_5132_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v_a_5130_);
v___x_5135_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
return v___x_5135_;
}
}
}
}
else
{
lean_object* v_a_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5145_; 
lean_dec_ref(v_tags_5105_);
lean_dec_ref(v_info_5103_);
lean_del_object(v___x_5101_);
v_a_5138_ = lean_ctor_get(v___x_5117_, 0);
v_isSharedCheck_5145_ = !lean_is_exclusive(v___x_5117_);
if (v_isSharedCheck_5145_ == 0)
{
v___x_5140_ = v___x_5117_;
v_isShared_5141_ = v_isSharedCheck_5145_;
goto v_resetjp_5139_;
}
else
{
lean_inc(v_a_5138_);
lean_dec(v___x_5117_);
v___x_5140_ = lean_box(0);
v_isShared_5141_ = v_isSharedCheck_5145_;
goto v_resetjp_5139_;
}
v_resetjp_5139_:
{
lean_object* v___x_5143_; 
if (v_isShared_5141_ == 0)
{
v___x_5143_ = v___x_5140_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v_a_5138_);
v___x_5143_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
return v___x_5143_;
}
}
}
}
}
}
else
{
lean_object* v_a_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5154_; 
lean_dec_ref(v_tags_5105_);
lean_dec_ref(v_kind_5104_);
lean_dec_ref(v_info_5103_);
lean_del_object(v___x_5101_);
v_a_5147_ = lean_ctor_get(v___x_5107_, 0);
v_isSharedCheck_5154_ = !lean_is_exclusive(v___x_5107_);
if (v_isSharedCheck_5154_ == 0)
{
v___x_5149_ = v___x_5107_;
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_a_5147_);
lean_dec(v___x_5107_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___x_5152_; 
if (v_isShared_5150_ == 0)
{
v___x_5152_ = v___x_5149_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_a_5147_);
v___x_5152_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
return v___x_5152_;
}
}
}
}
}
else
{
lean_object* v___x_5156_; lean_object* v___x_5158_; 
lean_dec(v_a_5095_);
lean_dec_ref(v_decl_5081_);
v___x_5156_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5098_ == 0)
{
lean_ctor_set(v___x_5097_, 0, v___x_5156_);
v___x_5158_ = v___x_5097_;
goto v_reusejp_5157_;
}
else
{
lean_object* v_reuseFailAlloc_5159_; 
v_reuseFailAlloc_5159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5159_, 0, v___x_5156_);
v___x_5158_ = v_reuseFailAlloc_5159_;
goto v_reusejp_5157_;
}
v_reusejp_5157_:
{
return v___x_5158_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_Completion_dotCompletion___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5079_ = stack[0].m_obj;
lean_object* v_declName_5080_ = stack[1].m_obj;
lean_object* v_decl_5081_ = stack[2].m_obj;
lean_object* v___y_5082_ = stack[3].m_obj;
lean_object* v___y_5083_ = stack[4].m_obj;
lean_object* v___y_5084_ = stack[5].m_obj;
lean_object* v___y_5085_ = stack[6].m_obj;
lean_object* v___y_5086_ = stack[7].m_obj;
lean_object* v___y_5087_ = stack[8].m_obj;
lean_object* v___y_5088_ = stack[9].m_obj;
lean_object* v_res_5161_;
v_res_5161_ = l_Lean_Server_Completion_dotCompletion___lam__0(v_a_5079_, v_declName_5080_, v_decl_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_);
stack->m_obj
 = v_res_5161_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__0___boxed(lean_object* v_a_5162_, lean_object* v_declName_5163_, lean_object* v_decl_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_){
_start:
{
lean_object* v_res_5173_; 
v_res_5173_ = l_Lean_Server_Completion_dotCompletion___lam__0(v_a_5162_, v_declName_5163_, v_decl_5164_, v___y_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_);
lean_dec(v___y_5171_);
lean_dec_ref(v___y_5170_);
lean_dec(v___y_5169_);
lean_dec_ref(v___y_5168_);
lean_dec_ref(v___y_5167_);
lean_dec(v___y_5166_);
lean_dec_ref(v___y_5165_);
return v_res_5173_;
}
}
lean_object* l_Lean_Server_Completion_dotCompletion___lam__1(lean_object* v_expr_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_){
_start:
{
lean_object* v_a_5187_; lean_object* v___y_5191_; uint8_t v___y_5192_; lean_object* v___y_5202_; lean_object* v_a_5203_; lean_object* v___x_5206_; 
lean_inc(v___y_5181_);
lean_inc_ref(v___y_5180_);
lean_inc(v___y_5179_);
lean_inc_ref(v___y_5178_);
v___x_5206_ = lean_infer_type(v_expr_5174_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_);
if (lean_obj_tag(v___x_5206_) == 0)
{
lean_object* v_a_5207_; lean_object* v___x_5208_; lean_object* v_a_5209_; lean_object* v_a_5210_; lean_object* v___x_5211_; 
v_a_5207_ = lean_ctor_get(v___x_5206_, 0);
lean_inc(v_a_5207_);
lean_dec_ref_known(v___x_5206_, 1);
v___x_5208_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_a_5207_, v___y_5179_);
v_a_5209_ = lean_ctor_get(v___x_5208_, 0);
lean_inc(v_a_5209_);
lean_dec_ref(v___x_5208_);
v_a_5210_ = lean_ctor_get(v_a_5209_, 0);
lean_inc(v_a_5210_);
lean_dec(v_a_5209_);
v___x_5211_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(v_a_5210_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_);
if (lean_obj_tag(v___x_5211_) == 0)
{
lean_object* v_a_5212_; 
v_a_5212_ = lean_ctor_get(v___x_5211_, 0);
lean_inc(v_a_5212_);
lean_dec_ref_known(v___x_5211_, 1);
v_a_5187_ = v_a_5212_;
goto v___jp_5186_;
}
else
{
lean_object* v_a_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5220_; 
v_a_5213_ = lean_ctor_get(v___x_5211_, 0);
v_isSharedCheck_5220_ = !lean_is_exclusive(v___x_5211_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5215_ = v___x_5211_;
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_a_5213_);
lean_dec(v___x_5211_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
lean_object* v___x_5218_; 
lean_inc(v_a_5213_);
if (v_isShared_5216_ == 0)
{
v___x_5218_ = v___x_5215_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_a_5213_);
v___x_5218_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
v___y_5202_ = v___x_5218_;
v_a_5203_ = v_a_5213_;
goto v___jp_5201_;
}
}
}
}
else
{
lean_object* v_a_5221_; lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5228_; 
v_a_5221_ = lean_ctor_get(v___x_5206_, 0);
v_isSharedCheck_5228_ = !lean_is_exclusive(v___x_5206_);
if (v_isSharedCheck_5228_ == 0)
{
v___x_5223_ = v___x_5206_;
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
else
{
lean_inc(v_a_5221_);
lean_dec(v___x_5206_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
lean_object* v___x_5226_; 
lean_inc(v_a_5221_);
if (v_isShared_5224_ == 0)
{
v___x_5226_ = v___x_5223_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_a_5221_);
v___x_5226_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
v___y_5202_ = v___x_5226_;
v_a_5203_ = v_a_5221_;
goto v___jp_5201_;
}
}
}
v___jp_5183_:
{
lean_object* v___x_5184_; lean_object* v___x_5185_; 
v___x_5184_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5185_, 0, v___x_5184_);
return v___x_5185_;
}
v___jp_5186_:
{
if (lean_obj_tag(v_a_5187_) == 0)
{
lean_object* v___f_5188_; lean_object* v___x_5189_; 
v___f_5188_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotCompletion___lam__0___boxed), 11, 1);
lean_closure_set(v___f_5188_, 0, v_a_5187_);
v___x_5189_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___f_5188_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_);
return v___x_5189_;
}
else
{
goto v___jp_5183_;
}
}
v___jp_5190_:
{
if (v___y_5192_ == 0)
{
lean_dec_ref(v___y_5191_);
goto v___jp_5183_;
}
else
{
lean_object* v_a_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5200_; 
v_a_5193_ = lean_ctor_get(v___y_5191_, 0);
v_isSharedCheck_5200_ = !lean_is_exclusive(v___y_5191_);
if (v_isSharedCheck_5200_ == 0)
{
v___x_5195_ = v___y_5191_;
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_a_5193_);
lean_dec(v___y_5191_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5198_; 
if (v_isShared_5196_ == 0)
{
v___x_5198_ = v___x_5195_;
goto v_reusejp_5197_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v_a_5193_);
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
v___jp_5201_:
{
uint8_t v___x_5204_; 
v___x_5204_ = l_Lean_Exception_isInterrupt(v_a_5203_);
if (v___x_5204_ == 0)
{
uint8_t v___x_5205_; 
v___x_5205_ = l_Lean_Exception_isRuntime(v_a_5203_);
v___y_5191_ = v___y_5202_;
v___y_5192_ = v___x_5205_;
goto v___jp_5190_;
}
else
{
lean_dec_ref(v_a_5203_);
v___y_5191_ = v___y_5202_;
v___y_5192_ = v___x_5204_;
goto v___jp_5190_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_Completion_dotCompletion___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_5174_ = stack[0].m_obj;
lean_object* v___y_5175_ = stack[1].m_obj;
lean_object* v___y_5176_ = stack[2].m_obj;
lean_object* v___y_5177_ = stack[3].m_obj;
lean_object* v___y_5178_ = stack[4].m_obj;
lean_object* v___y_5179_ = stack[5].m_obj;
lean_object* v___y_5180_ = stack[6].m_obj;
lean_object* v___y_5181_ = stack[7].m_obj;
lean_object* v_res_5229_;
v_res_5229_ = l_Lean_Server_Completion_dotCompletion___lam__1(v_expr_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_);
stack->m_obj
 = v_res_5229_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__1___boxed(lean_object* v_expr_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_){
_start:
{
lean_object* v_res_5239_; 
v_res_5239_ = l_Lean_Server_Completion_dotCompletion___lam__1(v_expr_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_, v___y_5237_);
lean_dec(v___y_5237_);
lean_dec_ref(v___y_5236_);
lean_dec(v___y_5235_);
lean_dec_ref(v___y_5234_);
lean_dec_ref(v___y_5233_);
lean_dec(v___y_5232_);
lean_dec_ref(v___y_5231_);
return v_res_5239_;
}
}
lean_object* l_Lean_Server_Completion_dotCompletion(lean_object* v_uri_5240_, lean_object* v_pos_5241_, lean_object* v_completionInfoPos_5242_, lean_object* v_ctx_5243_, lean_object* v_info_5244_, lean_object* v_a_5245_){
_start:
{
lean_object* v_lctx_5247_; lean_object* v_expr_5248_; lean_object* v___f_5249_; lean_object* v___x_5250_; 
v_lctx_5247_ = lean_ctor_get(v_info_5244_, 1);
lean_inc_ref(v_lctx_5247_);
v_expr_5248_ = lean_ctor_get(v_info_5244_, 3);
lean_inc_ref(v_expr_5248_);
lean_dec_ref(v_info_5244_);
v___f_5249_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotCompletion___lam__1___boxed), 9, 1);
lean_closure_set(v___f_5249_, 0, v_expr_5248_);
v___x_5250_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5240_, v_pos_5241_, v_completionInfoPos_5242_, v_ctx_5243_, v_lctx_5247_, v___f_5249_, v_a_5245_);
return v___x_5250_;
}
}
LEAN_EXPORT void l_Lean_Server_Completion_dotCompletion_0interp(lean_interpreter_value* stack)
{
lean_object* v_uri_5240_ = stack[0].m_obj;
lean_object* v_pos_5241_ = stack[1].m_obj;
lean_object* v_completionInfoPos_5242_ = stack[2].m_obj;
lean_object* v_ctx_5243_ = stack[3].m_obj;
lean_object* v_info_5244_ = stack[4].m_obj;
lean_object* v_a_5245_ = stack[5].m_obj;
lean_object* v_res_5251_;
v_res_5251_ = l_Lean_Server_Completion_dotCompletion(v_uri_5240_, v_pos_5241_, v_completionInfoPos_5242_, v_ctx_5243_, v_info_5244_, v_a_5245_);
stack->m_obj
 = v_res_5251_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___boxed(lean_object* v_uri_5252_, lean_object* v_pos_5253_, lean_object* v_completionInfoPos_5254_, lean_object* v_ctx_5255_, lean_object* v_info_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_){
_start:
{
lean_object* v_res_5259_; 
v_res_5259_ = l_Lean_Server_Completion_dotCompletion(v_uri_5252_, v_pos_5253_, v_completionInfoPos_5254_, v_ctx_5255_, v_info_5256_, v_a_5257_);
lean_dec_ref(v_a_5257_);
return v_res_5259_;
}
}
lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__0(lean_object* v___x_5260_, lean_object* v_id_5261_, lean_object* v_declName_5262_, lean_object* v_decl_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_){
_start:
{
lean_object* v___x_5272_; uint8_t v___x_5273_; 
v___x_5272_ = l_Lean_Name_getPrefix(v_declName_5262_);
lean_inc(v___x_5260_);
v___x_5273_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v___x_5272_, v___x_5260_);
if (v___x_5273_ == 0)
{
lean_object* v___x_5274_; lean_object* v___x_5275_; 
lean_dec_ref(v_decl_5263_);
lean_dec(v_declName_5262_);
lean_dec(v___x_5260_);
v___x_5274_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5275_, 0, v___x_5274_);
return v___x_5275_;
}
else
{
lean_object* v___x_5276_; lean_object* v_a_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5373_; 
v___x_5276_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_5262_, v___y_5270_);
v_a_5277_ = lean_ctor_get(v___x_5276_, 0);
v_isSharedCheck_5373_ = !lean_is_exclusive(v___x_5276_);
if (v_isSharedCheck_5373_ == 0)
{
v___x_5279_ = v___x_5276_;
v_isShared_5280_ = v_isSharedCheck_5373_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_a_5277_);
lean_dec(v___x_5276_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5373_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
if (lean_obj_tag(v_a_5277_) == 1)
{
lean_object* v_val_5281_; lean_object* v___x_5283_; uint8_t v_isShared_5284_; uint8_t v_isSharedCheck_5368_; 
lean_del_object(v___x_5279_);
v_val_5281_ = lean_ctor_get(v_a_5277_, 0);
v_isSharedCheck_5368_ = !lean_is_exclusive(v_a_5277_);
if (v_isSharedCheck_5368_ == 0)
{
v___x_5283_ = v_a_5277_;
v_isShared_5284_ = v_isSharedCheck_5368_;
goto v_resetjp_5282_;
}
else
{
lean_inc(v_val_5281_);
lean_dec(v_a_5277_);
v___x_5283_ = lean_box(0);
v_isShared_5284_ = v_isSharedCheck_5368_;
goto v_resetjp_5282_;
}
v_resetjp_5282_:
{
lean_object* v_info_5285_; lean_object* v_kind_5286_; lean_object* v_tags_5287_; lean_object* v___x_5288_; 
v_info_5285_ = lean_ctor_get(v_decl_5263_, 0);
lean_inc_ref(v_info_5285_);
v_kind_5286_ = lean_ctor_get(v_decl_5263_, 1);
lean_inc_ref(v_kind_5286_);
v_tags_5287_ = lean_ctor_get(v_decl_5263_, 2);
lean_inc_ref(v_tags_5287_);
lean_dec_ref(v_decl_5263_);
v___x_5288_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(v___x_5260_, v_info_5285_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_);
if (lean_obj_tag(v___x_5288_) == 0)
{
lean_object* v_a_5289_; lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5359_; 
v_a_5289_ = lean_ctor_get(v___x_5288_, 0);
v_isSharedCheck_5359_ = !lean_is_exclusive(v___x_5288_);
if (v_isSharedCheck_5359_ == 0)
{
v___x_5291_ = v___x_5288_;
v_isShared_5292_ = v_isSharedCheck_5359_;
goto v_resetjp_5290_;
}
else
{
lean_inc(v_a_5289_);
lean_dec(v___x_5288_);
v___x_5291_ = lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5359_;
goto v_resetjp_5290_;
}
v_resetjp_5290_:
{
uint8_t v___x_5293_; 
v___x_5293_ = lean_unbox(v_a_5289_);
lean_dec(v_a_5289_);
if (v___x_5293_ == 0)
{
lean_object* v___x_5294_; lean_object* v___x_5296_; 
lean_dec_ref(v_tags_5287_);
lean_dec_ref(v_kind_5286_);
lean_dec_ref(v_info_5285_);
lean_del_object(v___x_5283_);
lean_dec(v_val_5281_);
v___x_5294_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5292_ == 0)
{
lean_ctor_set(v___x_5291_, 0, v___x_5294_);
v___x_5296_ = v___x_5291_;
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
else
{
lean_object* v___x_5298_; 
lean_del_object(v___x_5291_);
lean_inc(v___y_5270_);
lean_inc_ref(v___y_5269_);
lean_inc(v___y_5268_);
lean_inc_ref(v___y_5267_);
v___x_5298_ = lean_apply_5(v_kind_5286_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, lean_box(0));
if (lean_obj_tag(v___x_5298_) == 0)
{
lean_object* v_a_5299_; lean_object* v___x_5300_; 
v_a_5299_ = lean_ctor_get(v___x_5298_, 0);
lean_inc(v_a_5299_);
lean_dec_ref_known(v___x_5298_, 1);
lean_inc(v___y_5270_);
lean_inc_ref(v___y_5269_);
lean_inc(v___y_5268_);
lean_inc_ref(v___y_5267_);
v___x_5300_ = lean_apply_5(v_tags_5287_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, lean_box(0));
if (lean_obj_tag(v___x_5300_) == 0)
{
lean_object* v_a_5301_; uint8_t v___x_5302_; 
v_a_5301_ = lean_ctor_get(v___x_5300_, 0);
lean_inc(v_a_5301_);
lean_dec_ref_known(v___x_5300_, 1);
v___x_5302_ = l_Lean_Name_isAnonymous(v_id_5261_);
if (v___x_5302_ == 0)
{
lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v_a_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5324_; 
lean_del_object(v___x_5283_);
v___x_5303_ = l_Lean_Name_getPrefix(v_val_5281_);
v___x_5304_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v___x_5303_, v_id_5261_, v___x_5302_, v_val_5281_, v___y_5270_);
lean_dec(v___x_5303_);
v_a_5305_ = lean_ctor_get(v___x_5304_, 0);
v_isSharedCheck_5324_ = !lean_is_exclusive(v___x_5304_);
if (v_isSharedCheck_5324_ == 0)
{
v___x_5307_ = v___x_5304_;
v_isShared_5308_ = v_isSharedCheck_5324_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_a_5305_);
lean_dec(v___x_5304_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5324_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
if (lean_obj_tag(v_a_5305_) == 1)
{
lean_object* v_val_5309_; lean_object* v___x_5311_; uint8_t v_isShared_5312_; uint8_t v_isSharedCheck_5319_; 
lean_del_object(v___x_5307_);
v_val_5309_ = lean_ctor_get(v_a_5305_, 0);
v_isSharedCheck_5319_ = !lean_is_exclusive(v_a_5305_);
if (v_isSharedCheck_5319_ == 0)
{
v___x_5311_ = v_a_5305_;
v_isShared_5312_ = v_isSharedCheck_5319_;
goto v_resetjp_5310_;
}
else
{
lean_inc(v_val_5309_);
lean_dec(v_a_5305_);
v___x_5311_ = lean_box(0);
v_isShared_5312_ = v_isSharedCheck_5319_;
goto v_resetjp_5310_;
}
v_resetjp_5310_:
{
lean_object* v___x_5313_; lean_object* v___x_5315_; 
v___x_5313_ = l_Lean_ConstantInfo_name(v_info_5285_);
lean_dec_ref(v_info_5285_);
if (v_isShared_5312_ == 0)
{
lean_ctor_set_tag(v___x_5311_, 0);
lean_ctor_set(v___x_5311_, 0, v___x_5313_);
v___x_5315_ = v___x_5311_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v___x_5313_);
v___x_5315_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
uint8_t v___x_5316_; lean_object* v___x_5317_; 
v___x_5316_ = lean_unbox(v_a_5299_);
lean_dec(v_a_5299_);
v___x_5317_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_val_5309_, v___x_5315_, v___x_5316_, v_a_5301_, v___y_5264_, v___y_5265_);
return v___x_5317_;
}
}
}
else
{
lean_object* v___x_5320_; lean_object* v___x_5322_; 
lean_dec(v_a_5305_);
lean_dec(v_a_5301_);
lean_dec(v_a_5299_);
lean_dec_ref(v_info_5285_);
v___x_5320_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 0, v___x_5320_);
v___x_5322_ = v___x_5307_;
goto v_reusejp_5321_;
}
else
{
lean_object* v_reuseFailAlloc_5323_; 
v_reuseFailAlloc_5323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5323_, 0, v___x_5320_);
v___x_5322_ = v_reuseFailAlloc_5323_;
goto v_reusejp_5321_;
}
v_reusejp_5321_:
{
return v___x_5322_;
}
}
}
}
else
{
lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5330_; 
lean_dec(v_val_5281_);
v___x_5325_ = l_Lean_ConstantInfo_name(v_info_5285_);
lean_dec_ref(v_info_5285_);
v___x_5326_ = l_Lean_Name_getString_x21(v___x_5325_);
v___x_5327_ = lean_box(0);
v___x_5328_ = l_Lean_Name_str___override(v___x_5327_, v___x_5326_);
if (v_isShared_5284_ == 0)
{
lean_ctor_set_tag(v___x_5283_, 0);
lean_ctor_set(v___x_5283_, 0, v___x_5325_);
v___x_5330_ = v___x_5283_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v___x_5325_);
v___x_5330_ = v_reuseFailAlloc_5342_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
uint8_t v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5334_; uint8_t v_isShared_5335_; uint8_t v_isSharedCheck_5340_; 
v___x_5331_ = lean_unbox(v_a_5299_);
lean_dec(v_a_5299_);
v___x_5332_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_5328_, v___x_5330_, v___x_5331_, v_a_5301_, v___y_5264_, v___y_5265_);
v_isSharedCheck_5340_ = !lean_is_exclusive(v___x_5332_);
if (v_isSharedCheck_5340_ == 0)
{
lean_object* v_unused_5341_; 
v_unused_5341_ = lean_ctor_get(v___x_5332_, 0);
lean_dec(v_unused_5341_);
v___x_5334_ = v___x_5332_;
v_isShared_5335_ = v_isSharedCheck_5340_;
goto v_resetjp_5333_;
}
else
{
lean_dec(v___x_5332_);
v___x_5334_ = lean_box(0);
v_isShared_5335_ = v_isSharedCheck_5340_;
goto v_resetjp_5333_;
}
v_resetjp_5333_:
{
lean_object* v___x_5336_; lean_object* v___x_5338_; 
v___x_5336_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5335_ == 0)
{
lean_ctor_set(v___x_5334_, 0, v___x_5336_);
v___x_5338_ = v___x_5334_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5339_; 
v_reuseFailAlloc_5339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5339_, 0, v___x_5336_);
v___x_5338_ = v_reuseFailAlloc_5339_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
return v___x_5338_;
}
}
}
}
}
else
{
lean_object* v_a_5343_; lean_object* v___x_5345_; uint8_t v_isShared_5346_; uint8_t v_isSharedCheck_5350_; 
lean_dec(v_a_5299_);
lean_dec_ref(v_info_5285_);
lean_del_object(v___x_5283_);
lean_dec(v_val_5281_);
v_a_5343_ = lean_ctor_get(v___x_5300_, 0);
v_isSharedCheck_5350_ = !lean_is_exclusive(v___x_5300_);
if (v_isSharedCheck_5350_ == 0)
{
v___x_5345_ = v___x_5300_;
v_isShared_5346_ = v_isSharedCheck_5350_;
goto v_resetjp_5344_;
}
else
{
lean_inc(v_a_5343_);
lean_dec(v___x_5300_);
v___x_5345_ = lean_box(0);
v_isShared_5346_ = v_isSharedCheck_5350_;
goto v_resetjp_5344_;
}
v_resetjp_5344_:
{
lean_object* v___x_5348_; 
if (v_isShared_5346_ == 0)
{
v___x_5348_ = v___x_5345_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5349_; 
v_reuseFailAlloc_5349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_a_5343_);
v___x_5348_ = v_reuseFailAlloc_5349_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
return v___x_5348_;
}
}
}
}
else
{
lean_object* v_a_5351_; lean_object* v___x_5353_; uint8_t v_isShared_5354_; uint8_t v_isSharedCheck_5358_; 
lean_dec_ref(v_tags_5287_);
lean_dec_ref(v_info_5285_);
lean_del_object(v___x_5283_);
lean_dec(v_val_5281_);
v_a_5351_ = lean_ctor_get(v___x_5298_, 0);
v_isSharedCheck_5358_ = !lean_is_exclusive(v___x_5298_);
if (v_isSharedCheck_5358_ == 0)
{
v___x_5353_ = v___x_5298_;
v_isShared_5354_ = v_isSharedCheck_5358_;
goto v_resetjp_5352_;
}
else
{
lean_inc(v_a_5351_);
lean_dec(v___x_5298_);
v___x_5353_ = lean_box(0);
v_isShared_5354_ = v_isSharedCheck_5358_;
goto v_resetjp_5352_;
}
v_resetjp_5352_:
{
lean_object* v___x_5356_; 
if (v_isShared_5354_ == 0)
{
v___x_5356_ = v___x_5353_;
goto v_reusejp_5355_;
}
else
{
lean_object* v_reuseFailAlloc_5357_; 
v_reuseFailAlloc_5357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5357_, 0, v_a_5351_);
v___x_5356_ = v_reuseFailAlloc_5357_;
goto v_reusejp_5355_;
}
v_reusejp_5355_:
{
return v___x_5356_;
}
}
}
}
}
}
else
{
lean_object* v_a_5360_; lean_object* v___x_5362_; uint8_t v_isShared_5363_; uint8_t v_isSharedCheck_5367_; 
lean_dec_ref(v_tags_5287_);
lean_dec_ref(v_kind_5286_);
lean_dec_ref(v_info_5285_);
lean_del_object(v___x_5283_);
lean_dec(v_val_5281_);
v_a_5360_ = lean_ctor_get(v___x_5288_, 0);
v_isSharedCheck_5367_ = !lean_is_exclusive(v___x_5288_);
if (v_isSharedCheck_5367_ == 0)
{
v___x_5362_ = v___x_5288_;
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
else
{
lean_inc(v_a_5360_);
lean_dec(v___x_5288_);
v___x_5362_ = lean_box(0);
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
v_resetjp_5361_:
{
lean_object* v___x_5365_; 
if (v_isShared_5363_ == 0)
{
v___x_5365_ = v___x_5362_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_a_5360_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
}
}
}
else
{
lean_object* v___x_5369_; lean_object* v___x_5371_; 
lean_dec(v_a_5277_);
lean_dec_ref(v_decl_5263_);
lean_dec(v___x_5260_);
v___x_5369_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5280_ == 0)
{
lean_ctor_set(v___x_5279_, 0, v___x_5369_);
v___x_5371_ = v___x_5279_;
goto v_reusejp_5370_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v___x_5369_);
v___x_5371_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5370_;
}
v_reusejp_5370_:
{
return v___x_5371_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_Completion_dotIdCompletion___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5260_ = stack[0].m_obj;
lean_object* v_id_5261_ = stack[1].m_obj;
lean_object* v_declName_5262_ = stack[2].m_obj;
lean_object* v_decl_5263_ = stack[3].m_obj;
lean_object* v___y_5264_ = stack[4].m_obj;
lean_object* v___y_5265_ = stack[5].m_obj;
lean_object* v___y_5266_ = stack[6].m_obj;
lean_object* v___y_5267_ = stack[7].m_obj;
lean_object* v___y_5268_ = stack[8].m_obj;
lean_object* v___y_5269_ = stack[9].m_obj;
lean_object* v___y_5270_ = stack[10].m_obj;
lean_object* v_res_5374_;
v_res_5374_ = l_Lean_Server_Completion_dotIdCompletion___lam__0(v___x_5260_, v_id_5261_, v_declName_5262_, v_decl_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_);
stack->m_obj
 = v_res_5374_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__0___boxed(lean_object* v___x_5375_, lean_object* v_id_5376_, lean_object* v_declName_5377_, lean_object* v_decl_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_){
_start:
{
lean_object* v_res_5387_; 
v_res_5387_ = l_Lean_Server_Completion_dotIdCompletion___lam__0(v___x_5375_, v_id_5376_, v_declName_5377_, v_decl_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_);
lean_dec(v___y_5385_);
lean_dec_ref(v___y_5384_);
lean_dec(v___y_5383_);
lean_dec_ref(v___y_5382_);
lean_dec_ref(v___y_5381_);
lean_dec(v___y_5380_);
lean_dec_ref(v___y_5379_);
lean_dec(v_id_5376_);
return v_res_5387_;
}
}
lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__1(lean_object* v_expectedType_x3f_5388_, lean_object* v_id_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_){
_start:
{
if (lean_obj_tag(v_expectedType_x3f_5388_) == 1)
{
lean_object* v_val_5398_; lean_object* v___x_5399_; 
v_val_5398_ = lean_ctor_get(v_expectedType_x3f_5388_, 0);
lean_inc(v_val_5398_);
lean_dec_ref_known(v_expectedType_x3f_5388_, 1);
v___x_5399_ = l_Lean_Server_Completion_getDotIdCompletionTypeNames(v_val_5398_, v___y_5393_, v___y_5394_, v___y_5395_, v___y_5396_);
if (lean_obj_tag(v___x_5399_) == 0)
{
lean_object* v_a_5400_; lean_object* v___x_5402_; uint8_t v_isShared_5403_; uint8_t v_isSharedCheck_5414_; 
v_a_5400_ = lean_ctor_get(v___x_5399_, 0);
v_isSharedCheck_5414_ = !lean_is_exclusive(v___x_5399_);
if (v_isSharedCheck_5414_ == 0)
{
v___x_5402_ = v___x_5399_;
v_isShared_5403_ = v_isSharedCheck_5414_;
goto v_resetjp_5401_;
}
else
{
lean_inc(v_a_5400_);
lean_dec(v___x_5399_);
v___x_5402_ = lean_box(0);
v_isShared_5403_ = v_isSharedCheck_5414_;
goto v_resetjp_5401_;
}
v_resetjp_5401_:
{
lean_object* v___x_5404_; lean_object* v___x_5405_; uint8_t v___x_5406_; 
v___x_5404_ = lean_array_get_size(v_a_5400_);
v___x_5405_ = lean_unsigned_to_nat(0u);
v___x_5406_ = lean_nat_dec_eq(v___x_5404_, v___x_5405_);
if (v___x_5406_ == 0)
{
lean_object* v___x_5407_; lean_object* v___f_5408_; lean_object* v___x_5409_; 
lean_del_object(v___x_5402_);
v___x_5407_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(v_a_5400_);
lean_dec(v_a_5400_);
v___f_5408_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotIdCompletion___lam__0___boxed), 12, 2);
lean_closure_set(v___f_5408_, 0, v___x_5407_);
lean_closure_set(v___f_5408_, 1, v_id_5389_);
v___x_5409_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___f_5408_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_, v___y_5395_, v___y_5396_);
return v___x_5409_;
}
else
{
lean_object* v___x_5410_; lean_object* v___x_5412_; 
lean_dec(v_a_5400_);
lean_dec(v_id_5389_);
v___x_5410_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5403_ == 0)
{
lean_ctor_set(v___x_5402_, 0, v___x_5410_);
v___x_5412_ = v___x_5402_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5413_; 
v_reuseFailAlloc_5413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5413_, 0, v___x_5410_);
v___x_5412_ = v_reuseFailAlloc_5413_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
return v___x_5412_;
}
}
}
}
else
{
lean_object* v_a_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5422_; 
lean_dec(v_id_5389_);
v_a_5415_ = lean_ctor_get(v___x_5399_, 0);
v_isSharedCheck_5422_ = !lean_is_exclusive(v___x_5399_);
if (v_isSharedCheck_5422_ == 0)
{
v___x_5417_ = v___x_5399_;
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_a_5415_);
lean_dec(v___x_5399_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
lean_object* v___x_5420_; 
if (v_isShared_5418_ == 0)
{
v___x_5420_ = v___x_5417_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5421_, 0, v_a_5415_);
v___x_5420_ = v_reuseFailAlloc_5421_;
goto v_reusejp_5419_;
}
v_reusejp_5419_:
{
return v___x_5420_;
}
}
}
}
else
{
lean_object* v___x_5423_; lean_object* v___x_5424_; 
lean_dec(v_id_5389_);
lean_dec(v_expectedType_x3f_5388_);
v___x_5423_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5424_, 0, v___x_5423_);
return v___x_5424_;
}
}
}
LEAN_EXPORT void l_Lean_Server_Completion_dotIdCompletion___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_expectedType_x3f_5388_ = stack[0].m_obj;
lean_object* v_id_5389_ = stack[1].m_obj;
lean_object* v___y_5390_ = stack[2].m_obj;
lean_object* v___y_5391_ = stack[3].m_obj;
lean_object* v___y_5392_ = stack[4].m_obj;
lean_object* v___y_5393_ = stack[5].m_obj;
lean_object* v___y_5394_ = stack[6].m_obj;
lean_object* v___y_5395_ = stack[7].m_obj;
lean_object* v___y_5396_ = stack[8].m_obj;
lean_object* v_res_5425_;
v_res_5425_ = l_Lean_Server_Completion_dotIdCompletion___lam__1(v_expectedType_x3f_5388_, v_id_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_, v___y_5395_, v___y_5396_);
stack->m_obj
 = v_res_5425_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__1___boxed(lean_object* v_expectedType_x3f_5426_, lean_object* v_id_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_){
_start:
{
lean_object* v_res_5436_; 
v_res_5436_ = l_Lean_Server_Completion_dotIdCompletion___lam__1(v_expectedType_x3f_5426_, v_id_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_);
lean_dec(v___y_5434_);
lean_dec_ref(v___y_5433_);
lean_dec(v___y_5432_);
lean_dec_ref(v___y_5431_);
lean_dec_ref(v___y_5430_);
lean_dec(v___y_5429_);
lean_dec_ref(v___y_5428_);
return v_res_5436_;
}
}
lean_object* l_Lean_Server_Completion_dotIdCompletion(lean_object* v_uri_5437_, lean_object* v_pos_5438_, lean_object* v_completionInfoPos_5439_, lean_object* v_ctx_5440_, lean_object* v_lctx_5441_, lean_object* v_id_5442_, lean_object* v_expectedType_x3f_5443_, lean_object* v_a_5444_){
_start:
{
lean_object* v___y_5446_; lean_object* v___x_5447_; 
v___y_5446_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotIdCompletion___lam__1___boxed), 10, 2);
lean_closure_set(v___y_5446_, 0, v_expectedType_x3f_5443_);
lean_closure_set(v___y_5446_, 1, v_id_5442_);
v___x_5447_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5437_, v_pos_5438_, v_completionInfoPos_5439_, v_ctx_5440_, v_lctx_5441_, v___y_5446_, v_a_5444_);
return v___x_5447_;
}
}
LEAN_EXPORT void l_Lean_Server_Completion_dotIdCompletion_0interp(lean_interpreter_value* stack)
{
lean_object* v_uri_5437_ = stack[0].m_obj;
lean_object* v_pos_5438_ = stack[1].m_obj;
lean_object* v_completionInfoPos_5439_ = stack[2].m_obj;
lean_object* v_ctx_5440_ = stack[3].m_obj;
lean_object* v_lctx_5441_ = stack[4].m_obj;
lean_object* v_id_5442_ = stack[5].m_obj;
lean_object* v_expectedType_x3f_5443_ = stack[6].m_obj;
lean_object* v_a_5444_ = stack[7].m_obj;
lean_object* v_res_5448_;
v_res_5448_ = l_Lean_Server_Completion_dotIdCompletion(v_uri_5437_, v_pos_5438_, v_completionInfoPos_5439_, v_ctx_5440_, v_lctx_5441_, v_id_5442_, v_expectedType_x3f_5443_, v_a_5444_);
stack->m_obj
 = v_res_5448_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___boxed(lean_object* v_uri_5449_, lean_object* v_pos_5450_, lean_object* v_completionInfoPos_5451_, lean_object* v_ctx_5452_, lean_object* v_lctx_5453_, lean_object* v_id_5454_, lean_object* v_expectedType_x3f_5455_, lean_object* v_a_5456_, lean_object* v_a_5457_){
_start:
{
lean_object* v_res_5458_; 
v_res_5458_ = l_Lean_Server_Completion_dotIdCompletion(v_uri_5449_, v_pos_5450_, v_completionInfoPos_5451_, v_ctx_5452_, v_lctx_5453_, v_id_5454_, v_expectedType_x3f_5455_, v_a_5456_);
lean_dec_ref(v_a_5456_);
return v_res_5458_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(lean_object* v___y_5465_, lean_object* v_as_5466_, size_t v_sz_5467_, size_t v_i_5468_, lean_object* v_b_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_){
_start:
{
lean_object* v_a_5474_; uint8_t v___x_5478_; 
v___x_5478_ = lean_usize_dec_lt(v_i_5468_, v_sz_5467_);
if (v___x_5478_ == 0)
{
lean_object* v___x_5479_; lean_object* v___x_5480_; 
v___x_5479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5479_, 0, v_b_5469_);
v___x_5480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5480_, 0, v___x_5479_);
return v___x_5480_;
}
else
{
lean_object* v___x_5481_; lean_object* v_a_5482_; 
v___x_5481_ = lean_box(0);
v_a_5482_ = lean_array_uget_borrowed(v_as_5466_, v_i_5468_);
if (lean_obj_tag(v_a_5482_) == 1)
{
lean_object* v_str_5483_; uint8_t v___x_5484_; 
v_str_5483_ = lean_ctor_get(v_a_5482_, 1);
v___x_5484_ = l_Lean_String_charactersIn(v___y_5465_, v_str_5483_);
if (v___x_5484_ == 0)
{
v_a_5474_ = v___x_5481_;
goto v___jp_5473_;
}
else
{
lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; 
v___x_5485_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__1));
v___x_5486_ = lean_box(0);
v___x_5487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__2));
lean_inc_ref(v_str_5483_);
v___x_5488_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5488_, 0, v_str_5483_);
lean_ctor_set(v___x_5488_, 1, v___x_5485_);
lean_ctor_set(v___x_5488_, 2, v___x_5486_);
lean_ctor_set(v___x_5488_, 3, v___x_5487_);
lean_ctor_set(v___x_5488_, 4, v___x_5486_);
lean_ctor_set(v___x_5488_, 5, v___x_5486_);
lean_ctor_set(v___x_5488_, 6, v___x_5486_);
lean_ctor_set(v___x_5488_, 7, v___x_5486_);
v___x_5489_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(v___x_5488_, v___x_5486_, v___y_5470_, v___y_5471_);
if (lean_obj_tag(v___x_5489_) == 0)
{
lean_object* v_a_5490_; 
v_a_5490_ = lean_ctor_get(v___x_5489_, 0);
if (lean_obj_tag(v_a_5490_) == 0)
{
return v___x_5489_;
}
else
{
lean_dec_ref_known(v___x_5489_, 1);
v_a_5474_ = v___x_5481_;
goto v___jp_5473_;
}
}
else
{
return v___x_5489_;
}
}
}
else
{
v_a_5474_ = v___x_5481_;
goto v___jp_5473_;
}
}
v___jp_5473_:
{
size_t v___x_5475_; size_t v___x_5476_; 
v___x_5475_ = ((size_t)1ULL);
v___x_5476_ = lean_usize_add(v_i_5468_, v___x_5475_);
v_i_5468_ = v___x_5476_;
v_b_5469_ = v_a_5474_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_5465_ = stack[0].m_obj;
lean_object* v_as_5466_ = stack[1].m_obj;
size_t v_sz_5467_ = stack[2].m_num;
size_t v_i_5468_ = stack[3].m_num;
lean_object* v_b_5469_ = stack[4].m_obj;
lean_object* v___y_5470_ = stack[5].m_obj;
lean_object* v___y_5471_ = stack[6].m_obj;
lean_object* v_res_5491_;
v_res_5491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5465_, v_as_5466_, v_sz_5467_, v_i_5468_, v_b_5469_, v___y_5470_, v___y_5471_);
stack->m_obj
 = v_res_5491_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___boxed(lean_object* v___y_5492_, lean_object* v_as_5493_, lean_object* v_sz_5494_, lean_object* v_i_5495_, lean_object* v_b_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_){
_start:
{
size_t v_sz_boxed_5500_; size_t v_i_boxed_5501_; lean_object* v_res_5502_; 
v_sz_boxed_5500_ = lean_unbox_usize(v_sz_5494_);
lean_dec(v_sz_5494_);
v_i_boxed_5501_ = lean_unbox_usize(v_i_5495_);
lean_dec(v_i_5495_);
v_res_5502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5492_, v_as_5493_, v_sz_boxed_5500_, v_i_boxed_5501_, v_b_5496_, v___y_5497_, v___y_5498_);
lean_dec(v___y_5498_);
lean_dec_ref(v___y_5497_);
lean_dec_ref(v_as_5493_);
lean_dec_ref(v___y_5492_);
return v_res_5502_;
}
}
lean_object* l_Lean_Server_Completion_fieldIdCompletion___lam__0(lean_object* v_structName_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_, lean_object* v___y_5506_, lean_object* v___y_5507_, lean_object* v___y_5508_, lean_object* v___y_5509_, lean_object* v___y_5510_, lean_object* v___y_5511_){
_start:
{
lean_object* v___x_5513_; lean_object* v_env_5514_; uint8_t v___x_5515_; lean_object* v_fieldNames_5516_; lean_object* v___x_5517_; size_t v_sz_5518_; size_t v___x_5519_; lean_object* v___x_5520_; 
v___x_5513_ = lean_st_ref_get(v___y_5511_);
v_env_5514_ = lean_ctor_get(v___x_5513_, 0);
lean_inc_ref(v_env_5514_);
lean_dec(v___x_5513_);
v___x_5515_ = 0;
v_fieldNames_5516_ = l_Lean_getStructureFieldsFlattened(v_env_5514_, v_structName_5503_, v___x_5515_);
v___x_5517_ = lean_box(0);
v_sz_5518_ = lean_array_size(v_fieldNames_5516_);
v___x_5519_ = ((size_t)0ULL);
v___x_5520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5504_, v_fieldNames_5516_, v_sz_5518_, v___x_5519_, v___x_5517_, v___y_5505_, v___y_5506_);
lean_dec_ref(v_fieldNames_5516_);
if (lean_obj_tag(v___x_5520_) == 0)
{
lean_object* v_a_5521_; 
v_a_5521_ = lean_ctor_get(v___x_5520_, 0);
if (lean_obj_tag(v_a_5521_) == 0)
{
return v___x_5520_;
}
else
{
lean_object* v___x_5523_; uint8_t v_isShared_5524_; uint8_t v_isSharedCheck_5529_; 
v_isSharedCheck_5529_ = !lean_is_exclusive(v___x_5520_);
if (v_isSharedCheck_5529_ == 0)
{
lean_object* v_unused_5530_; 
v_unused_5530_ = lean_ctor_get(v___x_5520_, 0);
lean_dec(v_unused_5530_);
v___x_5523_ = v___x_5520_;
v_isShared_5524_ = v_isSharedCheck_5529_;
goto v_resetjp_5522_;
}
else
{
lean_dec(v___x_5520_);
v___x_5523_ = lean_box(0);
v_isShared_5524_ = v_isSharedCheck_5529_;
goto v_resetjp_5522_;
}
v_resetjp_5522_:
{
lean_object* v___x_5525_; lean_object* v___x_5527_; 
v___x_5525_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5524_ == 0)
{
lean_ctor_set(v___x_5523_, 0, v___x_5525_);
v___x_5527_ = v___x_5523_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v___x_5525_);
v___x_5527_ = v_reuseFailAlloc_5528_;
goto v_reusejp_5526_;
}
v_reusejp_5526_:
{
return v___x_5527_;
}
}
}
}
else
{
return v___x_5520_;
}
}
}
LEAN_EXPORT void l_Lean_Server_Completion_fieldIdCompletion___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_structName_5503_ = stack[0].m_obj;
lean_object* v___y_5504_ = stack[1].m_obj;
lean_object* v___y_5505_ = stack[2].m_obj;
lean_object* v___y_5506_ = stack[3].m_obj;
lean_object* v___y_5507_ = stack[4].m_obj;
lean_object* v___y_5508_ = stack[5].m_obj;
lean_object* v___y_5509_ = stack[6].m_obj;
lean_object* v___y_5510_ = stack[7].m_obj;
lean_object* v___y_5511_ = stack[8].m_obj;
lean_object* v_res_5531_;
v_res_5531_ = l_Lean_Server_Completion_fieldIdCompletion___lam__0(v_structName_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_);
stack->m_obj
 = v_res_5531_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lam__0___boxed(lean_object* v_structName_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_){
_start:
{
lean_object* v_res_5542_; 
v_res_5542_ = l_Lean_Server_Completion_fieldIdCompletion___lam__0(v_structName_5532_, v___y_5533_, v___y_5534_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_, v___y_5539_, v___y_5540_);
lean_dec(v___y_5540_);
lean_dec_ref(v___y_5539_);
lean_dec(v___y_5538_);
lean_dec_ref(v___y_5537_);
lean_dec_ref(v___y_5536_);
lean_dec(v___y_5535_);
lean_dec_ref(v___y_5534_);
lean_dec_ref(v___y_5533_);
return v_res_5542_;
}
}
lean_object* l_Lean_Server_Completion_fieldIdCompletion(lean_object* v_uri_5544_, lean_object* v_pos_5545_, lean_object* v_completionInfoPos_5546_, lean_object* v_ctx_5547_, lean_object* v_lctx_5548_, lean_object* v_id_5549_, lean_object* v_structName_5550_, lean_object* v_a_5551_){
_start:
{
lean_object* v___y_5554_; 
if (lean_obj_tag(v_id_5549_) == 0)
{
lean_object* v___x_5557_; 
v___x_5557_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v___y_5554_ = v___x_5557_;
goto v___jp_5553_;
}
else
{
lean_object* v_val_5558_; uint8_t v___x_5559_; lean_object* v___x_5560_; 
v_val_5558_ = lean_ctor_get(v_id_5549_, 0);
lean_inc(v_val_5558_);
lean_dec_ref_known(v_id_5549_, 1);
v___x_5559_ = 1;
v___x_5560_ = l_Lean_Name_toString(v_val_5558_, v___x_5559_);
v___y_5554_ = v___x_5560_;
goto v___jp_5553_;
}
v___jp_5553_:
{
lean_object* v___f_5555_; lean_object* v___x_5556_; 
v___f_5555_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_fieldIdCompletion___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5555_, 0, v_structName_5550_);
lean_closure_set(v___f_5555_, 1, v___y_5554_);
v___x_5556_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5544_, v_pos_5545_, v_completionInfoPos_5546_, v_ctx_5547_, v_lctx_5548_, v___f_5555_, v_a_5551_);
return v___x_5556_;
}
}
}
LEAN_EXPORT void l_Lean_Server_Completion_fieldIdCompletion_0interp(lean_interpreter_value* stack)
{
lean_object* v_uri_5544_ = stack[0].m_obj;
lean_object* v_pos_5545_ = stack[1].m_obj;
lean_object* v_completionInfoPos_5546_ = stack[2].m_obj;
lean_object* v_ctx_5547_ = stack[3].m_obj;
lean_object* v_lctx_5548_ = stack[4].m_obj;
lean_object* v_id_5549_ = stack[5].m_obj;
lean_object* v_structName_5550_ = stack[6].m_obj;
lean_object* v_a_5551_ = stack[7].m_obj;
lean_object* v_res_5561_;
v_res_5561_ = l_Lean_Server_Completion_fieldIdCompletion(v_uri_5544_, v_pos_5545_, v_completionInfoPos_5546_, v_ctx_5547_, v_lctx_5548_, v_id_5549_, v_structName_5550_, v_a_5551_);
stack->m_obj
 = v_res_5561_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___boxed(lean_object* v_uri_5562_, lean_object* v_pos_5563_, lean_object* v_completionInfoPos_5564_, lean_object* v_ctx_5565_, lean_object* v_lctx_5566_, lean_object* v_id_5567_, lean_object* v_structName_5568_, lean_object* v_a_5569_, lean_object* v_a_5570_){
_start:
{
lean_object* v_res_5571_; 
v_res_5571_ = l_Lean_Server_Completion_fieldIdCompletion(v_uri_5562_, v_pos_5563_, v_completionInfoPos_5564_, v_ctx_5565_, v_lctx_5566_, v_id_5567_, v_structName_5568_, v_a_5569_);
lean_dec_ref(v_a_5569_);
return v_res_5571_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0(lean_object* v___y_5572_, lean_object* v_as_5573_, size_t v_sz_5574_, size_t v_i_5575_, lean_object* v_b_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_, lean_object* v___y_5581_, lean_object* v___y_5582_, lean_object* v___y_5583_){
_start:
{
lean_object* v___x_5585_; 
v___x_5585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5572_, v_as_5573_, v_sz_5574_, v_i_5575_, v_b_5576_, v___y_5577_, v___y_5578_);
return v___x_5585_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_5572_ = stack[0].m_obj;
lean_object* v_as_5573_ = stack[1].m_obj;
size_t v_sz_5574_ = stack[2].m_num;
size_t v_i_5575_ = stack[3].m_num;
lean_object* v_b_5576_ = stack[4].m_obj;
lean_object* v___y_5577_ = stack[5].m_obj;
lean_object* v___y_5578_ = stack[6].m_obj;
lean_object* v___y_5579_ = stack[7].m_obj;
lean_object* v___y_5580_ = stack[8].m_obj;
lean_object* v___y_5581_ = stack[9].m_obj;
lean_object* v___y_5582_ = stack[10].m_obj;
lean_object* v___y_5583_ = stack[11].m_obj;
lean_object* v_res_5586_;
v_res_5586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0(v___y_5572_, v_as_5573_, v_sz_5574_, v_i_5575_, v_b_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_);
stack->m_obj
 = v_res_5586_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___boxed(lean_object* v___y_5587_, lean_object* v_as_5588_, lean_object* v_sz_5589_, lean_object* v_i_5590_, lean_object* v_b_5591_, lean_object* v___y_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_){
_start:
{
size_t v_sz_boxed_5600_; size_t v_i_boxed_5601_; lean_object* v_res_5602_; 
v_sz_boxed_5600_ = lean_unbox_usize(v_sz_5589_);
lean_dec(v_sz_5589_);
v_i_boxed_5601_ = lean_unbox_usize(v_i_5590_);
lean_dec(v_i_5590_);
v_res_5602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0(v___y_5587_, v_as_5588_, v_sz_boxed_5600_, v_i_boxed_5601_, v_b_5591_, v___y_5592_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_, v___y_5597_, v___y_5598_);
lean_dec(v___y_5598_);
lean_dec_ref(v___y_5597_);
lean_dec(v___y_5596_);
lean_dec_ref(v___y_5595_);
lean_dec_ref(v___y_5594_);
lean_dec(v___y_5593_);
lean_dec_ref(v___y_5592_);
lean_dec_ref(v_as_5588_);
lean_dec_ref(v___y_5587_);
return v_res_5602_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0(lean_object* v_fst_5603_, lean_object* v_caps_5604_, lean_object* v_mkItem_5605_, lean_object* v_ctx_5606_, lean_object* v_stx_5607_, uint8_t v_snd_5608_, lean_object* v_x_5609_, lean_object* v_____s_5610_){
_start:
{
lean_object* v_fst_5611_; lean_object* v_snd_5612_; lean_object* v___x_5614_; uint8_t v_isShared_5615_; uint8_t v_isSharedCheck_5666_; 
v_fst_5611_ = lean_ctor_get(v_x_5609_, 0);
v_snd_5612_ = lean_ctor_get(v_x_5609_, 1);
v_isSharedCheck_5666_ = !lean_is_exclusive(v_x_5609_);
if (v_isSharedCheck_5666_ == 0)
{
v___x_5614_ = v_x_5609_;
v_isShared_5615_ = v_isSharedCheck_5666_;
goto v_resetjp_5613_;
}
else
{
lean_inc(v_snd_5612_);
lean_inc(v_fst_5611_);
lean_dec(v_x_5609_);
v___x_5614_ = lean_box(0);
v_isShared_5615_ = v_isSharedCheck_5666_;
goto v_resetjp_5613_;
}
v_resetjp_5613_:
{
lean_object* v___y_5617_; uint8_t v___x_5621_; lean_object* v___x_5622_; lean_object* v___y_5624_; lean_object* v___y_5625_; uint8_t v___y_5644_; uint8_t v___x_5654_; 
v___x_5621_ = 1;
lean_inc(v_fst_5611_);
v___x_5622_ = l_Lean_Name_toString(v_fst_5611_, v___x_5621_);
v___x_5654_ = l_Lean_String_charactersIn(v_fst_5603_, v___x_5622_);
if (v___x_5654_ == 0)
{
lean_object* v___x_5657_; 
lean_dec_ref(v___x_5622_);
lean_del_object(v___x_5614_);
lean_dec(v_snd_5612_);
lean_dec(v_fst_5611_);
lean_dec_ref(v_ctx_5606_);
lean_dec_ref(v_mkItem_5605_);
v___x_5657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5657_, 0, v_____s_5610_);
return v___x_5657_;
}
else
{
lean_object* v_textDocument_x3f_5658_; 
v_textDocument_x3f_5658_ = lean_ctor_get(v_caps_5604_, 0);
if (lean_obj_tag(v_textDocument_x3f_5658_) == 0)
{
goto v___jp_5655_;
}
else
{
lean_object* v_val_5659_; lean_object* v_completion_x3f_5660_; 
v_val_5659_ = lean_ctor_get(v_textDocument_x3f_5658_, 0);
v_completion_x3f_5660_ = lean_ctor_get(v_val_5659_, 0);
if (lean_obj_tag(v_completion_x3f_5660_) == 0)
{
goto v___jp_5655_;
}
else
{
lean_object* v_val_5661_; 
v_val_5661_ = lean_ctor_get(v_completion_x3f_5660_, 0);
if (lean_obj_tag(v_val_5661_) == 0)
{
goto v___jp_5655_;
}
else
{
lean_object* v_val_5662_; 
v_val_5662_ = lean_ctor_get(v_val_5661_, 0);
if (lean_obj_tag(v_val_5662_) == 0)
{
goto v___jp_5655_;
}
else
{
lean_object* v_val_5663_; uint8_t v___x_5664_; 
v_val_5663_ = lean_ctor_get(v_val_5662_, 0);
v___x_5664_ = lean_unbox(v_val_5663_);
if (v___x_5664_ == 0)
{
goto v___jp_5655_;
}
else
{
uint8_t v___x_5665_; 
v___x_5665_ = 0;
v___y_5644_ = v___x_5665_;
goto v___jp_5643_;
}
}
}
}
}
}
v___jp_5616_:
{
lean_object* v___x_5618_; lean_object* v_items_5619_; lean_object* v___x_5620_; 
v___x_5618_ = lean_apply_3(v_mkItem_5605_, v_fst_5611_, v_snd_5612_, v___y_5617_);
v_items_5619_ = lean_array_push(v_____s_5610_, v___x_5618_);
v___x_5620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5620_, 0, v_items_5619_);
return v___x_5620_;
}
v___jp_5623_:
{
lean_object* v_toCommandContextInfo_5626_; lean_object* v___x_5628_; uint8_t v_isShared_5629_; uint8_t v_isSharedCheck_5640_; 
v_toCommandContextInfo_5626_ = lean_ctor_get(v_ctx_5606_, 0);
v_isSharedCheck_5640_ = !lean_is_exclusive(v_ctx_5606_);
if (v_isSharedCheck_5640_ == 0)
{
lean_object* v_unused_5641_; lean_object* v_unused_5642_; 
v_unused_5641_ = lean_ctor_get(v_ctx_5606_, 2);
lean_dec(v_unused_5641_);
v_unused_5642_ = lean_ctor_get(v_ctx_5606_, 1);
lean_dec(v_unused_5642_);
v___x_5628_ = v_ctx_5606_;
v_isShared_5629_ = v_isSharedCheck_5640_;
goto v_resetjp_5627_;
}
else
{
lean_inc(v_toCommandContextInfo_5626_);
lean_dec(v_ctx_5606_);
v___x_5628_ = lean_box(0);
v_isShared_5629_ = v_isSharedCheck_5640_;
goto v_resetjp_5627_;
}
v_resetjp_5627_:
{
lean_object* v_fileMap_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v_range_5634_; 
v_fileMap_5630_ = lean_ctor_get(v_toCommandContextInfo_5626_, 2);
lean_inc_ref_n(v_fileMap_5630_, 2);
lean_dec_ref(v_toCommandContextInfo_5626_);
v___x_5631_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5630_, v___y_5624_);
lean_dec(v___y_5624_);
v___x_5632_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5630_, v___y_5625_);
lean_dec(v___y_5625_);
if (v_isShared_5615_ == 0)
{
lean_ctor_set(v___x_5614_, 1, v___x_5632_);
lean_ctor_set(v___x_5614_, 0, v___x_5631_);
v_range_5634_ = v___x_5614_;
goto v_reusejp_5633_;
}
else
{
lean_object* v_reuseFailAlloc_5639_; 
v_reuseFailAlloc_5639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5639_, 0, v___x_5631_);
lean_ctor_set(v_reuseFailAlloc_5639_, 1, v___x_5632_);
v_range_5634_ = v_reuseFailAlloc_5639_;
goto v_reusejp_5633_;
}
v_reusejp_5633_:
{
lean_object* v___x_5636_; 
lean_inc_ref(v_range_5634_);
if (v_isShared_5629_ == 0)
{
lean_ctor_set(v___x_5628_, 2, v_range_5634_);
lean_ctor_set(v___x_5628_, 1, v_range_5634_);
lean_ctor_set(v___x_5628_, 0, v___x_5622_);
v___x_5636_ = v___x_5628_;
goto v_reusejp_5635_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v___x_5622_);
lean_ctor_set(v_reuseFailAlloc_5638_, 1, v_range_5634_);
lean_ctor_set(v_reuseFailAlloc_5638_, 2, v_range_5634_);
v___x_5636_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5635_;
}
v_reusejp_5635_:
{
lean_object* v___x_5637_; 
v___x_5637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5637_, 0, v___x_5636_);
v___y_5617_ = v___x_5637_;
goto v___jp_5616_;
}
}
}
}
v___jp_5643_:
{
lean_object* v___x_5645_; 
v___x_5645_ = l_Lean_Syntax_getRange_x3f(v_stx_5607_, v___y_5644_);
if (lean_obj_tag(v___x_5645_) == 1)
{
lean_object* v_val_5646_; 
v_val_5646_ = lean_ctor_get(v___x_5645_, 0);
lean_inc(v_val_5646_);
lean_dec_ref_known(v___x_5645_, 1);
if (v_snd_5608_ == 0)
{
lean_object* v_start_5647_; lean_object* v_stop_5648_; 
v_start_5647_ = lean_ctor_get(v_val_5646_, 0);
lean_inc(v_start_5647_);
v_stop_5648_ = lean_ctor_get(v_val_5646_, 1);
lean_inc(v_stop_5648_);
lean_dec(v_val_5646_);
v___y_5624_ = v_start_5647_;
v___y_5625_ = v_stop_5648_;
goto v___jp_5623_;
}
else
{
lean_object* v_start_5649_; lean_object* v_stop_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; 
v_start_5649_ = lean_ctor_get(v_val_5646_, 0);
lean_inc(v_start_5649_);
v_stop_5650_ = lean_ctor_get(v_val_5646_, 1);
lean_inc(v_stop_5650_);
lean_dec(v_val_5646_);
v___x_5651_ = lean_unsigned_to_nat(1u);
v___x_5652_ = lean_nat_add(v_stop_5650_, v___x_5651_);
lean_dec(v_stop_5650_);
v___y_5624_ = v_start_5649_;
v___y_5625_ = v___x_5652_;
goto v___jp_5623_;
}
}
else
{
lean_object* v___x_5653_; 
lean_dec(v___x_5645_);
lean_dec_ref(v___x_5622_);
lean_del_object(v___x_5614_);
lean_dec_ref(v_ctx_5606_);
v___x_5653_ = lean_box(0);
v___y_5617_ = v___x_5653_;
goto v___jp_5616_;
}
}
v___jp_5655_:
{
if (v___x_5654_ == 0)
{
v___y_5644_ = v___x_5654_;
goto v___jp_5643_;
}
else
{
lean_object* v___x_5656_; 
lean_dec_ref(v___x_5622_);
lean_del_object(v___x_5614_);
lean_dec_ref(v_ctx_5606_);
v___x_5656_ = lean_box(0);
v___y_5617_ = v___x_5656_;
goto v___jp_5616_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_5603_ = stack[0].m_obj;
lean_object* v_caps_5604_ = stack[1].m_obj;
lean_object* v_mkItem_5605_ = stack[2].m_obj;
lean_object* v_ctx_5606_ = stack[3].m_obj;
lean_object* v_stx_5607_ = stack[4].m_obj;
uint8_t v_snd_5608_ = stack[5].m_num;
lean_object* v_x_5609_ = stack[6].m_obj;
lean_object* v_____s_5610_ = stack[7].m_obj;
lean_object* v_res_5667_;
v_res_5667_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0(v_fst_5603_, v_caps_5604_, v_mkItem_5605_, v_ctx_5606_, v_stx_5607_, v_snd_5608_, v_x_5609_, v_____s_5610_);
stack->m_obj
 = v_res_5667_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___boxed(lean_object* v_fst_5668_, lean_object* v_caps_5669_, lean_object* v_mkItem_5670_, lean_object* v_ctx_5671_, lean_object* v_stx_5672_, lean_object* v_snd_5673_, lean_object* v_x_5674_, lean_object* v_____s_5675_){
_start:
{
uint8_t v_snd_827__boxed_5676_; lean_object* v_res_5677_; 
v_snd_827__boxed_5676_ = lean_unbox(v_snd_5673_);
v_res_5677_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0(v_fst_5668_, v_caps_5669_, v_mkItem_5670_, v_ctx_5671_, v_stx_5672_, v_snd_827__boxed_5676_, v_x_5674_, v_____s_5675_);
lean_dec(v_stx_5672_);
lean_dec_ref(v_caps_5669_);
lean_dec_ref(v_fst_5668_);
return v_res_5677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg(lean_object* v_inst_5679_, lean_object* v_entries_5680_, lean_object* v_stx_5681_, lean_object* v_caps_5682_, lean_object* v_ctx_5683_, lean_object* v_mkItem_5684_){
_start:
{
lean_object* v_fst_5686_; uint8_t v_snd_5687_; uint8_t v___x_5692_; lean_object* v___x_5693_; 
v___x_5692_ = 0;
v___x_5693_ = l_Lean_Syntax_getSubstring_x3f(v_stx_5681_, v___x_5692_, v___x_5692_);
if (lean_obj_tag(v___x_5693_) == 0)
{
lean_object* v___x_5694_; 
v___x_5694_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_5686_ = v___x_5694_;
v_snd_5687_ = v___x_5692_;
goto v___jp_5685_;
}
else
{
lean_object* v_val_5695_; lean_object* v_str_5696_; lean_object* v_startPos_5697_; lean_object* v_stopPos_5698_; uint8_t v___y_5700_; uint8_t v___x_5702_; 
v_val_5695_ = lean_ctor_get(v___x_5693_, 0);
lean_inc(v_val_5695_);
lean_dec_ref_known(v___x_5693_, 1);
v_str_5696_ = lean_ctor_get(v_val_5695_, 0);
lean_inc_ref(v_str_5696_);
v_startPos_5697_ = lean_ctor_get(v_val_5695_, 1);
lean_inc(v_startPos_5697_);
v_stopPos_5698_ = lean_ctor_get(v_val_5695_, 2);
lean_inc(v_stopPos_5698_);
lean_dec(v_val_5695_);
v___x_5702_ = lean_string_utf8_at_end(v_str_5696_, v_stopPos_5698_);
if (v___x_5702_ == 0)
{
uint32_t v___x_5703_; uint32_t v___x_5704_; uint8_t v___x_5705_; 
v___x_5703_ = lean_string_utf8_get(v_str_5696_, v_stopPos_5698_);
v___x_5704_ = 46;
v___x_5705_ = lean_uint32_dec_eq(v___x_5703_, v___x_5704_);
if (v___x_5705_ == 0)
{
v___y_5700_ = v___x_5705_;
goto v___jp_5699_;
}
else
{
lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; 
v___x_5706_ = lean_string_utf8_extract(v_str_5696_, v_startPos_5697_, v_stopPos_5698_);
lean_dec(v_stopPos_5698_);
lean_dec(v_startPos_5697_);
lean_dec_ref(v_str_5696_);
v___x_5707_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_5708_ = lean_string_append(v___x_5706_, v___x_5707_);
v_fst_5686_ = v___x_5708_;
v_snd_5687_ = v___x_5705_;
goto v___jp_5685_;
}
}
else
{
v___y_5700_ = v___x_5692_;
goto v___jp_5699_;
}
v___jp_5699_:
{
lean_object* v___x_5701_; 
v___x_5701_ = lean_string_utf8_extract(v_str_5696_, v_startPos_5697_, v_stopPos_5698_);
lean_dec(v_stopPos_5698_);
lean_dec(v_startPos_5697_);
lean_dec_ref(v_str_5696_);
v_fst_5686_ = v___x_5701_;
v_snd_5687_ = v___y_5700_;
goto v___jp_5685_;
}
}
v___jp_5685_:
{
lean_object* v___x_5688_; lean_object* v___f_5689_; lean_object* v_items_5690_; lean_object* v___x_5691_; 
v___x_5688_ = lean_box(v_snd_5687_);
v___f_5689_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_5689_, 0, v_fst_5686_);
lean_closure_set(v___f_5689_, 1, v_caps_5682_);
lean_closure_set(v___f_5689_, 2, v_mkItem_5684_);
lean_closure_set(v___f_5689_, 3, v_ctx_5683_);
lean_closure_set(v___f_5689_, 4, v_stx_5681_);
lean_closure_set(v___f_5689_, 5, v___x_5688_);
v_items_5690_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v___x_5691_ = lean_apply_4(v_inst_5679_, lean_box(0), v_entries_5680_, v_items_5690_, v___f_5689_);
return v___x_5691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion(lean_object* v_Coll_5709_, lean_object* v_00_u03b1_5710_, lean_object* v_inst_5711_, lean_object* v_entries_5712_, lean_object* v_stx_5713_, lean_object* v_caps_5714_, lean_object* v_ctx_5715_, lean_object* v_mkItem_5716_){
_start:
{
lean_object* v___x_5717_; 
v___x_5717_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg(v_inst_5711_, v_entries_5712_, v_stx_5713_, v_caps_5714_, v_ctx_5715_, v_mkItem_5716_);
return v___x_5717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__0(lean_object* v___x_5723_, lean_object* v_completionInfoPos_5724_, lean_object* v_uri_5725_, lean_object* v_pos_5726_, lean_object* v_name_5727_, lean_object* v_decl_5728_, lean_object* v_textEdit_x3f_5729_){
_start:
{
lean_object* v_defValue_5730_; lean_object* v_descr_5731_; lean_object* v_map_5732_; uint8_t v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___y_5737_; lean_object* v___x_5750_; 
v_defValue_5730_ = lean_ctor_get(v_decl_5728_, 2);
lean_inc_ref(v_defValue_5730_);
v_descr_5731_ = lean_ctor_get(v_decl_5728_, 3);
lean_inc_ref(v_descr_5731_);
lean_dec_ref(v_decl_5728_);
v_map_5732_ = lean_ctor_get(v___x_5723_, 0);
v___x_5733_ = 1;
lean_inc(v_name_5727_);
v___x_5734_ = l_Lean_Name_toString(v_name_5727_, v___x_5733_);
v___x_5735_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__0));
v___x_5750_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5732_, v_name_5727_);
lean_dec(v_name_5727_);
if (lean_obj_tag(v___x_5750_) == 0)
{
v___y_5737_ = v_defValue_5730_;
goto v___jp_5736_;
}
else
{
if (lean_obj_tag(v___x_5750_) == 0)
{
v___y_5737_ = v_defValue_5730_;
goto v___jp_5736_;
}
else
{
lean_object* v_val_5751_; 
lean_dec_ref(v_defValue_5730_);
v_val_5751_ = lean_ctor_get(v___x_5750_, 0);
lean_inc(v_val_5751_);
lean_dec_ref_known(v___x_5750_, 1);
v___y_5737_ = v_val_5751_;
goto v___jp_5736_;
}
}
v___jp_5736_:
{
lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; 
v___x_5738_ = l_Lean_DataValue_str(v___y_5737_);
v___x_5739_ = lean_string_append(v___x_5735_, v___x_5738_);
lean_dec_ref(v___x_5738_);
v___x_5740_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__1));
v___x_5741_ = lean_string_append(v___x_5739_, v___x_5740_);
v___x_5742_ = lean_string_append(v___x_5741_, v_descr_5731_);
lean_dec_ref(v_descr_5731_);
v___x_5743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5743_, 0, v___x_5742_);
v___x_5744_ = lean_box(0);
v___x_5745_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__2));
v___x_5746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5746_, 0, v_completionInfoPos_5724_);
v___x_5747_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5747_, 0, v_uri_5725_);
lean_ctor_set(v___x_5747_, 1, v_pos_5726_);
lean_ctor_set(v___x_5747_, 2, v___x_5746_);
lean_ctor_set(v___x_5747_, 3, v___x_5744_);
v___x_5748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5748_, 0, v___x_5747_);
v___x_5749_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5749_, 0, v___x_5734_);
lean_ctor_set(v___x_5749_, 1, v___x_5743_);
lean_ctor_set(v___x_5749_, 2, v___x_5744_);
lean_ctor_set(v___x_5749_, 3, v___x_5745_);
lean_ctor_set(v___x_5749_, 4, v_textEdit_x3f_5729_);
lean_ctor_set(v___x_5749_, 5, v___x_5744_);
lean_ctor_set(v___x_5749_, 6, v___x_5748_);
lean_ctor_set(v___x_5749_, 7, v___x_5744_);
return v___x_5749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__0___boxed(lean_object* v___x_5752_, lean_object* v_completionInfoPos_5753_, lean_object* v_uri_5754_, lean_object* v_pos_5755_, lean_object* v_name_5756_, lean_object* v_decl_5757_, lean_object* v_textEdit_x3f_5758_){
_start:
{
lean_object* v_res_5759_; 
v_res_5759_ = l_Lean_Server_Completion_optionCompletion___lam__0(v___x_5752_, v_completionInfoPos_5753_, v_uri_5754_, v_pos_5755_, v_name_5756_, v_decl_5757_, v_textEdit_x3f_5758_);
lean_dec_ref(v___x_5752_);
return v_res_5759_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(lean_object* v_mkItem_5760_, lean_object* v_stx_5761_, lean_object* v_ctx_5762_, uint8_t v_snd_5763_, lean_object* v_fst_5764_, lean_object* v_caps_5765_, lean_object* v_init_5766_, lean_object* v_x_5767_){
_start:
{
if (lean_obj_tag(v_x_5767_) == 0)
{
lean_object* v_k_5768_; lean_object* v_v_5769_; lean_object* v_l_5770_; lean_object* v_r_5771_; lean_object* v___x_5772_; lean_object* v_a_5773_; lean_object* v___y_5775_; uint8_t v___x_5779_; lean_object* v___x_5780_; lean_object* v___y_5782_; lean_object* v___y_5783_; uint8_t v___y_5792_; uint8_t v___x_5802_; 
v_k_5768_ = lean_ctor_get(v_x_5767_, 1);
lean_inc_n(v_k_5768_, 2);
v_v_5769_ = lean_ctor_get(v_x_5767_, 2);
lean_inc(v_v_5769_);
v_l_5770_ = lean_ctor_get(v_x_5767_, 3);
lean_inc(v_l_5770_);
v_r_5771_ = lean_ctor_get(v_x_5767_, 4);
lean_inc(v_r_5771_);
lean_dec_ref_known(v_x_5767_, 5);
lean_inc_ref(v_ctx_5762_);
lean_inc_ref(v_mkItem_5760_);
v___x_5772_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5760_, v_stx_5761_, v_ctx_5762_, v_snd_5763_, v_fst_5764_, v_caps_5765_, v_init_5766_, v_l_5770_);
v_a_5773_ = lean_ctor_get(v___x_5772_, 0);
v___x_5779_ = 1;
v___x_5780_ = l_Lean_Name_toString(v_k_5768_, v___x_5779_);
v___x_5802_ = l_Lean_String_charactersIn(v_fst_5764_, v___x_5780_);
if (v___x_5802_ == 0)
{
lean_object* v_a_5805_; 
lean_dec_ref(v___x_5780_);
lean_dec(v_v_5769_);
lean_dec(v_k_5768_);
v_a_5805_ = lean_ctor_get(v___x_5772_, 0);
lean_inc(v_a_5805_);
lean_dec_ref(v___x_5772_);
v_init_5766_ = v_a_5805_;
v_x_5767_ = v_r_5771_;
goto _start;
}
else
{
lean_object* v_textDocument_x3f_5807_; 
lean_inc(v_a_5773_);
lean_dec_ref(v___x_5772_);
v_textDocument_x3f_5807_ = lean_ctor_get(v_caps_5765_, 0);
if (lean_obj_tag(v_textDocument_x3f_5807_) == 0)
{
goto v___jp_5803_;
}
else
{
lean_object* v_val_5808_; lean_object* v_completion_x3f_5809_; 
v_val_5808_ = lean_ctor_get(v_textDocument_x3f_5807_, 0);
v_completion_x3f_5809_ = lean_ctor_get(v_val_5808_, 0);
if (lean_obj_tag(v_completion_x3f_5809_) == 0)
{
goto v___jp_5803_;
}
else
{
lean_object* v_val_5810_; 
v_val_5810_ = lean_ctor_get(v_completion_x3f_5809_, 0);
if (lean_obj_tag(v_val_5810_) == 0)
{
goto v___jp_5803_;
}
else
{
lean_object* v_val_5811_; 
v_val_5811_ = lean_ctor_get(v_val_5810_, 0);
if (lean_obj_tag(v_val_5811_) == 0)
{
goto v___jp_5803_;
}
else
{
lean_object* v_val_5812_; uint8_t v___x_5813_; 
v_val_5812_ = lean_ctor_get(v_val_5811_, 0);
v___x_5813_ = lean_unbox(v_val_5812_);
if (v___x_5813_ == 0)
{
goto v___jp_5803_;
}
else
{
uint8_t v___x_5814_; 
v___x_5814_ = 0;
v___y_5792_ = v___x_5814_;
goto v___jp_5791_;
}
}
}
}
}
}
v___jp_5774_:
{
lean_object* v___x_5776_; lean_object* v_items_5777_; 
lean_inc_ref(v_mkItem_5760_);
v___x_5776_ = lean_apply_3(v_mkItem_5760_, v_k_5768_, v_v_5769_, v___y_5775_);
v_items_5777_ = lean_array_push(v_a_5773_, v___x_5776_);
v_init_5766_ = v_items_5777_;
v_x_5767_ = v_r_5771_;
goto _start;
}
v___jp_5781_:
{
lean_object* v_toCommandContextInfo_5784_; lean_object* v_fileMap_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v_range_5788_; lean_object* v___x_5789_; lean_object* v___x_5790_; 
v_toCommandContextInfo_5784_ = lean_ctor_get(v_ctx_5762_, 0);
v_fileMap_5785_ = lean_ctor_get(v_toCommandContextInfo_5784_, 2);
lean_inc_ref_n(v_fileMap_5785_, 2);
v___x_5786_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5785_, v___y_5782_);
lean_dec(v___y_5782_);
v___x_5787_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5785_, v___y_5783_);
lean_dec(v___y_5783_);
v_range_5788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_range_5788_, 0, v___x_5786_);
lean_ctor_set(v_range_5788_, 1, v___x_5787_);
lean_inc_ref(v_range_5788_);
v___x_5789_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5789_, 0, v___x_5780_);
lean_ctor_set(v___x_5789_, 1, v_range_5788_);
lean_ctor_set(v___x_5789_, 2, v_range_5788_);
v___x_5790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5790_, 0, v___x_5789_);
v___y_5775_ = v___x_5790_;
goto v___jp_5774_;
}
v___jp_5791_:
{
lean_object* v___x_5793_; 
v___x_5793_ = l_Lean_Syntax_getRange_x3f(v_stx_5761_, v___y_5792_);
if (lean_obj_tag(v___x_5793_) == 1)
{
lean_object* v_val_5794_; 
v_val_5794_ = lean_ctor_get(v___x_5793_, 0);
lean_inc(v_val_5794_);
lean_dec_ref_known(v___x_5793_, 1);
if (v_snd_5763_ == 0)
{
lean_object* v_start_5795_; lean_object* v_stop_5796_; 
v_start_5795_ = lean_ctor_get(v_val_5794_, 0);
lean_inc(v_start_5795_);
v_stop_5796_ = lean_ctor_get(v_val_5794_, 1);
lean_inc(v_stop_5796_);
lean_dec(v_val_5794_);
v___y_5782_ = v_start_5795_;
v___y_5783_ = v_stop_5796_;
goto v___jp_5781_;
}
else
{
lean_object* v_start_5797_; lean_object* v_stop_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; 
v_start_5797_ = lean_ctor_get(v_val_5794_, 0);
lean_inc(v_start_5797_);
v_stop_5798_ = lean_ctor_get(v_val_5794_, 1);
lean_inc(v_stop_5798_);
lean_dec(v_val_5794_);
v___x_5799_ = lean_unsigned_to_nat(1u);
v___x_5800_ = lean_nat_add(v_stop_5798_, v___x_5799_);
lean_dec(v_stop_5798_);
v___y_5782_ = v_start_5797_;
v___y_5783_ = v___x_5800_;
goto v___jp_5781_;
}
}
else
{
lean_object* v___x_5801_; 
lean_dec(v___x_5793_);
lean_dec_ref(v___x_5780_);
v___x_5801_ = lean_box(0);
v___y_5775_ = v___x_5801_;
goto v___jp_5774_;
}
}
v___jp_5803_:
{
if (v___x_5802_ == 0)
{
v___y_5792_ = v___x_5802_;
goto v___jp_5791_;
}
else
{
lean_object* v___x_5804_; 
lean_dec_ref(v___x_5780_);
v___x_5804_ = lean_box(0);
v___y_5775_ = v___x_5804_;
goto v___jp_5774_;
}
}
}
else
{
lean_object* v___x_5815_; 
lean_dec_ref(v_ctx_5762_);
lean_dec_ref(v_mkItem_5760_);
v___x_5815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5815_, 0, v_init_5766_);
return v___x_5815_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mkItem_5760_ = stack[0].m_obj;
lean_object* v_stx_5761_ = stack[1].m_obj;
lean_object* v_ctx_5762_ = stack[2].m_obj;
uint8_t v_snd_5763_ = stack[3].m_num;
lean_object* v_fst_5764_ = stack[4].m_obj;
lean_object* v_caps_5765_ = stack[5].m_obj;
lean_object* v_init_5766_ = stack[6].m_obj;
lean_object* v_x_5767_ = stack[7].m_obj;
lean_object* v_res_5816_;
v_res_5816_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5760_, v_stx_5761_, v_ctx_5762_, v_snd_5763_, v_fst_5764_, v_caps_5765_, v_init_5766_, v_x_5767_);
stack->m_obj
 = v_res_5816_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0___boxed(lean_object* v_mkItem_5817_, lean_object* v_stx_5818_, lean_object* v_ctx_5819_, lean_object* v_snd_5820_, lean_object* v_fst_5821_, lean_object* v_caps_5822_, lean_object* v_init_5823_, lean_object* v_x_5824_){
_start:
{
uint8_t v_snd_1469__boxed_5825_; lean_object* v_res_5826_; 
v_snd_1469__boxed_5825_ = lean_unbox(v_snd_5820_);
v_res_5826_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5817_, v_stx_5818_, v_ctx_5819_, v_snd_1469__boxed_5825_, v_fst_5821_, v_caps_5822_, v_init_5823_, v_x_5824_);
lean_dec_ref(v_caps_5822_);
lean_dec_ref(v_fst_5821_);
lean_dec(v_stx_5818_);
return v_res_5826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(lean_object* v_entries_5827_, lean_object* v_stx_5828_, lean_object* v_caps_5829_, lean_object* v_ctx_5830_, lean_object* v_mkItem_5831_){
_start:
{
lean_object* v_fst_5833_; uint8_t v_snd_5834_; uint8_t v___x_5838_; lean_object* v___x_5839_; 
v___x_5838_ = 0;
v___x_5839_ = l_Lean_Syntax_getSubstring_x3f(v_stx_5828_, v___x_5838_, v___x_5838_);
if (lean_obj_tag(v___x_5839_) == 0)
{
lean_object* v___x_5840_; 
v___x_5840_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_5833_ = v___x_5840_;
v_snd_5834_ = v___x_5838_;
goto v___jp_5832_;
}
else
{
lean_object* v_val_5841_; lean_object* v_str_5842_; lean_object* v_startPos_5843_; lean_object* v_stopPos_5844_; uint8_t v___y_5846_; uint8_t v___x_5848_; 
v_val_5841_ = lean_ctor_get(v___x_5839_, 0);
lean_inc(v_val_5841_);
lean_dec_ref_known(v___x_5839_, 1);
v_str_5842_ = lean_ctor_get(v_val_5841_, 0);
lean_inc_ref(v_str_5842_);
v_startPos_5843_ = lean_ctor_get(v_val_5841_, 1);
lean_inc(v_startPos_5843_);
v_stopPos_5844_ = lean_ctor_get(v_val_5841_, 2);
lean_inc(v_stopPos_5844_);
lean_dec(v_val_5841_);
v___x_5848_ = lean_string_utf8_at_end(v_str_5842_, v_stopPos_5844_);
if (v___x_5848_ == 0)
{
uint32_t v___x_5849_; uint32_t v___x_5850_; uint8_t v___x_5851_; 
v___x_5849_ = lean_string_utf8_get(v_str_5842_, v_stopPos_5844_);
v___x_5850_ = 46;
v___x_5851_ = lean_uint32_dec_eq(v___x_5849_, v___x_5850_);
if (v___x_5851_ == 0)
{
v___y_5846_ = v___x_5851_;
goto v___jp_5845_;
}
else
{
lean_object* v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; 
v___x_5852_ = lean_string_utf8_extract(v_str_5842_, v_startPos_5843_, v_stopPos_5844_);
lean_dec(v_stopPos_5844_);
lean_dec(v_startPos_5843_);
lean_dec_ref(v_str_5842_);
v___x_5853_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_5854_ = lean_string_append(v___x_5852_, v___x_5853_);
v_fst_5833_ = v___x_5854_;
v_snd_5834_ = v___x_5851_;
goto v___jp_5832_;
}
}
else
{
v___y_5846_ = v___x_5838_;
goto v___jp_5845_;
}
v___jp_5845_:
{
lean_object* v___x_5847_; 
v___x_5847_ = lean_string_utf8_extract(v_str_5842_, v_startPos_5843_, v_stopPos_5844_);
lean_dec(v_stopPos_5844_);
lean_dec(v_startPos_5843_);
lean_dec_ref(v_str_5842_);
v_fst_5833_ = v___x_5847_;
v_snd_5834_ = v___y_5846_;
goto v___jp_5832_;
}
}
v___jp_5832_:
{
lean_object* v_items_5835_; lean_object* v___x_5836_; lean_object* v_a_5837_; 
v_items_5835_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v___x_5836_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5831_, v_stx_5828_, v_ctx_5830_, v_snd_5834_, v_fst_5833_, v_caps_5829_, v_items_5835_, v_entries_5827_);
lean_dec_ref(v_fst_5833_);
v_a_5837_ = lean_ctor_get(v___x_5836_, 0);
lean_inc(v_a_5837_);
lean_dec_ref(v___x_5836_);
return v_a_5837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0___boxed(lean_object* v_entries_5855_, lean_object* v_stx_5856_, lean_object* v_caps_5857_, lean_object* v_ctx_5858_, lean_object* v_mkItem_5859_){
_start:
{
lean_object* v_res_5860_; 
v_res_5860_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(v_entries_5855_, v_stx_5856_, v_caps_5857_, v_ctx_5858_, v_mkItem_5859_);
lean_dec_ref(v_caps_5857_);
lean_dec(v_stx_5856_);
return v_res_5860_;
}
}
lean_object* l_Lean_Server_Completion_optionCompletion___lam__1(lean_object* v_completionInfoPos_5861_, lean_object* v_uri_5862_, lean_object* v_pos_5863_, lean_object* v_stx_5864_, lean_object* v_caps_5865_, lean_object* v_ctx_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_){
_start:
{
lean_object* v_ref_5872_; lean_object* v___x_5873_; 
v_ref_5872_ = lean_ctor_get(v___y_5869_, 2);
v___x_5873_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_5873_) == 0)
{
lean_object* v_a_5874_; lean_object* v___x_5876_; uint8_t v_isShared_5877_; uint8_t v_isSharedCheck_5886_; 
v_a_5874_ = lean_ctor_get(v___x_5873_, 0);
v_isSharedCheck_5886_ = !lean_is_exclusive(v___x_5873_);
if (v_isSharedCheck_5886_ == 0)
{
v___x_5876_ = v___x_5873_;
v_isShared_5877_ = v_isSharedCheck_5886_;
goto v_resetjp_5875_;
}
else
{
lean_inc(v_a_5874_);
lean_dec(v___x_5873_);
v___x_5876_ = lean_box(0);
v_isShared_5877_ = v_isSharedCheck_5886_;
goto v_resetjp_5875_;
}
v_resetjp_5875_:
{
lean_object* v___x_5878_; lean_object* v___f_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5884_; 
v___x_5878_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_5869_);
v___f_5879_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_optionCompletion___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5879_, 0, v___x_5878_);
lean_closure_set(v___f_5879_, 1, v_completionInfoPos_5861_);
lean_closure_set(v___f_5879_, 2, v_uri_5862_);
lean_closure_set(v___f_5879_, 3, v_pos_5863_);
v___x_5880_ = lean_unsigned_to_nat(1u);
v___x_5881_ = l_Lean_Syntax_getArg(v_stx_5864_, v___x_5880_);
v___x_5882_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(v_a_5874_, v___x_5881_, v_caps_5865_, v_ctx_5866_, v___f_5879_);
lean_dec(v___x_5881_);
if (v_isShared_5877_ == 0)
{
lean_ctor_set(v___x_5876_, 0, v___x_5882_);
v___x_5884_ = v___x_5876_;
goto v_reusejp_5883_;
}
else
{
lean_object* v_reuseFailAlloc_5885_; 
v_reuseFailAlloc_5885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5885_, 0, v___x_5882_);
v___x_5884_ = v_reuseFailAlloc_5885_;
goto v_reusejp_5883_;
}
v_reusejp_5883_:
{
return v___x_5884_;
}
}
}
else
{
lean_object* v_a_5887_; lean_object* v___x_5889_; uint8_t v_isShared_5890_; uint8_t v_isSharedCheck_5898_; 
lean_dec_ref(v_ctx_5866_);
lean_dec_ref(v_pos_5863_);
lean_dec_ref(v_uri_5862_);
lean_dec(v_completionInfoPos_5861_);
v_a_5887_ = lean_ctor_get(v___x_5873_, 0);
v_isSharedCheck_5898_ = !lean_is_exclusive(v___x_5873_);
if (v_isSharedCheck_5898_ == 0)
{
v___x_5889_ = v___x_5873_;
v_isShared_5890_ = v_isSharedCheck_5898_;
goto v_resetjp_5888_;
}
else
{
lean_inc(v_a_5887_);
lean_dec(v___x_5873_);
v___x_5889_ = lean_box(0);
v_isShared_5890_ = v_isSharedCheck_5898_;
goto v_resetjp_5888_;
}
v_resetjp_5888_:
{
lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5896_; 
v___x_5891_ = lean_io_error_to_string(v_a_5887_);
v___x_5892_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5892_, 0, v___x_5891_);
v___x_5893_ = l_Lean_MessageData_ofFormat(v___x_5892_);
lean_inc(v_ref_5872_);
v___x_5894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5894_, 0, v_ref_5872_);
lean_ctor_set(v___x_5894_, 1, v___x_5893_);
if (v_isShared_5890_ == 0)
{
lean_ctor_set(v___x_5889_, 0, v___x_5894_);
v___x_5896_ = v___x_5889_;
goto v_reusejp_5895_;
}
else
{
lean_object* v_reuseFailAlloc_5897_; 
v_reuseFailAlloc_5897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5897_, 0, v___x_5894_);
v___x_5896_ = v_reuseFailAlloc_5897_;
goto v_reusejp_5895_;
}
v_reusejp_5895_:
{
return v___x_5896_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_Completion_optionCompletion___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_completionInfoPos_5861_ = stack[0].m_obj;
lean_object* v_uri_5862_ = stack[1].m_obj;
lean_object* v_pos_5863_ = stack[2].m_obj;
lean_object* v_stx_5864_ = stack[3].m_obj;
lean_object* v_caps_5865_ = stack[4].m_obj;
lean_object* v_ctx_5866_ = stack[5].m_obj;
lean_object* v___y_5867_ = stack[6].m_obj;
lean_object* v___y_5868_ = stack[7].m_obj;
lean_object* v___y_5869_ = stack[8].m_obj;
lean_object* v___y_5870_ = stack[9].m_obj;
lean_object* v_res_5899_;
v_res_5899_ = l_Lean_Server_Completion_optionCompletion___lam__1(v_completionInfoPos_5861_, v_uri_5862_, v_pos_5863_, v_stx_5864_, v_caps_5865_, v_ctx_5866_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_);
stack->m_obj
 = v_res_5899_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__1___boxed(lean_object* v_completionInfoPos_5900_, lean_object* v_uri_5901_, lean_object* v_pos_5902_, lean_object* v_stx_5903_, lean_object* v_caps_5904_, lean_object* v_ctx_5905_, lean_object* v___y_5906_, lean_object* v___y_5907_, lean_object* v___y_5908_, lean_object* v___y_5909_, lean_object* v___y_5910_){
_start:
{
lean_object* v_res_5911_; 
v_res_5911_ = l_Lean_Server_Completion_optionCompletion___lam__1(v_completionInfoPos_5900_, v_uri_5901_, v_pos_5902_, v_stx_5903_, v_caps_5904_, v_ctx_5905_, v___y_5906_, v___y_5907_, v___y_5908_, v___y_5909_);
lean_dec(v___y_5909_);
lean_dec_ref(v___y_5908_);
lean_dec(v___y_5907_);
lean_dec_ref(v___y_5906_);
lean_dec_ref(v_caps_5904_);
lean_dec(v_stx_5903_);
return v_res_5911_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__0(void){
_start:
{
lean_object* v___x_5912_; 
v___x_5912_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_5912_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__1(void){
_start:
{
lean_object* v___x_5913_; lean_object* v___x_5914_; 
v___x_5913_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__0, &l_Lean_Server_Completion_optionCompletion___closed__0_once, _init_l_Lean_Server_Completion_optionCompletion___closed__0);
v___x_5914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5914_, 0, v___x_5913_);
return v___x_5914_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__2(void){
_start:
{
lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; 
v___x_5915_ = lean_unsigned_to_nat(32u);
v___x_5916_ = lean_mk_empty_array_with_capacity(v___x_5915_);
v___x_5917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5917_, 0, v___x_5916_);
return v___x_5917_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__3(void){
_start:
{
size_t v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; 
v___x_5918_ = ((size_t)5ULL);
v___x_5919_ = lean_unsigned_to_nat(0u);
v___x_5920_ = lean_unsigned_to_nat(32u);
v___x_5921_ = lean_mk_empty_array_with_capacity(v___x_5920_);
v___x_5922_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__2, &l_Lean_Server_Completion_optionCompletion___closed__2_once, _init_l_Lean_Server_Completion_optionCompletion___closed__2);
v___x_5923_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5923_, 0, v___x_5922_);
lean_ctor_set(v___x_5923_, 1, v___x_5921_);
lean_ctor_set(v___x_5923_, 2, v___x_5919_);
lean_ctor_set(v___x_5923_, 3, v___x_5919_);
lean_ctor_set_usize(v___x_5923_, 4, v___x_5918_);
return v___x_5923_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__4(void){
_start:
{
lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; 
v___x_5924_ = lean_box(1);
v___x_5925_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__3, &l_Lean_Server_Completion_optionCompletion___closed__3_once, _init_l_Lean_Server_Completion_optionCompletion___closed__3);
v___x_5926_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__1, &l_Lean_Server_Completion_optionCompletion___closed__1_once, _init_l_Lean_Server_Completion_optionCompletion___closed__1);
v___x_5927_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5927_, 0, v___x_5926_);
lean_ctor_set(v___x_5927_, 1, v___x_5925_);
lean_ctor_set(v___x_5927_, 2, v___x_5924_);
return v___x_5927_;
}
}
lean_object* l_Lean_Server_Completion_optionCompletion(lean_object* v_uri_5928_, lean_object* v_pos_5929_, lean_object* v_completionInfoPos_5930_, lean_object* v_ctx_5931_, lean_object* v_stx_5932_, lean_object* v_caps_5933_){
_start:
{
lean_object* v___f_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; 
lean_inc_ref(v_ctx_5931_);
v___f_5935_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_optionCompletion___lam__1___boxed), 11, 6);
lean_closure_set(v___f_5935_, 0, v_completionInfoPos_5930_);
lean_closure_set(v___f_5935_, 1, v_uri_5928_);
lean_closure_set(v___f_5935_, 2, v_pos_5929_);
lean_closure_set(v___f_5935_, 3, v_stx_5932_);
lean_closure_set(v___f_5935_, 4, v_caps_5933_);
lean_closure_set(v___f_5935_, 5, v_ctx_5931_);
v___x_5936_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__4, &l_Lean_Server_Completion_optionCompletion___closed__4_once, _init_l_Lean_Server_Completion_optionCompletion___closed__4);
v___x_5937_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_5931_, v___x_5936_, v___f_5935_);
return v___x_5937_;
}
}
LEAN_EXPORT void l_Lean_Server_Completion_optionCompletion_0interp(lean_interpreter_value* stack)
{
lean_object* v_uri_5928_ = stack[0].m_obj;
lean_object* v_pos_5929_ = stack[1].m_obj;
lean_object* v_completionInfoPos_5930_ = stack[2].m_obj;
lean_object* v_ctx_5931_ = stack[3].m_obj;
lean_object* v_stx_5932_ = stack[4].m_obj;
lean_object* v_caps_5933_ = stack[5].m_obj;
lean_object* v_res_5938_;
v_res_5938_ = l_Lean_Server_Completion_optionCompletion(v_uri_5928_, v_pos_5929_, v_completionInfoPos_5930_, v_ctx_5931_, v_stx_5932_, v_caps_5933_);
stack->m_obj
 = v_res_5938_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___boxed(lean_object* v_uri_5939_, lean_object* v_pos_5940_, lean_object* v_completionInfoPos_5941_, lean_object* v_ctx_5942_, lean_object* v_stx_5943_, lean_object* v_caps_5944_, lean_object* v_a_5945_){
_start:
{
lean_object* v_res_5946_; 
v_res_5946_ = l_Lean_Server_Completion_optionCompletion(v_uri_5939_, v_pos_5940_, v_completionInfoPos_5941_, v_ctx_5942_, v_stx_5943_, v_caps_5944_);
return v_res_5946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__0(lean_object* v_completionInfoPos_5956_, lean_object* v_uri_5957_, lean_object* v_pos_5958_, lean_object* v_name_5959_, lean_object* v_explan_5960_, lean_object* v_textEdit_x3f_5961_){
_start:
{
lean_object* v_metadata_5962_; lean_object* v_removedVersion_x3f_5963_; uint8_t v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; uint8_t v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; 
v_metadata_5962_ = lean_ctor_get(v_explan_5960_, 1);
v_removedVersion_x3f_5963_ = lean_ctor_get(v_metadata_5962_, 2);
v___x_5964_ = 1;
v___x_5965_ = l_Lean_Name_toString(v_name_5959_, v___x_5964_);
v___x_5966_ = ((lean_object*)(l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__1));
v___x_5967_ = 1;
v___x_5968_ = l_Lean_ErrorExplanation_summaryWithSeverity(v_explan_5960_);
v___x_5969_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5969_, 0, v___x_5968_);
lean_ctor_set_uint8(v___x_5969_, sizeof(void*)*1, v___x_5967_);
v___x_5970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5970_, 0, v___x_5969_);
v___x_5971_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__2));
v___x_5972_ = lean_box(0);
v___x_5973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5973_, 0, v_completionInfoPos_5956_);
v___x_5974_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5974_, 0, v_uri_5957_);
lean_ctor_set(v___x_5974_, 1, v_pos_5958_);
lean_ctor_set(v___x_5974_, 2, v___x_5973_);
lean_ctor_set(v___x_5974_, 3, v___x_5972_);
v___x_5975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5975_, 0, v___x_5974_);
if (lean_obj_tag(v_removedVersion_x3f_5963_) == 0)
{
lean_object* v___x_5976_; 
v___x_5976_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5976_, 0, v___x_5965_);
lean_ctor_set(v___x_5976_, 1, v___x_5966_);
lean_ctor_set(v___x_5976_, 2, v___x_5970_);
lean_ctor_set(v___x_5976_, 3, v___x_5971_);
lean_ctor_set(v___x_5976_, 4, v_textEdit_x3f_5961_);
lean_ctor_set(v___x_5976_, 5, v___x_5972_);
lean_ctor_set(v___x_5976_, 6, v___x_5975_);
lean_ctor_set(v___x_5976_, 7, v___x_5972_);
return v___x_5976_;
}
else
{
lean_object* v___x_5977_; lean_object* v___x_5978_; 
v___x_5977_ = ((lean_object*)(l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__3));
v___x_5978_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5978_, 0, v___x_5965_);
lean_ctor_set(v___x_5978_, 1, v___x_5966_);
lean_ctor_set(v___x_5978_, 2, v___x_5970_);
lean_ctor_set(v___x_5978_, 3, v___x_5971_);
lean_ctor_set(v___x_5978_, 4, v_textEdit_x3f_5961_);
lean_ctor_set(v___x_5978_, 5, v___x_5972_);
lean_ctor_set(v___x_5978_, 6, v___x_5975_);
lean_ctor_set(v___x_5978_, 7, v___x_5977_);
return v___x_5978_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__0___boxed(lean_object* v_completionInfoPos_5979_, lean_object* v_uri_5980_, lean_object* v_pos_5981_, lean_object* v_name_5982_, lean_object* v_explan_5983_, lean_object* v_textEdit_x3f_5984_){
_start:
{
lean_object* v_res_5985_; 
v_res_5985_ = l_Lean_Server_Completion_errorNameCompletion___lam__0(v_completionInfoPos_5979_, v_uri_5980_, v_pos_5981_, v_name_5982_, v_explan_5983_, v_textEdit_x3f_5984_);
lean_dec_ref(v_explan_5983_);
return v_res_5985_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(lean_object* v_init_5986_, lean_object* v_x_5987_){
_start:
{
if (lean_obj_tag(v_x_5987_) == 0)
{
lean_object* v_k_5988_; lean_object* v_v_5989_; lean_object* v_l_5990_; lean_object* v_r_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; 
v_k_5988_ = lean_ctor_get(v_x_5987_, 1);
v_v_5989_ = lean_ctor_get(v_x_5987_, 2);
v_l_5990_ = lean_ctor_get(v_x_5987_, 3);
v_r_5991_ = lean_ctor_get(v_x_5987_, 4);
v___x_5992_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v_init_5986_, v_l_5990_);
lean_inc(v_v_5989_);
lean_inc(v_k_5988_);
v___x_5993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5993_, 0, v_k_5988_);
lean_ctor_set(v___x_5993_, 1, v_v_5989_);
v___x_5994_ = lean_array_push(v___x_5992_, v___x_5993_);
v_init_5986_ = v___x_5994_;
v_x_5987_ = v_r_5991_;
goto _start;
}
else
{
return v_init_5986_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5996_, lean_object* v_x_5997_){
_start:
{
lean_object* v_res_5998_; 
v_res_5998_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v_init_5996_, v_x_5997_);
lean_dec(v_x_5997_);
return v_res_5998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(lean_object* v_hi_5999_, lean_object* v_pivot_6000_, lean_object* v_as_6001_, lean_object* v_i_6002_, lean_object* v_k_6003_){
_start:
{
uint8_t v___x_6004_; 
v___x_6004_ = lean_nat_dec_lt(v_k_6003_, v_hi_5999_);
if (v___x_6004_ == 0)
{
lean_object* v___x_6005_; lean_object* v___x_6006_; 
lean_dec(v_k_6003_);
lean_dec_ref(v_pivot_6000_);
v___x_6005_ = lean_array_fswap(v_as_6001_, v_i_6002_, v_hi_5999_);
v___x_6006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6006_, 0, v_i_6002_);
lean_ctor_set(v___x_6006_, 1, v___x_6005_);
return v___x_6006_;
}
else
{
lean_object* v___x_6007_; lean_object* v_fst_6008_; lean_object* v_fst_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; uint8_t v___x_6012_; 
v___x_6007_ = lean_array_fget_borrowed(v_as_6001_, v_k_6003_);
v_fst_6008_ = lean_ctor_get(v___x_6007_, 0);
v_fst_6009_ = lean_ctor_get(v_pivot_6000_, 0);
lean_inc(v_fst_6008_);
v___x_6010_ = l_Lean_Name_toString(v_fst_6008_, v___x_6004_);
lean_inc(v_fst_6009_);
v___x_6011_ = l_Lean_Name_toString(v_fst_6009_, v___x_6004_);
v___x_6012_ = lean_string_dec_lt(v___x_6010_, v___x_6011_);
lean_dec_ref(v___x_6011_);
lean_dec_ref(v___x_6010_);
if (v___x_6012_ == 0)
{
lean_object* v___x_6013_; lean_object* v___x_6014_; 
v___x_6013_ = lean_unsigned_to_nat(1u);
v___x_6014_ = lean_nat_add(v_k_6003_, v___x_6013_);
lean_dec(v_k_6003_);
v_k_6003_ = v___x_6014_;
goto _start;
}
else
{
lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; 
v___x_6016_ = lean_array_fswap(v_as_6001_, v_i_6002_, v_k_6003_);
v___x_6017_ = lean_unsigned_to_nat(1u);
v___x_6018_ = lean_nat_add(v_i_6002_, v___x_6017_);
lean_dec(v_i_6002_);
v___x_6019_ = lean_nat_add(v_k_6003_, v___x_6017_);
lean_dec(v_k_6003_);
v_as_6001_ = v___x_6016_;
v_i_6002_ = v___x_6018_;
v_k_6003_ = v___x_6019_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_hi_6021_, lean_object* v_pivot_6022_, lean_object* v_as_6023_, lean_object* v_i_6024_, lean_object* v_k_6025_){
_start:
{
lean_object* v_res_6026_; 
v_res_6026_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(v_hi_6021_, v_pivot_6022_, v_as_6023_, v_i_6024_, v_k_6025_);
lean_dec(v_hi_6021_);
return v_res_6026_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(uint8_t v___x_6027_, lean_object* v_e_6028_, lean_object* v_e_x27_6029_){
_start:
{
lean_object* v_fst_6030_; lean_object* v_fst_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; uint8_t v___x_6034_; 
v_fst_6030_ = lean_ctor_get(v_e_6028_, 0);
lean_inc(v_fst_6030_);
lean_dec_ref(v_e_6028_);
v_fst_6031_ = lean_ctor_get(v_e_x27_6029_, 0);
lean_inc(v_fst_6031_);
lean_dec_ref(v_e_x27_6029_);
v___x_6032_ = l_Lean_Name_toString(v_fst_6030_, v___x_6027_);
v___x_6033_ = l_Lean_Name_toString(v_fst_6031_, v___x_6027_);
v___x_6034_ = lean_string_dec_lt(v___x_6032_, v___x_6033_);
lean_dec_ref(v___x_6033_);
lean_dec_ref(v___x_6032_);
return v___x_6034_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_6027_ = stack[0].m_num;
lean_object* v_e_6028_ = stack[1].m_obj;
lean_object* v_e_x27_6029_ = stack[2].m_obj;
uint8_t v_res_6035_;
v_res_6035_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_6027_, v_e_6028_, v_e_x27_6029_);
stack->m_num = v_res_6035_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___x_6036_, lean_object* v_e_6037_, lean_object* v_e_x27_6038_){
_start:
{
uint8_t v___x_1665__boxed_6039_; uint8_t v_res_6040_; lean_object* v_r_6041_; 
v___x_1665__boxed_6039_ = lean_unbox(v___x_6036_);
v_res_6040_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_1665__boxed_6039_, v_e_6037_, v_e_x27_6038_);
v_r_6041_ = lean_box(v_res_6040_);
return v_r_6041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(lean_object* v_n_6042_, lean_object* v_as_6043_, lean_object* v_lo_6044_, lean_object* v_hi_6045_){
_start:
{
lean_object* v___y_6047_; uint8_t v___x_6057_; 
v___x_6057_ = lean_nat_dec_lt(v_lo_6044_, v_hi_6045_);
if (v___x_6057_ == 0)
{
lean_dec(v_lo_6044_);
return v_as_6043_;
}
else
{
lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v_mid_6060_; lean_object* v___y_6062_; lean_object* v___y_6068_; lean_object* v___x_6073_; lean_object* v___x_6074_; uint8_t v___x_6075_; 
v___x_6058_ = lean_nat_add(v_lo_6044_, v_hi_6045_);
v___x_6059_ = lean_unsigned_to_nat(1u);
v_mid_6060_ = lean_nat_shiftr(v___x_6058_, v___x_6059_);
lean_dec(v___x_6058_);
v___x_6073_ = lean_array_fget_borrowed(v_as_6043_, v_mid_6060_);
v___x_6074_ = lean_array_fget_borrowed(v_as_6043_, v_lo_6044_);
lean_inc(v___x_6074_);
lean_inc(v___x_6073_);
v___x_6075_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_6057_, v___x_6073_, v___x_6074_);
if (v___x_6075_ == 0)
{
v___y_6068_ = v_as_6043_;
goto v___jp_6067_;
}
else
{
lean_object* v___x_6076_; 
v___x_6076_ = lean_array_fswap(v_as_6043_, v_lo_6044_, v_mid_6060_);
v___y_6068_ = v___x_6076_;
goto v___jp_6067_;
}
v___jp_6061_:
{
lean_object* v___x_6063_; lean_object* v___x_6064_; uint8_t v___x_6065_; 
v___x_6063_ = lean_array_fget_borrowed(v___y_6062_, v_mid_6060_);
v___x_6064_ = lean_array_fget_borrowed(v___y_6062_, v_hi_6045_);
lean_inc(v___x_6064_);
lean_inc(v___x_6063_);
v___x_6065_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_6057_, v___x_6063_, v___x_6064_);
if (v___x_6065_ == 0)
{
lean_dec(v_mid_6060_);
v___y_6047_ = v___y_6062_;
goto v___jp_6046_;
}
else
{
lean_object* v___x_6066_; 
v___x_6066_ = lean_array_fswap(v___y_6062_, v_mid_6060_, v_hi_6045_);
lean_dec(v_mid_6060_);
v___y_6047_ = v___x_6066_;
goto v___jp_6046_;
}
}
v___jp_6067_:
{
lean_object* v___x_6069_; lean_object* v___x_6070_; uint8_t v___x_6071_; 
v___x_6069_ = lean_array_fget_borrowed(v___y_6068_, v_hi_6045_);
v___x_6070_ = lean_array_fget_borrowed(v___y_6068_, v_lo_6044_);
lean_inc(v___x_6070_);
lean_inc(v___x_6069_);
v___x_6071_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_6057_, v___x_6069_, v___x_6070_);
if (v___x_6071_ == 0)
{
v___y_6062_ = v___y_6068_;
goto v___jp_6061_;
}
else
{
lean_object* v___x_6072_; 
v___x_6072_ = lean_array_fswap(v___y_6068_, v_lo_6044_, v_hi_6045_);
v___y_6062_ = v___x_6072_;
goto v___jp_6061_;
}
}
}
v___jp_6046_:
{
lean_object* v_pivot_6048_; lean_object* v___x_6049_; lean_object* v_fst_6050_; lean_object* v_snd_6051_; uint8_t v___x_6052_; 
v_pivot_6048_ = lean_array_fget(v___y_6047_, v_hi_6045_);
lean_inc_n(v_lo_6044_, 2);
v___x_6049_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(v_hi_6045_, v_pivot_6048_, v___y_6047_, v_lo_6044_, v_lo_6044_);
v_fst_6050_ = lean_ctor_get(v___x_6049_, 0);
lean_inc(v_fst_6050_);
v_snd_6051_ = lean_ctor_get(v___x_6049_, 1);
lean_inc(v_snd_6051_);
lean_dec_ref(v___x_6049_);
v___x_6052_ = lean_nat_dec_le(v_hi_6045_, v_fst_6050_);
if (v___x_6052_ == 0)
{
lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; 
v___x_6053_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_n_6042_, v_snd_6051_, v_lo_6044_, v_fst_6050_);
v___x_6054_ = lean_unsigned_to_nat(1u);
v___x_6055_ = lean_nat_add(v_fst_6050_, v___x_6054_);
lean_dec(v_fst_6050_);
v_as_6043_ = v___x_6053_;
v_lo_6044_ = v___x_6055_;
goto _start;
}
else
{
lean_dec(v_fst_6050_);
lean_dec(v_lo_6044_);
return v_snd_6051_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___boxed(lean_object* v_n_6077_, lean_object* v_as_6078_, lean_object* v_lo_6079_, lean_object* v_hi_6080_){
_start:
{
lean_object* v_res_6081_; 
v_res_6081_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_n_6077_, v_as_6078_, v_lo_6079_, v_hi_6080_);
lean_dec(v_hi_6080_);
lean_dec(v_n_6077_);
return v_res_6081_;
}
}
lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(lean_object* v___y_6084_){
_start:
{
lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v_env_6088_; lean_object* v___x_6089_; lean_object* v_toEnvExtension_6090_; lean_object* v_asyncMode_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___y_6099_; lean_object* v___y_6100_; uint8_t v___x_6103_; 
v___x_6086_ = lean_box(1);
v___x_6087_ = lean_st_ref_get(v___y_6084_);
v_env_6088_ = lean_ctor_get(v___x_6087_, 0);
lean_inc_ref(v_env_6088_);
lean_dec(v___x_6087_);
v___x_6089_ = l_Lean_errorExplanationExt;
v_toEnvExtension_6090_ = lean_ctor_get(v___x_6089_, 0);
v_asyncMode_6091_ = lean_ctor_get(v_toEnvExtension_6090_, 2);
v___x_6092_ = lean_box(0);
v___x_6093_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6086_, v___x_6089_, v_env_6088_, v_asyncMode_6091_, v___x_6092_);
v___x_6094_ = lean_unsigned_to_nat(0u);
v___x_6095_ = ((lean_object*)(l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg___closed__0));
v___x_6096_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v___x_6095_, v___x_6093_);
lean_dec(v___x_6093_);
v___x_6097_ = lean_array_get_size(v___x_6096_);
v___x_6103_ = lean_nat_dec_eq(v___x_6097_, v___x_6094_);
if (v___x_6103_ == 0)
{
lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___y_6107_; uint8_t v___x_6109_; 
v___x_6104_ = lean_unsigned_to_nat(1u);
v___x_6105_ = lean_nat_sub(v___x_6097_, v___x_6104_);
v___x_6109_ = lean_nat_dec_le(v___x_6094_, v___x_6105_);
if (v___x_6109_ == 0)
{
lean_inc(v___x_6105_);
v___y_6107_ = v___x_6105_;
goto v___jp_6106_;
}
else
{
v___y_6107_ = v___x_6094_;
goto v___jp_6106_;
}
v___jp_6106_:
{
uint8_t v___x_6108_; 
v___x_6108_ = lean_nat_dec_le(v___y_6107_, v___x_6105_);
if (v___x_6108_ == 0)
{
lean_dec(v___x_6105_);
lean_inc(v___y_6107_);
v___y_6099_ = v___y_6107_;
v___y_6100_ = v___y_6107_;
goto v___jp_6098_;
}
else
{
v___y_6099_ = v___y_6107_;
v___y_6100_ = v___x_6105_;
goto v___jp_6098_;
}
}
}
else
{
lean_object* v___x_6110_; 
v___x_6110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6110_, 0, v___x_6096_);
return v___x_6110_;
}
v___jp_6098_:
{
lean_object* v___x_6101_; lean_object* v___x_6102_; 
v___x_6101_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v___x_6097_, v___x_6096_, v___y_6099_, v___y_6100_);
lean_dec(v___y_6100_);
v___x_6102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6102_, 0, v___x_6101_);
return v___x_6102_;
}
}
}
LEAN_EXPORT void l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_6084_ = stack[0].m_obj;
lean_object* v_res_6111_;
v_res_6111_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_6084_);
stack->m_obj
 = v_res_6111_;
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg___boxed(lean_object* v___y_6112_, lean_object* v___y_6113_){
_start:
{
lean_object* v_res_6114_; 
v_res_6114_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_6112_);
lean_dec(v___y_6112_);
return v_res_6114_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(lean_object* v_mkItem_6115_, lean_object* v_stx_6116_, lean_object* v_ctx_6117_, uint8_t v_snd_6118_, lean_object* v_fst_6119_, lean_object* v_caps_6120_, lean_object* v_as_6121_, size_t v_sz_6122_, size_t v_i_6123_, lean_object* v_b_6124_){
_start:
{
lean_object* v_a_6126_; uint8_t v___x_6130_; 
v___x_6130_ = lean_usize_dec_lt(v_i_6123_, v_sz_6122_);
if (v___x_6130_ == 0)
{
lean_dec_ref(v_ctx_6117_);
lean_dec_ref(v_mkItem_6115_);
return v_b_6124_;
}
else
{
lean_object* v_a_6131_; lean_object* v_fst_6132_; lean_object* v_snd_6133_; lean_object* v___x_6135_; uint8_t v_isShared_6136_; uint8_t v_isSharedCheck_6176_; 
v_a_6131_ = lean_array_uget(v_as_6121_, v_i_6123_);
v_fst_6132_ = lean_ctor_get(v_a_6131_, 0);
v_snd_6133_ = lean_ctor_get(v_a_6131_, 1);
v_isSharedCheck_6176_ = !lean_is_exclusive(v_a_6131_);
if (v_isSharedCheck_6176_ == 0)
{
v___x_6135_ = v_a_6131_;
v_isShared_6136_ = v_isSharedCheck_6176_;
goto v_resetjp_6134_;
}
else
{
lean_inc(v_snd_6133_);
lean_inc(v_fst_6132_);
lean_dec(v_a_6131_);
v___x_6135_ = lean_box(0);
v_isShared_6136_ = v_isSharedCheck_6176_;
goto v_resetjp_6134_;
}
v_resetjp_6134_:
{
lean_object* v___y_6138_; lean_object* v___x_6141_; lean_object* v___y_6143_; lean_object* v___y_6144_; uint8_t v___y_6155_; uint8_t v___x_6165_; 
lean_inc(v_fst_6132_);
v___x_6141_ = l_Lean_Name_toString(v_fst_6132_, v___x_6130_);
v___x_6165_ = l_Lean_String_charactersIn(v_fst_6119_, v___x_6141_);
if (v___x_6165_ == 0)
{
lean_dec_ref(v___x_6141_);
lean_del_object(v___x_6135_);
lean_dec(v_snd_6133_);
lean_dec(v_fst_6132_);
v_a_6126_ = v_b_6124_;
goto v___jp_6125_;
}
else
{
lean_object* v_textDocument_x3f_6168_; 
v_textDocument_x3f_6168_ = lean_ctor_get(v_caps_6120_, 0);
if (lean_obj_tag(v_textDocument_x3f_6168_) == 0)
{
goto v___jp_6166_;
}
else
{
lean_object* v_val_6169_; lean_object* v_completion_x3f_6170_; 
v_val_6169_ = lean_ctor_get(v_textDocument_x3f_6168_, 0);
v_completion_x3f_6170_ = lean_ctor_get(v_val_6169_, 0);
if (lean_obj_tag(v_completion_x3f_6170_) == 0)
{
goto v___jp_6166_;
}
else
{
lean_object* v_val_6171_; 
v_val_6171_ = lean_ctor_get(v_completion_x3f_6170_, 0);
if (lean_obj_tag(v_val_6171_) == 0)
{
goto v___jp_6166_;
}
else
{
lean_object* v_val_6172_; 
v_val_6172_ = lean_ctor_get(v_val_6171_, 0);
if (lean_obj_tag(v_val_6172_) == 0)
{
goto v___jp_6166_;
}
else
{
lean_object* v_val_6173_; uint8_t v___x_6174_; 
v_val_6173_ = lean_ctor_get(v_val_6172_, 0);
v___x_6174_ = lean_unbox(v_val_6173_);
if (v___x_6174_ == 0)
{
goto v___jp_6166_;
}
else
{
uint8_t v___x_6175_; 
v___x_6175_ = 0;
v___y_6155_ = v___x_6175_;
goto v___jp_6154_;
}
}
}
}
}
}
v___jp_6137_:
{
lean_object* v___x_6139_; lean_object* v_items_6140_; 
lean_inc_ref(v_mkItem_6115_);
v___x_6139_ = lean_apply_3(v_mkItem_6115_, v_fst_6132_, v_snd_6133_, v___y_6138_);
v_items_6140_ = lean_array_push(v_b_6124_, v___x_6139_);
v_a_6126_ = v_items_6140_;
goto v___jp_6125_;
}
v___jp_6142_:
{
lean_object* v_toCommandContextInfo_6145_; lean_object* v_fileMap_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v_range_6150_; 
v_toCommandContextInfo_6145_ = lean_ctor_get(v_ctx_6117_, 0);
v_fileMap_6146_ = lean_ctor_get(v_toCommandContextInfo_6145_, 2);
lean_inc_ref_n(v_fileMap_6146_, 2);
v___x_6147_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_6146_, v___y_6143_);
lean_dec(v___y_6143_);
v___x_6148_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_6146_, v___y_6144_);
lean_dec(v___y_6144_);
if (v_isShared_6136_ == 0)
{
lean_ctor_set(v___x_6135_, 1, v___x_6148_);
lean_ctor_set(v___x_6135_, 0, v___x_6147_);
v_range_6150_ = v___x_6135_;
goto v_reusejp_6149_;
}
else
{
lean_object* v_reuseFailAlloc_6153_; 
v_reuseFailAlloc_6153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6153_, 0, v___x_6147_);
lean_ctor_set(v_reuseFailAlloc_6153_, 1, v___x_6148_);
v_range_6150_ = v_reuseFailAlloc_6153_;
goto v_reusejp_6149_;
}
v_reusejp_6149_:
{
lean_object* v___x_6151_; lean_object* v___x_6152_; 
lean_inc_ref(v_range_6150_);
v___x_6151_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6151_, 0, v___x_6141_);
lean_ctor_set(v___x_6151_, 1, v_range_6150_);
lean_ctor_set(v___x_6151_, 2, v_range_6150_);
v___x_6152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6152_, 0, v___x_6151_);
v___y_6138_ = v___x_6152_;
goto v___jp_6137_;
}
}
v___jp_6154_:
{
lean_object* v___x_6156_; 
v___x_6156_ = l_Lean_Syntax_getRange_x3f(v_stx_6116_, v___y_6155_);
if (lean_obj_tag(v___x_6156_) == 1)
{
lean_object* v_val_6157_; 
v_val_6157_ = lean_ctor_get(v___x_6156_, 0);
lean_inc(v_val_6157_);
lean_dec_ref_known(v___x_6156_, 1);
if (v_snd_6118_ == 0)
{
lean_object* v_start_6158_; lean_object* v_stop_6159_; 
v_start_6158_ = lean_ctor_get(v_val_6157_, 0);
lean_inc(v_start_6158_);
v_stop_6159_ = lean_ctor_get(v_val_6157_, 1);
lean_inc(v_stop_6159_);
lean_dec(v_val_6157_);
v___y_6143_ = v_start_6158_;
v___y_6144_ = v_stop_6159_;
goto v___jp_6142_;
}
else
{
lean_object* v_start_6160_; lean_object* v_stop_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; 
v_start_6160_ = lean_ctor_get(v_val_6157_, 0);
lean_inc(v_start_6160_);
v_stop_6161_ = lean_ctor_get(v_val_6157_, 1);
lean_inc(v_stop_6161_);
lean_dec(v_val_6157_);
v___x_6162_ = lean_unsigned_to_nat(1u);
v___x_6163_ = lean_nat_add(v_stop_6161_, v___x_6162_);
lean_dec(v_stop_6161_);
v___y_6143_ = v_start_6160_;
v___y_6144_ = v___x_6163_;
goto v___jp_6142_;
}
}
else
{
lean_object* v___x_6164_; 
lean_dec(v___x_6156_);
lean_dec_ref(v___x_6141_);
lean_del_object(v___x_6135_);
v___x_6164_ = lean_box(0);
v___y_6138_ = v___x_6164_;
goto v___jp_6137_;
}
}
v___jp_6166_:
{
if (v___x_6165_ == 0)
{
v___y_6155_ = v___x_6165_;
goto v___jp_6154_;
}
else
{
lean_object* v___x_6167_; 
lean_dec_ref(v___x_6141_);
lean_del_object(v___x_6135_);
v___x_6167_ = lean_box(0);
v___y_6138_ = v___x_6167_;
goto v___jp_6137_;
}
}
}
}
v___jp_6125_:
{
size_t v___x_6127_; size_t v___x_6128_; 
v___x_6127_ = ((size_t)1ULL);
v___x_6128_ = lean_usize_add(v_i_6123_, v___x_6127_);
v_i_6123_ = v___x_6128_;
v_b_6124_ = v_a_6126_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mkItem_6115_ = stack[0].m_obj;
lean_object* v_stx_6116_ = stack[1].m_obj;
lean_object* v_ctx_6117_ = stack[2].m_obj;
uint8_t v_snd_6118_ = stack[3].m_num;
lean_object* v_fst_6119_ = stack[4].m_obj;
lean_object* v_caps_6120_ = stack[5].m_obj;
lean_object* v_as_6121_ = stack[6].m_obj;
size_t v_sz_6122_ = stack[7].m_num;
size_t v_i_6123_ = stack[8].m_num;
lean_object* v_b_6124_ = stack[9].m_obj;
lean_object* v_res_6177_;
v_res_6177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(v_mkItem_6115_, v_stx_6116_, v_ctx_6117_, v_snd_6118_, v_fst_6119_, v_caps_6120_, v_as_6121_, v_sz_6122_, v_i_6123_, v_b_6124_);
stack->m_obj
 = v_res_6177_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3___boxed(lean_object* v_mkItem_6178_, lean_object* v_stx_6179_, lean_object* v_ctx_6180_, lean_object* v_snd_6181_, lean_object* v_fst_6182_, lean_object* v_caps_6183_, lean_object* v_as_6184_, lean_object* v_sz_6185_, lean_object* v_i_6186_, lean_object* v_b_6187_){
_start:
{
uint8_t v_snd_1850__boxed_6188_; size_t v_sz_boxed_6189_; size_t v_i_boxed_6190_; lean_object* v_res_6191_; 
v_snd_1850__boxed_6188_ = lean_unbox(v_snd_6181_);
v_sz_boxed_6189_ = lean_unbox_usize(v_sz_6185_);
lean_dec(v_sz_6185_);
v_i_boxed_6190_ = lean_unbox_usize(v_i_6186_);
lean_dec(v_i_6186_);
v_res_6191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(v_mkItem_6178_, v_stx_6179_, v_ctx_6180_, v_snd_1850__boxed_6188_, v_fst_6182_, v_caps_6183_, v_as_6184_, v_sz_boxed_6189_, v_i_boxed_6190_, v_b_6187_);
lean_dec_ref(v_as_6184_);
lean_dec_ref(v_caps_6183_);
lean_dec_ref(v_fst_6182_);
lean_dec(v_stx_6179_);
return v_res_6191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(lean_object* v_entries_6192_, lean_object* v_stx_6193_, lean_object* v_caps_6194_, lean_object* v_ctx_6195_, lean_object* v_mkItem_6196_){
_start:
{
lean_object* v_fst_6198_; uint8_t v_snd_6199_; uint8_t v___x_6204_; lean_object* v___x_6205_; 
v___x_6204_ = 0;
v___x_6205_ = l_Lean_Syntax_getSubstring_x3f(v_stx_6193_, v___x_6204_, v___x_6204_);
if (lean_obj_tag(v___x_6205_) == 0)
{
lean_object* v___x_6206_; 
v___x_6206_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_6198_ = v___x_6206_;
v_snd_6199_ = v___x_6204_;
goto v___jp_6197_;
}
else
{
lean_object* v_val_6207_; lean_object* v_str_6208_; lean_object* v_startPos_6209_; lean_object* v_stopPos_6210_; uint8_t v___y_6212_; uint8_t v___x_6214_; 
v_val_6207_ = lean_ctor_get(v___x_6205_, 0);
lean_inc(v_val_6207_);
lean_dec_ref_known(v___x_6205_, 1);
v_str_6208_ = lean_ctor_get(v_val_6207_, 0);
lean_inc_ref(v_str_6208_);
v_startPos_6209_ = lean_ctor_get(v_val_6207_, 1);
lean_inc(v_startPos_6209_);
v_stopPos_6210_ = lean_ctor_get(v_val_6207_, 2);
lean_inc(v_stopPos_6210_);
lean_dec(v_val_6207_);
v___x_6214_ = lean_string_utf8_at_end(v_str_6208_, v_stopPos_6210_);
if (v___x_6214_ == 0)
{
uint32_t v___x_6215_; uint32_t v___x_6216_; uint8_t v___x_6217_; 
v___x_6215_ = lean_string_utf8_get(v_str_6208_, v_stopPos_6210_);
v___x_6216_ = 46;
v___x_6217_ = lean_uint32_dec_eq(v___x_6215_, v___x_6216_);
if (v___x_6217_ == 0)
{
v___y_6212_ = v___x_6217_;
goto v___jp_6211_;
}
else
{
lean_object* v___x_6218_; lean_object* v___x_6219_; lean_object* v___x_6220_; 
v___x_6218_ = lean_string_utf8_extract(v_str_6208_, v_startPos_6209_, v_stopPos_6210_);
lean_dec(v_stopPos_6210_);
lean_dec(v_startPos_6209_);
lean_dec_ref(v_str_6208_);
v___x_6219_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_6220_ = lean_string_append(v___x_6218_, v___x_6219_);
v_fst_6198_ = v___x_6220_;
v_snd_6199_ = v___x_6217_;
goto v___jp_6197_;
}
}
else
{
v___y_6212_ = v___x_6204_;
goto v___jp_6211_;
}
v___jp_6211_:
{
lean_object* v___x_6213_; 
v___x_6213_ = lean_string_utf8_extract(v_str_6208_, v_startPos_6209_, v_stopPos_6210_);
lean_dec(v_stopPos_6210_);
lean_dec(v_startPos_6209_);
lean_dec_ref(v_str_6208_);
v_fst_6198_ = v___x_6213_;
v_snd_6199_ = v___y_6212_;
goto v___jp_6197_;
}
}
v___jp_6197_:
{
lean_object* v_items_6200_; size_t v_sz_6201_; size_t v___x_6202_; lean_object* v___x_6203_; 
v_items_6200_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v_sz_6201_ = lean_array_size(v_entries_6192_);
v___x_6202_ = ((size_t)0ULL);
v___x_6203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(v_mkItem_6196_, v_stx_6193_, v_ctx_6195_, v_snd_6199_, v_fst_6198_, v_caps_6194_, v_entries_6192_, v_sz_6201_, v___x_6202_, v_items_6200_);
lean_dec_ref(v_fst_6198_);
return v___x_6203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1___boxed(lean_object* v_entries_6221_, lean_object* v_stx_6222_, lean_object* v_caps_6223_, lean_object* v_ctx_6224_, lean_object* v_mkItem_6225_){
_start:
{
lean_object* v_res_6226_; 
v_res_6226_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(v_entries_6221_, v_stx_6222_, v_caps_6223_, v_ctx_6224_, v_mkItem_6225_);
lean_dec_ref(v_caps_6223_);
lean_dec(v_stx_6222_);
lean_dec_ref(v_entries_6221_);
return v_res_6226_;
}
}
lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__1(lean_object* v_partialId_6227_, lean_object* v_caps_6228_, lean_object* v_ctx_6229_, lean_object* v___f_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_){
_start:
{
lean_object* v___x_6236_; lean_object* v_a_6237_; lean_object* v___x_6239_; uint8_t v_isShared_6240_; uint8_t v_isSharedCheck_6245_; 
v___x_6236_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_6234_);
v_a_6237_ = lean_ctor_get(v___x_6236_, 0);
v_isSharedCheck_6245_ = !lean_is_exclusive(v___x_6236_);
if (v_isSharedCheck_6245_ == 0)
{
v___x_6239_ = v___x_6236_;
v_isShared_6240_ = v_isSharedCheck_6245_;
goto v_resetjp_6238_;
}
else
{
lean_inc(v_a_6237_);
lean_dec(v___x_6236_);
v___x_6239_ = lean_box(0);
v_isShared_6240_ = v_isSharedCheck_6245_;
goto v_resetjp_6238_;
}
v_resetjp_6238_:
{
lean_object* v___x_6241_; lean_object* v___x_6243_; 
v___x_6241_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(v_a_6237_, v_partialId_6227_, v_caps_6228_, v_ctx_6229_, v___f_6230_);
lean_dec(v_a_6237_);
if (v_isShared_6240_ == 0)
{
lean_ctor_set(v___x_6239_, 0, v___x_6241_);
v___x_6243_ = v___x_6239_;
goto v_reusejp_6242_;
}
else
{
lean_object* v_reuseFailAlloc_6244_; 
v_reuseFailAlloc_6244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6244_, 0, v___x_6241_);
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
LEAN_EXPORT void l_Lean_Server_Completion_errorNameCompletion___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_partialId_6227_ = stack[0].m_obj;
lean_object* v_caps_6228_ = stack[1].m_obj;
lean_object* v_ctx_6229_ = stack[2].m_obj;
lean_object* v___f_6230_ = stack[3].m_obj;
lean_object* v___y_6231_ = stack[4].m_obj;
lean_object* v___y_6232_ = stack[5].m_obj;
lean_object* v___y_6233_ = stack[6].m_obj;
lean_object* v___y_6234_ = stack[7].m_obj;
lean_object* v_res_6246_;
v_res_6246_ = l_Lean_Server_Completion_errorNameCompletion___lam__1(v_partialId_6227_, v_caps_6228_, v_ctx_6229_, v___f_6230_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_);
stack->m_obj
 = v_res_6246_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__1___boxed(lean_object* v_partialId_6247_, lean_object* v_caps_6248_, lean_object* v_ctx_6249_, lean_object* v___f_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_){
_start:
{
lean_object* v_res_6256_; 
v_res_6256_ = l_Lean_Server_Completion_errorNameCompletion___lam__1(v_partialId_6247_, v_caps_6248_, v_ctx_6249_, v___f_6250_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_);
lean_dec(v___y_6254_);
lean_dec_ref(v___y_6253_);
lean_dec(v___y_6252_);
lean_dec_ref(v___y_6251_);
lean_dec_ref(v_caps_6248_);
lean_dec(v_partialId_6247_);
return v_res_6256_;
}
}
lean_object* l_Lean_Server_Completion_errorNameCompletion(lean_object* v_uri_6257_, lean_object* v_pos_6258_, lean_object* v_completionInfoPos_6259_, lean_object* v_ctx_6260_, lean_object* v_partialId_6261_, lean_object* v_caps_6262_){
_start:
{
lean_object* v___f_6264_; lean_object* v___f_6265_; lean_object* v___x_6266_; lean_object* v___x_6267_; lean_object* v___x_6268_; lean_object* v___x_6269_; 
v___f_6264_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_errorNameCompletion___lam__0___boxed), 6, 3);
lean_closure_set(v___f_6264_, 0, v_completionInfoPos_6259_);
lean_closure_set(v___f_6264_, 1, v_uri_6257_);
lean_closure_set(v___f_6264_, 2, v_pos_6258_);
lean_inc_ref(v_ctx_6260_);
v___f_6265_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_errorNameCompletion___lam__1___boxed), 9, 4);
lean_closure_set(v___f_6265_, 0, v_partialId_6261_);
lean_closure_set(v___f_6265_, 1, v_caps_6262_);
lean_closure_set(v___f_6265_, 2, v_ctx_6260_);
lean_closure_set(v___f_6265_, 3, v___f_6264_);
v___x_6266_ = lean_unsigned_to_nat(32u);
v___x_6267_ = lean_mk_empty_array_with_capacity(v___x_6266_);
lean_dec_ref(v___x_6267_);
v___x_6268_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__4, &l_Lean_Server_Completion_optionCompletion___closed__4_once, _init_l_Lean_Server_Completion_optionCompletion___closed__4);
v___x_6269_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_6260_, v___x_6268_, v___f_6265_);
return v___x_6269_;
}
}
LEAN_EXPORT void l_Lean_Server_Completion_errorNameCompletion_0interp(lean_interpreter_value* stack)
{
lean_object* v_uri_6257_ = stack[0].m_obj;
lean_object* v_pos_6258_ = stack[1].m_obj;
lean_object* v_completionInfoPos_6259_ = stack[2].m_obj;
lean_object* v_ctx_6260_ = stack[3].m_obj;
lean_object* v_partialId_6261_ = stack[4].m_obj;
lean_object* v_caps_6262_ = stack[5].m_obj;
lean_object* v_res_6270_;
v_res_6270_ = l_Lean_Server_Completion_errorNameCompletion(v_uri_6257_, v_pos_6258_, v_completionInfoPos_6259_, v_ctx_6260_, v_partialId_6261_, v_caps_6262_);
stack->m_obj
 = v_res_6270_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___boxed(lean_object* v_uri_6271_, lean_object* v_pos_6272_, lean_object* v_completionInfoPos_6273_, lean_object* v_ctx_6274_, lean_object* v_partialId_6275_, lean_object* v_caps_6276_, lean_object* v_a_6277_){
_start:
{
lean_object* v_res_6278_; 
v_res_6278_ = l_Lean_Server_Completion_errorNameCompletion(v_uri_6271_, v_pos_6272_, v_completionInfoPos_6273_, v_ctx_6274_, v_partialId_6275_, v_caps_6276_);
return v_res_6278_;
}
}
lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0(lean_object* v___y_6279_, lean_object* v___y_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_){
_start:
{
lean_object* v___x_6284_; 
v___x_6284_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_6282_);
return v___x_6284_;
}
}
LEAN_EXPORT void l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_6279_ = stack[0].m_obj;
lean_object* v___y_6280_ = stack[1].m_obj;
lean_object* v___y_6281_ = stack[2].m_obj;
lean_object* v___y_6282_ = stack[3].m_obj;
lean_object* v_res_6285_;
v_res_6285_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0(v___y_6279_, v___y_6280_, v___y_6281_, v___y_6282_);
stack->m_obj
 = v_res_6285_;
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___boxed(lean_object* v___y_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_, lean_object* v___y_6289_, lean_object* v___y_6290_){
_start:
{
lean_object* v_res_6291_; 
v_res_6291_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0(v___y_6286_, v___y_6287_, v___y_6288_, v___y_6289_);
lean_dec(v___y_6289_);
lean_dec_ref(v___y_6288_);
lean_dec(v___y_6287_);
lean_dec_ref(v___y_6286_);
return v_res_6291_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0(lean_object* v_init_6292_, lean_object* v_t_6293_){
_start:
{
lean_object* v___x_6294_; 
v___x_6294_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v_init_6292_, v_t_6293_);
return v___x_6294_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0___boxed(lean_object* v_init_6295_, lean_object* v_t_6296_){
_start:
{
lean_object* v_res_6297_; 
v_res_6297_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0(v_init_6295_, v_t_6296_);
lean_dec(v_t_6296_);
return v_res_6297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1(lean_object* v_n_6298_, lean_object* v_as_6299_, lean_object* v_lo_6300_, lean_object* v_hi_6301_, lean_object* v_w_6302_, lean_object* v_hlo_6303_, lean_object* v_hhi_6304_){
_start:
{
lean_object* v___x_6305_; 
v___x_6305_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_n_6298_, v_as_6299_, v_lo_6300_, v_hi_6301_);
return v___x_6305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___boxed(lean_object* v_n_6306_, lean_object* v_as_6307_, lean_object* v_lo_6308_, lean_object* v_hi_6309_, lean_object* v_w_6310_, lean_object* v_hlo_6311_, lean_object* v_hhi_6312_){
_start:
{
lean_object* v_res_6313_; 
v_res_6313_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1(v_n_6306_, v_as_6307_, v_lo_6308_, v_hi_6309_, v_w_6310_, v_hlo_6311_, v_hhi_6312_);
lean_dec(v_hi_6309_);
lean_dec(v_n_6306_);
return v_res_6313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3(lean_object* v_n_6314_, lean_object* v_lo_6315_, lean_object* v_hi_6316_, lean_object* v_hhi_6317_, lean_object* v_pivot_6318_, lean_object* v_as_6319_, lean_object* v_i_6320_, lean_object* v_k_6321_, lean_object* v_ilo_6322_, lean_object* v_ik_6323_, lean_object* v_w_6324_){
_start:
{
lean_object* v___x_6325_; 
v___x_6325_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(v_hi_6316_, v_pivot_6318_, v_as_6319_, v_i_6320_, v_k_6321_);
return v___x_6325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___boxed(lean_object* v_n_6326_, lean_object* v_lo_6327_, lean_object* v_hi_6328_, lean_object* v_hhi_6329_, lean_object* v_pivot_6330_, lean_object* v_as_6331_, lean_object* v_i_6332_, lean_object* v_k_6333_, lean_object* v_ilo_6334_, lean_object* v_ik_6335_, lean_object* v_w_6336_){
_start:
{
lean_object* v_res_6337_; 
v_res_6337_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3(v_n_6326_, v_lo_6327_, v_hi_6328_, v_hhi_6329_, v_pivot_6330_, v_as_6331_, v_i_6332_, v_k_6333_, v_ilo_6334_, v_ik_6335_, v_w_6336_);
lean_dec(v_hi_6328_);
lean_dec(v_lo_6327_);
lean_dec(v_n_6326_);
return v_res_6337_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(lean_object* v_completionInfoPos_6338_, lean_object* v_uri_6339_, lean_object* v_pos_6340_, size_t v_sz_6341_, size_t v_i_6342_, lean_object* v_bs_6343_){
_start:
{
uint8_t v___x_6344_; 
v___x_6344_ = lean_usize_dec_lt(v_i_6342_, v_sz_6341_);
if (v___x_6344_ == 0)
{
lean_dec_ref(v_pos_6340_);
lean_dec_ref(v_uri_6339_);
lean_dec(v_completionInfoPos_6338_);
return v_bs_6343_;
}
else
{
lean_object* v_v_6345_; lean_object* v_userName_6346_; lean_object* v_docString_6347_; lean_object* v___x_6348_; lean_object* v_bs_x27_6349_; lean_object* v___x_6350_; lean_object* v___y_6352_; 
v_v_6345_ = lean_array_uget_borrowed(v_bs_6343_, v_i_6342_);
v_userName_6346_ = lean_ctor_get(v_v_6345_, 1);
lean_inc_ref(v_userName_6346_);
v_docString_6347_ = lean_ctor_get(v_v_6345_, 3);
lean_inc(v_docString_6347_);
v___x_6348_ = lean_unsigned_to_nat(0u);
v_bs_x27_6349_ = lean_array_uset(v_bs_6343_, v_i_6342_, v___x_6348_);
v___x_6350_ = lean_box(0);
if (lean_obj_tag(v_docString_6347_) == 0)
{
v___y_6352_ = v___x_6350_;
goto v___jp_6351_;
}
else
{
lean_object* v_val_6362_; lean_object* v___x_6364_; uint8_t v_isShared_6365_; uint8_t v_isSharedCheck_6371_; 
v_val_6362_ = lean_ctor_get(v_docString_6347_, 0);
v_isSharedCheck_6371_ = !lean_is_exclusive(v_docString_6347_);
if (v_isSharedCheck_6371_ == 0)
{
v___x_6364_ = v_docString_6347_;
v_isShared_6365_ = v_isSharedCheck_6371_;
goto v_resetjp_6363_;
}
else
{
lean_inc(v_val_6362_);
lean_dec(v_docString_6347_);
v___x_6364_ = lean_box(0);
v_isShared_6365_ = v_isSharedCheck_6371_;
goto v_resetjp_6363_;
}
v_resetjp_6363_:
{
uint8_t v___x_6366_; lean_object* v___x_6367_; lean_object* v___x_6369_; 
v___x_6366_ = 1;
v___x_6367_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6367_, 0, v_val_6362_);
lean_ctor_set_uint8(v___x_6367_, sizeof(void*)*1, v___x_6366_);
if (v_isShared_6365_ == 0)
{
lean_ctor_set(v___x_6364_, 0, v___x_6367_);
v___x_6369_ = v___x_6364_;
goto v_reusejp_6368_;
}
else
{
lean_object* v_reuseFailAlloc_6370_; 
v_reuseFailAlloc_6370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6370_, 0, v___x_6367_);
v___x_6369_ = v_reuseFailAlloc_6370_;
goto v_reusejp_6368_;
}
v_reusejp_6368_:
{
v___y_6352_ = v___x_6369_;
goto v___jp_6351_;
}
}
}
v___jp_6351_:
{
lean_object* v___x_6353_; lean_object* v___x_6354_; lean_object* v___x_6355_; lean_object* v___x_6356_; lean_object* v___x_6357_; size_t v___x_6358_; size_t v___x_6359_; lean_object* v___x_6360_; 
v___x_6353_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__2));
lean_inc(v_completionInfoPos_6338_);
v___x_6354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6354_, 0, v_completionInfoPos_6338_);
lean_inc_ref(v_pos_6340_);
lean_inc_ref(v_uri_6339_);
v___x_6355_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6355_, 0, v_uri_6339_);
lean_ctor_set(v___x_6355_, 1, v_pos_6340_);
lean_ctor_set(v___x_6355_, 2, v___x_6354_);
lean_ctor_set(v___x_6355_, 3, v___x_6350_);
v___x_6356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6356_, 0, v___x_6355_);
v___x_6357_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6357_, 0, v_userName_6346_);
lean_ctor_set(v___x_6357_, 1, v___x_6350_);
lean_ctor_set(v___x_6357_, 2, v___y_6352_);
lean_ctor_set(v___x_6357_, 3, v___x_6353_);
lean_ctor_set(v___x_6357_, 4, v___x_6350_);
lean_ctor_set(v___x_6357_, 5, v___x_6350_);
lean_ctor_set(v___x_6357_, 6, v___x_6356_);
lean_ctor_set(v___x_6357_, 7, v___x_6350_);
v___x_6358_ = ((size_t)1ULL);
v___x_6359_ = lean_usize_add(v_i_6342_, v___x_6358_);
v___x_6360_ = lean_array_uset(v_bs_x27_6349_, v_i_6342_, v___x_6357_);
v_i_6342_ = v___x_6359_;
v_bs_6343_ = v___x_6360_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_completionInfoPos_6338_ = stack[0].m_obj;
lean_object* v_uri_6339_ = stack[1].m_obj;
lean_object* v_pos_6340_ = stack[2].m_obj;
size_t v_sz_6341_ = stack[3].m_num;
size_t v_i_6342_ = stack[4].m_num;
lean_object* v_bs_6343_ = stack[5].m_obj;
lean_object* v_res_6372_;
v_res_6372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(v_completionInfoPos_6338_, v_uri_6339_, v_pos_6340_, v_sz_6341_, v_i_6342_, v_bs_6343_);
stack->m_obj
 = v_res_6372_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0___boxed(lean_object* v_completionInfoPos_6373_, lean_object* v_uri_6374_, lean_object* v_pos_6375_, lean_object* v_sz_6376_, lean_object* v_i_6377_, lean_object* v_bs_6378_){
_start:
{
size_t v_sz_boxed_6379_; size_t v_i_boxed_6380_; lean_object* v_res_6381_; 
v_sz_boxed_6379_ = lean_unbox_usize(v_sz_6376_);
lean_dec(v_sz_6376_);
v_i_boxed_6380_ = lean_unbox_usize(v_i_6377_);
lean_dec(v_i_6377_);
v_res_6381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(v_completionInfoPos_6373_, v_uri_6374_, v_pos_6375_, v_sz_boxed_6379_, v_i_boxed_6380_, v_bs_6378_);
return v_res_6381_;
}
}
lean_object* l_Lean_Server_Completion_tacticCompletion___lam__0(uint8_t v___x_6382_, lean_object* v_completionInfoPos_6383_, lean_object* v_uri_6384_, lean_object* v_pos_6385_, lean_object* v___y_6386_, lean_object* v___y_6387_, lean_object* v___y_6388_, lean_object* v___y_6389_){
_start:
{
lean_object* v___x_6391_; 
v___x_6391_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v___x_6382_, v___y_6386_, v___y_6387_, v___y_6388_, v___y_6389_);
if (lean_obj_tag(v___x_6391_) == 0)
{
lean_object* v_a_6392_; lean_object* v___x_6394_; uint8_t v_isShared_6395_; uint8_t v_isSharedCheck_6402_; 
v_a_6392_ = lean_ctor_get(v___x_6391_, 0);
v_isSharedCheck_6402_ = !lean_is_exclusive(v___x_6391_);
if (v_isSharedCheck_6402_ == 0)
{
v___x_6394_ = v___x_6391_;
v_isShared_6395_ = v_isSharedCheck_6402_;
goto v_resetjp_6393_;
}
else
{
lean_inc(v_a_6392_);
lean_dec(v___x_6391_);
v___x_6394_ = lean_box(0);
v_isShared_6395_ = v_isSharedCheck_6402_;
goto v_resetjp_6393_;
}
v_resetjp_6393_:
{
size_t v_sz_6396_; size_t v___x_6397_; lean_object* v___x_6398_; lean_object* v___x_6400_; 
v_sz_6396_ = lean_array_size(v_a_6392_);
v___x_6397_ = ((size_t)0ULL);
v___x_6398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(v_completionInfoPos_6383_, v_uri_6384_, v_pos_6385_, v_sz_6396_, v___x_6397_, v_a_6392_);
if (v_isShared_6395_ == 0)
{
lean_ctor_set(v___x_6394_, 0, v___x_6398_);
v___x_6400_ = v___x_6394_;
goto v_reusejp_6399_;
}
else
{
lean_object* v_reuseFailAlloc_6401_; 
v_reuseFailAlloc_6401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6401_, 0, v___x_6398_);
v___x_6400_ = v_reuseFailAlloc_6401_;
goto v_reusejp_6399_;
}
v_reusejp_6399_:
{
return v___x_6400_;
}
}
}
else
{
lean_object* v_a_6403_; lean_object* v___x_6405_; uint8_t v_isShared_6406_; uint8_t v_isSharedCheck_6410_; 
lean_dec_ref(v_pos_6385_);
lean_dec_ref(v_uri_6384_);
lean_dec(v_completionInfoPos_6383_);
v_a_6403_ = lean_ctor_get(v___x_6391_, 0);
v_isSharedCheck_6410_ = !lean_is_exclusive(v___x_6391_);
if (v_isSharedCheck_6410_ == 0)
{
v___x_6405_ = v___x_6391_;
v_isShared_6406_ = v_isSharedCheck_6410_;
goto v_resetjp_6404_;
}
else
{
lean_inc(v_a_6403_);
lean_dec(v___x_6391_);
v___x_6405_ = lean_box(0);
v_isShared_6406_ = v_isSharedCheck_6410_;
goto v_resetjp_6404_;
}
v_resetjp_6404_:
{
lean_object* v___x_6408_; 
if (v_isShared_6406_ == 0)
{
v___x_6408_ = v___x_6405_;
goto v_reusejp_6407_;
}
else
{
lean_object* v_reuseFailAlloc_6409_; 
v_reuseFailAlloc_6409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6409_, 0, v_a_6403_);
v___x_6408_ = v_reuseFailAlloc_6409_;
goto v_reusejp_6407_;
}
v_reusejp_6407_:
{
return v___x_6408_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_Completion_tacticCompletion___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_6382_ = stack[0].m_num;
lean_object* v_completionInfoPos_6383_ = stack[1].m_obj;
lean_object* v_uri_6384_ = stack[2].m_obj;
lean_object* v_pos_6385_ = stack[3].m_obj;
lean_object* v___y_6386_ = stack[4].m_obj;
lean_object* v___y_6387_ = stack[5].m_obj;
lean_object* v___y_6388_ = stack[6].m_obj;
lean_object* v___y_6389_ = stack[7].m_obj;
lean_object* v_res_6411_;
v_res_6411_ = l_Lean_Server_Completion_tacticCompletion___lam__0(v___x_6382_, v_completionInfoPos_6383_, v_uri_6384_, v_pos_6385_, v___y_6386_, v___y_6387_, v___y_6388_, v___y_6389_);
stack->m_obj
 = v_res_6411_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___lam__0___boxed(lean_object* v___x_6412_, lean_object* v_completionInfoPos_6413_, lean_object* v_uri_6414_, lean_object* v_pos_6415_, lean_object* v___y_6416_, lean_object* v___y_6417_, lean_object* v___y_6418_, lean_object* v___y_6419_, lean_object* v___y_6420_){
_start:
{
uint8_t v___x_518__boxed_6421_; lean_object* v_res_6422_; 
v___x_518__boxed_6421_ = lean_unbox(v___x_6412_);
v_res_6422_ = l_Lean_Server_Completion_tacticCompletion___lam__0(v___x_518__boxed_6421_, v_completionInfoPos_6413_, v_uri_6414_, v_pos_6415_, v___y_6416_, v___y_6417_, v___y_6418_, v___y_6419_);
lean_dec(v___y_6419_);
lean_dec_ref(v___y_6418_);
lean_dec(v___y_6417_);
lean_dec_ref(v___y_6416_);
return v_res_6422_;
}
}
lean_object* l_Lean_Server_Completion_tacticCompletion(lean_object* v_uri_6423_, lean_object* v_pos_6424_, lean_object* v_completionInfoPos_6425_, lean_object* v_ctx_6426_){
_start:
{
lean_object* v___x_6428_; uint8_t v___x_6429_; lean_object* v___x_6430_; lean_object* v___f_6431_; lean_object* v___x_6432_; 
v___x_6428_ = l_Lean_LocalContext_empty;
v___x_6429_ = 0;
v___x_6430_ = lean_box(v___x_6429_);
v___f_6431_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_tacticCompletion___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6431_, 0, v___x_6430_);
lean_closure_set(v___f_6431_, 1, v_completionInfoPos_6425_);
lean_closure_set(v___f_6431_, 2, v_uri_6423_);
lean_closure_set(v___f_6431_, 3, v_pos_6424_);
v___x_6432_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_6426_, v___x_6428_, v___f_6431_);
return v___x_6432_;
}
}
LEAN_EXPORT void l_Lean_Server_Completion_tacticCompletion_0interp(lean_interpreter_value* stack)
{
lean_object* v_uri_6423_ = stack[0].m_obj;
lean_object* v_pos_6424_ = stack[1].m_obj;
lean_object* v_completionInfoPos_6425_ = stack[2].m_obj;
lean_object* v_ctx_6426_ = stack[3].m_obj;
lean_object* v_res_6433_;
v_res_6433_ = l_Lean_Server_Completion_tacticCompletion(v_uri_6423_, v_pos_6424_, v_completionInfoPos_6425_, v_ctx_6426_);
stack->m_obj
 = v_res_6433_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___boxed(lean_object* v_uri_6434_, lean_object* v_pos_6435_, lean_object* v_completionInfoPos_6436_, lean_object* v_ctx_6437_, lean_object* v_a_6438_){
_start:
{
lean_object* v_res_6439_; 
v_res_6439_ = l_Lean_Server_Completion_tacticCompletion(v_uri_6434_, v_pos_6435_, v_completionInfoPos_6436_, v_ctx_6437_);
return v_res_6439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(lean_object* v_a_6440_, lean_object* v_b_6441_){
_start:
{
lean_object* v_array_6442_; lean_object* v_start_6443_; lean_object* v_stop_6444_; lean_object* v___x_6446_; uint8_t v_isShared_6447_; uint8_t v_isSharedCheck_6457_; 
v_array_6442_ = lean_ctor_get(v_a_6440_, 0);
v_start_6443_ = lean_ctor_get(v_a_6440_, 1);
v_stop_6444_ = lean_ctor_get(v_a_6440_, 2);
v_isSharedCheck_6457_ = !lean_is_exclusive(v_a_6440_);
if (v_isSharedCheck_6457_ == 0)
{
v___x_6446_ = v_a_6440_;
v_isShared_6447_ = v_isSharedCheck_6457_;
goto v_resetjp_6445_;
}
else
{
lean_inc(v_stop_6444_);
lean_inc(v_start_6443_);
lean_inc(v_array_6442_);
lean_dec(v_a_6440_);
v___x_6446_ = lean_box(0);
v_isShared_6447_ = v_isSharedCheck_6457_;
goto v_resetjp_6445_;
}
v_resetjp_6445_:
{
uint8_t v___x_6448_; 
v___x_6448_ = lean_nat_dec_lt(v_start_6443_, v_stop_6444_);
if (v___x_6448_ == 0)
{
lean_del_object(v___x_6446_);
lean_dec(v_stop_6444_);
lean_dec(v_start_6443_);
lean_dec_ref(v_array_6442_);
return v_b_6441_;
}
else
{
lean_object* v___x_6449_; lean_object* v___x_6450_; lean_object* v___x_6452_; 
v___x_6449_ = lean_unsigned_to_nat(1u);
v___x_6450_ = lean_nat_add(v_start_6443_, v___x_6449_);
lean_inc_ref(v_array_6442_);
if (v_isShared_6447_ == 0)
{
lean_ctor_set(v___x_6446_, 1, v___x_6450_);
v___x_6452_ = v___x_6446_;
goto v_reusejp_6451_;
}
else
{
lean_object* v_reuseFailAlloc_6456_; 
v_reuseFailAlloc_6456_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6456_, 0, v_array_6442_);
lean_ctor_set(v_reuseFailAlloc_6456_, 1, v___x_6450_);
lean_ctor_set(v_reuseFailAlloc_6456_, 2, v_stop_6444_);
v___x_6452_ = v_reuseFailAlloc_6456_;
goto v_reusejp_6451_;
}
v_reusejp_6451_:
{
lean_object* v___x_6453_; lean_object* v___x_6454_; 
v___x_6453_ = lean_array_fget(v_array_6442_, v_start_6443_);
lean_dec(v_start_6443_);
lean_dec_ref(v_array_6442_);
v___x_6454_ = lean_array_push(v_b_6441_, v___x_6453_);
v_a_6440_ = v___x_6452_;
v_b_6441_ = v___x_6454_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(lean_object* v_scopeNames_6460_, lean_object* v_idx_6461_){
_start:
{
lean_object* v___x_6462_; lean_object* v___x_6463_; lean_object* v___x_6464_; lean_object* v___x_6465_; lean_object* v___x_6466_; lean_object* v___x_6467_; lean_object* v___x_6468_; 
v___x_6462_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_6463_ = lean_array_get_size(v_scopeNames_6460_);
v___x_6464_ = l_Array_toSubarray___redArg(v_scopeNames_6460_, v_idx_6461_, v___x_6463_);
v___x_6465_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___x_6466_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(v___x_6464_, v___x_6465_);
v___x_6467_ = lean_array_to_list(v___x_6466_);
v___x_6468_ = l_String_intercalate(v___x_6462_, v___x_6467_);
return v___x_6468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0(lean_object* v_inst_6469_, lean_object* v_R_6470_, lean_object* v_a_6471_, lean_object* v_b_6472_){
_start:
{
lean_object* v___x_6473_; 
v___x_6473_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(v_a_6471_, v_b_6472_);
return v___x_6473_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(lean_object* v_upperBound_6474_, lean_object* v_next_6475_, lean_object* v_scopeNames_6476_, lean_object* v_idComponents_6477_, lean_object* v_a_6478_, uint8_t v_b_6479_){
_start:
{
uint8_t v___x_6480_; 
v___x_6480_ = lean_nat_dec_lt(v_a_6478_, v_upperBound_6474_);
if (v___x_6480_ == 0)
{
lean_dec(v_a_6478_);
return v_b_6479_;
}
else
{
uint8_t v___x_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; uint8_t v___x_6484_; 
v___x_6481_ = 0;
v___x_6482_ = lean_nat_add(v_next_6475_, v_a_6478_);
v___x_6483_ = lean_array_get_size(v_scopeNames_6476_);
v___x_6484_ = lean_nat_dec_lt(v___x_6482_, v___x_6483_);
if (v___x_6484_ == 0)
{
lean_dec(v___x_6482_);
lean_dec(v_a_6478_);
return v___x_6481_;
}
else
{
lean_object* v___x_6485_; lean_object* v___x_6486_; lean_object* v___x_6487_; uint8_t v___x_6488_; 
v___x_6485_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v___x_6486_ = lean_array_fget_borrowed(v_scopeNames_6476_, v___x_6482_);
lean_dec(v___x_6482_);
v___x_6487_ = lean_array_get_borrowed(v___x_6485_, v_idComponents_6477_, v_a_6478_);
v___x_6488_ = lean_string_dec_eq(v___x_6487_, v___x_6486_);
if (v___x_6488_ == 0)
{
lean_dec(v_a_6478_);
return v___x_6481_;
}
else
{
lean_object* v___x_6489_; lean_object* v___x_6490_; 
v___x_6489_ = lean_unsigned_to_nat(1u);
v___x_6490_ = lean_nat_add(v_a_6478_, v___x_6489_);
lean_dec(v_a_6478_);
v_a_6478_ = v___x_6490_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_6474_ = stack[0].m_obj;
lean_object* v_next_6475_ = stack[1].m_obj;
lean_object* v_scopeNames_6476_ = stack[2].m_obj;
lean_object* v_idComponents_6477_ = stack[3].m_obj;
lean_object* v_a_6478_ = stack[4].m_obj;
uint8_t v_b_6479_ = stack[5].m_num;
uint8_t v_res_6492_;
v_res_6492_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v_upperBound_6474_, v_next_6475_, v_scopeNames_6476_, v_idComponents_6477_, v_a_6478_, v_b_6479_);
stack->m_num = v_res_6492_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg___boxed(lean_object* v_upperBound_6493_, lean_object* v_next_6494_, lean_object* v_scopeNames_6495_, lean_object* v_idComponents_6496_, lean_object* v_a_6497_, lean_object* v_b_6498_){
_start:
{
uint8_t v_b_boxed_6499_; uint8_t v_res_6500_; lean_object* v_r_6501_; 
v_b_boxed_6499_ = lean_unbox(v_b_6498_);
v_res_6500_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v_upperBound_6493_, v_next_6494_, v_scopeNames_6495_, v_idComponents_6496_, v_a_6497_, v_b_boxed_6499_);
lean_dec_ref(v_idComponents_6496_);
lean_dec_ref(v_scopeNames_6495_);
lean_dec(v_next_6494_);
lean_dec(v_upperBound_6493_);
v_r_6501_ = lean_box(v_res_6500_);
return v_r_6501_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(lean_object* v_upperBound_6502_, lean_object* v_idComponents_6503_, lean_object* v_scopeNames_6504_, lean_object* v_a_6505_, lean_object* v_b_6506_){
_start:
{
lean_object* v_a_6508_; uint8_t v___x_6512_; 
v___x_6512_ = lean_nat_dec_lt(v_a_6505_, v_upperBound_6502_);
if (v___x_6512_ == 0)
{
lean_dec(v_a_6505_);
lean_dec_ref(v_scopeNames_6504_);
return v_b_6506_;
}
else
{
lean_object* v___x_6513_; lean_object* v___x_6514_; lean_object* v___x_6515_; uint8_t v___x_6516_; 
v___x_6513_ = lean_array_get_size(v_idComponents_6503_);
v___x_6514_ = lean_unsigned_to_nat(1u);
v___x_6515_ = lean_nat_sub(v___x_6513_, v___x_6514_);
v___x_6516_ = lean_nat_dec_lt(v___x_6515_, v___x_6513_);
if (v___x_6516_ == 0)
{
lean_object* v___x_6517_; lean_object* v___x_6518_; 
lean_dec(v___x_6515_);
lean_inc(v_a_6505_);
lean_inc_ref(v_scopeNames_6504_);
v___x_6517_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(v_scopeNames_6504_, v_a_6505_);
v___x_6518_ = lean_array_push(v_b_6506_, v___x_6517_);
v_a_6508_ = v___x_6518_;
goto v___jp_6507_;
}
else
{
lean_object* v___x_6519_; lean_object* v___x_6520_; lean_object* v___x_6521_; uint8_t v___x_6522_; 
v___x_6519_ = lean_nat_add(v_a_6505_, v___x_6513_);
v___x_6520_ = lean_nat_sub(v___x_6519_, v___x_6514_);
lean_dec(v___x_6519_);
v___x_6521_ = lean_array_get_size(v_scopeNames_6504_);
v___x_6522_ = lean_nat_dec_lt(v___x_6520_, v___x_6521_);
if (v___x_6522_ == 0)
{
lean_dec(v___x_6520_);
lean_dec(v___x_6515_);
v_a_6508_ = v_b_6506_;
goto v___jp_6507_;
}
else
{
lean_object* v___x_6523_; lean_object* v___x_6524_; uint8_t v___x_6525_; 
v___x_6523_ = lean_array_fget_borrowed(v_idComponents_6503_, v___x_6515_);
v___x_6524_ = lean_array_fget_borrowed(v_scopeNames_6504_, v___x_6520_);
v___x_6525_ = l_Lean_String_charactersIn(v___x_6523_, v___x_6524_);
if (v___x_6525_ == 0)
{
lean_dec(v___x_6520_);
lean_dec(v___x_6515_);
v_a_6508_ = v_b_6506_;
goto v___jp_6507_;
}
else
{
lean_object* v___x_6526_; uint8_t v___x_6527_; 
v___x_6526_ = lean_unsigned_to_nat(0u);
v___x_6527_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v___x_6515_, v_a_6505_, v_scopeNames_6504_, v_idComponents_6503_, v___x_6526_, v___x_6512_);
lean_dec(v___x_6515_);
if (v___x_6527_ == 0)
{
lean_dec(v___x_6520_);
v_a_6508_ = v_b_6506_;
goto v___jp_6507_;
}
else
{
lean_object* v___x_6528_; lean_object* v___x_6529_; 
lean_inc_ref(v_scopeNames_6504_);
v___x_6528_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(v_scopeNames_6504_, v___x_6520_);
v___x_6529_ = lean_array_push(v_b_6506_, v___x_6528_);
v_a_6508_ = v___x_6529_;
goto v___jp_6507_;
}
}
}
}
}
v___jp_6507_:
{
lean_object* v___x_6509_; lean_object* v___x_6510_; 
v___x_6509_ = lean_unsigned_to_nat(1u);
v___x_6510_ = lean_nat_add(v_a_6505_, v___x_6509_);
lean_dec(v_a_6505_);
v_a_6505_ = v___x_6510_;
v_b_6506_ = v_a_6508_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg___boxed(lean_object* v_upperBound_6530_, lean_object* v_idComponents_6531_, lean_object* v_scopeNames_6532_, lean_object* v_a_6533_, lean_object* v_b_6534_){
_start:
{
lean_object* v_res_6535_; 
v_res_6535_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v_upperBound_6530_, v_idComponents_6531_, v_scopeNames_6532_, v_a_6533_, v_b_6534_);
lean_dec_ref(v_idComponents_6531_);
lean_dec(v_upperBound_6530_);
return v_res_6535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(lean_object* v_idComponents_6536_, lean_object* v_scopeNames_6537_){
_start:
{
lean_object* v___x_6538_; lean_object* v___x_6539_; lean_object* v_r_6540_; lean_object* v___x_6541_; 
v___x_6538_ = lean_unsigned_to_nat(0u);
v___x_6539_ = lean_array_get_size(v_scopeNames_6537_);
v_r_6540_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___x_6541_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v___x_6539_, v_idComponents_6536_, v_scopeNames_6537_, v___x_6538_, v_r_6540_);
return v___x_6541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates___boxed(lean_object* v_idComponents_6542_, lean_object* v_scopeNames_6543_){
_start:
{
lean_object* v_res_6544_; 
v_res_6544_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(v_idComponents_6542_, v_scopeNames_6543_);
lean_dec_ref(v_idComponents_6542_);
return v_res_6544_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0(lean_object* v_upperBound_6545_, lean_object* v_next_6546_, lean_object* v_scopeNames_6547_, lean_object* v_idComponents_6548_, lean_object* v_inst_6549_, lean_object* v_R_6550_, lean_object* v_a_6551_, uint8_t v_b_6552_, lean_object* v_c_6553_){
_start:
{
uint8_t v___x_6554_; 
v___x_6554_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v_upperBound_6545_, v_next_6546_, v_scopeNames_6547_, v_idComponents_6548_, v_a_6551_, v_b_6552_);
return v___x_6554_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_6545_ = stack[0].m_obj;
lean_object* v_next_6546_ = stack[1].m_obj;
lean_object* v_scopeNames_6547_ = stack[2].m_obj;
lean_object* v_idComponents_6548_ = stack[3].m_obj;
lean_object* v_a_6551_ = stack[6].m_obj;
uint8_t v_b_6552_ = stack[7].m_num;
uint8_t v_res_6555_;
v_res_6555_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0(v_upperBound_6545_, v_next_6546_, v_scopeNames_6547_, v_idComponents_6548_, lean_box(0), lean_box(0), v_a_6551_, v_b_6552_, lean_box(0));
stack->m_num = v_res_6555_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___boxed(lean_object* v_upperBound_6556_, lean_object* v_next_6557_, lean_object* v_scopeNames_6558_, lean_object* v_idComponents_6559_, lean_object* v_inst_6560_, lean_object* v_R_6561_, lean_object* v_a_6562_, lean_object* v_b_6563_, lean_object* v_c_6564_){
_start:
{
uint8_t v_b_boxed_6565_; uint8_t v_res_6566_; lean_object* v_r_6567_; 
v_b_boxed_6565_ = lean_unbox(v_b_6563_);
v_res_6566_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0(v_upperBound_6556_, v_next_6557_, v_scopeNames_6558_, v_idComponents_6559_, v_inst_6560_, v_R_6561_, v_a_6562_, v_b_boxed_6565_, v_c_6564_);
lean_dec_ref(v_idComponents_6559_);
lean_dec_ref(v_scopeNames_6558_);
lean_dec(v_next_6557_);
lean_dec(v_upperBound_6556_);
v_r_6567_ = lean_box(v_res_6566_);
return v_r_6567_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1(lean_object* v_upperBound_6568_, lean_object* v_idComponents_6569_, lean_object* v_scopeNames_6570_, lean_object* v_inst_6571_, lean_object* v_R_6572_, lean_object* v_a_6573_, lean_object* v_b_6574_, lean_object* v_c_6575_){
_start:
{
lean_object* v___x_6576_; 
v___x_6576_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v_upperBound_6568_, v_idComponents_6569_, v_scopeNames_6570_, v_a_6573_, v_b_6574_);
return v___x_6576_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___boxed(lean_object* v_upperBound_6577_, lean_object* v_idComponents_6578_, lean_object* v_scopeNames_6579_, lean_object* v_inst_6580_, lean_object* v_R_6581_, lean_object* v_a_6582_, lean_object* v_b_6583_, lean_object* v_c_6584_){
_start:
{
lean_object* v_res_6585_; 
v_res_6585_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1(v_upperBound_6577_, v_idComponents_6578_, v_scopeNames_6579_, v_inst_6580_, v_R_6581_, v_a_6582_, v_b_6583_, v_c_6584_);
lean_dec_ref(v_idComponents_6578_);
lean_dec(v_upperBound_6577_);
return v_res_6585_;
}
}
uint8_t l_Lean_Server_Completion_endSectionCompletion___lam__0(lean_object* v_x_6586_){
_start:
{
lean_object* v___x_6587_; lean_object* v___x_6588_; uint8_t v___x_6589_; 
v___x_6587_ = lean_string_utf8_byte_size(v_x_6586_);
v___x_6588_ = lean_unsigned_to_nat(0u);
v___x_6589_ = lean_nat_dec_eq(v___x_6587_, v___x_6588_);
if (v___x_6589_ == 0)
{
uint8_t v___x_6590_; 
v___x_6590_ = 1;
return v___x_6590_;
}
else
{
uint8_t v___x_6591_; 
v___x_6591_ = 0;
return v___x_6591_;
}
}
}
LEAN_EXPORT void l_Lean_Server_Completion_endSectionCompletion___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_6586_ = stack[0].m_obj;
uint8_t v_res_6592_;
v_res_6592_ = l_Lean_Server_Completion_endSectionCompletion___lam__0(v_x_6586_);
stack->m_num = v_res_6592_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion___lam__0___boxed(lean_object* v_x_6593_){
_start:
{
uint8_t v_res_6594_; lean_object* v_r_6595_; 
v_res_6594_ = l_Lean_Server_Completion_endSectionCompletion___lam__0(v_x_6593_);
lean_dec_ref(v_x_6593_);
v_r_6595_ = lean_box(v_res_6594_);
return v_r_6595_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(size_t v_sz_6596_, size_t v_i_6597_, lean_object* v_bs_6598_){
_start:
{
uint8_t v___x_6599_; 
v___x_6599_ = lean_usize_dec_lt(v_i_6597_, v_sz_6596_);
if (v___x_6599_ == 0)
{
return v_bs_6598_;
}
else
{
lean_object* v_v_6600_; lean_object* v___x_6601_; lean_object* v_bs_x27_6602_; lean_object* v___x_6603_; size_t v___x_6604_; size_t v___x_6605_; lean_object* v___x_6606_; 
v_v_6600_ = lean_array_uget(v_bs_6598_, v_i_6597_);
v___x_6601_ = lean_unsigned_to_nat(0u);
v_bs_x27_6602_ = lean_array_uset(v_bs_6598_, v_i_6597_, v___x_6601_);
v___x_6603_ = l_Lean_Name_toString(v_v_6600_, v___x_6599_);
v___x_6604_ = ((size_t)1ULL);
v___x_6605_ = lean_usize_add(v_i_6597_, v___x_6604_);
v___x_6606_ = lean_array_uset(v_bs_x27_6602_, v_i_6597_, v___x_6603_);
v_i_6597_ = v___x_6605_;
v_bs_6598_ = v___x_6606_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_6596_ = stack[0].m_num;
size_t v_i_6597_ = stack[1].m_num;
lean_object* v_bs_6598_ = stack[2].m_obj;
lean_object* v_res_6608_;
v_res_6608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(v_sz_6596_, v_i_6597_, v_bs_6598_);
stack->m_obj
 = v_res_6608_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1___boxed(lean_object* v_sz_6609_, lean_object* v_i_6610_, lean_object* v_bs_6611_){
_start:
{
size_t v_sz_boxed_6612_; size_t v_i_boxed_6613_; lean_object* v_res_6614_; 
v_sz_boxed_6612_ = lean_unbox_usize(v_sz_6609_);
lean_dec(v_sz_6609_);
v_i_boxed_6613_ = lean_unbox_usize(v_i_6610_);
lean_dec(v_i_6610_);
v_res_6614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(v_sz_boxed_6612_, v_i_boxed_6613_, v_bs_6611_);
return v_res_6614_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(lean_object* v_completionInfoPos_6615_, lean_object* v_uri_6616_, lean_object* v_pos_6617_, size_t v_sz_6618_, size_t v_i_6619_, lean_object* v_bs_6620_){
_start:
{
uint8_t v___x_6621_; 
v___x_6621_ = lean_usize_dec_lt(v_i_6619_, v_sz_6618_);
if (v___x_6621_ == 0)
{
lean_dec_ref(v_pos_6617_);
lean_dec_ref(v_uri_6616_);
lean_dec(v_completionInfoPos_6615_);
return v_bs_6620_;
}
else
{
lean_object* v_v_6622_; lean_object* v___x_6623_; lean_object* v_bs_x27_6624_; lean_object* v___x_6625_; lean_object* v___x_6626_; lean_object* v___x_6627_; lean_object* v___x_6628_; lean_object* v___x_6629_; lean_object* v___x_6630_; size_t v___x_6631_; size_t v___x_6632_; lean_object* v___x_6633_; 
v_v_6622_ = lean_array_uget(v_bs_6620_, v_i_6619_);
v___x_6623_ = lean_unsigned_to_nat(0u);
v_bs_x27_6624_ = lean_array_uset(v_bs_6620_, v_i_6619_, v___x_6623_);
v___x_6625_ = lean_box(0);
v___x_6626_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__2));
lean_inc(v_completionInfoPos_6615_);
v___x_6627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6627_, 0, v_completionInfoPos_6615_);
lean_inc_ref(v_pos_6617_);
lean_inc_ref(v_uri_6616_);
v___x_6628_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6628_, 0, v_uri_6616_);
lean_ctor_set(v___x_6628_, 1, v_pos_6617_);
lean_ctor_set(v___x_6628_, 2, v___x_6627_);
lean_ctor_set(v___x_6628_, 3, v___x_6625_);
v___x_6629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6629_, 0, v___x_6628_);
v___x_6630_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6630_, 0, v_v_6622_);
lean_ctor_set(v___x_6630_, 1, v___x_6625_);
lean_ctor_set(v___x_6630_, 2, v___x_6625_);
lean_ctor_set(v___x_6630_, 3, v___x_6626_);
lean_ctor_set(v___x_6630_, 4, v___x_6625_);
lean_ctor_set(v___x_6630_, 5, v___x_6625_);
lean_ctor_set(v___x_6630_, 6, v___x_6629_);
lean_ctor_set(v___x_6630_, 7, v___x_6625_);
v___x_6631_ = ((size_t)1ULL);
v___x_6632_ = lean_usize_add(v_i_6619_, v___x_6631_);
v___x_6633_ = lean_array_uset(v_bs_x27_6624_, v_i_6619_, v___x_6630_);
v_i_6619_ = v___x_6632_;
v_bs_6620_ = v___x_6633_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_completionInfoPos_6615_ = stack[0].m_obj;
lean_object* v_uri_6616_ = stack[1].m_obj;
lean_object* v_pos_6617_ = stack[2].m_obj;
size_t v_sz_6618_ = stack[3].m_num;
size_t v_i_6619_ = stack[4].m_num;
lean_object* v_bs_6620_ = stack[5].m_obj;
lean_object* v_res_6635_;
v_res_6635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(v_completionInfoPos_6615_, v_uri_6616_, v_pos_6617_, v_sz_6618_, v_i_6619_, v_bs_6620_);
stack->m_obj
 = v_res_6635_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0___boxed(lean_object* v_completionInfoPos_6636_, lean_object* v_uri_6637_, lean_object* v_pos_6638_, lean_object* v_sz_6639_, lean_object* v_i_6640_, lean_object* v_bs_6641_){
_start:
{
size_t v_sz_boxed_6642_; size_t v_i_boxed_6643_; lean_object* v_res_6644_; 
v_sz_boxed_6642_ = lean_unbox_usize(v_sz_6639_);
lean_dec(v_sz_6639_);
v_i_boxed_6643_ = lean_unbox_usize(v_i_6640_);
lean_dec(v_i_6640_);
v_res_6644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(v_completionInfoPos_6636_, v_uri_6637_, v_pos_6638_, v_sz_boxed_6642_, v_i_boxed_6643_, v_bs_6641_);
return v_res_6644_;
}
}
lean_object* l_Lean_Server_Completion_endSectionCompletion(lean_object* v_uri_6646_, lean_object* v_pos_6647_, lean_object* v_completionInfoPos_6648_, lean_object* v_id_x3f_6649_, uint8_t v_danglingDot_6650_, lean_object* v_scopeNames_6651_){
_start:
{
lean_object* v___f_6653_; lean_object* v_idComponents_6655_; lean_object* v___y_6666_; 
v___f_6653_ = ((lean_object*)(l_Lean_Server_Completion_endSectionCompletion___closed__0));
if (lean_obj_tag(v_id_x3f_6649_) == 0)
{
lean_object* v___x_6669_; 
v___x_6669_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___y_6666_ = v___x_6669_;
goto v___jp_6665_;
}
else
{
lean_object* v_val_6670_; lean_object* v___x_6671_; lean_object* v___x_6672_; size_t v_sz_6673_; size_t v___x_6674_; lean_object* v___x_6675_; 
v_val_6670_ = lean_ctor_get(v_id_x3f_6649_, 0);
lean_inc(v_val_6670_);
lean_dec_ref_known(v_id_x3f_6649_, 1);
v___x_6671_ = l_Lean_Name_components(v_val_6670_);
v___x_6672_ = lean_array_mk(v___x_6671_);
v_sz_6673_ = lean_array_size(v___x_6672_);
v___x_6674_ = ((size_t)0ULL);
v___x_6675_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(v_sz_6673_, v___x_6674_, v___x_6672_);
v___y_6666_ = v___x_6675_;
goto v___jp_6665_;
}
v___jp_6654_:
{
lean_object* v___x_6656_; lean_object* v___x_6657_; lean_object* v___x_6658_; lean_object* v_scopeNames_6659_; lean_object* v_candidates_6660_; size_t v_sz_6661_; size_t v___x_6662_; lean_object* v___x_6663_; lean_object* v___x_6664_; 
v___x_6656_ = lean_array_mk(v_scopeNames_6651_);
v___x_6657_ = lean_array_pop(v___x_6656_);
v___x_6658_ = l_Array_takeWhile___redArg(v___f_6653_, v___x_6657_);
lean_dec_ref(v___x_6657_);
v_scopeNames_6659_ = l_Array_reverse___redArg(v___x_6658_);
v_candidates_6660_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(v_idComponents_6655_, v_scopeNames_6659_);
lean_dec_ref(v_idComponents_6655_);
v_sz_6661_ = lean_array_size(v_candidates_6660_);
v___x_6662_ = ((size_t)0ULL);
v___x_6663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(v_completionInfoPos_6648_, v_uri_6646_, v_pos_6647_, v_sz_6661_, v___x_6662_, v_candidates_6660_);
v___x_6664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6664_, 0, v___x_6663_);
return v___x_6664_;
}
v___jp_6665_:
{
if (v_danglingDot_6650_ == 0)
{
v_idComponents_6655_ = v___y_6666_;
goto v___jp_6654_;
}
else
{
lean_object* v___x_6667_; lean_object* v_idComponents_6668_; 
v___x_6667_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_idComponents_6668_ = lean_array_push(v___y_6666_, v___x_6667_);
v_idComponents_6655_ = v_idComponents_6668_;
goto v___jp_6654_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_Completion_endSectionCompletion_0interp(lean_interpreter_value* stack)
{
lean_object* v_uri_6646_ = stack[0].m_obj;
lean_object* v_pos_6647_ = stack[1].m_obj;
lean_object* v_completionInfoPos_6648_ = stack[2].m_obj;
lean_object* v_id_x3f_6649_ = stack[3].m_obj;
uint8_t v_danglingDot_6650_ = stack[4].m_num;
lean_object* v_scopeNames_6651_ = stack[5].m_obj;
lean_object* v_res_6676_;
v_res_6676_ = l_Lean_Server_Completion_endSectionCompletion(v_uri_6646_, v_pos_6647_, v_completionInfoPos_6648_, v_id_x3f_6649_, v_danglingDot_6650_, v_scopeNames_6651_);
stack->m_obj
 = v_res_6676_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion___boxed(lean_object* v_uri_6677_, lean_object* v_pos_6678_, lean_object* v_completionInfoPos_6679_, lean_object* v_id_x3f_6680_, lean_object* v_danglingDot_6681_, lean_object* v_scopeNames_6682_, lean_object* v_a_6683_){
_start:
{
uint8_t v_danglingDot_boxed_6684_; lean_object* v_res_6685_; 
v_danglingDot_boxed_6684_ = lean_unbox(v_danglingDot_6681_);
v_res_6685_ = l_Lean_Server_Completion_endSectionCompletion(v_uri_6677_, v_pos_6678_, v_completionInfoPos_6679_, v_id_x3f_6680_, v_danglingDot_boxed_6684_, v_scopeNames_6682_);
return v_res_6685_;
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
