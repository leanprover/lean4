// Lean compiler output
// Module: Lean.LibrarySuggestions.SymbolFrequency
// Imports: public import Lean.Meta.Basic import Lean.LibrarySuggestions.Basic
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LibrarySuggestions_isDeniedPremise(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_wasOriginallyTheorem(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadEnvMetaM;
lean_object* l_instMonadFinallyEST___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_tryFinally___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withoutExporting___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
lean_object* l_Lean_Meta_MetaM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Core_CoreM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EIO_toBaseIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeBaseIO___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___lam__0___boxed(lean_object*);
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__0;
static lean_once_cell_t l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__1;
static lean_once_cell_t l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2;
static lean_once_cell_t l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_localSymbolFrequencyMap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_localSymbolFrequencyMap___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_localSymbolFrequencyMapRef;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequency(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequency___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__2 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__3 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__4 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__5 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadFinallyEST___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__6 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__6_value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_tryFinally___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__6_value)} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__7 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__7_value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_tryFinally___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__7_value)} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__8 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__8_value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_tryFinally___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__8_value)} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__9 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__9_value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_tryFinally___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__10 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__10_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15;
static const lean_array_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21;
static const lean_string_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "symbolFrequency"};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25;
static const lean_string_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33;
static const lean_string_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.LibrarySuggestions.SymbolFrequency"};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34_value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "_private.Lean.LibrarySuggestions.SymbolFrequency.0.Lean.Environment.unsafeRunMetaM"};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35_value;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__0 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__0_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LibrarySuggestions_initFn___lam__3___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "symbol frequency extension"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___lam__3___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__3___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___lam__3___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__3___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___lam__3___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__3___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed(lean_object*);
static const lean_array_object l_Lean_LibrarySuggestions_initFn___lam__4___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___lam__4___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__4___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22_value),LEAN_SCALAR_PTR_LITERAL(10, 33, 51, 182, 202, 68, 104, 66)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value;
static const lean_array_object l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyMapRef;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instZeroNameMapNat;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__0 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__0_value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__0_value)} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__1 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___closed__0 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___lam__0(lean_object* v_i_x3f_1_){
_start:
{
lean_object* v___y_3_; 
if (lean_obj_tag(v_i_x3f_1_) == 0)
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(0u);
v___y_3_ = v___x_7_;
goto v___jp_2_;
}
else
{
lean_object* v_val_8_; 
v_val_8_ = lean_ctor_get(v_i_x3f_1_, 0);
v___y_3_ = v_val_8_;
goto v___jp_2_;
}
v___jp_2_:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_nat_add(v___y_3_, v___x_4_);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___lam__0___boxed(lean_object* v_i_x3f_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___lam__0(v_i_x3f_9_);
lean_dec(v_i_x3f_9_);
return v_res_10_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_box(0);
v___x_12_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___lam__0(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg(lean_object* v_k_13_, lean_object* v_t_14_){
_start:
{
if (lean_obj_tag(v_t_14_) == 0)
{
lean_object* v_size_15_; lean_object* v_k_16_; lean_object* v_v_17_; lean_object* v_l_18_; lean_object* v_r_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_34_; 
v_size_15_ = lean_ctor_get(v_t_14_, 0);
v_k_16_ = lean_ctor_get(v_t_14_, 1);
v_v_17_ = lean_ctor_get(v_t_14_, 2);
v_l_18_ = lean_ctor_get(v_t_14_, 3);
v_r_19_ = lean_ctor_get(v_t_14_, 4);
v_isSharedCheck_34_ = !lean_is_exclusive(v_t_14_);
if (v_isSharedCheck_34_ == 0)
{
v___x_21_ = v_t_14_;
v_isShared_22_ = v_isSharedCheck_34_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_r_19_);
lean_inc(v_l_18_);
lean_inc(v_v_17_);
lean_inc(v_k_16_);
lean_inc(v_size_15_);
lean_dec(v_t_14_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_34_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
uint8_t v___x_23_; 
v___x_23_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_13_, v_k_16_);
switch(v___x_23_)
{
case 0:
{
lean_object* v_impl_24_; lean_object* v___x_25_; 
lean_del_object(v___x_21_);
lean_dec(v_size_15_);
v_impl_24_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg(v_k_13_, v_l_18_);
v___x_25_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_16_, v_v_17_, v_impl_24_, v_r_19_);
return v___x_25_;
}
case 1:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v_val_28_; lean_object* v___x_30_; 
lean_dec(v_k_16_);
v___x_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_26_, 0, v_v_17_);
v___x_27_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___lam__0(v___x_26_);
lean_dec_ref(v___x_26_);
v_val_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_val_28_);
lean_dec(v___x_27_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 2, v_val_28_);
lean_ctor_set(v___x_21_, 1, v_k_13_);
v___x_30_ = v___x_21_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_size_15_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_31_, 2, v_val_28_);
lean_ctor_set(v_reuseFailAlloc_31_, 3, v_l_18_);
lean_ctor_set(v_reuseFailAlloc_31_, 4, v_r_19_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
default: 
{
lean_object* v_impl_32_; lean_object* v___x_33_; 
lean_del_object(v___x_21_);
lean_dec(v_size_15_);
v_impl_32_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg(v_k_13_, v_r_19_);
v___x_33_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_16_, v_v_17_, v_l_18_, v_impl_32_);
return v___x_33_;
}
}
}
}
else
{
lean_object* v___x_35_; lean_object* v_val_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_35_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___closed__0);
v_val_36_ = lean_ctor_get(v___x_35_, 0);
lean_inc(v_val_36_);
v___x_37_ = lean_unsigned_to_nat(1u);
v___x_38_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v_k_13_);
lean_ctor_set(v___x_38_, 2, v_val_36_);
lean_ctor_set(v___x_38_, 3, v_t_14_);
lean_ctor_set(v___x_38_, 4, v_t_14_);
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__0(lean_object* v_n_x27_39_, lean_object* v_acc_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg(v_n_x27_39_, v_acc_40_);
v___x_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__0___boxed(lean_object* v_n_x27_48_, lean_object* v_acc_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__0(v_n_x27_48_, v_acc_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_55_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__0(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_unsigned_to_nat(64u);
v___x_57_ = l_Lean_mkPtrSet___redArg(v___x_56_);
return v___x_57_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__1(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_box(0);
v___x_59_ = lean_unsigned_to_nat(16u);
v___x_60_ = lean_mk_array(v___x_59_, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_obj_once(&l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__1, &l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__1_once, _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__1);
v___x_62_ = lean_unsigned_to_nat(0u);
v___x_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__3(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_obj_once(&l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2, &l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2_once, _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2);
v___x_65_ = lean_obj_once(&l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__0, &l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__0_once, _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__0);
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1(lean_object* v___f_67_, lean_object* v_env_68_, lean_object* v_acc_69_, lean_object* v_m_70_, lean_object* v_ci_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
uint8_t v___y_78_; uint8_t v___x_100_; uint8_t v___x_101_; 
v___x_100_ = 0;
lean_inc(v_m_70_);
lean_inc_ref(v_env_68_);
v___x_101_ = l_Lean_LibrarySuggestions_isDeniedPremise(v_env_68_, v_m_70_, v___x_100_);
if (v___x_101_ == 0)
{
uint8_t v___x_102_; 
v___x_102_ = l_Lean_wasOriginallyTheorem(v_env_68_, v_m_70_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec_ref(v___f_67_);
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v_acc_69_);
return v___x_103_;
}
else
{
v___y_78_ = v___x_101_;
goto v___jp_77_;
}
}
else
{
lean_dec(v_m_70_);
lean_dec_ref(v_env_68_);
v___y_78_ = v___x_101_;
goto v___jp_77_;
}
v___jp_77_:
{
if (v___y_78_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = l_Lean_ConstantInfo_type(v_ci_71_);
v___x_80_ = lean_obj_once(&l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__3, &l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__3_once, _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__3);
v___x_81_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit(lean_box(0), v___f_67_, v___x_79_, v_acc_69_, v___x_80_, v___y_72_, v___y_73_, v___y_74_, v___y_75_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_90_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_90_ == 0)
{
v___x_84_ = v___x_81_;
v_isShared_85_ = v_isSharedCheck_90_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_81_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_90_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v_fst_86_; lean_object* v___x_88_; 
v_fst_86_ = lean_ctor_get(v_a_82_, 0);
lean_inc(v_fst_86_);
lean_dec(v_a_82_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 0, v_fst_86_);
v___x_88_ = v___x_84_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_fst_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
else
{
lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
v_a_91_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v___x_81_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___x_81_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_91_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
else
{
lean_object* v___x_99_; 
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec_ref(v___f_67_);
v___x_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_99_, 0, v_acc_69_);
return v___x_99_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___boxed(lean_object* v___f_104_, lean_object* v_env_105_, lean_object* v_acc_106_, lean_object* v_m_107_, lean_object* v_ci_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1(v___f_104_, v_env_105_, v_acc_106_, v_m_107_, v_ci_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
lean_dec_ref(v_ci_108_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___redArg(lean_object* v_f_115_, lean_object* v_keys_116_, lean_object* v_vals_117_, lean_object* v_i_118_, lean_object* v_acc_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = lean_array_get_size(v_keys_116_);
v___x_126_ = lean_nat_dec_lt(v_i_118_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v_i_118_);
lean_dec_ref(v_f_115_);
v___x_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_127_, 0, v_acc_119_);
return v___x_127_;
}
else
{
lean_object* v_k_128_; lean_object* v_v_129_; lean_object* v___x_130_; 
v_k_128_ = lean_array_fget_borrowed(v_keys_116_, v_i_118_);
v_v_129_ = lean_array_fget_borrowed(v_vals_117_, v_i_118_);
lean_inc_ref(v_f_115_);
lean_inc(v___y_123_);
lean_inc_ref(v___y_122_);
lean_inc(v___y_121_);
lean_inc_ref(v___y_120_);
lean_inc(v_v_129_);
lean_inc(v_k_128_);
v___x_130_ = lean_apply_8(v_f_115_, v_acc_119_, v_k_128_, v_v_129_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, lean_box(0));
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_a_131_);
lean_dec_ref(v___x_130_);
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lean_nat_add(v_i_118_, v___x_132_);
lean_dec(v_i_118_);
v_i_118_ = v___x_133_;
v_acc_119_ = v_a_131_;
goto _start;
}
else
{
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v_i_118_);
lean_dec_ref(v_f_115_);
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_f_135_, lean_object* v_keys_136_, lean_object* v_vals_137_, lean_object* v_i_138_, lean_object* v_acc_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___redArg(v_f_135_, v_keys_136_, v_vals_137_, v_i_138_, v_acc_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec_ref(v_vals_137_);
lean_dec_ref(v_keys_136_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(lean_object* v_f_146_, lean_object* v_x_147_, lean_object* v_x_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
if (lean_obj_tag(v_x_147_) == 0)
{
lean_object* v_es_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_174_; 
v_es_154_ = lean_ctor_get(v_x_147_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v_x_147_);
if (v_isSharedCheck_174_ == 0)
{
v___x_156_ = v_x_147_;
v_isShared_157_ = v_isSharedCheck_174_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_es_154_);
lean_dec(v_x_147_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_174_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_array_get_size(v_es_154_);
v___x_160_ = lean_nat_dec_lt(v___x_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_162_; 
lean_dec_ref(v_es_154_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec_ref(v_f_146_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v_x_148_);
v___x_162_ = v___x_156_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_x_148_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
else
{
uint8_t v___x_164_; 
v___x_164_ = lean_nat_dec_le(v___x_159_, v___x_159_);
if (v___x_164_ == 0)
{
if (v___x_160_ == 0)
{
lean_object* v___x_166_; 
lean_dec_ref(v_es_154_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec_ref(v_f_146_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v_x_148_);
v___x_166_ = v___x_156_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_x_148_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
else
{
size_t v___x_168_; size_t v___x_169_; lean_object* v___x_170_; 
lean_del_object(v___x_156_);
v___x_168_ = ((size_t)0ULL);
v___x_169_ = lean_usize_of_nat(v___x_159_);
v___x_170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(v_f_146_, v_es_154_, v___x_168_, v___x_169_, v_x_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
lean_dec_ref(v_es_154_);
return v___x_170_;
}
}
else
{
size_t v___x_171_; size_t v___x_172_; lean_object* v___x_173_; 
lean_del_object(v___x_156_);
v___x_171_ = ((size_t)0ULL);
v___x_172_ = lean_usize_of_nat(v___x_159_);
v___x_173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(v_f_146_, v_es_154_, v___x_171_, v___x_172_, v_x_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
lean_dec_ref(v_es_154_);
return v___x_173_;
}
}
}
}
else
{
lean_object* v_ks_175_; lean_object* v_vs_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v_ks_175_ = lean_ctor_get(v_x_147_, 0);
lean_inc_ref(v_ks_175_);
v_vs_176_ = lean_ctor_get(v_x_147_, 1);
lean_inc_ref(v_vs_176_);
lean_dec_ref(v_x_147_);
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___redArg(v_f_146_, v_ks_175_, v_vs_176_, v___x_177_, v_x_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
lean_dec_ref(v_vs_176_);
lean_dec_ref(v_ks_175_);
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(lean_object* v_f_179_, lean_object* v_as_180_, size_t v_i_181_, size_t v_stop_182_, lean_object* v_b_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_a_190_; lean_object* v___y_195_; uint8_t v___x_197_; 
v___x_197_ = lean_usize_dec_eq(v_i_181_, v_stop_182_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
v___x_198_ = lean_array_uget_borrowed(v_as_180_, v_i_181_);
switch(lean_obj_tag(v___x_198_))
{
case 0:
{
lean_object* v_key_199_; lean_object* v_val_200_; lean_object* v___x_201_; 
v_key_199_ = lean_ctor_get(v___x_198_, 0);
v_val_200_ = lean_ctor_get(v___x_198_, 1);
lean_inc_ref(v_f_179_);
lean_inc(v___y_187_);
lean_inc_ref(v___y_186_);
lean_inc(v___y_185_);
lean_inc_ref(v___y_184_);
lean_inc(v_val_200_);
lean_inc(v_key_199_);
v___x_201_ = lean_apply_8(v_f_179_, v_b_183_, v_key_199_, v_val_200_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, lean_box(0));
v___y_195_ = v___x_201_;
goto v___jp_194_;
}
case 1:
{
lean_object* v_node_202_; lean_object* v___x_203_; 
v_node_202_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v___y_187_);
lean_inc_ref(v___y_186_);
lean_inc(v___y_185_);
lean_inc_ref(v___y_184_);
lean_inc(v_node_202_);
lean_inc_ref(v_f_179_);
v___x_203_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_179_, v_node_202_, v_b_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
v___y_195_ = v___x_203_;
goto v___jp_194_;
}
default: 
{
v_a_190_ = v_b_183_;
goto v___jp_189_;
}
}
}
else
{
lean_object* v___x_204_; 
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec_ref(v_f_179_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v_b_183_);
return v___x_204_;
}
v___jp_189_:
{
size_t v___x_191_; size_t v___x_192_; 
v___x_191_ = ((size_t)1ULL);
v___x_192_ = lean_usize_add(v_i_181_, v___x_191_);
v_i_181_ = v___x_192_;
v_b_183_ = v_a_190_;
goto _start;
}
v___jp_194_:
{
if (lean_obj_tag(v___y_195_) == 0)
{
lean_object* v_a_196_; 
v_a_196_ = lean_ctor_get(v___y_195_, 0);
lean_inc(v_a_196_);
lean_dec_ref(v___y_195_);
v_a_190_ = v_a_196_;
goto v___jp_189_;
}
else
{
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec_ref(v_f_179_);
return v___y_195_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_205_, lean_object* v_as_206_, lean_object* v_i_207_, lean_object* v_stop_208_, lean_object* v_b_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
size_t v_i_boxed_215_; size_t v_stop_boxed_216_; lean_object* v_res_217_; 
v_i_boxed_215_ = lean_unbox_usize(v_i_207_);
lean_dec(v_i_207_);
v_stop_boxed_216_ = lean_unbox_usize(v_stop_208_);
lean_dec(v_stop_208_);
v_res_217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(v_f_205_, v_as_206_, v_i_boxed_215_, v_stop_boxed_216_, v_b_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
lean_dec_ref(v_as_206_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg___boxed(lean_object* v_f_218_, lean_object* v_x_219_, lean_object* v_x_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_218_, v_x_219_, v_x_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap(lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v___x_233_; lean_object* v_env_234_; lean_object* v___x_235_; lean_object* v_map_u2082_236_; lean_object* v___f_237_; lean_object* v___f_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_233_ = lean_st_ref_get(v_a_231_);
v_env_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc_ref(v_env_234_);
lean_dec(v___x_233_);
lean_inc_ref(v_env_234_);
v___x_235_ = l_Lean_Environment_constants(v_env_234_);
v_map_u2082_236_ = lean_ctor_get(v___x_235_, 1);
lean_inc_ref(v_map_u2082_236_);
lean_dec_ref(v___x_235_);
v___f_237_ = ((lean_object*)(l_Lean_LibrarySuggestions_localSymbolFrequencyMap___closed__0));
v___f_238_ = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___boxed), 10, 2);
lean_closure_set(v___f_238_, 0, v___f_237_);
lean_closure_set(v___f_238_, 1, v_env_234_);
v___x_239_ = lean_box(1);
v___x_240_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v___f_238_, v_map_u2082_236_, v___x_239_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap___boxed(lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_LibrarySuggestions_localSymbolFrequencyMap(v_a_241_, v_a_242_, v_a_243_, v_a_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0(lean_object* v_k_247_, lean_object* v_t_248_, lean_object* v_hl_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg(v_k_247_, v_t_248_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1___redArg(lean_object* v_map_251_, lean_object* v_f_252_, lean_object* v_init_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_252_, v_map_251_, v_init_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1___redArg___boxed(lean_object* v_map_260_, lean_object* v_f_261_, lean_object* v_init_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1___redArg(v_map_260_, v_f_261_, v_init_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1(lean_object* v_00_u03c3_269_, lean_object* v_00_u03b2_270_, lean_object* v_map_271_, lean_object* v_f_272_, lean_object* v_init_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_272_, v_map_271_, v_init_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1___boxed(lean_object* v_00_u03c3_280_, lean_object* v_00_u03b2_281_, lean_object* v_map_282_, lean_object* v_f_283_, lean_object* v_init_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1(v_00_u03c3_280_, v_00_u03b2_281_, v_map_282_, v_f_283_, v_init_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1(lean_object* v_00_u03c3_291_, lean_object* v_00_u03b1_292_, lean_object* v_00_u03b2_293_, lean_object* v_f_294_, lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_294_, v_x_295_, v_x_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___boxed(lean_object* v_00_u03c3_303_, lean_object* v_00_u03b1_304_, lean_object* v_00_u03b2_305_, lean_object* v_f_306_, lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1(v_00_u03c3_303_, v_00_u03b1_304_, v_00_u03b2_305_, v_f_306_, v_x_307_, v_x_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_315_, lean_object* v_00_u03b2_316_, lean_object* v_00_u03c3_317_, lean_object* v_f_318_, lean_object* v_as_319_, size_t v_i_320_, size_t v_stop_321_, lean_object* v_b_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(v_f_318_, v_as_319_, v_i_320_, v_stop_321_, v_b_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_329_, lean_object* v_00_u03b2_330_, lean_object* v_00_u03c3_331_, lean_object* v_f_332_, lean_object* v_as_333_, lean_object* v_i_334_, lean_object* v_stop_335_, lean_object* v_b_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
size_t v_i_boxed_342_; size_t v_stop_boxed_343_; lean_object* v_res_344_; 
v_i_boxed_342_ = lean_unbox_usize(v_i_334_);
lean_dec(v_i_334_);
v_stop_boxed_343_ = lean_unbox_usize(v_stop_335_);
lean_dec(v_stop_335_);
v_res_344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2(v_00_u03b1_329_, v_00_u03b2_330_, v_00_u03c3_331_, v_f_332_, v_as_333_, v_i_boxed_342_, v_stop_boxed_343_, v_b_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec_ref(v_as_333_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3(lean_object* v_00_u03c3_345_, lean_object* v_00_u03b1_346_, lean_object* v_00_u03b2_347_, lean_object* v_f_348_, lean_object* v_keys_349_, lean_object* v_vals_350_, lean_object* v_heq_351_, lean_object* v_i_352_, lean_object* v_acc_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___redArg(v_f_348_, v_keys_349_, v_vals_350_, v_i_352_, v_acc_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03c3_360_, lean_object* v_00_u03b1_361_, lean_object* v_00_u03b2_362_, lean_object* v_f_363_, lean_object* v_keys_364_, lean_object* v_vals_365_, lean_object* v_heq_366_, lean_object* v_i_367_, lean_object* v_acc_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3(v_00_u03c3_360_, v_00_u03b1_361_, v_00_u03b2_362_, v_f_363_, v_keys_364_, v_vals_365_, v_heq_366_, v_i_367_, v_acc_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
lean_dec_ref(v_vals_365_);
lean_dec_ref(v_keys_364_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = lean_box(0);
v___x_377_ = lean_st_mk_ref(v___x_376_);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2____boxed(lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2_();
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap(lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_localSymbolFrequencyMapRef;
v___x_387_ = lean_st_ref_get(v___x_386_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_LibrarySuggestions_localSymbolFrequencyMap(v_a_381_, v_a_382_, v_a_383_, v_a_384_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_398_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_398_ == 0)
{
v___x_391_ = v___x_388_;
v_isShared_392_ = v_isSharedCheck_398_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_398_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
lean_inc(v_a_389_);
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v_a_389_);
v___x_394_ = lean_st_ref_set(v___x_386_, v___x_393_);
if (v_isShared_392_ == 0)
{
v___x_396_ = v___x_391_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_389_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
else
{
return v___x_388_;
}
}
else
{
lean_object* v_val_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
v_val_399_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_387_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_val_399_);
lean_dec(v___x_387_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
lean_ctor_set_tag(v___x_401_, 0);
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_val_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap___boxed(lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap(v_a_407_, v_a_408_, v_a_409_, v_a_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(lean_object* v_t_413_, lean_object* v_k_414_, lean_object* v_fallback_415_){
_start:
{
if (lean_obj_tag(v_t_413_) == 0)
{
lean_object* v_k_416_; lean_object* v_v_417_; lean_object* v_l_418_; lean_object* v_r_419_; uint8_t v___x_420_; 
v_k_416_ = lean_ctor_get(v_t_413_, 1);
v_v_417_ = lean_ctor_get(v_t_413_, 2);
v_l_418_ = lean_ctor_get(v_t_413_, 3);
v_r_419_ = lean_ctor_get(v_t_413_, 4);
v___x_420_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_414_, v_k_416_);
switch(v___x_420_)
{
case 0:
{
v_t_413_ = v_l_418_;
goto _start;
}
case 1:
{
lean_inc(v_v_417_);
return v_v_417_;
}
default: 
{
v_t_413_ = v_r_419_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_415_);
return v_fallback_415_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg___boxed(lean_object* v_t_423_, lean_object* v_k_424_, lean_object* v_fallback_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_t_423_, v_k_424_, v_fallback_425_);
lean_dec(v_fallback_425_);
lean_dec(v_k_424_);
lean_dec(v_t_423_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequency(lean_object* v_n_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap(v_a_428_, v_a_429_, v_a_430_, v_a_431_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_443_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_443_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_443_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_443_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_a_434_, v_n_427_, v___x_438_);
lean_dec(v_a_434_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_439_);
v___x_441_ = v___x_436_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
v_a_444_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_433_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_433_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequency___boxed(lean_object* v_n_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_LibrarySuggestions_localSymbolFrequency(v_n_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
lean_dec(v_n_452_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0(lean_object* v_00_u03b4_459_, lean_object* v_t_460_, lean_object* v_k_461_, lean_object* v_fallback_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_t_460_, v_k_461_, v_fallback_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___boxed(lean_object* v_00_u03b4_464_, lean_object* v_t_465_, lean_object* v_k_466_, lean_object* v_fallback_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0(v_00_u03b4_464_, v_t_465_, v_k_466_, v_fallback_467_);
lean_dec(v_fallback_467_);
lean_dec(v_k_466_);
lean_dec(v_t_465_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___lam__0(lean_object* v___x_469_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = l_Lean_MessageData_toString(v___x_469_);
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___lam__0___boxed(lean_object* v___x_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___lam__0(v___x_473_);
return v_res_475_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0(void){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_476_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0);
v___x_478_ = l_ReaderT_instMonad___redArg(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11(void){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_492_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_unsigned_to_nat(32u);
v___x_496_ = lean_mk_empty_array_with_capacity(v___x_495_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14(void){
_start:
{
size_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_498_ = ((size_t)5ULL);
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = lean_unsigned_to_nat(32u);
v___x_501_ = lean_mk_empty_array_with_capacity(v___x_500_);
v___x_502_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13);
v___x_503_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_503_, 0, v___x_502_);
lean_ctor_set(v___x_503_, 1, v___x_501_);
lean_ctor_set(v___x_503_, 2, v___x_499_);
lean_ctor_set(v___x_503_, 3, v___x_499_);
lean_ctor_set_usize(v___x_503_, 4, v___x_498_);
return v___x_503_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_504_ = lean_box(1);
v___x_505_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14);
v___x_506_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12);
v___x_507_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v___x_505_);
lean_ctor_set(v___x_507_, 2, v___x_504_);
return v___x_507_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17(void){
_start:
{
uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_510_ = 1;
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_box(0);
v___x_513_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16));
v___x_514_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
v___x_515_ = lean_box(1);
v___x_516_ = 0;
v___x_517_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_518_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_518_, 0, v___x_517_);
lean_ctor_set(v___x_518_, 1, v___x_515_);
lean_ctor_set(v___x_518_, 2, v___x_514_);
lean_ctor_set(v___x_518_, 3, v___x_513_);
lean_ctor_set(v___x_518_, 4, v___x_512_);
lean_ctor_set(v___x_518_, 5, v___x_511_);
lean_ctor_set(v___x_518_, 6, v___x_512_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*7, v___x_516_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*7 + 1, v___x_516_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*7 + 2, v___x_516_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*7 + 3, v___x_510_);
return v___x_518_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_519_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12);
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
lean_ctor_set(v___x_521_, 2, v___x_520_);
lean_ctor_set(v___x_521_, 3, v___x_519_);
lean_ctor_set(v___x_521_, 4, v___x_519_);
lean_ctor_set(v___x_521_, 5, v___x_519_);
lean_ctor_set(v___x_521_, 6, v___x_519_);
lean_ctor_set(v___x_521_, 7, v___x_519_);
lean_ctor_set(v___x_521_, 8, v___x_519_);
return v___x_521_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12);
v___x_523_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
lean_ctor_set(v___x_523_, 2, v___x_522_);
lean_ctor_set(v___x_523_, 3, v___x_522_);
lean_ctor_set(v___x_523_, 4, v___x_522_);
lean_ctor_set(v___x_523_, 5, v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12);
v___x_525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
lean_ctor_set(v___x_525_, 2, v___x_524_);
lean_ctor_set(v___x_525_, 3, v___x_524_);
lean_ctor_set(v___x_525_, 4, v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_526_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20);
v___x_527_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14);
v___x_528_ = lean_box(1);
v___x_529_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19);
v___x_530_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18);
v___x_531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___x_529_);
lean_ctor_set(v___x_531_, 2, v___x_528_);
lean_ctor_set(v___x_531_, 3, v___x_527_);
lean_ctor_set(v___x_531_, 4, v___x_526_);
return v___x_531_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = l_Lean_Options_empty;
v___x_534_ = l_Lean_Core_getMaxHeartbeats(v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_535_ = lean_obj_once(&l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2, &l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2_once, _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2);
v___x_536_ = lean_box(0);
v___x_537_ = 0;
v___x_538_ = l_Lean_firstFrontendMacroScope;
v___x_539_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23);
v___x_540_ = lean_box(0);
v___x_541_ = lean_box(0);
v___x_542_ = lean_box(0);
v___x_543_ = lean_unsigned_to_nat(1000u);
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = l_Lean_Options_empty;
v___x_546_ = l_Lean_instInhabitedFileMap_default;
v___x_547_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22));
v___x_548_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v___x_546_);
lean_ctor_set(v___x_548_, 2, v___x_545_);
lean_ctor_set(v___x_548_, 3, v___x_544_);
lean_ctor_set(v___x_548_, 4, v___x_543_);
lean_ctor_set(v___x_548_, 5, v___x_542_);
lean_ctor_set(v___x_548_, 6, v___x_541_);
lean_ctor_set(v___x_548_, 7, v___x_540_);
lean_ctor_set(v___x_548_, 8, v___x_544_);
lean_ctor_set(v___x_548_, 9, v___x_539_);
lean_ctor_set(v___x_548_, 10, v___x_541_);
lean_ctor_set(v___x_548_, 11, v___x_538_);
lean_ctor_set(v___x_548_, 12, v___x_536_);
lean_ctor_set(v___x_548_, 13, v___x_535_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*14, v___x_537_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*14 + 1, v___x_537_);
return v___x_548_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = l_Lean_firstFrontendMacroScope;
v___x_551_ = lean_nat_add(v___x_550_, v___x_549_);
return v___x_551_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30(void){
_start:
{
lean_object* v___x_562_; uint64_t v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14);
v___x_563_ = 0ULL;
v___x_564_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_564_, 0, v___x_562_);
lean_ctor_set_uint64(v___x_564_, sizeof(void*)*1, v___x_563_);
return v___x_564_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
return v___x_566_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = l_Lean_NameSet_empty;
v___x_568_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14);
v___x_569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
lean_ctor_set(v___x_569_, 2, v___x_567_);
return v___x_569_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; lean_object* v___x_573_; 
v___x_570_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14);
v___x_571_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12);
v___x_572_ = 1;
v___x_573_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_573_, 0, v___x_571_);
lean_ctor_set(v___x_573_, 1, v___x_571_);
lean_ctor_set(v___x_573_, 2, v___x_570_);
lean_ctor_set_uint8(v___x_573_, sizeof(void*)*3, v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(lean_object* v_inst_576_, lean_object* v_env_577_, lean_object* v_x_578_){
_start:
{
lean_object* v___x_579_; lean_object* v_toApplicative_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_674_; 
v___x_579_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1);
v_toApplicative_580_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; 
v_unused_675_ = lean_ctor_get(v___x_579_, 1);
lean_dec(v_unused_675_);
v___x_582_ = v___x_579_;
v_isShared_583_ = v_isSharedCheck_674_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_toApplicative_580_);
lean_dec(v___x_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_674_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v_toFunctor_584_; lean_object* v_toSeq_585_; lean_object* v_toSeqLeft_586_; lean_object* v_toSeqRight_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_672_; 
v_toFunctor_584_ = lean_ctor_get(v_toApplicative_580_, 0);
v_toSeq_585_ = lean_ctor_get(v_toApplicative_580_, 2);
v_toSeqLeft_586_ = lean_ctor_get(v_toApplicative_580_, 3);
v_toSeqRight_587_ = lean_ctor_get(v_toApplicative_580_, 4);
v_isSharedCheck_672_ = !lean_is_exclusive(v_toApplicative_580_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; 
v_unused_673_ = lean_ctor_get(v_toApplicative_580_, 1);
lean_dec(v_unused_673_);
v___x_589_ = v_toApplicative_580_;
v_isShared_590_ = v_isSharedCheck_672_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_toSeqRight_587_);
lean_inc(v_toSeqLeft_586_);
lean_inc(v_toSeq_585_);
lean_inc(v_toFunctor_584_);
lean_dec(v_toApplicative_580_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_672_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___f_591_; lean_object* v___f_592_; lean_object* v___f_593_; lean_object* v___f_594_; lean_object* v___x_595_; lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___x_600_; 
v___f_591_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__2));
v___f_592_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__3));
lean_inc_ref(v_toFunctor_584_);
v___f_593_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_593_, 0, v_toFunctor_584_);
v___f_594_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_594_, 0, v_toFunctor_584_);
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v___f_593_);
lean_ctor_set(v___x_595_, 1, v___f_594_);
v___f_596_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_596_, 0, v_toSeqRight_587_);
v___f_597_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_597_, 0, v_toSeqLeft_586_);
v___f_598_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_598_, 0, v_toSeq_585_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 4, v___f_596_);
lean_ctor_set(v___x_589_, 3, v___f_597_);
lean_ctor_set(v___x_589_, 2, v___f_598_);
lean_ctor_set(v___x_589_, 1, v___f_591_);
lean_ctor_set(v___x_589_, 0, v___x_595_);
v___x_600_ = v___x_589_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v___f_591_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v___f_598_);
lean_ctor_set(v_reuseFailAlloc_671_, 3, v___f_597_);
lean_ctor_set(v_reuseFailAlloc_671_, 4, v___f_596_);
v___x_600_ = v_reuseFailAlloc_671_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_602_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 1, v___f_592_);
lean_ctor_set(v___x_582_, 0, v___x_600_);
v___x_602_ = v___x_582_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v___f_592_);
v___x_602_ = v_reuseFailAlloc_670_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; lean_object* v_toApplicative_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_668_; 
v___x_603_ = l_ReaderT_instMonad___redArg(v___x_602_);
v_toApplicative_604_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; 
v_unused_669_ = lean_ctor_get(v___x_603_, 1);
lean_dec(v_unused_669_);
v___x_606_ = v___x_603_;
v_isShared_607_ = v_isSharedCheck_668_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_toApplicative_604_);
lean_dec(v___x_603_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_668_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v_toFunctor_608_; lean_object* v_toSeq_609_; lean_object* v_toSeqLeft_610_; lean_object* v_toSeqRight_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_666_; 
v_toFunctor_608_ = lean_ctor_get(v_toApplicative_604_, 0);
v_toSeq_609_ = lean_ctor_get(v_toApplicative_604_, 2);
v_toSeqLeft_610_ = lean_ctor_get(v_toApplicative_604_, 3);
v_toSeqRight_611_ = lean_ctor_get(v_toApplicative_604_, 4);
v_isSharedCheck_666_ = !lean_is_exclusive(v_toApplicative_604_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; 
v_unused_667_ = lean_ctor_get(v_toApplicative_604_, 1);
lean_dec(v_unused_667_);
v___x_613_ = v_toApplicative_604_;
v_isShared_614_ = v_isSharedCheck_666_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_toSeqRight_611_);
lean_inc(v_toSeqLeft_610_);
lean_inc(v_toSeq_609_);
lean_inc(v_toFunctor_608_);
lean_dec(v_toApplicative_604_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_666_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___f_615_; lean_object* v___f_616_; lean_object* v___f_617_; lean_object* v___f_618_; lean_object* v___x_619_; lean_object* v___f_620_; lean_object* v___f_621_; lean_object* v___f_622_; lean_object* v___x_624_; 
v___f_615_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__4));
v___f_616_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__5));
lean_inc_ref(v_toFunctor_608_);
v___f_617_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_617_, 0, v_toFunctor_608_);
v___f_618_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_618_, 0, v_toFunctor_608_);
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v___f_617_);
lean_ctor_set(v___x_619_, 1, v___f_618_);
v___f_620_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_620_, 0, v_toSeqRight_611_);
v___f_621_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_621_, 0, v_toSeqLeft_610_);
v___f_622_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_622_, 0, v_toSeq_609_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 4, v___f_620_);
lean_ctor_set(v___x_613_, 3, v___f_621_);
lean_ctor_set(v___x_613_, 2, v___f_622_);
lean_ctor_set(v___x_613_, 1, v___f_615_);
lean_ctor_set(v___x_613_, 0, v___x_619_);
v___x_624_ = v___x_613_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___f_615_);
lean_ctor_set(v_reuseFailAlloc_665_, 2, v___f_622_);
lean_ctor_set(v_reuseFailAlloc_665_, 3, v___f_621_);
lean_ctor_set(v_reuseFailAlloc_665_, 4, v___f_620_);
v___x_624_ = v_reuseFailAlloc_665_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_626_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v___f_616_);
lean_ctor_set(v___x_606_, 0, v___x_624_);
v___x_626_ = v___x_606_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___f_616_);
v___x_626_ = v_reuseFailAlloc_664_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_627_; lean_object* v___f_628_; uint8_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_627_ = l_Lean_Meta_instMonadEnvMetaM;
v___f_628_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__10));
v___x_629_ = 1;
v___x_630_ = l_Lean_withoutExporting___redArg(v___x_626_, v___x_627_, v___f_628_, v_x_578_, v___x_629_);
v___x_631_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16));
v___x_632_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
v___x_633_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21);
v___x_634_ = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_run_x27___boxed), 7, 4);
lean_closure_set(v___x_634_, 0, lean_box(0));
lean_closure_set(v___x_634_, 1, v___x_630_);
lean_closure_set(v___x_634_, 2, v___x_632_);
lean_closure_set(v___x_634_, 3, v___x_633_);
v___x_635_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24);
v___x_636_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25);
v___x_637_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28));
v___x_638_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29));
v___x_639_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30);
v___x_640_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31);
v___x_641_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32);
v___x_642_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33);
v___x_643_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_643_, 0, v_env_577_);
lean_ctor_set(v___x_643_, 1, v___x_636_);
lean_ctor_set(v___x_643_, 2, v___x_637_);
lean_ctor_set(v___x_643_, 3, v___x_638_);
lean_ctor_set(v___x_643_, 4, v___x_639_);
lean_ctor_set(v___x_643_, 5, v___x_640_);
lean_ctor_set(v___x_643_, 6, v___x_641_);
lean_ctor_set(v___x_643_, 7, v___x_642_);
lean_ctor_set(v___x_643_, 8, v___x_631_);
v___x_644_ = lean_alloc_closure((void*)(l_Lean_Core_CoreM_run_x27___boxed), 5, 4);
lean_closure_set(v___x_644_, 0, lean_box(0));
lean_closure_set(v___x_644_, 1, v___x_634_);
lean_closure_set(v___x_644_, 2, v___x_635_);
lean_closure_set(v___x_644_, 3, v___x_643_);
v___x_645_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_645_, 0, lean_box(0));
lean_closure_set(v___x_645_, 1, lean_box(0));
lean_closure_set(v___x_645_, 2, v___x_644_);
v___x_646_ = l_unsafeBaseIO___redArg(v___x_645_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___y_653_; lean_object* v___x_656_; lean_object* v___f_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref(v___x_646_);
v___x_648_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34));
v___x_649_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35));
v___x_650_ = lean_unsigned_to_nat(71u);
v___x_651_ = lean_unsigned_to_nat(24u);
v___x_656_ = l_Lean_Exception_toMessageData(v_a_647_);
v___f_657_ = lean_alloc_closure((void*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_657_, 0, v___x_656_);
v___x_658_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_658_, 0, lean_box(0));
lean_closure_set(v___x_658_, 1, lean_box(0));
lean_closure_set(v___x_658_, 2, v___f_657_);
v___x_659_ = l_unsafeBaseIO___redArg(v___x_658_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_661_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref(v___x_659_);
v___x_661_ = lean_io_error_to_string(v_a_660_);
v___y_653_ = v___x_661_;
goto v___jp_652_;
}
else
{
lean_object* v_a_662_; 
v_a_662_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_662_);
lean_dec_ref(v___x_659_);
v___y_653_ = v_a_662_;
goto v___jp_652_;
}
v___jp_652_:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = l_mkPanicMessageWithDecl(v___x_648_, v___x_649_, v___x_650_, v___x_651_, v___y_653_);
lean_dec_ref(v___y_653_);
v___x_655_ = l_panic___redArg(v_inst_576_, v___x_654_);
return v___x_655_;
}
}
else
{
lean_object* v_a_663_; 
lean_dec(v_inst_576_);
v_a_663_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_663_);
lean_dec_ref(v___x_646_);
return v_a_663_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM(lean_object* v_00_u03b1_676_, lean_object* v_inst_677_, lean_object* v_env_678_, lean_object* v_x_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(v_inst_677_, v_env_678_, v_x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0(lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap(v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_697_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_697_ == 0)
{
v___x_689_ = v___x_686_;
v_isShared_690_ = v_isSharedCheck_697_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_686_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_697_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_691_ = lean_unsigned_to_nat(1u);
v___x_692_ = lean_mk_empty_array_with_capacity(v___x_691_);
v___x_693_ = lean_array_push(v___x_692_, v_a_687_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_693_);
v___x_695_ = v___x_689_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
v_a_698_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_686_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_686_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0___boxed(lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0(v___y_706_, v___y_707_, v___y_708_, v___y_709_);
return v_res_711_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1(void){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Array_instInhabited(lean_box(0));
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3(lean_object* v_env_714_){
_start:
{
lean_object* v___f_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___f_715_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__0));
v___x_716_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1);
v___x_717_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(v___x_716_, v_env_714_, v___f_715_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_(lean_object* v_mapss_718_, lean_object* v_x_719_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v_mapss_718_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed(lean_object* v_mapss_722_, lean_object* v_x_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_(v_mapss_722_, v_x_723_);
lean_dec_ref(v_x_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_(lean_object* v_a_726_, uint8_t v_a_727_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed(lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
uint8_t v_a_166__boxed_730_; lean_object* v_res_731_; 
v_a_166__boxed_730_ = lean_unbox(v_a_729_);
v_res_731_ = l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_(v_a_728_, v_a_166__boxed_730_);
lean_dec_ref(v_a_728_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_(lean_object* v_env_732_, lean_object* v_x_733_, uint8_t v_x_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3(v_env_732_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed(lean_object* v_env_736_, lean_object* v_x_737_, lean_object* v_x_738_){
_start:
{
uint8_t v_x_172__boxed_739_; lean_object* v_res_740_; 
v_x_172__boxed_739_ = lean_unbox(v_x_738_);
v_res_740_ = l_Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_(v_env_736_, v_x_737_, v_x_172__boxed_739_);
lean_dec_ref(v_x_737_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_(lean_object* v_x_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___lam__3___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_));
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed(lean_object* v_x_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_(v_x_746_);
lean_dec_ref(v_x_746_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_(lean_object* v_x_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___lam__4___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_));
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed(lean_object* v_x_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_(v_x_752_);
lean_dec_ref(v_x_752_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_(lean_object* v___x_754_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed(lean_object* v___x_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_(v___x_757_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_));
v___x_785_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2____boxed(lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_();
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_789_ = lean_box(0);
v___x_790_ = lean_st_mk_ref(v___x_789_);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2____boxed(lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2_();
return v_res_793_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instZeroNameMapNat(void){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = lean_box(1);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0(lean_object* v___x_795_, lean_object* v_x_x27_796_, lean_object* v_n_797_, lean_object* v_c_798_){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_799_ = lean_unsigned_to_nat(0u);
lean_inc(v_n_797_);
lean_inc(v_x_x27_796_);
v___x_800_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v___x_795_, v_x_x27_796_, v_n_797_, v___x_799_);
v___x_801_ = lean_nat_add(v___x_800_, v_c_798_);
lean_dec(v___x_800_);
v___x_802_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_797_, v___x_801_, v_x_x27_796_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0___boxed(lean_object* v___x_803_, lean_object* v_x_x27_804_, lean_object* v_n_805_, lean_object* v_c_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0(v___x_803_, v_x_x27_804_, v_n_805_, v_c_806_);
lean_dec(v_c_806_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1(lean_object* v_x_811_, lean_object* v_y_812_){
_start:
{
lean_object* v___f_813_; lean_object* v___x_814_; 
v___f_813_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__1));
v___x_814_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_813_, v_x_811_, v_y_812_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(lean_object* v_init_817_, lean_object* v_x_818_){
_start:
{
if (lean_obj_tag(v_x_818_) == 0)
{
lean_object* v_k_819_; lean_object* v_v_820_; lean_object* v_l_821_; lean_object* v_r_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_k_819_ = lean_ctor_get(v_x_818_, 1);
lean_inc(v_k_819_);
v_v_820_ = lean_ctor_get(v_x_818_, 2);
lean_inc(v_v_820_);
v_l_821_ = lean_ctor_get(v_x_818_, 3);
lean_inc(v_l_821_);
v_r_822_ = lean_ctor_get(v_x_818_, 4);
lean_inc(v_r_822_);
lean_dec_ref(v_x_818_);
v___x_823_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(v_init_817_, v_l_821_);
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v___x_823_, v_k_819_, v___x_824_);
v___x_826_ = lean_nat_add(v___x_825_, v_v_820_);
lean_dec(v_v_820_);
lean_dec(v___x_825_);
v___x_827_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_819_, v___x_826_, v___x_823_);
v_init_817_ = v___x_827_;
v_x_818_ = v_r_822_;
goto _start;
}
else
{
return v_init_817_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(lean_object* v_as_829_, size_t v_i_830_, size_t v_stop_831_, lean_object* v_b_832_){
_start:
{
uint8_t v___x_833_; 
v___x_833_ = lean_usize_dec_eq(v_i_830_, v_stop_831_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; size_t v___x_836_; size_t v___x_837_; 
v___x_834_ = lean_array_uget_borrowed(v_as_829_, v_i_830_);
lean_inc(v___x_834_);
v___x_835_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(v_b_832_, v___x_834_);
v___x_836_ = ((size_t)1ULL);
v___x_837_ = lean_usize_add(v_i_830_, v___x_836_);
v_i_830_ = v___x_837_;
v_b_832_ = v___x_835_;
goto _start;
}
else
{
return v_b_832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___boxed(lean_object* v_as_839_, lean_object* v_i_840_, lean_object* v_stop_841_, lean_object* v_b_842_){
_start:
{
size_t v_i_boxed_843_; size_t v_stop_boxed_844_; lean_object* v_res_845_; 
v_i_boxed_843_ = lean_unbox_usize(v_i_840_);
lean_dec(v_i_840_);
v_stop_boxed_844_ = lean_unbox_usize(v_stop_841_);
lean_dec(v_stop_841_);
v_res_845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(v_as_839_, v_i_boxed_843_, v_stop_boxed_844_, v_b_842_);
lean_dec_ref(v_as_839_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(lean_object* v_as_846_, size_t v_i_847_, size_t v_stop_848_, lean_object* v_b_849_){
_start:
{
lean_object* v___y_851_; uint8_t v___x_855_; 
v___x_855_ = lean_usize_dec_eq(v_i_847_, v_stop_848_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_856_ = lean_array_uget_borrowed(v_as_846_, v_i_847_);
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_array_get_size(v___x_856_);
v___x_859_ = lean_nat_dec_lt(v___x_857_, v___x_858_);
if (v___x_859_ == 0)
{
v___y_851_ = v_b_849_;
goto v___jp_850_;
}
else
{
uint8_t v___x_860_; 
v___x_860_ = lean_nat_dec_le(v___x_858_, v___x_858_);
if (v___x_860_ == 0)
{
if (v___x_859_ == 0)
{
v___y_851_ = v_b_849_;
goto v___jp_850_;
}
else
{
size_t v___x_861_; size_t v___x_862_; lean_object* v___x_863_; 
v___x_861_ = ((size_t)0ULL);
v___x_862_ = lean_usize_of_nat(v___x_858_);
v___x_863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(v___x_856_, v___x_861_, v___x_862_, v_b_849_);
v___y_851_ = v___x_863_;
goto v___jp_850_;
}
}
else
{
size_t v___x_864_; size_t v___x_865_; lean_object* v___x_866_; 
v___x_864_ = ((size_t)0ULL);
v___x_865_ = lean_usize_of_nat(v___x_858_);
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(v___x_856_, v___x_864_, v___x_865_, v_b_849_);
v___y_851_ = v___x_866_;
goto v___jp_850_;
}
}
}
else
{
return v_b_849_;
}
v___jp_850_:
{
size_t v___x_852_; size_t v___x_853_; 
v___x_852_ = ((size_t)1ULL);
v___x_853_ = lean_usize_add(v_i_847_, v___x_852_);
v_i_847_ = v___x_853_;
v_b_849_ = v___y_851_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2___boxed(lean_object* v_as_867_, lean_object* v_i_868_, lean_object* v_stop_869_, lean_object* v_b_870_){
_start:
{
size_t v_i_boxed_871_; size_t v_stop_boxed_872_; lean_object* v_res_873_; 
v_i_boxed_871_ = lean_unbox_usize(v_i_868_);
lean_dec(v_i_868_);
v_stop_boxed_872_ = lean_unbox_usize(v_stop_869_);
lean_dec(v_stop_869_);
v_res_873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(v_as_867_, v_i_boxed_871_, v_stop_boxed_872_, v_b_870_);
lean_dec_ref(v_as_867_);
return v_res_873_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0(void){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Array_instInhabited(lean_box(0));
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(lean_object* v_a_875_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyMapRef;
v___x_878_ = lean_st_ref_get(v___x_877_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v___x_879_; lean_object* v___y_881_; lean_object* v_env_885_; lean_object* v___x_886_; lean_object* v_toEnvExtension_887_; lean_object* v_asyncMode_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_879_ = lean_st_ref_get(v_a_875_);
v_env_885_ = lean_ctor_get(v___x_879_, 0);
lean_inc_ref(v_env_885_);
lean_dec(v___x_879_);
v___x_886_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt;
v_toEnvExtension_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc_ref(v_toEnvExtension_887_);
v_asyncMode_888_ = lean_ctor_get(v_toEnvExtension_887_, 2);
lean_inc(v_asyncMode_888_);
lean_dec_ref(v_toEnvExtension_887_);
v___x_889_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0, &l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0);
v___x_890_ = lean_box(0);
v___x_891_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_889_, v___x_886_, v_env_885_, v_asyncMode_888_, v___x_890_);
lean_dec(v_asyncMode_888_);
v___x_892_ = lean_box(1);
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = lean_array_get_size(v___x_891_);
v___x_895_ = lean_nat_dec_lt(v___x_893_, v___x_894_);
if (v___x_895_ == 0)
{
lean_dec(v___x_891_);
v___y_881_ = v___x_892_;
goto v___jp_880_;
}
else
{
uint8_t v___x_896_; 
v___x_896_ = lean_nat_dec_le(v___x_894_, v___x_894_);
if (v___x_896_ == 0)
{
if (v___x_895_ == 0)
{
lean_dec(v___x_891_);
v___y_881_ = v___x_892_;
goto v___jp_880_;
}
else
{
size_t v___x_897_; size_t v___x_898_; lean_object* v___x_899_; 
v___x_897_ = ((size_t)0ULL);
v___x_898_ = lean_usize_of_nat(v___x_894_);
v___x_899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(v___x_891_, v___x_897_, v___x_898_, v___x_892_);
lean_dec(v___x_891_);
v___y_881_ = v___x_899_;
goto v___jp_880_;
}
}
else
{
size_t v___x_900_; size_t v___x_901_; lean_object* v___x_902_; 
v___x_900_ = ((size_t)0ULL);
v___x_901_ = lean_usize_of_nat(v___x_894_);
v___x_902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(v___x_891_, v___x_900_, v___x_901_, v___x_892_);
lean_dec(v___x_891_);
v___y_881_ = v___x_902_;
goto v___jp_880_;
}
}
v___jp_880_:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
lean_inc(v___y_881_);
v___x_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_882_, 0, v___y_881_);
v___x_883_ = lean_st_ref_set(v___x_877_, v___x_882_);
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v___y_881_);
return v___x_884_;
}
}
else
{
lean_object* v_val_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
v_val_903_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_878_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_val_903_);
lean_dec(v___x_878_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
lean_ctor_set_tag(v___x_905_, 0);
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_val_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___boxed(lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(v_a_911_);
lean_dec(v_a_911_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap(lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(v_a_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___boxed(lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_LibrarySuggestions_symbolFrequencyMap(v_a_918_, v_a_919_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0(lean_object* v_init_922_, lean_object* v_t_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(v_init_922_, v_t_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency___redArg(lean_object* v_n_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_928_; lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_938_; 
v___x_928_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(v_a_926_);
v_a_929_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_938_ == 0)
{
v___x_931_ = v___x_928_;
v_isShared_932_ = v_isSharedCheck_938_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_928_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_938_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_a_929_, v_n_925_, v___x_933_);
lean_dec(v_a_929_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_934_);
v___x_936_ = v___x_931_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency___redArg___boxed(lean_object* v_n_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_LibrarySuggestions_symbolFrequency___redArg(v_n_939_, v_a_940_);
lean_dec(v_a_940_);
lean_dec(v_n_939_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency(lean_object* v_n_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_LibrarySuggestions_symbolFrequency___redArg(v_n_943_, v_a_945_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency___boxed(lean_object* v_n_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_LibrarySuggestions_symbolFrequency(v_n_948_, v_a_949_, v_a_950_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_n_948_);
return v_res_952_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_LibrarySuggestions_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_LibrarySuggestions_SymbolFrequency(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LibrarySuggestions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_localSymbolFrequencyMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_localSymbolFrequencyMapRef);
lean_dec_ref(res);
res = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_277729666____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt);
lean_dec_ref(res);
res = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyMapRef);
lean_dec_ref(res);
l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instZeroNameMapNat = _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instZeroNameMapNat();
lean_mark_persistent(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instZeroNameMapNat);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_LibrarySuggestions_SymbolFrequency(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_LibrarySuggestions_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_LibrarySuggestions_SymbolFrequency(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LibrarySuggestions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
}
#ifdef __cplusplus
}
#endif
