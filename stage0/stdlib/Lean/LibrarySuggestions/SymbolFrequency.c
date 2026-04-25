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
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
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
lean_object* l_instMonadFinallyEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadFinallyStateRefT_x27___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_tryFinally___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withoutExporting___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_MetaM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadFinallyEIO___aux__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__6 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__6_value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadFinallyStateRefT_x27___aux__1___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__6_value)} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__7 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__7_value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_tryFinally___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__7_value)} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__8 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__8_value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadFinallyStateRefT_x27___aux__1___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__8_value)} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__9 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__9_value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_tryFinally___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__10 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__10_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18;
static const lean_array_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24;
static const lean_string_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "symbolFrequency"};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27;
static const lean_string_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35;
static const lean_string_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.LibrarySuggestions.SymbolFrequency"};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__36 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__36_value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "_private.Lean.LibrarySuggestions.SymbolFrequency.0.Lean.Environment.unsafeRunMetaM"};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__37 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__37_value;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__0 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__0_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3(lean_object*);
static const lean_array_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "symbol frequency extension"};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(10, 33, 51, 182, 202, 68, 104, 66)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2____boxed(lean_object*);
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
v___x_37_ = lean_unsigned_to_nat(1u);
lean_inc(v_val_36_);
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
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
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
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
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
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec_ref(v_as_206_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg___boxed(lean_object* v_f_218_, lean_object* v_x_219_, lean_object* v_x_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_218_, v_x_219_, v_x_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap(lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v___x_233_; lean_object* v_env_234_; lean_object* v___x_235_; lean_object* v_map_u2082_236_; lean_object* v___f_237_; lean_object* v___f_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_233_ = lean_st_ref_get(v_a_231_);
v_env_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc_ref_n(v_env_234_, 2);
lean_dec(v___x_233_);
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
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
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
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
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
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
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
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
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
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
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
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec_ref(v_vals_365_);
lean_dec_ref(v_keys_364_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2_(){
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
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2____boxed(lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2_();
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
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
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
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
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
v___x_476_ = l_instMonadEIO(lean_box(0));
return v___x_476_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0);
v___x_478_ = l_StateRefT_x27_instMonad___redArg(v___x_477_);
return v___x_478_;
}
}
static uint64_t _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12(void){
_start:
{
lean_object* v___x_498_; uint64_t v___x_499_; 
v___x_498_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11));
v___x_499_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13(void){
_start:
{
uint64_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = lean_uint64_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12);
v___x_501_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11));
v___x_502_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_502_, 0, v___x_501_);
lean_ctor_set_uint64(v___x_502_, sizeof(void*)*1, v___x_500_);
return v___x_502_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14(void){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_503_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = lean_unsigned_to_nat(32u);
v___x_507_ = lean_mk_empty_array_with_capacity(v___x_506_);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17(void){
_start:
{
size_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_509_ = ((size_t)5ULL);
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = lean_unsigned_to_nat(32u);
v___x_512_ = lean_mk_empty_array_with_capacity(v___x_511_);
v___x_513_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16);
v___x_514_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_514_, 0, v___x_513_);
lean_ctor_set(v___x_514_, 1, v___x_512_);
lean_ctor_set(v___x_514_, 2, v___x_510_);
lean_ctor_set(v___x_514_, 3, v___x_510_);
lean_ctor_set_usize(v___x_514_, 4, v___x_509_);
return v___x_514_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_515_ = lean_box(1);
v___x_516_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
v___x_517_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
v___x_518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
lean_ctor_set(v___x_518_, 1, v___x_516_);
lean_ctor_set(v___x_518_, 2, v___x_515_);
return v___x_518_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20(void){
_start:
{
uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_521_ = 1;
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lean_box(0);
v___x_524_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19));
v___x_525_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18);
v___x_526_ = lean_box(1);
v___x_527_ = 0;
v___x_528_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13);
v___x_529_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v___x_526_);
lean_ctor_set(v___x_529_, 2, v___x_525_);
lean_ctor_set(v___x_529_, 3, v___x_524_);
lean_ctor_set(v___x_529_, 4, v___x_523_);
lean_ctor_set(v___x_529_, 5, v___x_522_);
lean_ctor_set(v___x_529_, 6, v___x_523_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*7, v___x_527_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*7 + 1, v___x_527_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*7 + 2, v___x_527_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*7 + 3, v___x_521_);
return v___x_529_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
lean_ctor_set(v___x_532_, 2, v___x_531_);
lean_ctor_set(v___x_532_, 3, v___x_531_);
lean_ctor_set(v___x_532_, 4, v___x_530_);
lean_ctor_set(v___x_532_, 5, v___x_530_);
lean_ctor_set(v___x_532_, 6, v___x_530_);
lean_ctor_set(v___x_532_, 7, v___x_530_);
lean_ctor_set(v___x_532_, 8, v___x_530_);
lean_ctor_set(v___x_532_, 9, v___x_530_);
return v___x_532_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
v___x_534_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
lean_ctor_set(v___x_534_, 2, v___x_533_);
lean_ctor_set(v___x_534_, 3, v___x_533_);
lean_ctor_set(v___x_534_, 4, v___x_533_);
lean_ctor_set(v___x_534_, 5, v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
v___x_536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
lean_ctor_set(v___x_536_, 2, v___x_535_);
lean_ctor_set(v___x_536_, 3, v___x_535_);
lean_ctor_set(v___x_536_, 4, v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_537_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23);
v___x_538_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
v___x_539_ = lean_box(1);
v___x_540_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22);
v___x_541_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21);
v___x_542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v___x_540_);
lean_ctor_set(v___x_542_, 2, v___x_539_);
lean_ctor_set(v___x_542_, 3, v___x_538_);
lean_ctor_set(v___x_542_, 4, v___x_537_);
return v___x_542_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_544_ = lean_obj_once(&l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2, &l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2_once, _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2);
v___x_545_ = lean_box(0);
v___x_546_ = 0;
v___x_547_ = l_Lean_firstFrontendMacroScope;
v___x_548_ = lean_box(0);
v___x_549_ = lean_box(0);
v___x_550_ = lean_box(0);
v___x_551_ = lean_unsigned_to_nat(1000u);
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = l_Lean_Options_empty;
v___x_554_ = l_Lean_instInhabitedFileMap_default;
v___x_555_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25));
v___x_556_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set(v___x_556_, 1, v___x_554_);
lean_ctor_set(v___x_556_, 2, v___x_553_);
lean_ctor_set(v___x_556_, 3, v___x_552_);
lean_ctor_set(v___x_556_, 4, v___x_551_);
lean_ctor_set(v___x_556_, 5, v___x_550_);
lean_ctor_set(v___x_556_, 6, v___x_549_);
lean_ctor_set(v___x_556_, 7, v___x_548_);
lean_ctor_set(v___x_556_, 8, v___x_552_);
lean_ctor_set(v___x_556_, 9, v___x_552_);
lean_ctor_set(v___x_556_, 10, v___x_549_);
lean_ctor_set(v___x_556_, 11, v___x_547_);
lean_ctor_set(v___x_556_, 12, v___x_545_);
lean_ctor_set(v___x_556_, 13, v___x_544_);
lean_ctor_set_uint8(v___x_556_, sizeof(void*)*14, v___x_546_);
lean_ctor_set_uint8(v___x_556_, sizeof(void*)*14 + 1, v___x_546_);
return v___x_556_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = l_Lean_firstFrontendMacroScope;
v___x_559_ = lean_nat_add(v___x_558_, v___x_557_);
return v___x_559_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32(void){
_start:
{
lean_object* v___x_570_; uint64_t v___x_571_; lean_object* v___x_572_; 
v___x_570_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
v___x_571_ = 0ULL;
v___x_572_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set_uint64(v___x_572_, sizeof(void*)*1, v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = l_Lean_NameSet_empty;
v___x_576_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
v___x_577_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
lean_ctor_set(v___x_577_, 2, v___x_575_);
return v___x_577_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; lean_object* v___x_581_; 
v___x_578_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
v___x_579_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
v___x_580_ = 1;
v___x_581_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_579_);
lean_ctor_set(v___x_581_, 2, v___x_578_);
lean_ctor_set_uint8(v___x_581_, sizeof(void*)*3, v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(lean_object* v_inst_584_, lean_object* v_env_585_, lean_object* v_x_586_){
_start:
{
lean_object* v___x_587_; lean_object* v_toApplicative_588_; lean_object* v_toFunctor_589_; lean_object* v_toSeq_590_; lean_object* v_toSeqLeft_591_; lean_object* v_toSeqRight_592_; lean_object* v___f_593_; lean_object* v___f_594_; lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___x_597_; lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___f_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v_toApplicative_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_668_; 
v___x_587_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1);
v_toApplicative_588_ = lean_ctor_get(v___x_587_, 0);
v_toFunctor_589_ = lean_ctor_get(v_toApplicative_588_, 0);
v_toSeq_590_ = lean_ctor_get(v_toApplicative_588_, 2);
v_toSeqLeft_591_ = lean_ctor_get(v_toApplicative_588_, 3);
v_toSeqRight_592_ = lean_ctor_get(v_toApplicative_588_, 4);
v___f_593_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__2));
v___f_594_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_589_, 2);
v___f_595_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_595_, 0, v_toFunctor_589_);
v___f_596_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_596_, 0, v_toFunctor_589_);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v___f_595_);
lean_ctor_set(v___x_597_, 1, v___f_596_);
lean_inc(v_toSeqRight_592_);
v___f_598_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_598_, 0, v_toSeqRight_592_);
lean_inc(v_toSeqLeft_591_);
v___f_599_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_599_, 0, v_toSeqLeft_591_);
lean_inc(v_toSeq_590_);
v___f_600_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_600_, 0, v_toSeq_590_);
v___x_601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_601_, 0, v___x_597_);
lean_ctor_set(v___x_601_, 1, v___f_593_);
lean_ctor_set(v___x_601_, 2, v___f_600_);
lean_ctor_set(v___x_601_, 3, v___f_599_);
lean_ctor_set(v___x_601_, 4, v___f_598_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___f_594_);
v___x_603_ = l_StateRefT_x27_instMonad___redArg(v___x_602_);
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
v___x_630_ = l_Lean_withoutExporting___redArg(v___x_626_, v___x_627_, v___f_628_, v_x_586_, v___x_629_);
v___x_631_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19));
v___x_632_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20);
v___x_633_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24);
v___x_634_ = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_run_x27___boxed), 7, 4);
lean_closure_set(v___x_634_, 0, lean_box(0));
lean_closure_set(v___x_634_, 1, v___x_630_);
lean_closure_set(v___x_634_, 2, v___x_632_);
lean_closure_set(v___x_634_, 3, v___x_633_);
v___x_635_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26);
v___x_636_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27);
v___x_637_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30));
v___x_638_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31));
v___x_639_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32);
v___x_640_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33);
v___x_641_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34);
v___x_642_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35);
v___x_643_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_643_, 0, v_env_585_);
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
v___x_648_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__36));
v___x_649_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__37));
v___x_650_ = lean_unsigned_to_nat(75u);
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
v___x_655_ = l_panic___redArg(v_inst_584_, v___x_654_);
return v___x_655_;
}
}
else
{
lean_object* v_a_663_; 
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
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___boxed(lean_object* v_inst_670_, lean_object* v_env_671_, lean_object* v_x_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(v_inst_670_, v_env_671_, v_x_672_);
lean_dec(v_inst_670_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM(lean_object* v_00_u03b1_674_, lean_object* v_inst_675_, lean_object* v_env_676_, lean_object* v_x_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(v_inst_675_, v_env_676_, v_x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___boxed(lean_object* v_00_u03b1_679_, lean_object* v_inst_680_, lean_object* v_env_681_, lean_object* v_x_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM(v_00_u03b1_679_, v_inst_680_, v_env_681_, v_x_682_);
lean_dec(v_inst_680_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0(lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap(v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_700_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_700_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_700_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_700_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = lean_mk_empty_array_with_capacity(v___x_694_);
v___x_696_ = lean_array_push(v___x_695_, v_a_690_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_696_);
v___x_698_ = v___x_692_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
v_a_701_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_689_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_689_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0___boxed(lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0(v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
return v_res_714_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1(void){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Array_instInhabited(lean_box(0));
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3(lean_object* v_env_717_){
_start:
{
lean_object* v___f_718_; lean_object* v___x_719_; lean_object* v_ents_720_; lean_object* v___x_721_; 
v___f_718_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__0));
v___x_719_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1);
v_ents_720_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(v___x_719_, v_env_717_, v___f_718_);
lean_inc_n(v_ents_720_, 2);
v___x_721_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_721_, 0, v_ents_720_);
lean_ctor_set(v___x_721_, 1, v_ents_720_);
lean_ctor_set(v___x_721_, 2, v_ents_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object* v_x_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_));
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object* v_x_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v_x_726_);
lean_dec_ref(v_x_726_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object* v_x_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_));
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object* v_x_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v_x_733_);
lean_dec_ref(v_x_733_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object* v_env_735_, lean_object* v_x_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3(v_env_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object* v_env_738_, lean_object* v_x_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v_env_738_, v_x_739_);
lean_dec_ref(v_x_739_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object* v_a_741_, uint8_t v_a_742_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
uint8_t v_a_110__boxed_745_; lean_object* v_res_746_; 
v_a_110__boxed_745_ = lean_unbox(v_a_744_);
v_res_746_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v_a_743_, v_a_110__boxed_745_);
lean_dec_ref(v_a_743_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object* v_mapss_747_, lean_object* v_x_748_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v_mapss_747_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object* v_mapss_751_, lean_object* v_x_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v_mapss_751_, v_x_752_);
lean_dec_ref(v_x_752_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object* v___x_755_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object* v___x_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v___x_758_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_));
v___x_786_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_();
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_790_ = lean_box(0);
v___x_791_ = lean_st_mk_ref(v___x_790_);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2____boxed(lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2_();
return v_res_794_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instZeroNameMapNat(void){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = lean_box(1);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0(lean_object* v___x_796_, lean_object* v_x_x27_797_, lean_object* v_n_798_, lean_object* v_c_799_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_800_ = lean_unsigned_to_nat(0u);
lean_inc(v_n_798_);
lean_inc(v_x_x27_797_);
v___x_801_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v___x_796_, v_x_x27_797_, v_n_798_, v___x_800_);
v___x_802_ = lean_nat_add(v___x_801_, v_c_799_);
lean_dec(v___x_801_);
v___x_803_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_798_, v___x_802_, v_x_x27_797_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0___boxed(lean_object* v___x_804_, lean_object* v_x_x27_805_, lean_object* v_n_806_, lean_object* v_c_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0(v___x_804_, v_x_x27_805_, v_n_806_, v_c_807_);
lean_dec(v_c_807_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1(lean_object* v_x_812_, lean_object* v_y_813_){
_start:
{
lean_object* v___f_814_; lean_object* v___x_815_; 
v___f_814_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__1));
v___x_815_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_814_, v_x_812_, v_y_813_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(lean_object* v_init_818_, lean_object* v_x_819_){
_start:
{
if (lean_obj_tag(v_x_819_) == 0)
{
lean_object* v_k_820_; lean_object* v_v_821_; lean_object* v_l_822_; lean_object* v_r_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_k_820_ = lean_ctor_get(v_x_819_, 1);
lean_inc(v_k_820_);
v_v_821_ = lean_ctor_get(v_x_819_, 2);
lean_inc(v_v_821_);
v_l_822_ = lean_ctor_get(v_x_819_, 3);
lean_inc(v_l_822_);
v_r_823_ = lean_ctor_get(v_x_819_, 4);
lean_inc(v_r_823_);
lean_dec_ref(v_x_819_);
v___x_824_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(v_init_818_, v_l_822_);
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v___x_824_, v_k_820_, v___x_825_);
v___x_827_ = lean_nat_add(v___x_826_, v_v_821_);
lean_dec(v_v_821_);
lean_dec(v___x_826_);
v___x_828_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_820_, v___x_827_, v___x_824_);
v_init_818_ = v___x_828_;
v_x_819_ = v_r_823_;
goto _start;
}
else
{
return v_init_818_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(lean_object* v_as_830_, size_t v_i_831_, size_t v_stop_832_, lean_object* v_b_833_){
_start:
{
uint8_t v___x_834_; 
v___x_834_ = lean_usize_dec_eq(v_i_831_, v_stop_832_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; size_t v___x_837_; size_t v___x_838_; 
v___x_835_ = lean_array_uget_borrowed(v_as_830_, v_i_831_);
lean_inc(v___x_835_);
v___x_836_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(v_b_833_, v___x_835_);
v___x_837_ = ((size_t)1ULL);
v___x_838_ = lean_usize_add(v_i_831_, v___x_837_);
v_i_831_ = v___x_838_;
v_b_833_ = v___x_836_;
goto _start;
}
else
{
return v_b_833_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___boxed(lean_object* v_as_840_, lean_object* v_i_841_, lean_object* v_stop_842_, lean_object* v_b_843_){
_start:
{
size_t v_i_boxed_844_; size_t v_stop_boxed_845_; lean_object* v_res_846_; 
v_i_boxed_844_ = lean_unbox_usize(v_i_841_);
lean_dec(v_i_841_);
v_stop_boxed_845_ = lean_unbox_usize(v_stop_842_);
lean_dec(v_stop_842_);
v_res_846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(v_as_840_, v_i_boxed_844_, v_stop_boxed_845_, v_b_843_);
lean_dec_ref(v_as_840_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(lean_object* v_as_847_, size_t v_i_848_, size_t v_stop_849_, lean_object* v_b_850_){
_start:
{
lean_object* v___y_852_; uint8_t v___x_856_; 
v___x_856_ = lean_usize_dec_eq(v_i_848_, v_stop_849_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_857_ = lean_array_uget_borrowed(v_as_847_, v_i_848_);
v___x_858_ = lean_unsigned_to_nat(0u);
v___x_859_ = lean_array_get_size(v___x_857_);
v___x_860_ = lean_nat_dec_lt(v___x_858_, v___x_859_);
if (v___x_860_ == 0)
{
v___y_852_ = v_b_850_;
goto v___jp_851_;
}
else
{
uint8_t v___x_861_; 
v___x_861_ = lean_nat_dec_le(v___x_859_, v___x_859_);
if (v___x_861_ == 0)
{
if (v___x_860_ == 0)
{
v___y_852_ = v_b_850_;
goto v___jp_851_;
}
else
{
size_t v___x_862_; size_t v___x_863_; lean_object* v___x_864_; 
v___x_862_ = ((size_t)0ULL);
v___x_863_ = lean_usize_of_nat(v___x_859_);
v___x_864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(v___x_857_, v___x_862_, v___x_863_, v_b_850_);
v___y_852_ = v___x_864_;
goto v___jp_851_;
}
}
else
{
size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; 
v___x_865_ = ((size_t)0ULL);
v___x_866_ = lean_usize_of_nat(v___x_859_);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(v___x_857_, v___x_865_, v___x_866_, v_b_850_);
v___y_852_ = v___x_867_;
goto v___jp_851_;
}
}
}
else
{
return v_b_850_;
}
v___jp_851_:
{
size_t v___x_853_; size_t v___x_854_; 
v___x_853_ = ((size_t)1ULL);
v___x_854_ = lean_usize_add(v_i_848_, v___x_853_);
v_i_848_ = v___x_854_;
v_b_850_ = v___y_852_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2___boxed(lean_object* v_as_868_, lean_object* v_i_869_, lean_object* v_stop_870_, lean_object* v_b_871_){
_start:
{
size_t v_i_boxed_872_; size_t v_stop_boxed_873_; lean_object* v_res_874_; 
v_i_boxed_872_ = lean_unbox_usize(v_i_869_);
lean_dec(v_i_869_);
v_stop_boxed_873_ = lean_unbox_usize(v_stop_870_);
lean_dec(v_stop_870_);
v_res_874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(v_as_868_, v_i_boxed_872_, v_stop_boxed_873_, v_b_871_);
lean_dec_ref(v_as_868_);
return v_res_874_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0(void){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Array_instInhabited(lean_box(0));
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(lean_object* v_a_876_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyMapRef;
v___x_879_ = lean_st_ref_get(v___x_878_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v___x_880_; lean_object* v___y_882_; lean_object* v_env_886_; lean_object* v___x_887_; lean_object* v_toEnvExtension_888_; lean_object* v_asyncMode_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_880_ = lean_st_ref_get(v_a_876_);
v_env_886_ = lean_ctor_get(v___x_880_, 0);
lean_inc_ref(v_env_886_);
lean_dec(v___x_880_);
v___x_887_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt;
v_toEnvExtension_888_ = lean_ctor_get(v___x_887_, 0);
v_asyncMode_889_ = lean_ctor_get(v_toEnvExtension_888_, 2);
v___x_890_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0, &l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0);
v___x_891_ = lean_box(0);
v___x_892_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_890_, v___x_887_, v_env_886_, v_asyncMode_889_, v___x_891_);
v___x_893_ = lean_box(1);
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = lean_array_get_size(v___x_892_);
v___x_896_ = lean_nat_dec_lt(v___x_894_, v___x_895_);
if (v___x_896_ == 0)
{
lean_dec(v___x_892_);
v___y_882_ = v___x_893_;
goto v___jp_881_;
}
else
{
uint8_t v___x_897_; 
v___x_897_ = lean_nat_dec_le(v___x_895_, v___x_895_);
if (v___x_897_ == 0)
{
if (v___x_896_ == 0)
{
lean_dec(v___x_892_);
v___y_882_ = v___x_893_;
goto v___jp_881_;
}
else
{
size_t v___x_898_; size_t v___x_899_; lean_object* v___x_900_; 
v___x_898_ = ((size_t)0ULL);
v___x_899_ = lean_usize_of_nat(v___x_895_);
v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(v___x_892_, v___x_898_, v___x_899_, v___x_893_);
lean_dec(v___x_892_);
v___y_882_ = v___x_900_;
goto v___jp_881_;
}
}
else
{
size_t v___x_901_; size_t v___x_902_; lean_object* v___x_903_; 
v___x_901_ = ((size_t)0ULL);
v___x_902_ = lean_usize_of_nat(v___x_895_);
v___x_903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(v___x_892_, v___x_901_, v___x_902_, v___x_893_);
lean_dec(v___x_892_);
v___y_882_ = v___x_903_;
goto v___jp_881_;
}
}
v___jp_881_:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
lean_inc(v___y_882_);
v___x_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_883_, 0, v___y_882_);
v___x_884_ = lean_st_ref_set(v___x_878_, v___x_883_);
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v___y_882_);
return v___x_885_;
}
}
else
{
lean_object* v_val_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
v_val_904_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_879_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_val_904_);
lean_dec(v___x_879_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
lean_ctor_set_tag(v___x_906_, 0);
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_val_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___boxed(lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(v_a_912_);
lean_dec(v_a_912_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap(lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(v_a_916_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___boxed(lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_LibrarySuggestions_symbolFrequencyMap(v_a_919_, v_a_920_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0(lean_object* v_init_923_, lean_object* v_t_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(v_init_923_, v_t_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency___redArg(lean_object* v_n_926_, lean_object* v_a_927_){
_start:
{
lean_object* v___x_929_; lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_939_; 
v___x_929_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(v_a_927_);
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_939_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_939_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_939_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_934_ = lean_unsigned_to_nat(0u);
v___x_935_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_a_930_, v_n_926_, v___x_934_);
lean_dec(v_a_930_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_935_);
v___x_937_ = v___x_932_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency___redArg___boxed(lean_object* v_n_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_LibrarySuggestions_symbolFrequency___redArg(v_n_940_, v_a_941_);
lean_dec(v_a_941_);
lean_dec(v_n_940_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency(lean_object* v_n_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_LibrarySuggestions_symbolFrequency___redArg(v_n_944_, v_a_946_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency___boxed(lean_object* v_n_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_LibrarySuggestions_symbolFrequency(v_n_949_, v_a_950_, v_a_951_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_n_949_);
return v_res_953_;
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
res = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_localSymbolFrequencyMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_localSymbolFrequencyMapRef);
lean_dec_ref(res);
res = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt);
lean_dec_ref(res);
res = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2_();
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
