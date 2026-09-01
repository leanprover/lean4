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
extern lean_object* l_Lean_Options_empty;
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LibrarySuggestions_isDeniedPremise(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_wasOriginallyTheorem(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28;
static const lean_string_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__36;
static const lean_string_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.LibrarySuggestions.SymbolFrequency"};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__37 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__37_value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "_private.Lean.LibrarySuggestions.SymbolFrequency.0.Lean.Environment.unsafeRunMetaM"};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__38 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__38_value;
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
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(10, 33, 51, 182, 202, 68, 104, 66)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value;
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
lean_dec_ref_known(v___x_26_, 1);
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
lean_dec_ref_known(v___x_130_, 1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(lean_object* v_f_146_, lean_object* v_as_147_, size_t v_i_148_, size_t v_stop_149_, lean_object* v_b_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_a_157_; lean_object* v___y_162_; uint8_t v___x_164_; 
v___x_164_ = lean_usize_dec_eq(v_i_148_, v_stop_149_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; 
v___x_165_ = lean_array_uget_borrowed(v_as_147_, v_i_148_);
switch(lean_obj_tag(v___x_165_))
{
case 0:
{
lean_object* v_key_166_; lean_object* v_val_167_; lean_object* v___x_168_; 
v_key_166_ = lean_ctor_get(v___x_165_, 0);
v_val_167_ = lean_ctor_get(v___x_165_, 1);
lean_inc_ref(v_f_146_);
lean_inc(v___y_154_);
lean_inc_ref(v___y_153_);
lean_inc(v___y_152_);
lean_inc_ref(v___y_151_);
lean_inc(v_val_167_);
lean_inc(v_key_166_);
v___x_168_ = lean_apply_8(v_f_146_, v_b_150_, v_key_166_, v_val_167_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, lean_box(0));
v___y_162_ = v___x_168_;
goto v___jp_161_;
}
case 1:
{
lean_object* v_node_169_; lean_object* v___x_170_; 
v_node_169_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_node_169_);
lean_inc_ref(v_f_146_);
v___x_170_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_146_, v_node_169_, v_b_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
v___y_162_ = v___x_170_;
goto v___jp_161_;
}
default: 
{
v_a_157_ = v_b_150_;
goto v___jp_156_;
}
}
}
else
{
lean_object* v___x_171_; 
lean_dec_ref(v_f_146_);
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v_b_150_);
return v___x_171_;
}
v___jp_156_:
{
size_t v___x_158_; size_t v___x_159_; 
v___x_158_ = ((size_t)1ULL);
v___x_159_ = lean_usize_add(v_i_148_, v___x_158_);
v_i_148_ = v___x_159_;
v_b_150_ = v_a_157_;
goto _start;
}
v___jp_161_:
{
if (lean_obj_tag(v___y_162_) == 0)
{
lean_object* v_a_163_; 
v_a_163_ = lean_ctor_get(v___y_162_, 0);
lean_inc(v_a_163_);
lean_dec_ref_known(v___y_162_, 1);
v_a_157_ = v_a_163_;
goto v___jp_156_;
}
else
{
lean_dec_ref(v_f_146_);
return v___y_162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(lean_object* v_f_172_, lean_object* v_x_173_, lean_object* v_x_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
if (lean_obj_tag(v_x_173_) == 0)
{
lean_object* v_es_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_193_; 
v_es_180_ = lean_ctor_get(v_x_173_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v_x_173_);
if (v_isSharedCheck_193_ == 0)
{
v___x_182_ = v_x_173_;
v_isShared_183_ = v_isSharedCheck_193_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_es_180_);
lean_dec(v_x_173_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_193_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_array_get_size(v_es_180_);
v___x_186_ = lean_nat_dec_lt(v___x_184_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_188_; 
lean_dec_ref(v_es_180_);
lean_dec_ref(v_f_172_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v_x_174_);
v___x_188_ = v___x_182_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_x_174_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
else
{
size_t v___x_190_; size_t v___x_191_; lean_object* v___x_192_; 
lean_del_object(v___x_182_);
v___x_190_ = ((size_t)0ULL);
v___x_191_ = lean_usize_of_nat(v___x_185_);
v___x_192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(v_f_172_, v_es_180_, v___x_190_, v___x_191_, v_x_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec_ref(v_es_180_);
return v___x_192_;
}
}
}
else
{
lean_object* v_ks_194_; lean_object* v_vs_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_ks_194_ = lean_ctor_get(v_x_173_, 0);
lean_inc_ref(v_ks_194_);
v_vs_195_ = lean_ctor_get(v_x_173_, 1);
lean_inc_ref(v_vs_195_);
lean_dec_ref_known(v_x_173_, 2);
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___redArg(v_f_172_, v_ks_194_, v_vs_195_, v___x_196_, v_x_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec_ref(v_vs_195_);
lean_dec_ref(v_ks_194_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg___boxed(lean_object* v_f_198_, lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_198_, v_x_199_, v_x_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_207_, lean_object* v_as_208_, lean_object* v_i_209_, lean_object* v_stop_210_, lean_object* v_b_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
size_t v_i_boxed_217_; size_t v_stop_boxed_218_; lean_object* v_res_219_; 
v_i_boxed_217_ = lean_unbox_usize(v_i_209_);
lean_dec(v_i_209_);
v_stop_boxed_218_ = lean_unbox_usize(v_stop_210_);
lean_dec(v_stop_210_);
v_res_219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(v_f_207_, v_as_208_, v_i_boxed_217_, v_stop_boxed_218_, v_b_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec_ref(v_as_208_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap(lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v___x_226_; lean_object* v_env_227_; lean_object* v___x_228_; lean_object* v_map_u2082_229_; lean_object* v___f_230_; lean_object* v___f_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_226_ = lean_st_ref_get(v_a_224_);
v_env_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc_ref_n(v_env_227_, 2);
lean_dec(v___x_226_);
v___x_228_ = l_Lean_Environment_constants(v_env_227_);
v_map_u2082_229_ = lean_ctor_get(v___x_228_, 1);
lean_inc_ref(v_map_u2082_229_);
lean_dec_ref(v___x_228_);
v___f_230_ = ((lean_object*)(l_Lean_LibrarySuggestions_localSymbolFrequencyMap___closed__0));
v___f_231_ = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___boxed), 10, 2);
lean_closure_set(v___f_231_, 0, v___f_230_);
lean_closure_set(v___f_231_, 1, v_env_227_);
v___x_232_ = lean_box(1);
v___x_233_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v___f_231_, v_map_u2082_229_, v___x_232_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequencyMap___boxed(lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_LibrarySuggestions_localSymbolFrequencyMap(v_a_234_, v_a_235_, v_a_236_, v_a_237_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0(lean_object* v_k_240_, lean_object* v_t_241_, lean_object* v_hl_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg(v_k_240_, v_t_241_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1___redArg(lean_object* v_map_244_, lean_object* v_f_245_, lean_object* v_init_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_245_, v_map_244_, v_init_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1___redArg___boxed(lean_object* v_map_253_, lean_object* v_f_254_, lean_object* v_init_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1___redArg(v_map_253_, v_f_254_, v_init_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1(lean_object* v_00_u03c3_262_, lean_object* v_00_u03b2_263_, lean_object* v_map_264_, lean_object* v_f_265_, lean_object* v_init_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_265_, v_map_264_, v_init_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1___boxed(lean_object* v_00_u03c3_273_, lean_object* v_00_u03b2_274_, lean_object* v_map_275_, lean_object* v_f_276_, lean_object* v_init_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1(v_00_u03c3_273_, v_00_u03b2_274_, v_map_275_, v_f_276_, v_init_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1(lean_object* v_00_u03c3_284_, lean_object* v_00_u03b1_285_, lean_object* v_00_u03b2_286_, lean_object* v_f_287_, lean_object* v_x_288_, lean_object* v_x_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_287_, v_x_288_, v_x_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___boxed(lean_object* v_00_u03c3_296_, lean_object* v_00_u03b1_297_, lean_object* v_00_u03b2_298_, lean_object* v_f_299_, lean_object* v_x_300_, lean_object* v_x_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1(v_00_u03c3_296_, v_00_u03b1_297_, v_00_u03b2_298_, v_f_299_, v_x_300_, v_x_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_308_, lean_object* v_00_u03b2_309_, lean_object* v_00_u03c3_310_, lean_object* v_f_311_, lean_object* v_as_312_, size_t v_i_313_, size_t v_stop_314_, lean_object* v_b_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(v_f_311_, v_as_312_, v_i_313_, v_stop_314_, v_b_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_322_, lean_object* v_00_u03b2_323_, lean_object* v_00_u03c3_324_, lean_object* v_f_325_, lean_object* v_as_326_, lean_object* v_i_327_, lean_object* v_stop_328_, lean_object* v_b_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
size_t v_i_boxed_335_; size_t v_stop_boxed_336_; lean_object* v_res_337_; 
v_i_boxed_335_ = lean_unbox_usize(v_i_327_);
lean_dec(v_i_327_);
v_stop_boxed_336_ = lean_unbox_usize(v_stop_328_);
lean_dec(v_stop_328_);
v_res_337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2(v_00_u03b1_322_, v_00_u03b2_323_, v_00_u03c3_324_, v_f_325_, v_as_326_, v_i_boxed_335_, v_stop_boxed_336_, v_b_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec_ref(v_as_326_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3(lean_object* v_00_u03c3_338_, lean_object* v_00_u03b1_339_, lean_object* v_00_u03b2_340_, lean_object* v_f_341_, lean_object* v_keys_342_, lean_object* v_vals_343_, lean_object* v_heq_344_, lean_object* v_i_345_, lean_object* v_acc_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___redArg(v_f_341_, v_keys_342_, v_vals_343_, v_i_345_, v_acc_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03c3_353_, lean_object* v_00_u03b1_354_, lean_object* v_00_u03b2_355_, lean_object* v_f_356_, lean_object* v_keys_357_, lean_object* v_vals_358_, lean_object* v_heq_359_, lean_object* v_i_360_, lean_object* v_acc_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3(v_00_u03c3_353_, v_00_u03b1_354_, v_00_u03b2_355_, v_f_356_, v_keys_357_, v_vals_358_, v_heq_359_, v_i_360_, v_acc_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec_ref(v_vals_358_);
lean_dec_ref(v_keys_357_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = lean_box(0);
v___x_370_ = lean_st_mk_ref(v___x_369_);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2____boxed(lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2_();
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap(lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_localSymbolFrequencyMapRef;
v___x_380_ = lean_st_ref_get(v___x_379_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_LibrarySuggestions_localSymbolFrequencyMap(v_a_374_, v_a_375_, v_a_376_, v_a_377_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_391_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_391_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_391_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_391_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
lean_inc(v_a_382_);
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v_a_382_);
v___x_387_ = lean_st_ref_swap(v___x_379_, v___x_386_);
lean_dec(v___x_387_);
if (v_isShared_385_ == 0)
{
v___x_389_ = v___x_384_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_382_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
else
{
return v___x_381_;
}
}
else
{
lean_object* v_val_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
v_val_392_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_380_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_val_392_);
lean_dec(v___x_380_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
lean_ctor_set_tag(v___x_394_, 0);
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_val_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap___boxed(lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap(v_a_400_, v_a_401_, v_a_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(lean_object* v_t_406_, lean_object* v_k_407_, lean_object* v_fallback_408_){
_start:
{
if (lean_obj_tag(v_t_406_) == 0)
{
lean_object* v_k_409_; lean_object* v_v_410_; lean_object* v_l_411_; lean_object* v_r_412_; uint8_t v___x_413_; 
v_k_409_ = lean_ctor_get(v_t_406_, 1);
v_v_410_ = lean_ctor_get(v_t_406_, 2);
v_l_411_ = lean_ctor_get(v_t_406_, 3);
v_r_412_ = lean_ctor_get(v_t_406_, 4);
v___x_413_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_407_, v_k_409_);
switch(v___x_413_)
{
case 0:
{
v_t_406_ = v_l_411_;
goto _start;
}
case 1:
{
lean_inc(v_v_410_);
return v_v_410_;
}
default: 
{
v_t_406_ = v_r_412_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_408_);
return v_fallback_408_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg___boxed(lean_object* v_t_416_, lean_object* v_k_417_, lean_object* v_fallback_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_t_416_, v_k_417_, v_fallback_418_);
lean_dec(v_fallback_418_);
lean_dec(v_k_417_);
lean_dec(v_t_416_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequency(lean_object* v_n_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap(v_a_421_, v_a_422_, v_a_423_, v_a_424_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_436_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_436_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_436_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_436_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_431_ = lean_unsigned_to_nat(0u);
v___x_432_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_a_427_, v_n_420_, v___x_431_);
lean_dec(v_a_427_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_432_);
v___x_434_ = v___x_429_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
v_a_437_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_426_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_426_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_localSymbolFrequency___boxed(lean_object* v_n_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_LibrarySuggestions_localSymbolFrequency(v_n_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec(v_n_445_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0(lean_object* v_00_u03b4_452_, lean_object* v_t_453_, lean_object* v_k_454_, lean_object* v_fallback_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_t_453_, v_k_454_, v_fallback_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___boxed(lean_object* v_00_u03b4_457_, lean_object* v_t_458_, lean_object* v_k_459_, lean_object* v_fallback_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0(v_00_u03b4_457_, v_t_458_, v_k_459_, v_fallback_460_);
lean_dec(v_fallback_460_);
lean_dec(v_k_459_);
lean_dec(v_t_458_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___lam__0(lean_object* v___x_462_){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = l_Lean_MessageData_toString(v___x_462_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___lam__0___boxed(lean_object* v___x_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___lam__0(v___x_466_);
return v_res_468_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0(void){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_instMonadEIO(lean_box(0));
return v___x_469_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0);
v___x_471_ = l_StateRefT_x27_instMonad___redArg(v___x_470_);
return v___x_471_;
}
}
static uint64_t _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12(void){
_start:
{
lean_object* v___x_491_; uint64_t v___x_492_; 
v___x_491_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11));
v___x_492_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13(void){
_start:
{
uint64_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_uint64_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12);
v___x_494_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11));
v___x_495_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set_uint64(v___x_495_, sizeof(void*)*1, v___x_493_);
return v___x_495_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14(void){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_496_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = lean_unsigned_to_nat(32u);
v___x_500_ = lean_mk_empty_array_with_capacity(v___x_499_);
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17(void){
_start:
{
size_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_502_ = ((size_t)5ULL);
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = lean_unsigned_to_nat(32u);
v___x_505_ = lean_mk_empty_array_with_capacity(v___x_504_);
v___x_506_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16);
v___x_507_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v___x_505_);
lean_ctor_set(v___x_507_, 2, v___x_503_);
lean_ctor_set(v___x_507_, 3, v___x_503_);
lean_ctor_set_usize(v___x_507_, 4, v___x_502_);
return v___x_507_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_508_ = lean_box(1);
v___x_509_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
v___x_510_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
v___x_511_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set(v___x_511_, 1, v___x_509_);
lean_ctor_set(v___x_511_, 2, v___x_508_);
return v___x_511_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20(void){
_start:
{
uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_514_ = 1;
v___x_515_ = lean_unsigned_to_nat(0u);
v___x_516_ = lean_box(0);
v___x_517_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19));
v___x_518_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18);
v___x_519_ = lean_box(1);
v___x_520_ = 0;
v___x_521_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13);
v___x_522_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v___x_519_);
lean_ctor_set(v___x_522_, 2, v___x_518_);
lean_ctor_set(v___x_522_, 3, v___x_517_);
lean_ctor_set(v___x_522_, 4, v___x_516_);
lean_ctor_set(v___x_522_, 5, v___x_515_);
lean_ctor_set(v___x_522_, 6, v___x_516_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*7, v___x_520_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*7 + 1, v___x_520_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*7 + 2, v___x_520_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*7 + 3, v___x_514_);
return v___x_522_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
lean_ctor_set(v___x_525_, 2, v___x_524_);
lean_ctor_set(v___x_525_, 3, v___x_524_);
lean_ctor_set(v___x_525_, 4, v___x_523_);
lean_ctor_set(v___x_525_, 5, v___x_523_);
lean_ctor_set(v___x_525_, 6, v___x_523_);
lean_ctor_set(v___x_525_, 7, v___x_523_);
lean_ctor_set(v___x_525_, 8, v___x_523_);
lean_ctor_set(v___x_525_, 9, v___x_523_);
lean_ctor_set(v___x_525_, 10, v___x_523_);
return v___x_525_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
v___x_527_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
lean_ctor_set(v___x_527_, 2, v___x_526_);
lean_ctor_set(v___x_527_, 3, v___x_526_);
lean_ctor_set(v___x_527_, 4, v___x_526_);
lean_ctor_set(v___x_527_, 5, v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
v___x_529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
lean_ctor_set(v___x_529_, 2, v___x_528_);
lean_ctor_set(v___x_529_, 3, v___x_528_);
lean_ctor_set(v___x_529_, 4, v___x_528_);
return v___x_529_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_530_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23);
v___x_531_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
v___x_532_ = lean_box(1);
v___x_533_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22);
v___x_534_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21);
v___x_535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v___x_533_);
lean_ctor_set(v___x_535_, 2, v___x_532_);
lean_ctor_set(v___x_535_, 3, v___x_531_);
lean_ctor_set(v___x_535_, 4, v___x_530_);
return v___x_535_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_537_ = lean_obj_once(&l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2, &l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2_once, _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2);
v___x_538_ = lean_box(0);
v___x_539_ = lean_box(0);
v___x_540_ = l_Lean_instInhabitedFileMap_default;
v___x_541_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25));
v___x_542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v___x_540_);
lean_ctor_set(v___x_542_, 2, v___x_539_);
lean_ctor_set(v___x_542_, 3, v___x_538_);
lean_ctor_set(v___x_542_, 4, v___x_537_);
return v___x_542_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27(void){
_start:
{
uint8_t v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_543_ = 0;
v___x_544_ = l_Lean_firstFrontendMacroScope;
v___x_545_ = lean_box(0);
v___x_546_ = lean_box(0);
v___x_547_ = lean_box(0);
v___x_548_ = lean_unsigned_to_nat(1000u);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = l_Lean_Options_empty;
v___x_551_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26);
v___x_552_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v___x_550_);
lean_ctor_set(v___x_552_, 2, v___x_549_);
lean_ctor_set(v___x_552_, 3, v___x_548_);
lean_ctor_set(v___x_552_, 4, v___x_547_);
lean_ctor_set(v___x_552_, 5, v___x_546_);
lean_ctor_set(v___x_552_, 6, v___x_545_);
lean_ctor_set(v___x_552_, 7, v___x_549_);
lean_ctor_set(v___x_552_, 8, v___x_549_);
lean_ctor_set(v___x_552_, 9, v___x_544_);
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*10, v___x_543_);
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*10 + 1, v___x_543_);
return v___x_552_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_553_ = lean_unsigned_to_nat(1u);
v___x_554_ = l_Lean_firstFrontendMacroScope;
v___x_555_ = lean_nat_add(v___x_554_, v___x_553_);
return v___x_555_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33(void){
_start:
{
lean_object* v___x_566_; uint64_t v___x_567_; lean_object* v___x_568_; 
v___x_566_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
v___x_567_ = 0ULL;
v___x_568_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_568_, 0, v___x_566_);
lean_ctor_set_uint64(v___x_568_, sizeof(void*)*1, v___x_567_);
return v___x_568_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
return v___x_570_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = l_Lean_NameSet_empty;
v___x_572_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
v___x_573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
lean_ctor_set(v___x_573_, 2, v___x_571_);
return v___x_573_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__36(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; lean_object* v___x_577_; 
v___x_574_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
v___x_575_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
v___x_576_ = 1;
v___x_577_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_575_);
lean_ctor_set(v___x_577_, 2, v___x_574_);
lean_ctor_set_uint8(v___x_577_, sizeof(void*)*3, v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(lean_object* v_inst_580_, lean_object* v_env_581_, lean_object* v_x_582_){
_start:
{
lean_object* v___x_583_; lean_object* v_toApplicative_584_; lean_object* v_toFunctor_585_; lean_object* v_toSeq_586_; lean_object* v_toSeqLeft_587_; lean_object* v_toSeqRight_588_; lean_object* v___f_589_; lean_object* v___f_590_; lean_object* v___f_591_; lean_object* v___f_592_; lean_object* v___x_593_; lean_object* v___f_594_; lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v_toApplicative_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_664_; 
v___x_583_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1);
v_toApplicative_584_ = lean_ctor_get(v___x_583_, 0);
v_toFunctor_585_ = lean_ctor_get(v_toApplicative_584_, 0);
v_toSeq_586_ = lean_ctor_get(v_toApplicative_584_, 2);
v_toSeqLeft_587_ = lean_ctor_get(v_toApplicative_584_, 3);
v_toSeqRight_588_ = lean_ctor_get(v_toApplicative_584_, 4);
v___f_589_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__2));
v___f_590_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_585_, 2);
v___f_591_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_591_, 0, v_toFunctor_585_);
v___f_592_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_592_, 0, v_toFunctor_585_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v___f_591_);
lean_ctor_set(v___x_593_, 1, v___f_592_);
lean_inc(v_toSeqRight_588_);
v___f_594_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_594_, 0, v_toSeqRight_588_);
lean_inc(v_toSeqLeft_587_);
v___f_595_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_595_, 0, v_toSeqLeft_587_);
lean_inc(v_toSeq_586_);
v___f_596_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_596_, 0, v_toSeq_586_);
v___x_597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_597_, 0, v___x_593_);
lean_ctor_set(v___x_597_, 1, v___f_589_);
lean_ctor_set(v___x_597_, 2, v___f_596_);
lean_ctor_set(v___x_597_, 3, v___f_595_);
lean_ctor_set(v___x_597_, 4, v___f_594_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
lean_ctor_set(v___x_598_, 1, v___f_590_);
v___x_599_ = l_StateRefT_x27_instMonad___redArg(v___x_598_);
v_toApplicative_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_664_ == 0)
{
lean_object* v_unused_665_; 
v_unused_665_ = lean_ctor_get(v___x_599_, 1);
lean_dec(v_unused_665_);
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_664_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_toApplicative_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_664_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v_toFunctor_604_; lean_object* v_toSeq_605_; lean_object* v_toSeqLeft_606_; lean_object* v_toSeqRight_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_662_; 
v_toFunctor_604_ = lean_ctor_get(v_toApplicative_600_, 0);
v_toSeq_605_ = lean_ctor_get(v_toApplicative_600_, 2);
v_toSeqLeft_606_ = lean_ctor_get(v_toApplicative_600_, 3);
v_toSeqRight_607_ = lean_ctor_get(v_toApplicative_600_, 4);
v_isSharedCheck_662_ = !lean_is_exclusive(v_toApplicative_600_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; 
v_unused_663_ = lean_ctor_get(v_toApplicative_600_, 1);
lean_dec(v_unused_663_);
v___x_609_ = v_toApplicative_600_;
v_isShared_610_ = v_isSharedCheck_662_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_toSeqRight_607_);
lean_inc(v_toSeqLeft_606_);
lean_inc(v_toSeq_605_);
lean_inc(v_toFunctor_604_);
lean_dec(v_toApplicative_600_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_662_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___f_611_; lean_object* v___f_612_; lean_object* v___f_613_; lean_object* v___f_614_; lean_object* v___x_615_; lean_object* v___f_616_; lean_object* v___f_617_; lean_object* v___f_618_; lean_object* v___x_620_; 
v___f_611_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__4));
v___f_612_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__5));
lean_inc_ref(v_toFunctor_604_);
v___f_613_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_613_, 0, v_toFunctor_604_);
v___f_614_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_614_, 0, v_toFunctor_604_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___f_613_);
lean_ctor_set(v___x_615_, 1, v___f_614_);
v___f_616_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_616_, 0, v_toSeqRight_607_);
v___f_617_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_617_, 0, v_toSeqLeft_606_);
v___f_618_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_618_, 0, v_toSeq_605_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 4, v___f_616_);
lean_ctor_set(v___x_609_, 3, v___f_617_);
lean_ctor_set(v___x_609_, 2, v___f_618_);
lean_ctor_set(v___x_609_, 1, v___f_611_);
lean_ctor_set(v___x_609_, 0, v___x_615_);
v___x_620_ = v___x_609_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v___f_611_);
lean_ctor_set(v_reuseFailAlloc_661_, 2, v___f_618_);
lean_ctor_set(v_reuseFailAlloc_661_, 3, v___f_617_);
lean_ctor_set(v_reuseFailAlloc_661_, 4, v___f_616_);
v___x_620_ = v_reuseFailAlloc_661_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_622_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 1, v___f_612_);
lean_ctor_set(v___x_602_, 0, v___x_620_);
v___x_622_ = v___x_602_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v___f_612_);
v___x_622_ = v_reuseFailAlloc_660_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; lean_object* v___f_624_; uint8_t v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_623_ = l_Lean_Meta_instMonadEnvMetaM;
v___f_624_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__10));
v___x_625_ = 1;
v___x_626_ = l_Lean_withoutExporting___redArg(v___x_622_, v___x_623_, v___f_624_, v_x_582_, v___x_625_);
v___x_627_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19));
v___x_628_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20);
v___x_629_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24);
v___x_630_ = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_run_x27___boxed), 7, 4);
lean_closure_set(v___x_630_, 0, lean_box(0));
lean_closure_set(v___x_630_, 1, v___x_626_);
lean_closure_set(v___x_630_, 2, v___x_628_);
lean_closure_set(v___x_630_, 3, v___x_629_);
v___x_631_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27);
v___x_632_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28);
v___x_633_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31));
v___x_634_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32));
v___x_635_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33);
v___x_636_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34);
v___x_637_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35);
v___x_638_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__36, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__36_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__36);
v___x_639_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_639_, 0, v_env_581_);
lean_ctor_set(v___x_639_, 1, v___x_632_);
lean_ctor_set(v___x_639_, 2, v___x_633_);
lean_ctor_set(v___x_639_, 3, v___x_634_);
lean_ctor_set(v___x_639_, 4, v___x_635_);
lean_ctor_set(v___x_639_, 5, v___x_636_);
lean_ctor_set(v___x_639_, 6, v___x_637_);
lean_ctor_set(v___x_639_, 7, v___x_638_);
lean_ctor_set(v___x_639_, 8, v___x_627_);
v___x_640_ = lean_alloc_closure((void*)(l_Lean_Core_CoreM_run_x27___boxed), 5, 4);
lean_closure_set(v___x_640_, 0, lean_box(0));
lean_closure_set(v___x_640_, 1, v___x_630_);
lean_closure_set(v___x_640_, 2, v___x_631_);
lean_closure_set(v___x_640_, 3, v___x_639_);
v___x_641_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_641_, 0, lean_box(0));
lean_closure_set(v___x_641_, 1, lean_box(0));
lean_closure_set(v___x_641_, 2, v___x_640_);
v___x_642_ = l_unsafeBaseIO___redArg(v___x_641_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___y_649_; lean_object* v___x_652_; lean_object* v___f_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_642_, 1);
v___x_644_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__37));
v___x_645_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__38));
v___x_646_ = lean_unsigned_to_nat(75u);
v___x_647_ = lean_unsigned_to_nat(24u);
v___x_652_ = l_Lean_Exception_toMessageData(v_a_643_);
v___f_653_ = lean_alloc_closure((void*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_653_, 0, v___x_652_);
v___x_654_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_654_, 0, lean_box(0));
lean_closure_set(v___x_654_, 1, lean_box(0));
lean_closure_set(v___x_654_, 2, v___f_653_);
v___x_655_ = l_unsafeBaseIO___redArg(v___x_654_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_657_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v___x_657_ = lean_io_error_to_string(v_a_656_);
v___y_649_ = v___x_657_;
goto v___jp_648_;
}
else
{
lean_object* v_a_658_; 
v_a_658_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_655_, 1);
v___y_649_ = v_a_658_;
goto v___jp_648_;
}
v___jp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = l_mkPanicMessageWithDecl(v___x_644_, v___x_645_, v___x_646_, v___x_647_, v___y_649_);
lean_dec_ref(v___y_649_);
v___x_651_ = l_panic___redArg(v_inst_580_, v___x_650_);
return v___x_651_;
}
}
else
{
lean_object* v_a_659_; 
v_a_659_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_642_, 1);
return v_a_659_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___boxed(lean_object* v_inst_666_, lean_object* v_env_667_, lean_object* v_x_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(v_inst_666_, v_env_667_, v_x_668_);
lean_dec(v_inst_666_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM(lean_object* v_00_u03b1_670_, lean_object* v_inst_671_, lean_object* v_env_672_, lean_object* v_x_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(v_inst_671_, v_env_672_, v_x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___boxed(lean_object* v_00_u03b1_675_, lean_object* v_inst_676_, lean_object* v_env_677_, lean_object* v_x_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM(v_00_u03b1_675_, v_inst_676_, v_env_677_, v_x_678_);
lean_dec(v_inst_676_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0(lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap(v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_696_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_696_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_696_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_696_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_690_ = lean_unsigned_to_nat(1u);
v___x_691_ = lean_mk_empty_array_with_capacity(v___x_690_);
v___x_692_ = lean_array_push(v___x_691_, v_a_686_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_692_);
v___x_694_ = v___x_688_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
v_a_697_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_685_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_685_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0___boxed(lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0(v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
return v_res_710_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1(void){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Array_instInhabited(lean_box(0));
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3(lean_object* v_env_713_){
_start:
{
lean_object* v___f_714_; lean_object* v___x_715_; lean_object* v_ents_716_; lean_object* v___x_717_; 
v___f_714_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__0));
v___x_715_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1);
v_ents_716_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(v___x_715_, v_env_713_, v___f_714_);
lean_inc_n(v_ents_716_, 2);
v___x_717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_717_, 0, v_ents_716_);
lean_ctor_set(v___x_717_, 1, v_ents_716_);
lean_ctor_set(v___x_717_, 2, v_ents_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object* v_x_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_));
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object* v_x_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v_x_722_);
lean_dec_ref(v_x_722_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object* v_x_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_));
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object* v_x_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v_x_729_);
lean_dec_ref(v_x_729_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap(v___y_731_, v___y_732_, v___y_733_, v___y_734_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_747_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_747_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_747_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_747_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_741_ = lean_unsigned_to_nat(1u);
v___x_742_ = lean_mk_empty_array_with_capacity(v___x_741_);
v___x_743_ = lean_array_push(v___x_742_, v_a_737_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_743_);
v___x_745_ = v___x_739_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
v_a_748_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_736_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_736_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object* v___f_762_, lean_object* v_env_763_, lean_object* v_x_764_){
_start:
{
lean_object* v___x_765_; lean_object* v_ents_766_; lean_object* v___x_767_; 
v___x_765_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1, &l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1_once, _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1);
v_ents_766_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(v___x_765_, v_env_763_, v___f_762_);
lean_inc_n(v_ents_766_, 2);
v___x_767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_767_, 0, v_ents_766_);
lean_ctor_set(v___x_767_, 1, v_ents_766_);
lean_ctor_set(v___x_767_, 2, v_ents_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object* v___f_768_, lean_object* v_env_769_, lean_object* v_x_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v___f_768_, v_env_769_, v_x_770_);
lean_dec_ref(v_x_770_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object* v_a_772_, uint8_t v_a_773_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
uint8_t v_a_207__boxed_776_; lean_object* v_res_777_; 
v_a_207__boxed_776_ = lean_unbox(v_a_775_);
v_res_777_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v_a_774_, v_a_207__boxed_776_);
lean_dec_ref(v_a_774_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object* v_mapss_778_, lean_object* v_x_779_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v_mapss_778_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object* v_mapss_782_, lean_object* v_x_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v_mapss_782_, v_x_783_);
lean_dec_ref(v_x_783_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(lean_object* v___x_786_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_786_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object* v___x_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v___x_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_));
v___x_819_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_();
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = lean_box(0);
v___x_824_ = lean_st_mk_ref(v___x_823_);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2____boxed(lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2_();
return v_res_827_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instZeroNameMapNat(void){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = lean_box(1);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0(lean_object* v___x_829_, lean_object* v_x_x27_830_, lean_object* v_n_831_, lean_object* v_c_832_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_833_ = lean_unsigned_to_nat(0u);
lean_inc(v_n_831_);
lean_inc(v_x_x27_830_);
v___x_834_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v___x_829_, v_x_x27_830_, v_n_831_, v___x_833_);
v___x_835_ = lean_nat_add(v___x_834_, v_c_832_);
lean_dec(v___x_834_);
v___x_836_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_831_, v___x_835_, v_x_x27_830_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0___boxed(lean_object* v___x_837_, lean_object* v_x_x27_838_, lean_object* v_n_839_, lean_object* v_c_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0(v___x_837_, v_x_x27_838_, v_n_839_, v_c_840_);
lean_dec(v_c_840_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1(lean_object* v_x_845_, lean_object* v_y_846_){
_start:
{
lean_object* v___f_847_; lean_object* v___x_848_; 
v___f_847_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__1));
v___x_848_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_847_, v_x_845_, v_y_846_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(lean_object* v_init_851_, lean_object* v_x_852_){
_start:
{
if (lean_obj_tag(v_x_852_) == 0)
{
lean_object* v_k_853_; lean_object* v_v_854_; lean_object* v_l_855_; lean_object* v_r_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_k_853_ = lean_ctor_get(v_x_852_, 1);
lean_inc(v_k_853_);
v_v_854_ = lean_ctor_get(v_x_852_, 2);
lean_inc(v_v_854_);
v_l_855_ = lean_ctor_get(v_x_852_, 3);
lean_inc(v_l_855_);
v_r_856_ = lean_ctor_get(v_x_852_, 4);
lean_inc(v_r_856_);
lean_dec_ref_known(v_x_852_, 5);
v___x_857_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(v_init_851_, v_l_855_);
v___x_858_ = lean_unsigned_to_nat(0u);
v___x_859_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v___x_857_, v_k_853_, v___x_858_);
v___x_860_ = lean_nat_add(v___x_859_, v_v_854_);
lean_dec(v_v_854_);
lean_dec(v___x_859_);
v___x_861_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_853_, v___x_860_, v___x_857_);
v_init_851_ = v___x_861_;
v_x_852_ = v_r_856_;
goto _start;
}
else
{
return v_init_851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(lean_object* v_as_863_, size_t v_i_864_, size_t v_stop_865_, lean_object* v_b_866_){
_start:
{
uint8_t v___x_867_; 
v___x_867_ = lean_usize_dec_eq(v_i_864_, v_stop_865_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; lean_object* v___x_869_; size_t v___x_870_; size_t v___x_871_; 
v___x_868_ = lean_array_uget_borrowed(v_as_863_, v_i_864_);
lean_inc(v___x_868_);
v___x_869_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(v_b_866_, v___x_868_);
v___x_870_ = ((size_t)1ULL);
v___x_871_ = lean_usize_add(v_i_864_, v___x_870_);
v_i_864_ = v___x_871_;
v_b_866_ = v___x_869_;
goto _start;
}
else
{
return v_b_866_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___boxed(lean_object* v_as_873_, lean_object* v_i_874_, lean_object* v_stop_875_, lean_object* v_b_876_){
_start:
{
size_t v_i_boxed_877_; size_t v_stop_boxed_878_; lean_object* v_res_879_; 
v_i_boxed_877_ = lean_unbox_usize(v_i_874_);
lean_dec(v_i_874_);
v_stop_boxed_878_ = lean_unbox_usize(v_stop_875_);
lean_dec(v_stop_875_);
v_res_879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(v_as_873_, v_i_boxed_877_, v_stop_boxed_878_, v_b_876_);
lean_dec_ref(v_as_873_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(lean_object* v_as_880_, size_t v_i_881_, size_t v_stop_882_, lean_object* v_b_883_){
_start:
{
lean_object* v___y_885_; uint8_t v___x_889_; 
v___x_889_ = lean_usize_dec_eq(v_i_881_, v_stop_882_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_890_ = lean_array_uget_borrowed(v_as_880_, v_i_881_);
v___x_891_ = lean_unsigned_to_nat(0u);
v___x_892_ = lean_array_get_size(v___x_890_);
v___x_893_ = lean_nat_dec_lt(v___x_891_, v___x_892_);
if (v___x_893_ == 0)
{
v___y_885_ = v_b_883_;
goto v___jp_884_;
}
else
{
uint8_t v___x_894_; 
v___x_894_ = lean_nat_dec_le(v___x_892_, v___x_892_);
if (v___x_894_ == 0)
{
if (v___x_893_ == 0)
{
v___y_885_ = v_b_883_;
goto v___jp_884_;
}
else
{
size_t v___x_895_; size_t v___x_896_; lean_object* v___x_897_; 
v___x_895_ = ((size_t)0ULL);
v___x_896_ = lean_usize_of_nat(v___x_892_);
v___x_897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(v___x_890_, v___x_895_, v___x_896_, v_b_883_);
v___y_885_ = v___x_897_;
goto v___jp_884_;
}
}
else
{
size_t v___x_898_; size_t v___x_899_; lean_object* v___x_900_; 
v___x_898_ = ((size_t)0ULL);
v___x_899_ = lean_usize_of_nat(v___x_892_);
v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(v___x_890_, v___x_898_, v___x_899_, v_b_883_);
v___y_885_ = v___x_900_;
goto v___jp_884_;
}
}
}
else
{
return v_b_883_;
}
v___jp_884_:
{
size_t v___x_886_; size_t v___x_887_; 
v___x_886_ = ((size_t)1ULL);
v___x_887_ = lean_usize_add(v_i_881_, v___x_886_);
v_i_881_ = v___x_887_;
v_b_883_ = v___y_885_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2___boxed(lean_object* v_as_901_, lean_object* v_i_902_, lean_object* v_stop_903_, lean_object* v_b_904_){
_start:
{
size_t v_i_boxed_905_; size_t v_stop_boxed_906_; lean_object* v_res_907_; 
v_i_boxed_905_ = lean_unbox_usize(v_i_902_);
lean_dec(v_i_902_);
v_stop_boxed_906_ = lean_unbox_usize(v_stop_903_);
lean_dec(v_stop_903_);
v_res_907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(v_as_901_, v_i_boxed_905_, v_stop_boxed_906_, v_b_904_);
lean_dec_ref(v_as_901_);
return v_res_907_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0(void){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Array_instInhabited(lean_box(0));
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(lean_object* v_a_909_){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyMapRef;
v___x_912_ = lean_st_ref_get(v___x_911_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v___x_913_; lean_object* v___y_915_; lean_object* v_env_919_; lean_object* v___x_920_; lean_object* v_toEnvExtension_921_; lean_object* v_asyncMode_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_913_ = lean_st_ref_get(v_a_909_);
v_env_919_ = lean_ctor_get(v___x_913_, 0);
lean_inc_ref(v_env_919_);
lean_dec(v___x_913_);
v___x_920_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt;
v_toEnvExtension_921_ = lean_ctor_get(v___x_920_, 0);
v_asyncMode_922_ = lean_ctor_get(v_toEnvExtension_921_, 2);
v___x_923_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0, &l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0);
v___x_924_ = lean_box(0);
v___x_925_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_923_, v___x_920_, v_env_919_, v_asyncMode_922_, v___x_924_);
v___x_926_ = lean_box(1);
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_array_get_size(v___x_925_);
v___x_929_ = lean_nat_dec_lt(v___x_927_, v___x_928_);
if (v___x_929_ == 0)
{
lean_dec(v___x_925_);
v___y_915_ = v___x_926_;
goto v___jp_914_;
}
else
{
uint8_t v___x_930_; 
v___x_930_ = lean_nat_dec_le(v___x_928_, v___x_928_);
if (v___x_930_ == 0)
{
if (v___x_929_ == 0)
{
lean_dec(v___x_925_);
v___y_915_ = v___x_926_;
goto v___jp_914_;
}
else
{
size_t v___x_931_; size_t v___x_932_; lean_object* v___x_933_; 
v___x_931_ = ((size_t)0ULL);
v___x_932_ = lean_usize_of_nat(v___x_928_);
v___x_933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(v___x_925_, v___x_931_, v___x_932_, v___x_926_);
lean_dec(v___x_925_);
v___y_915_ = v___x_933_;
goto v___jp_914_;
}
}
else
{
size_t v___x_934_; size_t v___x_935_; lean_object* v___x_936_; 
v___x_934_ = ((size_t)0ULL);
v___x_935_ = lean_usize_of_nat(v___x_928_);
v___x_936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(v___x_925_, v___x_934_, v___x_935_, v___x_926_);
lean_dec(v___x_925_);
v___y_915_ = v___x_936_;
goto v___jp_914_;
}
}
v___jp_914_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
lean_inc(v___y_915_);
v___x_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_916_, 0, v___y_915_);
v___x_917_ = lean_st_ref_swap(v___x_911_, v___x_916_);
lean_dec(v___x_917_);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___y_915_);
return v___x_918_;
}
}
else
{
lean_object* v_val_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
v_val_937_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_912_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_val_937_);
lean_dec(v___x_912_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set_tag(v___x_939_, 0);
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_val_937_);
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
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___boxed(lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(v_a_945_);
lean_dec(v_a_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap(lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(v_a_949_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___boxed(lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_LibrarySuggestions_symbolFrequencyMap(v_a_952_, v_a_953_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0(lean_object* v_init_956_, lean_object* v_t_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(v_init_956_, v_t_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency___redArg(lean_object* v_n_959_, lean_object* v_a_960_){
_start:
{
lean_object* v___x_962_; lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_972_; 
v___x_962_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(v_a_960_);
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_972_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_972_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_972_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_a_963_, v_n_959_, v___x_967_);
lean_dec(v_a_963_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_968_);
v___x_970_ = v___x_965_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency___redArg___boxed(lean_object* v_n_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_LibrarySuggestions_symbolFrequency___redArg(v_n_973_, v_a_974_);
lean_dec(v_a_974_);
lean_dec(v_n_973_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency(lean_object* v_n_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_LibrarySuggestions_symbolFrequency___redArg(v_n_977_, v_a_979_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency___boxed(lean_object* v_n_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_LibrarySuggestions_symbolFrequency(v_n_982_, v_a_983_, v_a_984_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_n_982_);
return v_res_986_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_LibrarySuggestions_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_LibrarySuggestions_SymbolFrequency(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
