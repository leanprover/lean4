// Lean compiler output
// Module: Lean.Elab.Tactic.Meta
// Imports: public import Lean.Elab.SyntheticMVars
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_instInhabitedLocalContext_default;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_sharecommon_quick(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__0;
static const lean_closure_object l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__1 = (const lean_object*)&l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__2 = (const lean_object*)&l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__3 = (const lean_object*)&l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__4 = (const lean_object*)&l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.MetavarContext"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.instantiateLCtxMVars"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "Invalid auxiliary declaration found in local context: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = " does not have an associated full name."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic___lam__0(lean_object* v_tacticCode_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Lean_Elab_Tactic_evalTactic(v_tacticCode_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_12_; 
lean_dec_ref(v___x_11_);
v___x_12_ = l_Lean_Elab_Tactic_pruneSolvedGoals(v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
return v___x_12_;
}
else
{
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic___lam__0___boxed(lean_object* v_tacticCode_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Elab_runTactic___lam__0(v_tacticCode_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic___lam__1(lean_object* v___x_24_, uint8_t v___x_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_24_, v___x_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic___lam__1___boxed(lean_object* v___x_34_, lean_object* v___x_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
uint8_t v___x_5196__boxed_43_; lean_object* v_res_44_; 
v___x_5196__boxed_43_ = lean_unbox(v___x_35_);
v_res_44_ = l_Lean_Elab_runTactic___lam__1(v___x_34_, v___x_5196__boxed_43_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
return v_res_44_;
}
}
static lean_object* _init_l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_instMonadEIO(lean_box(0));
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2(lean_object* v_msg_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v_toApplicative_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_119_; 
v___x_56_ = lean_obj_once(&l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__0, &l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__0_once, _init_l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__0);
v___x_57_ = l_StateRefT_x27_instMonad___redArg(v___x_56_);
v_toApplicative_58_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_119_ == 0)
{
lean_object* v_unused_120_; 
v_unused_120_ = lean_ctor_get(v___x_57_, 1);
lean_dec(v_unused_120_);
v___x_60_ = v___x_57_;
v_isShared_61_ = v_isSharedCheck_119_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_toApplicative_58_);
lean_dec(v___x_57_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_119_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v_toFunctor_62_; lean_object* v_toSeq_63_; lean_object* v_toSeqLeft_64_; lean_object* v_toSeqRight_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_117_; 
v_toFunctor_62_ = lean_ctor_get(v_toApplicative_58_, 0);
v_toSeq_63_ = lean_ctor_get(v_toApplicative_58_, 2);
v_toSeqLeft_64_ = lean_ctor_get(v_toApplicative_58_, 3);
v_toSeqRight_65_ = lean_ctor_get(v_toApplicative_58_, 4);
v_isSharedCheck_117_ = !lean_is_exclusive(v_toApplicative_58_);
if (v_isSharedCheck_117_ == 0)
{
lean_object* v_unused_118_; 
v_unused_118_ = lean_ctor_get(v_toApplicative_58_, 1);
lean_dec(v_unused_118_);
v___x_67_ = v_toApplicative_58_;
v_isShared_68_ = v_isSharedCheck_117_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_toSeqRight_65_);
lean_inc(v_toSeqLeft_64_);
lean_inc(v_toSeq_63_);
lean_inc(v_toFunctor_62_);
lean_dec(v_toApplicative_58_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_117_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___f_69_; lean_object* v___f_70_; lean_object* v___f_71_; lean_object* v___f_72_; lean_object* v___x_73_; lean_object* v___f_74_; lean_object* v___f_75_; lean_object* v___f_76_; lean_object* v___x_78_; 
v___f_69_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__1));
v___f_70_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__2));
lean_inc_ref(v_toFunctor_62_);
v___f_71_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_71_, 0, v_toFunctor_62_);
v___f_72_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_72_, 0, v_toFunctor_62_);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v___f_71_);
lean_ctor_set(v___x_73_, 1, v___f_72_);
v___f_74_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_74_, 0, v_toSeqRight_65_);
v___f_75_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_75_, 0, v_toSeqLeft_64_);
v___f_76_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_76_, 0, v_toSeq_63_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 4, v___f_74_);
lean_ctor_set(v___x_67_, 3, v___f_75_);
lean_ctor_set(v___x_67_, 2, v___f_76_);
lean_ctor_set(v___x_67_, 1, v___f_69_);
lean_ctor_set(v___x_67_, 0, v___x_73_);
v___x_78_ = v___x_67_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_73_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v___f_69_);
lean_ctor_set(v_reuseFailAlloc_116_, 2, v___f_76_);
lean_ctor_set(v_reuseFailAlloc_116_, 3, v___f_75_);
lean_ctor_set(v_reuseFailAlloc_116_, 4, v___f_74_);
v___x_78_ = v_reuseFailAlloc_116_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
lean_object* v___x_80_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 1, v___f_70_);
lean_ctor_set(v___x_60_, 0, v___x_78_);
v___x_80_ = v___x_60_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_78_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v___f_70_);
v___x_80_ = v_reuseFailAlloc_115_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
lean_object* v___x_81_; lean_object* v_toApplicative_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_113_; 
v___x_81_ = l_StateRefT_x27_instMonad___redArg(v___x_80_);
v_toApplicative_82_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_113_ == 0)
{
lean_object* v_unused_114_; 
v_unused_114_ = lean_ctor_get(v___x_81_, 1);
lean_dec(v_unused_114_);
v___x_84_ = v___x_81_;
v_isShared_85_ = v_isSharedCheck_113_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_toApplicative_82_);
lean_dec(v___x_81_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_113_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v_toFunctor_86_; lean_object* v_toSeq_87_; lean_object* v_toSeqLeft_88_; lean_object* v_toSeqRight_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_111_; 
v_toFunctor_86_ = lean_ctor_get(v_toApplicative_82_, 0);
v_toSeq_87_ = lean_ctor_get(v_toApplicative_82_, 2);
v_toSeqLeft_88_ = lean_ctor_get(v_toApplicative_82_, 3);
v_toSeqRight_89_ = lean_ctor_get(v_toApplicative_82_, 4);
v_isSharedCheck_111_ = !lean_is_exclusive(v_toApplicative_82_);
if (v_isSharedCheck_111_ == 0)
{
lean_object* v_unused_112_; 
v_unused_112_ = lean_ctor_get(v_toApplicative_82_, 1);
lean_dec(v_unused_112_);
v___x_91_ = v_toApplicative_82_;
v_isShared_92_ = v_isSharedCheck_111_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_toSeqRight_89_);
lean_inc(v_toSeqLeft_88_);
lean_inc(v_toSeq_87_);
lean_inc(v_toFunctor_86_);
lean_dec(v_toApplicative_82_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_111_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___f_95_; lean_object* v___f_96_; lean_object* v___x_97_; lean_object* v___f_98_; lean_object* v___f_99_; lean_object* v___f_100_; lean_object* v___x_102_; 
v___f_93_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__3));
v___f_94_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__4));
lean_inc_ref(v_toFunctor_86_);
v___f_95_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_95_, 0, v_toFunctor_86_);
v___f_96_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_96_, 0, v_toFunctor_86_);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___f_95_);
lean_ctor_set(v___x_97_, 1, v___f_96_);
v___f_98_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_98_, 0, v_toSeqRight_89_);
v___f_99_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_99_, 0, v_toSeqLeft_88_);
v___f_100_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_100_, 0, v_toSeq_87_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 4, v___f_98_);
lean_ctor_set(v___x_91_, 3, v___f_99_);
lean_ctor_set(v___x_91_, 2, v___f_100_);
lean_ctor_set(v___x_91_, 1, v___f_93_);
lean_ctor_set(v___x_91_, 0, v___x_97_);
v___x_102_ = v___x_91_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_97_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v___f_93_);
lean_ctor_set(v_reuseFailAlloc_110_, 2, v___f_100_);
lean_ctor_set(v_reuseFailAlloc_110_, 3, v___f_99_);
lean_ctor_set(v_reuseFailAlloc_110_, 4, v___f_98_);
v___x_102_ = v_reuseFailAlloc_110_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_104_; 
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v___f_94_);
lean_ctor_set(v___x_84_, 0, v___x_102_);
v___x_104_ = v___x_84_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v___f_94_);
v___x_104_ = v_reuseFailAlloc_109_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_2498__overap_107_; lean_object* v___x_108_; 
v___x_105_ = l_Lean_instInhabitedLocalContext_default;
v___x_106_ = l_instInhabitedOfMonad___redArg(v___x_104_, v___x_105_);
v___x_2498__overap_107_ = lean_panic_fn_borrowed(v___x_106_, v_msg_50_);
lean_dec(v___x_106_);
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
v___x_108_ = lean_apply_5(v___x_2498__overap_107_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, lean_box(0));
return v___x_108_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___boxed(lean_object* v_msg_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2(v_msg_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(lean_object* v_e_128_, lean_object* v___y_129_){
_start:
{
uint8_t v___x_131_; 
v___x_131_ = l_Lean_Expr_hasMVar(v_e_128_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; 
v___x_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_132_, 0, v_e_128_);
return v___x_132_;
}
else
{
lean_object* v___x_133_; lean_object* v_mctx_134_; lean_object* v___x_135_; lean_object* v_fst_136_; lean_object* v_snd_137_; lean_object* v___x_138_; lean_object* v_cache_139_; lean_object* v_zetaDeltaFVarIds_140_; lean_object* v_postponed_141_; lean_object* v_diag_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_151_; 
v___x_133_ = lean_st_ref_get(v___y_129_);
v_mctx_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc_ref(v_mctx_134_);
lean_dec(v___x_133_);
v___x_135_ = l_Lean_instantiateMVarsCore(v_mctx_134_, v_e_128_);
v_fst_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_fst_136_);
v_snd_137_ = lean_ctor_get(v___x_135_, 1);
lean_inc(v_snd_137_);
lean_dec_ref(v___x_135_);
v___x_138_ = lean_st_ref_take(v___y_129_);
v_cache_139_ = lean_ctor_get(v___x_138_, 1);
v_zetaDeltaFVarIds_140_ = lean_ctor_get(v___x_138_, 2);
v_postponed_141_ = lean_ctor_get(v___x_138_, 3);
v_diag_142_ = lean_ctor_get(v___x_138_, 4);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_151_ == 0)
{
lean_object* v_unused_152_; 
v_unused_152_ = lean_ctor_get(v___x_138_, 0);
lean_dec(v_unused_152_);
v___x_144_ = v___x_138_;
v_isShared_145_ = v_isSharedCheck_151_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_diag_142_);
lean_inc(v_postponed_141_);
lean_inc(v_zetaDeltaFVarIds_140_);
lean_inc(v_cache_139_);
lean_dec(v___x_138_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_151_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v_snd_137_);
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_snd_137_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_cache_139_);
lean_ctor_set(v_reuseFailAlloc_150_, 2, v_zetaDeltaFVarIds_140_);
lean_ctor_set(v_reuseFailAlloc_150_, 3, v_postponed_141_);
lean_ctor_set(v_reuseFailAlloc_150_, 4, v_diag_142_);
v___x_147_ = v_reuseFailAlloc_150_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_st_ref_set(v___y_129_, v___x_147_);
v___x_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_149_, 0, v_fst_136_);
return v___x_149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg___boxed(lean_object* v_e_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_e_153_, v___y_154_);
lean_dec(v___y_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg(lean_object* v_t_157_, lean_object* v_k_158_){
_start:
{
if (lean_obj_tag(v_t_157_) == 0)
{
lean_object* v_k_159_; lean_object* v_v_160_; lean_object* v_l_161_; lean_object* v_r_162_; uint8_t v___x_163_; 
v_k_159_ = lean_ctor_get(v_t_157_, 1);
v_v_160_ = lean_ctor_get(v_t_157_, 2);
v_l_161_ = lean_ctor_get(v_t_157_, 3);
v_r_162_ = lean_ctor_get(v_t_157_, 4);
v___x_163_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_158_, v_k_159_);
switch(v___x_163_)
{
case 0:
{
v_t_157_ = v_l_161_;
goto _start;
}
case 1:
{
lean_object* v___x_165_; 
lean_inc(v_v_160_);
v___x_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_165_, 0, v_v_160_);
return v___x_165_;
}
default: 
{
v_t_157_ = v_r_162_;
goto _start;
}
}
}
else
{
lean_object* v___x_167_; 
v___x_167_ = lean_box(0);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_t_168_, lean_object* v_k_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg(v_t_168_, v_k_169_);
lean_dec(v_k_169_);
lean_dec(v_t_168_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(lean_object* v_auxDeclToFullName_175_, lean_object* v_as_176_, size_t v_i_177_, size_t v_stop_178_, lean_object* v_b_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_a_186_; uint8_t v___x_190_; 
v___x_190_ = lean_usize_dec_eq(v_i_177_, v_stop_178_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
v___x_191_ = lean_array_uget_borrowed(v_as_176_, v_i_177_);
if (lean_obj_tag(v___x_191_) == 0)
{
v_a_186_ = v_b_179_;
goto v___jp_185_;
}
else
{
lean_object* v_val_192_; 
v_val_192_ = lean_ctor_get(v___x_191_, 0);
if (lean_obj_tag(v_val_192_) == 0)
{
uint8_t v_kind_193_; 
v_kind_193_ = lean_ctor_get_uint8(v_val_192_, sizeof(void*)*4 + 1);
if (v_kind_193_ == 2)
{
lean_object* v_fvarId_194_; lean_object* v_userName_195_; lean_object* v_type_196_; lean_object* v___x_197_; 
v_fvarId_194_ = lean_ctor_get(v_val_192_, 1);
v_userName_195_ = lean_ctor_get(v_val_192_, 2);
v_type_196_ = lean_ctor_get(v_val_192_, 3);
lean_inc_ref(v_type_196_);
v___x_197_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_type_196_, v___y_181_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; lean_object* v___x_199_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_a_198_);
lean_dec_ref(v___x_197_);
v___x_199_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg(v_auxDeclToFullName_175_, v_fvarId_194_);
if (lean_obj_tag(v___x_199_) == 1)
{
lean_object* v_val_200_; lean_object* v___x_201_; 
v_val_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_val_200_);
lean_dec_ref(v___x_199_);
lean_inc(v_userName_195_);
lean_inc(v_fvarId_194_);
v___x_201_ = l_Lean_LocalContext_mkAuxDecl(v_b_179_, v_fvarId_194_, v_userName_195_, v_a_198_, v_val_200_);
v_a_186_ = v___x_201_;
goto v___jp_185_;
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec(v___x_199_);
lean_dec(v_a_198_);
lean_dec_ref(v_b_179_);
v___x_202_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__0));
v___x_203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__1));
v___x_204_ = lean_unsigned_to_nat(635u);
v___x_205_ = lean_unsigned_to_nat(12u);
v___x_206_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__2));
v___x_207_ = 1;
lean_inc(v_userName_195_);
v___x_208_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_195_, v___x_207_);
v___x_209_ = lean_string_append(v___x_206_, v___x_208_);
lean_dec_ref(v___x_208_);
v___x_210_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__3));
v___x_211_ = lean_string_append(v___x_209_, v___x_210_);
v___x_212_ = l_mkPanicMessageWithDecl(v___x_202_, v___x_203_, v___x_204_, v___x_205_, v___x_211_);
lean_dec_ref(v___x_211_);
v___x_213_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2(v___x_212_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref(v___x_213_);
v_a_186_ = v_a_214_;
goto v___jp_185_;
}
else
{
return v___x_213_;
}
}
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
lean_dec_ref(v_b_179_);
v_a_215_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_197_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_197_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
else
{
lean_object* v_fvarId_223_; lean_object* v_userName_224_; lean_object* v_type_225_; uint8_t v_bi_226_; lean_object* v___x_227_; 
v_fvarId_223_ = lean_ctor_get(v_val_192_, 1);
v_userName_224_ = lean_ctor_get(v_val_192_, 2);
v_type_225_ = lean_ctor_get(v_val_192_, 3);
v_bi_226_ = lean_ctor_get_uint8(v_val_192_, sizeof(void*)*4);
lean_inc_ref(v_type_225_);
v___x_227_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_type_225_, v___y_181_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_229_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref(v___x_227_);
lean_inc(v_userName_224_);
lean_inc(v_fvarId_223_);
v___x_229_ = l_Lean_LocalContext_mkLocalDecl(v_b_179_, v_fvarId_223_, v_userName_224_, v_a_228_, v_bi_226_, v_kind_193_);
v_a_186_ = v___x_229_;
goto v___jp_185_;
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
lean_dec_ref(v_b_179_);
v_a_230_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_227_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_227_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
else
{
lean_object* v_fvarId_238_; lean_object* v_userName_239_; lean_object* v_type_240_; lean_object* v_value_241_; uint8_t v_nondep_242_; uint8_t v_kind_243_; lean_object* v___x_244_; 
v_fvarId_238_ = lean_ctor_get(v_val_192_, 1);
v_userName_239_ = lean_ctor_get(v_val_192_, 2);
v_type_240_ = lean_ctor_get(v_val_192_, 3);
v_value_241_ = lean_ctor_get(v_val_192_, 4);
v_nondep_242_ = lean_ctor_get_uint8(v_val_192_, sizeof(void*)*5);
v_kind_243_ = lean_ctor_get_uint8(v_val_192_, sizeof(void*)*5 + 1);
lean_inc_ref(v_type_240_);
v___x_244_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_type_240_, v___y_181_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_246_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_a_245_);
lean_dec_ref(v___x_244_);
lean_inc_ref(v_value_241_);
v___x_246_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_value_241_, v___y_181_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___x_248_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_a_247_);
lean_dec_ref(v___x_246_);
lean_inc(v_userName_239_);
lean_inc(v_fvarId_238_);
v___x_248_ = l_Lean_LocalContext_mkLetDecl(v_b_179_, v_fvarId_238_, v_userName_239_, v_a_245_, v_a_247_, v_nondep_242_, v_kind_243_);
v_a_186_ = v___x_248_;
goto v___jp_185_;
}
else
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
lean_dec(v_a_245_);
lean_dec_ref(v_b_179_);
v_a_249_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_246_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_246_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
else
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
lean_dec_ref(v_b_179_);
v_a_257_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_244_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_244_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
}
else
{
lean_object* v___x_265_; 
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v_b_179_);
return v___x_265_;
}
v___jp_185_:
{
size_t v___x_187_; size_t v___x_188_; 
v___x_187_ = ((size_t)1ULL);
v___x_188_ = lean_usize_add(v_i_177_, v___x_187_);
v_i_177_ = v___x_188_;
v_b_179_ = v_a_186_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___boxed(lean_object* v_auxDeclToFullName_266_, lean_object* v_as_267_, lean_object* v_i_268_, lean_object* v_stop_269_, lean_object* v_b_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
size_t v_i_boxed_276_; size_t v_stop_boxed_277_; lean_object* v_res_278_; 
v_i_boxed_276_ = lean_unbox_usize(v_i_268_);
lean_dec(v_i_268_);
v_stop_boxed_277_ = lean_unbox_usize(v_stop_269_);
lean_dec(v_stop_269_);
v_res_278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_266_, v_as_267_, v_i_boxed_276_, v_stop_boxed_277_, v_b_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec_ref(v_as_267_);
lean_dec(v_auxDeclToFullName_266_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(lean_object* v_auxDeclToFullName_279_, lean_object* v_x_280_, lean_object* v_x_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
if (lean_obj_tag(v_x_280_) == 0)
{
lean_object* v_cs_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_307_; 
v_cs_287_ = lean_ctor_get(v_x_280_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v_x_280_);
if (v_isSharedCheck_307_ == 0)
{
v___x_289_ = v_x_280_;
v_isShared_290_ = v_isSharedCheck_307_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_cs_287_);
lean_dec(v_x_280_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_307_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = lean_array_get_size(v_cs_287_);
v___x_293_ = lean_nat_dec_lt(v___x_291_, v___x_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_295_; 
lean_dec_ref(v_cs_287_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v_x_281_);
v___x_295_ = v___x_289_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_x_281_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
else
{
uint8_t v___x_297_; 
v___x_297_ = lean_nat_dec_le(v___x_292_, v___x_292_);
if (v___x_297_ == 0)
{
if (v___x_293_ == 0)
{
lean_object* v___x_299_; 
lean_dec_ref(v_cs_287_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v_x_281_);
v___x_299_ = v___x_289_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_x_281_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
else
{
size_t v___x_301_; size_t v___x_302_; lean_object* v___x_303_; 
lean_del_object(v___x_289_);
v___x_301_ = ((size_t)0ULL);
v___x_302_ = lean_usize_of_nat(v___x_292_);
v___x_303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_279_, v_cs_287_, v___x_301_, v___x_302_, v_x_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec_ref(v_cs_287_);
return v___x_303_;
}
}
else
{
size_t v___x_304_; size_t v___x_305_; lean_object* v___x_306_; 
lean_del_object(v___x_289_);
v___x_304_ = ((size_t)0ULL);
v___x_305_ = lean_usize_of_nat(v___x_292_);
v___x_306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_279_, v_cs_287_, v___x_304_, v___x_305_, v_x_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec_ref(v_cs_287_);
return v___x_306_;
}
}
}
}
else
{
lean_object* v_vs_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_328_; 
v_vs_308_ = lean_ctor_get(v_x_280_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v_x_280_);
if (v_isSharedCheck_328_ == 0)
{
v___x_310_ = v_x_280_;
v_isShared_311_ = v_isSharedCheck_328_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_vs_308_);
lean_dec(v_x_280_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_328_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = lean_array_get_size(v_vs_308_);
v___x_314_ = lean_nat_dec_lt(v___x_312_, v___x_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_316_; 
lean_dec_ref(v_vs_308_);
if (v_isShared_311_ == 0)
{
lean_ctor_set_tag(v___x_310_, 0);
lean_ctor_set(v___x_310_, 0, v_x_281_);
v___x_316_ = v___x_310_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_x_281_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
else
{
uint8_t v___x_318_; 
v___x_318_ = lean_nat_dec_le(v___x_313_, v___x_313_);
if (v___x_318_ == 0)
{
if (v___x_314_ == 0)
{
lean_object* v___x_320_; 
lean_dec_ref(v_vs_308_);
if (v_isShared_311_ == 0)
{
lean_ctor_set_tag(v___x_310_, 0);
lean_ctor_set(v___x_310_, 0, v_x_281_);
v___x_320_ = v___x_310_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_x_281_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
else
{
size_t v___x_322_; size_t v___x_323_; lean_object* v___x_324_; 
lean_del_object(v___x_310_);
v___x_322_ = ((size_t)0ULL);
v___x_323_ = lean_usize_of_nat(v___x_313_);
v___x_324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_279_, v_vs_308_, v___x_322_, v___x_323_, v_x_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec_ref(v_vs_308_);
return v___x_324_;
}
}
else
{
size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; 
lean_del_object(v___x_310_);
v___x_325_ = ((size_t)0ULL);
v___x_326_ = lean_usize_of_nat(v___x_313_);
v___x_327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_279_, v_vs_308_, v___x_325_, v___x_326_, v_x_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec_ref(v_vs_308_);
return v___x_327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(lean_object* v_auxDeclToFullName_329_, lean_object* v_as_330_, size_t v_i_331_, size_t v_stop_332_, lean_object* v_b_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
uint8_t v___x_339_; 
v___x_339_ = lean_usize_dec_eq(v_i_331_, v_stop_332_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_array_uget_borrowed(v_as_330_, v_i_331_);
lean_inc(v___x_340_);
v___x_341_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(v_auxDeclToFullName_329_, v___x_340_, v_b_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; size_t v___x_343_; size_t v___x_344_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
lean_dec_ref(v___x_341_);
v___x_343_ = ((size_t)1ULL);
v___x_344_ = lean_usize_add(v_i_331_, v___x_343_);
v_i_331_ = v___x_344_;
v_b_333_ = v_a_342_;
goto _start;
}
else
{
return v___x_341_;
}
}
else
{
lean_object* v___x_346_; 
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v_b_333_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9___boxed(lean_object* v_auxDeclToFullName_347_, lean_object* v_as_348_, lean_object* v_i_349_, lean_object* v_stop_350_, lean_object* v_b_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
size_t v_i_boxed_357_; size_t v_stop_boxed_358_; lean_object* v_res_359_; 
v_i_boxed_357_ = lean_unbox_usize(v_i_349_);
lean_dec(v_i_349_);
v_stop_boxed_358_ = lean_unbox_usize(v_stop_350_);
lean_dec(v_stop_350_);
v_res_359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_347_, v_as_348_, v_i_boxed_357_, v_stop_boxed_358_, v_b_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec_ref(v_as_348_);
lean_dec(v_auxDeclToFullName_347_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9___boxed(lean_object* v_auxDeclToFullName_360_, lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(v_auxDeclToFullName_360_, v_x_361_, v_x_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v_auxDeclToFullName_360_);
return v_res_368_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(lean_object* v_auxDeclToFullName_370_, lean_object* v_x_371_, size_t v_x_372_, size_t v_x_373_, lean_object* v_x_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
if (lean_obj_tag(v_x_371_) == 0)
{
lean_object* v_cs_380_; lean_object* v___x_381_; size_t v___x_382_; lean_object* v_j_383_; lean_object* v___x_384_; size_t v___x_385_; size_t v___x_386_; size_t v___x_387_; size_t v___x_388_; size_t v___x_389_; size_t v___x_390_; lean_object* v___x_391_; 
v_cs_380_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_cs_380_);
lean_dec_ref(v_x_371_);
v___x_381_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0);
v___x_382_ = lean_usize_shift_right(v_x_372_, v_x_373_);
v_j_383_ = lean_usize_to_nat(v___x_382_);
v___x_384_ = lean_array_get_borrowed(v___x_381_, v_cs_380_, v_j_383_);
v___x_385_ = ((size_t)1ULL);
v___x_386_ = lean_usize_shift_left(v___x_385_, v_x_373_);
v___x_387_ = lean_usize_sub(v___x_386_, v___x_385_);
v___x_388_ = lean_usize_land(v_x_372_, v___x_387_);
v___x_389_ = ((size_t)5ULL);
v___x_390_ = lean_usize_sub(v_x_373_, v___x_389_);
lean_inc(v___x_384_);
v___x_391_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(v_auxDeclToFullName_370_, v___x_384_, v___x_388_, v___x_390_, v_x_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_a_392_);
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = lean_nat_add(v_j_383_, v___x_393_);
lean_dec(v_j_383_);
v___x_395_ = lean_array_get_size(v_cs_380_);
v___x_396_ = lean_nat_dec_lt(v___x_394_, v___x_395_);
if (v___x_396_ == 0)
{
lean_dec(v___x_394_);
lean_dec(v_a_392_);
lean_dec_ref(v_cs_380_);
return v___x_391_;
}
else
{
uint8_t v___x_397_; 
v___x_397_ = lean_nat_dec_le(v___x_395_, v___x_395_);
if (v___x_397_ == 0)
{
if (v___x_396_ == 0)
{
lean_dec(v___x_394_);
lean_dec(v_a_392_);
lean_dec_ref(v_cs_380_);
return v___x_391_;
}
else
{
size_t v___x_398_; size_t v___x_399_; lean_object* v___x_400_; 
lean_dec_ref(v___x_391_);
v___x_398_ = lean_usize_of_nat(v___x_394_);
lean_dec(v___x_394_);
v___x_399_ = lean_usize_of_nat(v___x_395_);
v___x_400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_370_, v_cs_380_, v___x_398_, v___x_399_, v_a_392_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
lean_dec_ref(v_cs_380_);
return v___x_400_;
}
}
else
{
size_t v___x_401_; size_t v___x_402_; lean_object* v___x_403_; 
lean_dec_ref(v___x_391_);
v___x_401_ = lean_usize_of_nat(v___x_394_);
lean_dec(v___x_394_);
v___x_402_ = lean_usize_of_nat(v___x_395_);
v___x_403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_370_, v_cs_380_, v___x_401_, v___x_402_, v_a_392_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
lean_dec_ref(v_cs_380_);
return v___x_403_;
}
}
}
else
{
lean_dec(v_j_383_);
lean_dec_ref(v_cs_380_);
return v___x_391_;
}
}
else
{
lean_object* v_vs_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_424_; 
v_vs_404_ = lean_ctor_get(v_x_371_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v_x_371_);
if (v_isSharedCheck_424_ == 0)
{
v___x_406_ = v_x_371_;
v_isShared_407_ = v_isSharedCheck_424_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_vs_404_);
lean_dec(v_x_371_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_424_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_408_ = lean_usize_to_nat(v_x_372_);
v___x_409_ = lean_array_get_size(v_vs_404_);
v___x_410_ = lean_nat_dec_lt(v___x_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_412_; 
lean_dec(v___x_408_);
lean_dec_ref(v_vs_404_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 0);
lean_ctor_set(v___x_406_, 0, v_x_374_);
v___x_412_ = v___x_406_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_x_374_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
else
{
uint8_t v___x_414_; 
v___x_414_ = lean_nat_dec_le(v___x_409_, v___x_409_);
if (v___x_414_ == 0)
{
if (v___x_410_ == 0)
{
lean_object* v___x_416_; 
lean_dec(v___x_408_);
lean_dec_ref(v_vs_404_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 0);
lean_ctor_set(v___x_406_, 0, v_x_374_);
v___x_416_ = v___x_406_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_x_374_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
else
{
size_t v___x_418_; size_t v___x_419_; lean_object* v___x_420_; 
lean_del_object(v___x_406_);
v___x_418_ = lean_usize_of_nat(v___x_408_);
lean_dec(v___x_408_);
v___x_419_ = lean_usize_of_nat(v___x_409_);
v___x_420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_370_, v_vs_404_, v___x_418_, v___x_419_, v_x_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
lean_dec_ref(v_vs_404_);
return v___x_420_;
}
}
else
{
size_t v___x_421_; size_t v___x_422_; lean_object* v___x_423_; 
lean_del_object(v___x_406_);
v___x_421_ = lean_usize_of_nat(v___x_408_);
lean_dec(v___x_408_);
v___x_422_ = lean_usize_of_nat(v___x_409_);
v___x_423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_370_, v_vs_404_, v___x_421_, v___x_422_, v_x_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
lean_dec_ref(v_vs_404_);
return v___x_423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___boxed(lean_object* v_auxDeclToFullName_425_, lean_object* v_x_426_, lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v_x_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
size_t v_x_5752__boxed_435_; size_t v_x_5753__boxed_436_; lean_object* v_res_437_; 
v_x_5752__boxed_435_ = lean_unbox_usize(v_x_427_);
lean_dec(v_x_427_);
v_x_5753__boxed_436_ = lean_unbox_usize(v_x_428_);
lean_dec(v_x_428_);
v_res_437_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(v_auxDeclToFullName_425_, v_x_426_, v_x_5752__boxed_435_, v_x_5753__boxed_436_, v_x_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v_auxDeclToFullName_425_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5(lean_object* v_auxDeclToFullName_438_, lean_object* v_t_439_, lean_object* v_init_440_, lean_object* v_start_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_447_ = lean_unsigned_to_nat(0u);
v___x_448_ = lean_nat_dec_eq(v_start_441_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v_root_449_; lean_object* v_tail_450_; size_t v_shift_451_; lean_object* v_tailOff_452_; uint8_t v___x_453_; 
v_root_449_ = lean_ctor_get(v_t_439_, 0);
lean_inc_ref(v_root_449_);
v_tail_450_ = lean_ctor_get(v_t_439_, 1);
lean_inc_ref(v_tail_450_);
v_shift_451_ = lean_ctor_get_usize(v_t_439_, 4);
v_tailOff_452_ = lean_ctor_get(v_t_439_, 3);
lean_inc(v_tailOff_452_);
lean_dec_ref(v_t_439_);
v___x_453_ = lean_nat_dec_le(v_tailOff_452_, v_start_441_);
if (v___x_453_ == 0)
{
size_t v___x_454_; lean_object* v___x_455_; 
lean_dec(v_tailOff_452_);
v___x_454_ = lean_usize_of_nat(v_start_441_);
v___x_455_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(v_auxDeclToFullName_438_, v_root_449_, v___x_454_, v_shift_451_, v_init_440_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
v___x_457_ = lean_array_get_size(v_tail_450_);
v___x_458_ = lean_nat_dec_lt(v___x_447_, v___x_457_);
if (v___x_458_ == 0)
{
lean_dec(v_a_456_);
lean_dec_ref(v_tail_450_);
return v___x_455_;
}
else
{
uint8_t v___x_459_; 
v___x_459_ = lean_nat_dec_le(v___x_457_, v___x_457_);
if (v___x_459_ == 0)
{
if (v___x_458_ == 0)
{
lean_dec(v_a_456_);
lean_dec_ref(v_tail_450_);
return v___x_455_;
}
else
{
size_t v___x_460_; size_t v___x_461_; lean_object* v___x_462_; 
lean_dec_ref(v___x_455_);
v___x_460_ = ((size_t)0ULL);
v___x_461_ = lean_usize_of_nat(v___x_457_);
v___x_462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_438_, v_tail_450_, v___x_460_, v___x_461_, v_a_456_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec_ref(v_tail_450_);
return v___x_462_;
}
}
else
{
size_t v___x_463_; size_t v___x_464_; lean_object* v___x_465_; 
lean_dec_ref(v___x_455_);
v___x_463_ = ((size_t)0ULL);
v___x_464_ = lean_usize_of_nat(v___x_457_);
v___x_465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_438_, v_tail_450_, v___x_463_, v___x_464_, v_a_456_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec_ref(v_tail_450_);
return v___x_465_;
}
}
}
else
{
lean_dec_ref(v_tail_450_);
return v___x_455_;
}
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
lean_dec_ref(v_root_449_);
v___x_466_ = lean_nat_sub(v_start_441_, v_tailOff_452_);
lean_dec(v_tailOff_452_);
v___x_467_ = lean_array_get_size(v_tail_450_);
v___x_468_ = lean_nat_dec_lt(v___x_466_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; 
lean_dec(v___x_466_);
lean_dec_ref(v_tail_450_);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v_init_440_);
return v___x_469_;
}
else
{
uint8_t v___x_470_; 
v___x_470_ = lean_nat_dec_le(v___x_467_, v___x_467_);
if (v___x_470_ == 0)
{
if (v___x_468_ == 0)
{
lean_object* v___x_471_; 
lean_dec(v___x_466_);
lean_dec_ref(v_tail_450_);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v_init_440_);
return v___x_471_;
}
else
{
size_t v___x_472_; size_t v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_usize_of_nat(v___x_466_);
lean_dec(v___x_466_);
v___x_473_ = lean_usize_of_nat(v___x_467_);
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_438_, v_tail_450_, v___x_472_, v___x_473_, v_init_440_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec_ref(v_tail_450_);
return v___x_474_;
}
}
else
{
size_t v___x_475_; size_t v___x_476_; lean_object* v___x_477_; 
v___x_475_ = lean_usize_of_nat(v___x_466_);
lean_dec(v___x_466_);
v___x_476_ = lean_usize_of_nat(v___x_467_);
v___x_477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_438_, v_tail_450_, v___x_475_, v___x_476_, v_init_440_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec_ref(v_tail_450_);
return v___x_477_;
}
}
}
}
else
{
lean_object* v_root_478_; lean_object* v_tail_479_; lean_object* v___x_480_; 
v_root_478_ = lean_ctor_get(v_t_439_, 0);
lean_inc_ref(v_root_478_);
v_tail_479_ = lean_ctor_get(v_t_439_, 1);
lean_inc_ref(v_tail_479_);
lean_dec_ref(v_t_439_);
v___x_480_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(v_auxDeclToFullName_438_, v_root_478_, v_init_440_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_481_);
v___x_482_ = lean_array_get_size(v_tail_479_);
v___x_483_ = lean_nat_dec_lt(v___x_447_, v___x_482_);
if (v___x_483_ == 0)
{
lean_dec(v_a_481_);
lean_dec_ref(v_tail_479_);
return v___x_480_;
}
else
{
uint8_t v___x_484_; 
v___x_484_ = lean_nat_dec_le(v___x_482_, v___x_482_);
if (v___x_484_ == 0)
{
if (v___x_483_ == 0)
{
lean_dec(v_a_481_);
lean_dec_ref(v_tail_479_);
return v___x_480_;
}
else
{
size_t v___x_485_; size_t v___x_486_; lean_object* v___x_487_; 
lean_dec_ref(v___x_480_);
v___x_485_ = ((size_t)0ULL);
v___x_486_ = lean_usize_of_nat(v___x_482_);
v___x_487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_438_, v_tail_479_, v___x_485_, v___x_486_, v_a_481_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec_ref(v_tail_479_);
return v___x_487_;
}
}
else
{
size_t v___x_488_; size_t v___x_489_; lean_object* v___x_490_; 
lean_dec_ref(v___x_480_);
v___x_488_ = ((size_t)0ULL);
v___x_489_ = lean_usize_of_nat(v___x_482_);
v___x_490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_438_, v_tail_479_, v___x_488_, v___x_489_, v_a_481_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec_ref(v_tail_479_);
return v___x_490_;
}
}
}
else
{
lean_dec_ref(v_tail_479_);
return v___x_480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5___boxed(lean_object* v_auxDeclToFullName_491_, lean_object* v_t_492_, lean_object* v_init_493_, lean_object* v_start_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5(v_auxDeclToFullName_491_, v_t_492_, v_init_493_, v_start_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v_start_494_);
lean_dec(v_auxDeclToFullName_491_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3(lean_object* v_auxDeclToFullName_501_, lean_object* v_lctx_502_, lean_object* v_init_503_, lean_object* v_start_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_decls_510_; lean_object* v___x_511_; 
v_decls_510_ = lean_ctor_get(v_lctx_502_, 1);
lean_inc_ref(v_decls_510_);
lean_dec_ref(v_lctx_502_);
v___x_511_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5(v_auxDeclToFullName_501_, v_decls_510_, v_init_503_, v_start_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3___boxed(lean_object* v_auxDeclToFullName_512_, lean_object* v_lctx_513_, lean_object* v_init_514_, lean_object* v_start_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3(v_auxDeclToFullName_512_, v_lctx_513_, v_init_514_, v_start_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v_start_515_);
lean_dec(v_auxDeclToFullName_512_);
return v_res_521_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_522_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = lean_unsigned_to_nat(32u);
v___x_526_ = lean_mk_empty_array_with_capacity(v___x_525_);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_528_ = ((size_t)5ULL);
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = lean_unsigned_to_nat(32u);
v___x_531_ = lean_mk_empty_array_with_capacity(v___x_530_);
v___x_532_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2);
v___x_533_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v___x_531_);
lean_ctor_set(v___x_533_, 2, v___x_529_);
lean_ctor_set(v___x_533_, 3, v___x_529_);
lean_ctor_set_usize(v___x_533_, 4, v___x_528_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_534_ = lean_box(1);
v___x_535_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3);
v___x_536_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1);
v___x_537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___x_535_);
lean_ctor_set(v___x_537_, 2, v___x_534_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0(lean_object* v_lctx_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_auxDeclToFullName_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_auxDeclToFullName_544_ = lean_ctor_get(v_lctx_538_, 2);
lean_inc(v_auxDeclToFullName_544_);
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4);
v___x_547_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3(v_auxDeclToFullName_544_, v_lctx_538_, v___x_546_, v___x_545_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
lean_dec(v_auxDeclToFullName_544_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___boxed(lean_object* v_lctx_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0(v_lctx_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12___redArg(lean_object* v_x_555_, lean_object* v_x_556_, lean_object* v_x_557_, lean_object* v_x_558_){
_start:
{
lean_object* v_ks_559_; lean_object* v_vs_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_584_; 
v_ks_559_ = lean_ctor_get(v_x_555_, 0);
v_vs_560_ = lean_ctor_get(v_x_555_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_x_555_);
if (v_isSharedCheck_584_ == 0)
{
v___x_562_ = v_x_555_;
v_isShared_563_ = v_isSharedCheck_584_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_vs_560_);
lean_inc(v_ks_559_);
lean_dec(v_x_555_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_584_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_564_ = lean_array_get_size(v_ks_559_);
v___x_565_ = lean_nat_dec_lt(v_x_556_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
lean_dec(v_x_556_);
v___x_566_ = lean_array_push(v_ks_559_, v_x_557_);
v___x_567_ = lean_array_push(v_vs_560_, v_x_558_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v___x_567_);
lean_ctor_set(v___x_562_, 0, v___x_566_);
v___x_569_ = v___x_562_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
else
{
lean_object* v_k_x27_571_; uint8_t v___x_572_; 
v_k_x27_571_ = lean_array_fget_borrowed(v_ks_559_, v_x_556_);
v___x_572_ = l_Lean_instBEqMVarId_beq(v_x_557_, v_k_x27_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_574_; 
if (v_isShared_563_ == 0)
{
v___x_574_ = v___x_562_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_ks_559_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_vs_560_);
v___x_574_ = v_reuseFailAlloc_578_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_unsigned_to_nat(1u);
v___x_576_ = lean_nat_add(v_x_556_, v___x_575_);
lean_dec(v_x_556_);
v_x_555_ = v___x_574_;
v_x_556_ = v___x_576_;
goto _start;
}
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_579_ = lean_array_fset(v_ks_559_, v_x_556_, v_x_557_);
v___x_580_ = lean_array_fset(v_vs_560_, v_x_556_, v_x_558_);
lean_dec(v_x_556_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v___x_580_);
lean_ctor_set(v___x_562_, 0, v___x_579_);
v___x_582_ = v___x_562_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8___redArg(lean_object* v_n_585_, lean_object* v_k_586_, lean_object* v_v_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12___redArg(v_n_585_, v___x_588_, v_k_586_, v_v_587_);
return v___x_589_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0(void){
_start:
{
size_t v___x_590_; size_t v___x_591_; size_t v___x_592_; 
v___x_590_ = ((size_t)5ULL);
v___x_591_ = ((size_t)1ULL);
v___x_592_ = lean_usize_shift_left(v___x_591_, v___x_590_);
return v___x_592_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_593_; size_t v___x_594_; size_t v___x_595_; 
v___x_593_ = ((size_t)1ULL);
v___x_594_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0);
v___x_595_ = lean_usize_sub(v___x_594_, v___x_593_);
return v___x_595_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(lean_object* v_x_597_, size_t v_x_598_, size_t v_x_599_, lean_object* v_x_600_, lean_object* v_x_601_){
_start:
{
if (lean_obj_tag(v_x_597_) == 0)
{
lean_object* v_es_602_; size_t v___x_603_; size_t v___x_604_; size_t v___x_605_; size_t v___x_606_; lean_object* v_j_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v_es_602_ = lean_ctor_get(v_x_597_, 0);
v___x_603_ = ((size_t)5ULL);
v___x_604_ = ((size_t)1ULL);
v___x_605_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__1);
v___x_606_ = lean_usize_land(v_x_598_, v___x_605_);
v_j_607_ = lean_usize_to_nat(v___x_606_);
v___x_608_ = lean_array_get_size(v_es_602_);
v___x_609_ = lean_nat_dec_lt(v_j_607_, v___x_608_);
if (v___x_609_ == 0)
{
lean_dec(v_j_607_);
lean_dec(v_x_601_);
lean_dec(v_x_600_);
return v_x_597_;
}
else
{
lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_646_; 
lean_inc_ref(v_es_602_);
v_isSharedCheck_646_ = !lean_is_exclusive(v_x_597_);
if (v_isSharedCheck_646_ == 0)
{
lean_object* v_unused_647_; 
v_unused_647_ = lean_ctor_get(v_x_597_, 0);
lean_dec(v_unused_647_);
v___x_611_ = v_x_597_;
v_isShared_612_ = v_isSharedCheck_646_;
goto v_resetjp_610_;
}
else
{
lean_dec(v_x_597_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_646_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v_v_613_; lean_object* v___x_614_; lean_object* v_xs_x27_615_; lean_object* v___y_617_; 
v_v_613_ = lean_array_fget(v_es_602_, v_j_607_);
v___x_614_ = lean_box(0);
v_xs_x27_615_ = lean_array_fset(v_es_602_, v_j_607_, v___x_614_);
switch(lean_obj_tag(v_v_613_))
{
case 0:
{
lean_object* v_key_622_; lean_object* v_val_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_633_; 
v_key_622_ = lean_ctor_get(v_v_613_, 0);
v_val_623_ = lean_ctor_get(v_v_613_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_v_613_);
if (v_isSharedCheck_633_ == 0)
{
v___x_625_ = v_v_613_;
v_isShared_626_ = v_isSharedCheck_633_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_val_623_);
lean_inc(v_key_622_);
lean_dec(v_v_613_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_633_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
uint8_t v___x_627_; 
v___x_627_ = l_Lean_instBEqMVarId_beq(v_x_600_, v_key_622_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
lean_del_object(v___x_625_);
v___x_628_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_622_, v_val_623_, v_x_600_, v_x_601_);
v___x_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
v___y_617_ = v___x_629_;
goto v___jp_616_;
}
else
{
lean_object* v___x_631_; 
lean_dec(v_val_623_);
lean_dec(v_key_622_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v_x_601_);
lean_ctor_set(v___x_625_, 0, v_x_600_);
v___x_631_ = v___x_625_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_x_600_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_x_601_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
v___y_617_ = v___x_631_;
goto v___jp_616_;
}
}
}
}
case 1:
{
lean_object* v_node_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_644_; 
v_node_634_ = lean_ctor_get(v_v_613_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v_v_613_);
if (v_isSharedCheck_644_ == 0)
{
v___x_636_ = v_v_613_;
v_isShared_637_ = v_isSharedCheck_644_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_node_634_);
lean_dec(v_v_613_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_644_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
size_t v___x_638_; size_t v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_638_ = lean_usize_shift_right(v_x_598_, v___x_603_);
v___x_639_ = lean_usize_add(v_x_599_, v___x_604_);
v___x_640_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_node_634_, v___x_638_, v___x_639_, v_x_600_, v_x_601_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_640_);
v___x_642_ = v___x_636_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
v___y_617_ = v___x_642_;
goto v___jp_616_;
}
}
}
default: 
{
lean_object* v___x_645_; 
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v_x_600_);
lean_ctor_set(v___x_645_, 1, v_x_601_);
v___y_617_ = v___x_645_;
goto v___jp_616_;
}
}
v___jp_616_:
{
lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_618_ = lean_array_fset(v_xs_x27_615_, v_j_607_, v___y_617_);
lean_dec(v_j_607_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_618_);
v___x_620_ = v___x_611_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
}
else
{
lean_object* v_ks_648_; lean_object* v_vs_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_669_; 
v_ks_648_ = lean_ctor_get(v_x_597_, 0);
v_vs_649_ = lean_ctor_get(v_x_597_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v_x_597_);
if (v_isSharedCheck_669_ == 0)
{
v___x_651_ = v_x_597_;
v_isShared_652_ = v_isSharedCheck_669_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_vs_649_);
lean_inc(v_ks_648_);
lean_dec(v_x_597_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_669_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_ks_648_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_vs_649_);
v___x_654_ = v_reuseFailAlloc_668_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v_newNode_655_; uint8_t v___y_657_; size_t v___x_663_; uint8_t v___x_664_; 
v_newNode_655_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8___redArg(v___x_654_, v_x_600_, v_x_601_);
v___x_663_ = ((size_t)7ULL);
v___x_664_ = lean_usize_dec_le(v___x_663_, v_x_599_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_665_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_655_);
v___x_666_ = lean_unsigned_to_nat(4u);
v___x_667_ = lean_nat_dec_lt(v___x_665_, v___x_666_);
lean_dec(v___x_665_);
v___y_657_ = v___x_667_;
goto v___jp_656_;
}
else
{
v___y_657_ = v___x_664_;
goto v___jp_656_;
}
v___jp_656_:
{
if (v___y_657_ == 0)
{
lean_object* v_ks_658_; lean_object* v_vs_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v_ks_658_ = lean_ctor_get(v_newNode_655_, 0);
lean_inc_ref(v_ks_658_);
v_vs_659_ = lean_ctor_get(v_newNode_655_, 1);
lean_inc_ref(v_vs_659_);
lean_dec_ref(v_newNode_655_);
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__2);
v___x_662_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(v_x_599_, v_ks_658_, v_vs_659_, v___x_660_, v___x_661_);
lean_dec_ref(v_vs_659_);
lean_dec_ref(v_ks_658_);
return v___x_662_;
}
else
{
return v_newNode_655_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(size_t v_depth_670_, lean_object* v_keys_671_, lean_object* v_vals_672_, lean_object* v_i_673_, lean_object* v_entries_674_){
_start:
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = lean_array_get_size(v_keys_671_);
v___x_676_ = lean_nat_dec_lt(v_i_673_, v___x_675_);
if (v___x_676_ == 0)
{
lean_dec(v_i_673_);
return v_entries_674_;
}
else
{
lean_object* v_k_677_; lean_object* v_v_678_; uint64_t v___x_679_; size_t v_h_680_; size_t v___x_681_; lean_object* v___x_682_; size_t v___x_683_; size_t v___x_684_; size_t v___x_685_; size_t v_h_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_k_677_ = lean_array_fget_borrowed(v_keys_671_, v_i_673_);
v_v_678_ = lean_array_fget_borrowed(v_vals_672_, v_i_673_);
v___x_679_ = l_Lean_instHashableMVarId_hash(v_k_677_);
v_h_680_ = lean_uint64_to_usize(v___x_679_);
v___x_681_ = ((size_t)5ULL);
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = ((size_t)1ULL);
v___x_684_ = lean_usize_sub(v_depth_670_, v___x_683_);
v___x_685_ = lean_usize_mul(v___x_681_, v___x_684_);
v_h_686_ = lean_usize_shift_right(v_h_680_, v___x_685_);
v___x_687_ = lean_nat_add(v_i_673_, v___x_682_);
lean_dec(v_i_673_);
lean_inc(v_v_678_);
lean_inc(v_k_677_);
v___x_688_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_entries_674_, v_h_686_, v_depth_670_, v_k_677_, v_v_678_);
v_i_673_ = v___x_687_;
v_entries_674_ = v___x_688_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg___boxed(lean_object* v_depth_690_, lean_object* v_keys_691_, lean_object* v_vals_692_, lean_object* v_i_693_, lean_object* v_entries_694_){
_start:
{
size_t v_depth_boxed_695_; lean_object* v_res_696_; 
v_depth_boxed_695_ = lean_unbox_usize(v_depth_690_);
lean_dec(v_depth_690_);
v_res_696_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(v_depth_boxed_695_, v_keys_691_, v_vals_692_, v_i_693_, v_entries_694_);
lean_dec_ref(v_vals_692_);
lean_dec_ref(v_keys_691_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_x_697_, lean_object* v_x_698_, lean_object* v_x_699_, lean_object* v_x_700_, lean_object* v_x_701_){
_start:
{
size_t v_x_6138__boxed_702_; size_t v_x_6139__boxed_703_; lean_object* v_res_704_; 
v_x_6138__boxed_702_ = lean_unbox_usize(v_x_698_);
lean_dec(v_x_698_);
v_x_6139__boxed_703_ = lean_unbox_usize(v_x_699_);
lean_dec(v_x_699_);
v_res_704_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_x_697_, v_x_6138__boxed_702_, v_x_6139__boxed_703_, v_x_700_, v_x_701_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2___redArg(lean_object* v_x_705_, lean_object* v_x_706_, lean_object* v_x_707_){
_start:
{
uint64_t v___x_708_; size_t v___x_709_; size_t v___x_710_; lean_object* v___x_711_; 
v___x_708_ = l_Lean_instHashableMVarId_hash(v_x_706_);
v___x_709_ = lean_uint64_to_usize(v___x_708_);
v___x_710_ = ((size_t)1ULL);
v___x_711_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_x_705_, v___x_709_, v___x_710_, v_x_706_, v_x_707_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0(lean_object* v_mvarId_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; lean_object* v_mctx_719_; lean_object* v_mvarDecl_720_; lean_object* v_userName_721_; lean_object* v_lctx_722_; lean_object* v_type_723_; lean_object* v_depth_724_; lean_object* v_localInstances_725_; uint8_t v_kind_726_; lean_object* v_numScopeArgs_727_; lean_object* v_index_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_791_; 
v___x_718_ = lean_st_ref_get(v___y_714_);
v_mctx_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc_ref(v_mctx_719_);
lean_dec(v___x_718_);
lean_inc(v_mvarId_712_);
v_mvarDecl_720_ = l_Lean_MetavarContext_getDecl(v_mctx_719_, v_mvarId_712_);
v_userName_721_ = lean_ctor_get(v_mvarDecl_720_, 0);
v_lctx_722_ = lean_ctor_get(v_mvarDecl_720_, 1);
v_type_723_ = lean_ctor_get(v_mvarDecl_720_, 2);
v_depth_724_ = lean_ctor_get(v_mvarDecl_720_, 3);
v_localInstances_725_ = lean_ctor_get(v_mvarDecl_720_, 4);
v_kind_726_ = lean_ctor_get_uint8(v_mvarDecl_720_, sizeof(void*)*7);
v_numScopeArgs_727_ = lean_ctor_get(v_mvarDecl_720_, 5);
v_index_728_ = lean_ctor_get(v_mvarDecl_720_, 6);
v_isSharedCheck_791_ = !lean_is_exclusive(v_mvarDecl_720_);
if (v_isSharedCheck_791_ == 0)
{
v___x_730_ = v_mvarDecl_720_;
v_isShared_731_ = v_isSharedCheck_791_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_index_728_);
lean_inc(v_numScopeArgs_727_);
lean_inc(v_localInstances_725_);
lean_inc(v_depth_724_);
lean_inc(v_type_723_);
lean_inc(v_lctx_722_);
lean_inc(v_userName_721_);
lean_dec(v_mvarDecl_720_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_791_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0(v_lctx_722_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_782_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref(v___x_732_);
v___x_734_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_type_723_, v___y_714_);
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_782_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_782_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_782_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v_fst_741_; lean_object* v_snd_742_; lean_object* v___x_743_; lean_object* v_mctx_744_; lean_object* v_cache_745_; lean_object* v_zetaDeltaFVarIds_746_; lean_object* v_postponed_747_; lean_object* v_diag_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_781_; 
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v_a_733_);
lean_ctor_set(v___x_739_, 1, v_a_735_);
v___x_740_ = lean_sharecommon_quick(v___x_739_);
lean_dec_ref(v___x_739_);
v_fst_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_fst_741_);
v_snd_742_ = lean_ctor_get(v___x_740_, 1);
lean_inc(v_snd_742_);
lean_dec(v___x_740_);
v___x_743_ = lean_st_ref_take(v___y_714_);
v_mctx_744_ = lean_ctor_get(v___x_743_, 0);
v_cache_745_ = lean_ctor_get(v___x_743_, 1);
v_zetaDeltaFVarIds_746_ = lean_ctor_get(v___x_743_, 2);
v_postponed_747_ = lean_ctor_get(v___x_743_, 3);
v_diag_748_ = lean_ctor_get(v___x_743_, 4);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_781_ == 0)
{
v___x_750_ = v___x_743_;
v_isShared_751_ = v_isSharedCheck_781_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_diag_748_);
lean_inc(v_postponed_747_);
lean_inc(v_zetaDeltaFVarIds_746_);
lean_inc(v_cache_745_);
lean_inc(v_mctx_744_);
lean_dec(v___x_743_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_781_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v_depth_752_; lean_object* v_levelAssignDepth_753_; lean_object* v_lmvarCounter_754_; lean_object* v_mvarCounter_755_; lean_object* v_lDecls_756_; lean_object* v_decls_757_; lean_object* v_userNames_758_; lean_object* v_lAssignment_759_; lean_object* v_eAssignment_760_; lean_object* v_dAssignment_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_780_; 
v_depth_752_ = lean_ctor_get(v_mctx_744_, 0);
v_levelAssignDepth_753_ = lean_ctor_get(v_mctx_744_, 1);
v_lmvarCounter_754_ = lean_ctor_get(v_mctx_744_, 2);
v_mvarCounter_755_ = lean_ctor_get(v_mctx_744_, 3);
v_lDecls_756_ = lean_ctor_get(v_mctx_744_, 4);
v_decls_757_ = lean_ctor_get(v_mctx_744_, 5);
v_userNames_758_ = lean_ctor_get(v_mctx_744_, 6);
v_lAssignment_759_ = lean_ctor_get(v_mctx_744_, 7);
v_eAssignment_760_ = lean_ctor_get(v_mctx_744_, 8);
v_dAssignment_761_ = lean_ctor_get(v_mctx_744_, 9);
v_isSharedCheck_780_ = !lean_is_exclusive(v_mctx_744_);
if (v_isSharedCheck_780_ == 0)
{
v___x_763_ = v_mctx_744_;
v_isShared_764_ = v_isSharedCheck_780_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_dAssignment_761_);
lean_inc(v_eAssignment_760_);
lean_inc(v_lAssignment_759_);
lean_inc(v_userNames_758_);
lean_inc(v_decls_757_);
lean_inc(v_lDecls_756_);
lean_inc(v_mvarCounter_755_);
lean_inc(v_lmvarCounter_754_);
lean_inc(v_levelAssignDepth_753_);
lean_inc(v_depth_752_);
lean_dec(v_mctx_744_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_780_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 2, v_snd_742_);
lean_ctor_set(v___x_730_, 1, v_fst_741_);
v___x_766_ = v___x_730_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_userName_721_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_fst_741_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_snd_742_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v_depth_724_);
lean_ctor_set(v_reuseFailAlloc_779_, 4, v_localInstances_725_);
lean_ctor_set(v_reuseFailAlloc_779_, 5, v_numScopeArgs_727_);
lean_ctor_set(v_reuseFailAlloc_779_, 6, v_index_728_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, sizeof(void*)*7, v_kind_726_);
v___x_766_ = v_reuseFailAlloc_779_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_767_ = l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2___redArg(v_decls_757_, v_mvarId_712_, v___x_766_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 5, v___x_767_);
v___x_769_ = v___x_763_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_depth_752_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_levelAssignDepth_753_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v_lmvarCounter_754_);
lean_ctor_set(v_reuseFailAlloc_778_, 3, v_mvarCounter_755_);
lean_ctor_set(v_reuseFailAlloc_778_, 4, v_lDecls_756_);
lean_ctor_set(v_reuseFailAlloc_778_, 5, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_778_, 6, v_userNames_758_);
lean_ctor_set(v_reuseFailAlloc_778_, 7, v_lAssignment_759_);
lean_ctor_set(v_reuseFailAlloc_778_, 8, v_eAssignment_760_);
lean_ctor_set(v_reuseFailAlloc_778_, 9, v_dAssignment_761_);
v___x_769_ = v_reuseFailAlloc_778_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_771_; 
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_769_);
v___x_771_ = v___x_750_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_cache_745_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_zetaDeltaFVarIds_746_);
lean_ctor_set(v_reuseFailAlloc_777_, 3, v_postponed_747_);
lean_ctor_set(v_reuseFailAlloc_777_, 4, v_diag_748_);
v___x_771_ = v_reuseFailAlloc_777_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_772_ = lean_st_ref_set(v___y_714_, v___x_771_);
v___x_773_ = lean_box(0);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_773_);
v___x_775_ = v___x_737_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
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
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_del_object(v___x_730_);
lean_dec(v_index_728_);
lean_dec(v_numScopeArgs_727_);
lean_dec_ref(v_localInstances_725_);
lean_dec(v_depth_724_);
lean_dec_ref(v_type_723_);
lean_dec(v_userName_721_);
lean_dec(v_mvarId_712_);
v_a_783_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_732_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_732_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0___boxed(lean_object* v_mvarId_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0(v_mvarId_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic(lean_object* v_mvarId_799_, lean_object* v_tacticCode_800_, lean_object* v_ctx_801_, lean_object* v_s_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___x_808_; 
lean_inc(v_mvarId_799_);
v___x_808_ = l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0(v_mvarId_799_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v___f_809_; lean_object* v___x_810_; uint8_t v___x_811_; lean_object* v___x_812_; lean_object* v___f_813_; lean_object* v___x_814_; 
lean_dec_ref(v___x_808_);
v___f_809_ = lean_alloc_closure((void*)(l_Lean_Elab_runTactic___lam__0___boxed), 10, 1);
lean_closure_set(v___f_809_, 0, v_tacticCode_800_);
v___x_810_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_810_, 0, v_mvarId_799_);
lean_closure_set(v___x_810_, 1, v___f_809_);
v___x_811_ = 1;
v___x_812_ = lean_box(v___x_811_);
v___f_813_ = lean_alloc_closure((void*)(l_Lean_Elab_runTactic___lam__1___boxed), 9, 2);
lean_closure_set(v___f_813_, 0, v___x_810_);
lean_closure_set(v___f_813_, 1, v___x_812_);
v___x_814_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_813_, v_ctx_801_, v_s_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
return v___x_814_;
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec_ref(v_s_802_);
lean_dec_ref(v_ctx_801_);
lean_dec(v_tacticCode_800_);
lean_dec(v_mvarId_799_);
v_a_815_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_808_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_808_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic___boxed(lean_object* v_mvarId_823_, lean_object* v_tacticCode_824_, lean_object* v_ctx_825_, lean_object* v_s_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_Elab_runTactic(v_mvarId_823_, v_tacticCode_824_, v_ctx_825_, v_s_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1(lean_object* v_e_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_e_833_, v___y_835_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___boxed(lean_object* v_e_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1(v_e_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2(lean_object* v_00_u03b2_847_, lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2___redArg(v_x_848_, v_x_849_, v_x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1(lean_object* v_00_u03b4_852_, lean_object* v_t_853_, lean_object* v_k_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg(v_t_853_, v_k_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b4_856_, lean_object* v_t_857_, lean_object* v_k_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1(v_00_u03b4_856_, v_t_857_, v_k_858_);
lean_dec(v_k_858_);
lean_dec(v_t_857_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_860_, lean_object* v_x_861_, size_t v_x_862_, size_t v_x_863_, lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_x_861_, v_x_862_, v_x_863_, v_x_864_, v_x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_867_, lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_x_870_, lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
size_t v_x_6489__boxed_873_; size_t v_x_6490__boxed_874_; lean_object* v_res_875_; 
v_x_6489__boxed_873_ = lean_unbox_usize(v_x_869_);
lean_dec(v_x_869_);
v_x_6490__boxed_874_ = lean_unbox_usize(v_x_870_);
lean_dec(v_x_870_);
v_res_875_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6(v_00_u03b2_867_, v_x_868_, v_x_6489__boxed_873_, v_x_6490__boxed_874_, v_x_871_, v_x_872_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8(lean_object* v_00_u03b2_876_, lean_object* v_n_877_, lean_object* v_k_878_, lean_object* v_v_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8___redArg(v_n_877_, v_k_878_, v_v_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9(lean_object* v_00_u03b2_881_, size_t v_depth_882_, lean_object* v_keys_883_, lean_object* v_vals_884_, lean_object* v_heq_885_, lean_object* v_i_886_, lean_object* v_entries_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(v_depth_882_, v_keys_883_, v_vals_884_, v_i_886_, v_entries_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___boxed(lean_object* v_00_u03b2_889_, lean_object* v_depth_890_, lean_object* v_keys_891_, lean_object* v_vals_892_, lean_object* v_heq_893_, lean_object* v_i_894_, lean_object* v_entries_895_){
_start:
{
size_t v_depth_boxed_896_; lean_object* v_res_897_; 
v_depth_boxed_896_ = lean_unbox_usize(v_depth_890_);
lean_dec(v_depth_890_);
v_res_897_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9(v_00_u03b2_889_, v_depth_boxed_896_, v_keys_891_, v_vals_892_, v_heq_893_, v_i_894_, v_entries_895_);
lean_dec_ref(v_vals_892_);
lean_dec_ref(v_keys_891_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12(lean_object* v_00_u03b2_898_, lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_x_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12___redArg(v_x_899_, v_x_900_, v_x_901_, v_x_902_);
return v___x_903_;
}
}
lean_object* runtime_initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Meta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_SyntheticMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Meta(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Meta(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_SyntheticMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Meta(builtin);
}
#ifdef __cplusplus
}
#endif
