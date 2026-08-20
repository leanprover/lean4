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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0;
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
lean_dec_ref_known(v___x_11_, 1);
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
uint8_t v___x_4825__boxed_43_; lean_object* v_res_44_; 
v___x_4825__boxed_43_ = lean_unbox(v___x_35_);
v_res_44_ = l_Lean_Elab_runTactic___lam__1(v___x_34_, v___x_4825__boxed_43_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
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
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_2563__overap_107_; lean_object* v___x_108_; 
v___x_105_ = l_Lean_instInhabitedLocalContext_default;
v___x_106_ = l_instInhabitedOfMonad___redArg(v___x_104_, v___x_105_);
v___x_2563__overap_107_ = lean_panic_fn_borrowed(v___x_106_, v_msg_50_);
lean_dec(v___x_106_);
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
v___x_108_ = lean_apply_5(v___x_2563__overap_107_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, lean_box(0));
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
v___x_148_ = lean_st_ref_put(v___y_129_, v___x_147_);
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
lean_dec_ref_known(v___x_197_, 1);
v___x_199_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg(v_auxDeclToFullName_175_, v_fvarId_194_);
if (lean_obj_tag(v___x_199_) == 1)
{
lean_object* v_val_200_; lean_object* v___x_201_; 
v_val_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_val_200_);
lean_dec_ref_known(v___x_199_, 1);
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
v___x_204_ = lean_unsigned_to_nat(660u);
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
lean_dec_ref_known(v___x_213_, 1);
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
lean_dec_ref_known(v___x_227_, 1);
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
lean_dec_ref_known(v___x_244_, 1);
lean_inc_ref(v_value_241_);
v___x_246_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_value_241_, v___y_181_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___x_248_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_a_247_);
lean_dec_ref_known(v___x_246_, 1);
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
lean_object* v_cs_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_300_; 
v_cs_287_ = lean_ctor_get(v_x_280_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v_x_280_);
if (v_isSharedCheck_300_ == 0)
{
v___x_289_ = v_x_280_;
v_isShared_290_ = v_isSharedCheck_300_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_cs_287_);
lean_dec(v_x_280_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_300_;
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
size_t v___x_297_; size_t v___x_298_; lean_object* v___x_299_; 
lean_del_object(v___x_289_);
v___x_297_ = ((size_t)0ULL);
v___x_298_ = lean_usize_of_nat(v___x_292_);
v___x_299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_279_, v_cs_287_, v___x_297_, v___x_298_, v_x_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec_ref(v_cs_287_);
return v___x_299_;
}
}
}
else
{
lean_object* v_vs_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_314_; 
v_vs_301_ = lean_ctor_get(v_x_280_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v_x_280_);
if (v_isSharedCheck_314_ == 0)
{
v___x_303_ = v_x_280_;
v_isShared_304_ = v_isSharedCheck_314_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_vs_301_);
lean_dec(v_x_280_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_314_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = lean_array_get_size(v_vs_301_);
v___x_307_ = lean_nat_dec_lt(v___x_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_309_; 
lean_dec_ref(v_vs_301_);
if (v_isShared_304_ == 0)
{
lean_ctor_set_tag(v___x_303_, 0);
lean_ctor_set(v___x_303_, 0, v_x_281_);
v___x_309_ = v___x_303_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_x_281_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
else
{
size_t v___x_311_; size_t v___x_312_; lean_object* v___x_313_; 
lean_del_object(v___x_303_);
v___x_311_ = ((size_t)0ULL);
v___x_312_ = lean_usize_of_nat(v___x_306_);
v___x_313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_279_, v_vs_301_, v___x_311_, v___x_312_, v_x_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec_ref(v_vs_301_);
return v___x_313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(lean_object* v_auxDeclToFullName_315_, lean_object* v_as_316_, size_t v_i_317_, size_t v_stop_318_, lean_object* v_b_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
uint8_t v___x_325_; 
v___x_325_ = lean_usize_dec_eq(v_i_317_, v_stop_318_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_array_uget_borrowed(v_as_316_, v_i_317_);
lean_inc(v___x_326_);
v___x_327_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(v_auxDeclToFullName_315_, v___x_326_, v_b_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; size_t v___x_329_; size_t v___x_330_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_328_);
lean_dec_ref_known(v___x_327_, 1);
v___x_329_ = ((size_t)1ULL);
v___x_330_ = lean_usize_add(v_i_317_, v___x_329_);
v_i_317_ = v___x_330_;
v_b_319_ = v_a_328_;
goto _start;
}
else
{
return v___x_327_;
}
}
else
{
lean_object* v___x_332_; 
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v_b_319_);
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9___boxed(lean_object* v_auxDeclToFullName_333_, lean_object* v_as_334_, lean_object* v_i_335_, lean_object* v_stop_336_, lean_object* v_b_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
size_t v_i_boxed_343_; size_t v_stop_boxed_344_; lean_object* v_res_345_; 
v_i_boxed_343_ = lean_unbox_usize(v_i_335_);
lean_dec(v_i_335_);
v_stop_boxed_344_ = lean_unbox_usize(v_stop_336_);
lean_dec(v_stop_336_);
v_res_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_333_, v_as_334_, v_i_boxed_343_, v_stop_boxed_344_, v_b_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec_ref(v_as_334_);
lean_dec(v_auxDeclToFullName_333_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9___boxed(lean_object* v_auxDeclToFullName_346_, lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(v_auxDeclToFullName_346_, v_x_347_, v_x_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v_auxDeclToFullName_346_);
return v_res_354_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(lean_object* v_auxDeclToFullName_356_, lean_object* v_x_357_, size_t v_x_358_, size_t v_x_359_, lean_object* v_x_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
if (lean_obj_tag(v_x_357_) == 0)
{
lean_object* v_cs_366_; lean_object* v___x_367_; size_t v___x_368_; lean_object* v_j_369_; lean_object* v___x_370_; size_t v___x_371_; size_t v___x_372_; size_t v___x_373_; size_t v___x_374_; size_t v___x_375_; size_t v___x_376_; lean_object* v___x_377_; 
v_cs_366_ = lean_ctor_get(v_x_357_, 0);
lean_inc_ref(v_cs_366_);
lean_dec_ref_known(v_x_357_, 1);
v___x_367_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0);
v___x_368_ = lean_usize_shift_right(v_x_358_, v_x_359_);
v_j_369_ = lean_usize_to_nat(v___x_368_);
v___x_370_ = lean_array_get_borrowed(v___x_367_, v_cs_366_, v_j_369_);
v___x_371_ = ((size_t)1ULL);
v___x_372_ = lean_usize_shift_left(v___x_371_, v_x_359_);
v___x_373_ = lean_usize_sub(v___x_372_, v___x_371_);
v___x_374_ = lean_usize_land(v_x_358_, v___x_373_);
v___x_375_ = ((size_t)5ULL);
v___x_376_ = lean_usize_sub(v_x_359_, v___x_375_);
lean_inc(v___x_370_);
v___x_377_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(v_auxDeclToFullName_356_, v___x_370_, v___x_374_, v___x_376_, v_x_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_a_378_);
v___x_379_ = lean_unsigned_to_nat(1u);
v___x_380_ = lean_nat_add(v_j_369_, v___x_379_);
lean_dec(v_j_369_);
v___x_381_ = lean_array_get_size(v_cs_366_);
v___x_382_ = lean_nat_dec_lt(v___x_380_, v___x_381_);
if (v___x_382_ == 0)
{
lean_dec(v___x_380_);
lean_dec(v_a_378_);
lean_dec_ref(v_cs_366_);
return v___x_377_;
}
else
{
size_t v___x_383_; size_t v___x_384_; lean_object* v___x_385_; 
lean_dec_ref_known(v___x_377_, 1);
v___x_383_ = lean_usize_of_nat(v___x_380_);
lean_dec(v___x_380_);
v___x_384_ = lean_usize_of_nat(v___x_381_);
v___x_385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_356_, v_cs_366_, v___x_383_, v___x_384_, v_a_378_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec_ref(v_cs_366_);
return v___x_385_;
}
}
else
{
lean_dec(v_j_369_);
lean_dec_ref(v_cs_366_);
return v___x_377_;
}
}
else
{
lean_object* v_vs_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_399_; 
v_vs_386_ = lean_ctor_get(v_x_357_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v_x_357_);
if (v_isSharedCheck_399_ == 0)
{
v___x_388_ = v_x_357_;
v_isShared_389_ = v_isSharedCheck_399_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_vs_386_);
lean_dec(v_x_357_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_399_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_390_ = lean_usize_to_nat(v_x_358_);
v___x_391_ = lean_array_get_size(v_vs_386_);
v___x_392_ = lean_nat_dec_lt(v___x_390_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_394_; 
lean_dec(v___x_390_);
lean_dec_ref(v_vs_386_);
if (v_isShared_389_ == 0)
{
lean_ctor_set_tag(v___x_388_, 0);
lean_ctor_set(v___x_388_, 0, v_x_360_);
v___x_394_ = v___x_388_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_x_360_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
else
{
size_t v___x_396_; size_t v___x_397_; lean_object* v___x_398_; 
lean_del_object(v___x_388_);
v___x_396_ = lean_usize_of_nat(v___x_390_);
lean_dec(v___x_390_);
v___x_397_ = lean_usize_of_nat(v___x_391_);
v___x_398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_356_, v_vs_386_, v___x_396_, v___x_397_, v_x_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec_ref(v_vs_386_);
return v___x_398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___boxed(lean_object* v_auxDeclToFullName_400_, lean_object* v_x_401_, lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
size_t v_x_5353__boxed_410_; size_t v_x_5354__boxed_411_; lean_object* v_res_412_; 
v_x_5353__boxed_410_ = lean_unbox_usize(v_x_402_);
lean_dec(v_x_402_);
v_x_5354__boxed_411_ = lean_unbox_usize(v_x_403_);
lean_dec(v_x_403_);
v_res_412_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(v_auxDeclToFullName_400_, v_x_401_, v_x_5353__boxed_410_, v_x_5354__boxed_411_, v_x_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v_auxDeclToFullName_400_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5(lean_object* v_auxDeclToFullName_413_, lean_object* v_t_414_, lean_object* v_init_415_, lean_object* v_start_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_nat_dec_eq(v_start_416_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v_root_424_; lean_object* v_tail_425_; size_t v_shift_426_; lean_object* v_tailOff_427_; uint8_t v___x_428_; 
v_root_424_ = lean_ctor_get(v_t_414_, 0);
lean_inc_ref(v_root_424_);
v_tail_425_ = lean_ctor_get(v_t_414_, 1);
lean_inc_ref(v_tail_425_);
v_shift_426_ = lean_ctor_get_usize(v_t_414_, 4);
v_tailOff_427_ = lean_ctor_get(v_t_414_, 3);
lean_inc(v_tailOff_427_);
lean_dec_ref(v_t_414_);
v___x_428_ = lean_nat_dec_le(v_tailOff_427_, v_start_416_);
if (v___x_428_ == 0)
{
size_t v___x_429_; lean_object* v___x_430_; 
lean_dec(v_tailOff_427_);
v___x_429_ = lean_usize_of_nat(v_start_416_);
v___x_430_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(v_auxDeclToFullName_413_, v_root_424_, v___x_429_, v_shift_426_, v_init_415_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
v___x_432_ = lean_array_get_size(v_tail_425_);
v___x_433_ = lean_nat_dec_lt(v___x_422_, v___x_432_);
if (v___x_433_ == 0)
{
lean_dec(v_a_431_);
lean_dec_ref(v_tail_425_);
return v___x_430_;
}
else
{
size_t v___x_434_; size_t v___x_435_; lean_object* v___x_436_; 
lean_dec_ref_known(v___x_430_, 1);
v___x_434_ = ((size_t)0ULL);
v___x_435_ = lean_usize_of_nat(v___x_432_);
v___x_436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_413_, v_tail_425_, v___x_434_, v___x_435_, v_a_431_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec_ref(v_tail_425_);
return v___x_436_;
}
}
else
{
lean_dec_ref(v_tail_425_);
return v___x_430_;
}
}
else
{
lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
lean_dec_ref(v_root_424_);
v___x_437_ = lean_nat_sub(v_start_416_, v_tailOff_427_);
lean_dec(v_tailOff_427_);
v___x_438_ = lean_array_get_size(v_tail_425_);
v___x_439_ = lean_nat_dec_lt(v___x_437_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; 
lean_dec(v___x_437_);
lean_dec_ref(v_tail_425_);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v_init_415_);
return v___x_440_;
}
else
{
size_t v___x_441_; size_t v___x_442_; lean_object* v___x_443_; 
v___x_441_ = lean_usize_of_nat(v___x_437_);
lean_dec(v___x_437_);
v___x_442_ = lean_usize_of_nat(v___x_438_);
v___x_443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_413_, v_tail_425_, v___x_441_, v___x_442_, v_init_415_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec_ref(v_tail_425_);
return v___x_443_;
}
}
}
else
{
lean_object* v_root_444_; lean_object* v_tail_445_; lean_object* v___x_446_; 
v_root_444_ = lean_ctor_get(v_t_414_, 0);
lean_inc_ref(v_root_444_);
v_tail_445_ = lean_ctor_get(v_t_414_, 1);
lean_inc_ref(v_tail_445_);
lean_dec_ref(v_t_414_);
v___x_446_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(v_auxDeclToFullName_413_, v_root_444_, v_init_415_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_447_);
v___x_448_ = lean_array_get_size(v_tail_445_);
v___x_449_ = lean_nat_dec_lt(v___x_422_, v___x_448_);
if (v___x_449_ == 0)
{
lean_dec(v_a_447_);
lean_dec_ref(v_tail_445_);
return v___x_446_;
}
else
{
size_t v___x_450_; size_t v___x_451_; lean_object* v___x_452_; 
lean_dec_ref_known(v___x_446_, 1);
v___x_450_ = ((size_t)0ULL);
v___x_451_ = lean_usize_of_nat(v___x_448_);
v___x_452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_413_, v_tail_445_, v___x_450_, v___x_451_, v_a_447_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec_ref(v_tail_445_);
return v___x_452_;
}
}
else
{
lean_dec_ref(v_tail_445_);
return v___x_446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5___boxed(lean_object* v_auxDeclToFullName_453_, lean_object* v_t_454_, lean_object* v_init_455_, lean_object* v_start_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5(v_auxDeclToFullName_453_, v_t_454_, v_init_455_, v_start_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v_start_456_);
lean_dec(v_auxDeclToFullName_453_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3(lean_object* v_auxDeclToFullName_463_, lean_object* v_lctx_464_, lean_object* v_init_465_, lean_object* v_start_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_decls_472_; lean_object* v___x_473_; 
v_decls_472_ = lean_ctor_get(v_lctx_464_, 1);
lean_inc_ref(v_decls_472_);
lean_dec_ref(v_lctx_464_);
v___x_473_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5(v_auxDeclToFullName_463_, v_decls_472_, v_init_465_, v_start_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3___boxed(lean_object* v_auxDeclToFullName_474_, lean_object* v_lctx_475_, lean_object* v_init_476_, lean_object* v_start_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3(v_auxDeclToFullName_474_, v_lctx_475_, v_init_476_, v_start_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v_start_477_);
lean_dec(v_auxDeclToFullName_474_);
return v_res_483_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_484_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_unsigned_to_nat(32u);
v___x_488_ = lean_mk_empty_array_with_capacity(v___x_487_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_490_ = ((size_t)5ULL);
v___x_491_ = lean_unsigned_to_nat(0u);
v___x_492_ = lean_unsigned_to_nat(32u);
v___x_493_ = lean_mk_empty_array_with_capacity(v___x_492_);
v___x_494_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2);
v___x_495_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___x_493_);
lean_ctor_set(v___x_495_, 2, v___x_491_);
lean_ctor_set(v___x_495_, 3, v___x_491_);
lean_ctor_set_usize(v___x_495_, 4, v___x_490_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_496_ = lean_box(1);
v___x_497_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3);
v___x_498_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1);
v___x_499_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v___x_497_);
lean_ctor_set(v___x_499_, 2, v___x_496_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0(lean_object* v_lctx_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_auxDeclToFullName_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v_auxDeclToFullName_506_ = lean_ctor_get(v_lctx_500_, 2);
lean_inc(v_auxDeclToFullName_506_);
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4);
v___x_509_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3(v_auxDeclToFullName_506_, v_lctx_500_, v___x_508_, v___x_507_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v_auxDeclToFullName_506_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___boxed(lean_object* v_lctx_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0(v_lctx_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12___redArg(lean_object* v_x_517_, lean_object* v_x_518_, lean_object* v_x_519_, lean_object* v_x_520_){
_start:
{
lean_object* v_ks_521_; lean_object* v_vs_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_546_; 
v_ks_521_ = lean_ctor_get(v_x_517_, 0);
v_vs_522_ = lean_ctor_get(v_x_517_, 1);
v_isSharedCheck_546_ = !lean_is_exclusive(v_x_517_);
if (v_isSharedCheck_546_ == 0)
{
v___x_524_ = v_x_517_;
v_isShared_525_ = v_isSharedCheck_546_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_vs_522_);
lean_inc(v_ks_521_);
lean_dec(v_x_517_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_546_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_526_ = lean_array_get_size(v_ks_521_);
v___x_527_ = lean_nat_dec_lt(v_x_518_, v___x_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
lean_dec(v_x_518_);
v___x_528_ = lean_array_push(v_ks_521_, v_x_519_);
v___x_529_ = lean_array_push(v_vs_522_, v_x_520_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 1, v___x_529_);
lean_ctor_set(v___x_524_, 0, v___x_528_);
v___x_531_ = v___x_524_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
else
{
lean_object* v_k_x27_533_; uint8_t v___x_534_; 
v_k_x27_533_ = lean_array_fget_borrowed(v_ks_521_, v_x_518_);
v___x_534_ = l_Lean_instBEqMVarId_beq(v_x_519_, v_k_x27_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_536_; 
if (v_isShared_525_ == 0)
{
v___x_536_ = v___x_524_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_ks_521_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_vs_522_);
v___x_536_ = v_reuseFailAlloc_540_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_unsigned_to_nat(1u);
v___x_538_ = lean_nat_add(v_x_518_, v___x_537_);
lean_dec(v_x_518_);
v_x_517_ = v___x_536_;
v_x_518_ = v___x_538_;
goto _start;
}
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_541_ = lean_array_fset(v_ks_521_, v_x_518_, v_x_519_);
v___x_542_ = lean_array_fset(v_vs_522_, v_x_518_, v_x_520_);
lean_dec(v_x_518_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 1, v___x_542_);
lean_ctor_set(v___x_524_, 0, v___x_541_);
v___x_544_ = v___x_524_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v___x_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8___redArg(lean_object* v_n_547_, lean_object* v_k_548_, lean_object* v_v_549_){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12___redArg(v_n_547_, v___x_550_, v_k_548_, v_v_549_);
return v___x_551_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(lean_object* v_x_553_, size_t v_x_554_, size_t v_x_555_, lean_object* v_x_556_, lean_object* v_x_557_){
_start:
{
if (lean_obj_tag(v_x_553_) == 0)
{
lean_object* v_es_558_; size_t v___x_559_; size_t v___x_560_; lean_object* v_j_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v_es_558_ = lean_ctor_get(v_x_553_, 0);
v___x_559_ = ((size_t)31ULL);
v___x_560_ = lean_usize_land(v_x_554_, v___x_559_);
v_j_561_ = lean_usize_to_nat(v___x_560_);
v___x_562_ = lean_array_get_size(v_es_558_);
v___x_563_ = lean_nat_dec_lt(v_j_561_, v___x_562_);
if (v___x_563_ == 0)
{
lean_dec(v_j_561_);
lean_dec(v_x_557_);
lean_dec(v_x_556_);
return v_x_553_;
}
else
{
lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_602_; 
lean_inc_ref(v_es_558_);
v_isSharedCheck_602_ = !lean_is_exclusive(v_x_553_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v_x_553_, 0);
lean_dec(v_unused_603_);
v___x_565_ = v_x_553_;
v_isShared_566_ = v_isSharedCheck_602_;
goto v_resetjp_564_;
}
else
{
lean_dec(v_x_553_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_602_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v_v_567_; lean_object* v___x_568_; lean_object* v_xs_x27_569_; lean_object* v___y_571_; 
v_v_567_ = lean_array_fget(v_es_558_, v_j_561_);
v___x_568_ = lean_box(0);
v_xs_x27_569_ = lean_array_fset(v_es_558_, v_j_561_, v___x_568_);
switch(lean_obj_tag(v_v_567_))
{
case 0:
{
lean_object* v_key_576_; lean_object* v_val_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_587_; 
v_key_576_ = lean_ctor_get(v_v_567_, 0);
v_val_577_ = lean_ctor_get(v_v_567_, 1);
v_isSharedCheck_587_ = !lean_is_exclusive(v_v_567_);
if (v_isSharedCheck_587_ == 0)
{
v___x_579_ = v_v_567_;
v_isShared_580_ = v_isSharedCheck_587_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_val_577_);
lean_inc(v_key_576_);
lean_dec(v_v_567_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_587_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
uint8_t v___x_581_; 
v___x_581_ = l_Lean_instBEqMVarId_beq(v_x_556_, v_key_576_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_del_object(v___x_579_);
v___x_582_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_576_, v_val_577_, v_x_556_, v_x_557_);
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
v___y_571_ = v___x_583_;
goto v___jp_570_;
}
else
{
lean_object* v___x_585_; 
lean_dec(v_val_577_);
lean_dec(v_key_576_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 1, v_x_557_);
lean_ctor_set(v___x_579_, 0, v_x_556_);
v___x_585_ = v___x_579_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_x_556_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_x_557_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
v___y_571_ = v___x_585_;
goto v___jp_570_;
}
}
}
}
case 1:
{
lean_object* v_node_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_600_; 
v_node_588_ = lean_ctor_get(v_v_567_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v_v_567_);
if (v_isSharedCheck_600_ == 0)
{
v___x_590_ = v_v_567_;
v_isShared_591_ = v_isSharedCheck_600_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_node_588_);
lean_dec(v_v_567_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_600_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
size_t v___x_592_; size_t v___x_593_; size_t v___x_594_; size_t v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_592_ = ((size_t)5ULL);
v___x_593_ = lean_usize_shift_right(v_x_554_, v___x_592_);
v___x_594_ = ((size_t)1ULL);
v___x_595_ = lean_usize_add(v_x_555_, v___x_594_);
v___x_596_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_node_588_, v___x_593_, v___x_595_, v_x_556_, v_x_557_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_596_);
v___x_598_ = v___x_590_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
v___y_571_ = v___x_598_;
goto v___jp_570_;
}
}
}
default: 
{
lean_object* v___x_601_; 
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v_x_556_);
lean_ctor_set(v___x_601_, 1, v_x_557_);
v___y_571_ = v___x_601_;
goto v___jp_570_;
}
}
v___jp_570_:
{
lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_572_ = lean_array_fset(v_xs_x27_569_, v_j_561_, v___y_571_);
lean_dec(v_j_561_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_572_);
v___x_574_ = v___x_565_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
else
{
lean_object* v_ks_604_; lean_object* v_vs_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_623_; 
v_ks_604_ = lean_ctor_get(v_x_553_, 0);
v_vs_605_ = lean_ctor_get(v_x_553_, 1);
v_isSharedCheck_623_ = !lean_is_exclusive(v_x_553_);
if (v_isSharedCheck_623_ == 0)
{
v___x_607_ = v_x_553_;
v_isShared_608_ = v_isSharedCheck_623_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_vs_605_);
lean_inc(v_ks_604_);
lean_dec(v_x_553_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_623_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_ks_604_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_vs_605_);
v___x_610_ = v_reuseFailAlloc_622_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v_newNode_611_; size_t v___x_612_; uint8_t v___x_613_; 
v_newNode_611_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8___redArg(v___x_610_, v_x_556_, v_x_557_);
v___x_612_ = ((size_t)7ULL);
v___x_613_ = lean_usize_dec_le(v___x_612_, v_x_555_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_614_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_611_);
v___x_615_ = lean_unsigned_to_nat(4u);
v___x_616_ = lean_nat_dec_lt(v___x_614_, v___x_615_);
lean_dec(v___x_614_);
if (v___x_616_ == 0)
{
lean_object* v_ks_617_; lean_object* v_vs_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_ks_617_ = lean_ctor_get(v_newNode_611_, 0);
lean_inc_ref(v_ks_617_);
v_vs_618_ = lean_ctor_get(v_newNode_611_, 1);
lean_inc_ref(v_vs_618_);
lean_dec_ref(v_newNode_611_);
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0);
v___x_621_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(v_x_555_, v_ks_617_, v_vs_618_, v___x_619_, v___x_620_);
lean_dec_ref(v_vs_618_);
lean_dec_ref(v_ks_617_);
return v___x_621_;
}
else
{
return v_newNode_611_;
}
}
else
{
return v_newNode_611_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(size_t v_depth_624_, lean_object* v_keys_625_, lean_object* v_vals_626_, lean_object* v_i_627_, lean_object* v_entries_628_){
_start:
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = lean_array_get_size(v_keys_625_);
v___x_630_ = lean_nat_dec_lt(v_i_627_, v___x_629_);
if (v___x_630_ == 0)
{
lean_dec(v_i_627_);
return v_entries_628_;
}
else
{
lean_object* v_k_631_; lean_object* v_v_632_; uint64_t v___x_633_; size_t v_h_634_; size_t v___x_635_; lean_object* v___x_636_; size_t v___x_637_; size_t v___x_638_; size_t v___x_639_; size_t v_h_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_k_631_ = lean_array_fget_borrowed(v_keys_625_, v_i_627_);
v_v_632_ = lean_array_fget_borrowed(v_vals_626_, v_i_627_);
v___x_633_ = l_Lean_instHashableMVarId_hash(v_k_631_);
v_h_634_ = lean_uint64_to_usize(v___x_633_);
v___x_635_ = ((size_t)5ULL);
v___x_636_ = lean_unsigned_to_nat(1u);
v___x_637_ = ((size_t)1ULL);
v___x_638_ = lean_usize_sub(v_depth_624_, v___x_637_);
v___x_639_ = lean_usize_mul(v___x_635_, v___x_638_);
v_h_640_ = lean_usize_shift_right(v_h_634_, v___x_639_);
v___x_641_ = lean_nat_add(v_i_627_, v___x_636_);
lean_dec(v_i_627_);
lean_inc(v_v_632_);
lean_inc(v_k_631_);
v___x_642_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_entries_628_, v_h_640_, v_depth_624_, v_k_631_, v_v_632_);
v_i_627_ = v___x_641_;
v_entries_628_ = v___x_642_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg___boxed(lean_object* v_depth_644_, lean_object* v_keys_645_, lean_object* v_vals_646_, lean_object* v_i_647_, lean_object* v_entries_648_){
_start:
{
size_t v_depth_boxed_649_; lean_object* v_res_650_; 
v_depth_boxed_649_ = lean_unbox_usize(v_depth_644_);
lean_dec(v_depth_644_);
v_res_650_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(v_depth_boxed_649_, v_keys_645_, v_vals_646_, v_i_647_, v_entries_648_);
lean_dec_ref(v_vals_646_);
lean_dec_ref(v_keys_645_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_){
_start:
{
size_t v_x_5679__boxed_656_; size_t v_x_5680__boxed_657_; lean_object* v_res_658_; 
v_x_5679__boxed_656_ = lean_unbox_usize(v_x_652_);
lean_dec(v_x_652_);
v_x_5680__boxed_657_ = lean_unbox_usize(v_x_653_);
lean_dec(v_x_653_);
v_res_658_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_x_651_, v_x_5679__boxed_656_, v_x_5680__boxed_657_, v_x_654_, v_x_655_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2___redArg(lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
uint64_t v___x_662_; size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; 
v___x_662_ = l_Lean_instHashableMVarId_hash(v_x_660_);
v___x_663_ = lean_uint64_to_usize(v___x_662_);
v___x_664_ = ((size_t)1ULL);
v___x_665_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_x_659_, v___x_663_, v___x_664_, v_x_660_, v_x_661_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0(lean_object* v_mvarId_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_672_; lean_object* v_mctx_673_; lean_object* v_mvarDecl_674_; lean_object* v_userName_675_; lean_object* v_lctx_676_; lean_object* v_type_677_; lean_object* v_depth_678_; lean_object* v_localInstances_679_; uint8_t v_kind_680_; lean_object* v_numScopeArgs_681_; lean_object* v_index_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_746_; 
v___x_672_ = lean_st_ref_get(v___y_668_);
v_mctx_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc_ref(v_mctx_673_);
lean_dec(v___x_672_);
lean_inc(v_mvarId_666_);
v_mvarDecl_674_ = l_Lean_MetavarContext_getDecl(v_mctx_673_, v_mvarId_666_);
lean_dec_ref(v_mctx_673_);
v_userName_675_ = lean_ctor_get(v_mvarDecl_674_, 0);
v_lctx_676_ = lean_ctor_get(v_mvarDecl_674_, 1);
v_type_677_ = lean_ctor_get(v_mvarDecl_674_, 2);
v_depth_678_ = lean_ctor_get(v_mvarDecl_674_, 3);
v_localInstances_679_ = lean_ctor_get(v_mvarDecl_674_, 4);
v_kind_680_ = lean_ctor_get_uint8(v_mvarDecl_674_, sizeof(void*)*7);
v_numScopeArgs_681_ = lean_ctor_get(v_mvarDecl_674_, 5);
v_index_682_ = lean_ctor_get(v_mvarDecl_674_, 6);
v_isSharedCheck_746_ = !lean_is_exclusive(v_mvarDecl_674_);
if (v_isSharedCheck_746_ == 0)
{
v___x_684_ = v_mvarDecl_674_;
v_isShared_685_ = v_isSharedCheck_746_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_index_682_);
lean_inc(v_numScopeArgs_681_);
lean_inc(v_localInstances_679_);
lean_inc(v_depth_678_);
lean_inc(v_type_677_);
lean_inc(v_lctx_676_);
lean_inc(v_userName_675_);
lean_dec(v_mvarDecl_674_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_746_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0(v_lctx_676_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_688_; lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_737_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
v___x_688_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_type_677_, v___y_668_);
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_737_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_737_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_737_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v_fst_695_; lean_object* v_snd_696_; lean_object* v___x_697_; lean_object* v_mctx_698_; lean_object* v_cache_699_; lean_object* v_zetaDeltaFVarIds_700_; lean_object* v_postponed_701_; lean_object* v_diag_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_736_; 
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v_a_687_);
lean_ctor_set(v___x_693_, 1, v_a_689_);
v___x_694_ = lean_sharecommon_quick(v___x_693_);
lean_dec_ref_known(v___x_693_, 2);
v_fst_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_fst_695_);
v_snd_696_ = lean_ctor_get(v___x_694_, 1);
lean_inc(v_snd_696_);
lean_dec(v___x_694_);
v___x_697_ = lean_st_ref_take(v___y_668_);
v_mctx_698_ = lean_ctor_get(v___x_697_, 0);
v_cache_699_ = lean_ctor_get(v___x_697_, 1);
v_zetaDeltaFVarIds_700_ = lean_ctor_get(v___x_697_, 2);
v_postponed_701_ = lean_ctor_get(v___x_697_, 3);
v_diag_702_ = lean_ctor_get(v___x_697_, 4);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_736_ == 0)
{
v___x_704_ = v___x_697_;
v_isShared_705_ = v_isSharedCheck_736_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_diag_702_);
lean_inc(v_postponed_701_);
lean_inc(v_zetaDeltaFVarIds_700_);
lean_inc(v_cache_699_);
lean_inc(v_mctx_698_);
lean_dec(v___x_697_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_736_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v_depth_706_; lean_object* v_levelAssignDepth_707_; lean_object* v_lmvarCounter_708_; lean_object* v_mvarCounter_709_; lean_object* v_lDecls_710_; lean_object* v_decls_711_; lean_object* v_userNames_712_; lean_object* v_lAssignment_713_; lean_object* v_eAssignment_714_; lean_object* v_dAssignment_715_; lean_object* v_instanceTypedMVars_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_735_; 
v_depth_706_ = lean_ctor_get(v_mctx_698_, 0);
v_levelAssignDepth_707_ = lean_ctor_get(v_mctx_698_, 1);
v_lmvarCounter_708_ = lean_ctor_get(v_mctx_698_, 2);
v_mvarCounter_709_ = lean_ctor_get(v_mctx_698_, 3);
v_lDecls_710_ = lean_ctor_get(v_mctx_698_, 4);
v_decls_711_ = lean_ctor_get(v_mctx_698_, 5);
v_userNames_712_ = lean_ctor_get(v_mctx_698_, 6);
v_lAssignment_713_ = lean_ctor_get(v_mctx_698_, 7);
v_eAssignment_714_ = lean_ctor_get(v_mctx_698_, 8);
v_dAssignment_715_ = lean_ctor_get(v_mctx_698_, 9);
v_instanceTypedMVars_716_ = lean_ctor_get(v_mctx_698_, 10);
v_isSharedCheck_735_ = !lean_is_exclusive(v_mctx_698_);
if (v_isSharedCheck_735_ == 0)
{
v___x_718_ = v_mctx_698_;
v_isShared_719_ = v_isSharedCheck_735_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_instanceTypedMVars_716_);
lean_inc(v_dAssignment_715_);
lean_inc(v_eAssignment_714_);
lean_inc(v_lAssignment_713_);
lean_inc(v_userNames_712_);
lean_inc(v_decls_711_);
lean_inc(v_lDecls_710_);
lean_inc(v_mvarCounter_709_);
lean_inc(v_lmvarCounter_708_);
lean_inc(v_levelAssignDepth_707_);
lean_inc(v_depth_706_);
lean_dec(v_mctx_698_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_735_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 2, v_snd_696_);
lean_ctor_set(v___x_684_, 1, v_fst_695_);
v___x_721_ = v___x_684_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_userName_675_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_fst_695_);
lean_ctor_set(v_reuseFailAlloc_734_, 2, v_snd_696_);
lean_ctor_set(v_reuseFailAlloc_734_, 3, v_depth_678_);
lean_ctor_set(v_reuseFailAlloc_734_, 4, v_localInstances_679_);
lean_ctor_set(v_reuseFailAlloc_734_, 5, v_numScopeArgs_681_);
lean_ctor_set(v_reuseFailAlloc_734_, 6, v_index_682_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, sizeof(void*)*7, v_kind_680_);
v___x_721_ = v_reuseFailAlloc_734_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_722_ = l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2___redArg(v_decls_711_, v_mvarId_666_, v___x_721_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 5, v___x_722_);
v___x_724_ = v___x_718_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_depth_706_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_levelAssignDepth_707_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v_lmvarCounter_708_);
lean_ctor_set(v_reuseFailAlloc_733_, 3, v_mvarCounter_709_);
lean_ctor_set(v_reuseFailAlloc_733_, 4, v_lDecls_710_);
lean_ctor_set(v_reuseFailAlloc_733_, 5, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_733_, 6, v_userNames_712_);
lean_ctor_set(v_reuseFailAlloc_733_, 7, v_lAssignment_713_);
lean_ctor_set(v_reuseFailAlloc_733_, 8, v_eAssignment_714_);
lean_ctor_set(v_reuseFailAlloc_733_, 9, v_dAssignment_715_);
lean_ctor_set(v_reuseFailAlloc_733_, 10, v_instanceTypedMVars_716_);
v___x_724_ = v_reuseFailAlloc_733_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_726_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_724_);
v___x_726_ = v___x_704_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_cache_699_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v_zetaDeltaFVarIds_700_);
lean_ctor_set(v_reuseFailAlloc_732_, 3, v_postponed_701_);
lean_ctor_set(v_reuseFailAlloc_732_, 4, v_diag_702_);
v___x_726_ = v_reuseFailAlloc_732_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_727_ = lean_st_ref_put(v___y_668_, v___x_726_);
v___x_728_ = lean_box(0);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_728_);
v___x_730_ = v___x_691_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
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
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_del_object(v___x_684_);
lean_dec(v_index_682_);
lean_dec(v_numScopeArgs_681_);
lean_dec_ref(v_localInstances_679_);
lean_dec(v_depth_678_);
lean_dec_ref(v_type_677_);
lean_dec(v_userName_675_);
lean_dec(v_mvarId_666_);
v_a_738_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_686_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_686_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0___boxed(lean_object* v_mvarId_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0(v_mvarId_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic(lean_object* v_mvarId_754_, lean_object* v_tacticCode_755_, lean_object* v_ctx_756_, lean_object* v_s_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v___x_763_; 
lean_inc(v_mvarId_754_);
v___x_763_ = l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0(v_mvarId_754_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v___f_764_; lean_object* v___x_765_; uint8_t v___x_766_; lean_object* v___x_767_; lean_object* v___f_768_; lean_object* v___x_769_; 
lean_dec_ref_known(v___x_763_, 1);
v___f_764_ = lean_alloc_closure((void*)(l_Lean_Elab_runTactic___lam__0___boxed), 10, 1);
lean_closure_set(v___f_764_, 0, v_tacticCode_755_);
v___x_765_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_765_, 0, v_mvarId_754_);
lean_closure_set(v___x_765_, 1, v___f_764_);
v___x_766_ = 1;
v___x_767_ = lean_box(v___x_766_);
v___f_768_ = lean_alloc_closure((void*)(l_Lean_Elab_runTactic___lam__1___boxed), 9, 2);
lean_closure_set(v___f_768_, 0, v___x_765_);
lean_closure_set(v___f_768_, 1, v___x_767_);
v___x_769_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_768_, v_ctx_756_, v_s_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
return v___x_769_;
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec_ref(v_s_757_);
lean_dec_ref(v_ctx_756_);
lean_dec(v_tacticCode_755_);
lean_dec(v_mvarId_754_);
v_a_770_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_763_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_763_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic___boxed(lean_object* v_mvarId_778_, lean_object* v_tacticCode_779_, lean_object* v_ctx_780_, lean_object* v_s_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Elab_runTactic(v_mvarId_778_, v_tacticCode_779_, v_ctx_780_, v_s_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1(lean_object* v_e_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_e_788_, v___y_790_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___boxed(lean_object* v_e_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1(v_e_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2(lean_object* v_00_u03b2_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2___redArg(v_x_803_, v_x_804_, v_x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1(lean_object* v_00_u03b4_807_, lean_object* v_t_808_, lean_object* v_k_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg(v_t_808_, v_k_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b4_811_, lean_object* v_t_812_, lean_object* v_k_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1(v_00_u03b4_811_, v_t_812_, v_k_813_);
lean_dec(v_k_813_);
lean_dec(v_t_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_815_, lean_object* v_x_816_, size_t v_x_817_, size_t v_x_818_, lean_object* v_x_819_, lean_object* v_x_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_x_816_, v_x_817_, v_x_818_, v_x_819_, v_x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_822_, lean_object* v_x_823_, lean_object* v_x_824_, lean_object* v_x_825_, lean_object* v_x_826_, lean_object* v_x_827_){
_start:
{
size_t v_x_6020__boxed_828_; size_t v_x_6021__boxed_829_; lean_object* v_res_830_; 
v_x_6020__boxed_828_ = lean_unbox_usize(v_x_824_);
lean_dec(v_x_824_);
v_x_6021__boxed_829_ = lean_unbox_usize(v_x_825_);
lean_dec(v_x_825_);
v_res_830_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6(v_00_u03b2_822_, v_x_823_, v_x_6020__boxed_828_, v_x_6021__boxed_829_, v_x_826_, v_x_827_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8(lean_object* v_00_u03b2_831_, lean_object* v_n_832_, lean_object* v_k_833_, lean_object* v_v_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8___redArg(v_n_832_, v_k_833_, v_v_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9(lean_object* v_00_u03b2_836_, size_t v_depth_837_, lean_object* v_keys_838_, lean_object* v_vals_839_, lean_object* v_heq_840_, lean_object* v_i_841_, lean_object* v_entries_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(v_depth_837_, v_keys_838_, v_vals_839_, v_i_841_, v_entries_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___boxed(lean_object* v_00_u03b2_844_, lean_object* v_depth_845_, lean_object* v_keys_846_, lean_object* v_vals_847_, lean_object* v_heq_848_, lean_object* v_i_849_, lean_object* v_entries_850_){
_start:
{
size_t v_depth_boxed_851_; lean_object* v_res_852_; 
v_depth_boxed_851_ = lean_unbox_usize(v_depth_845_);
lean_dec(v_depth_845_);
v_res_852_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9(v_00_u03b2_844_, v_depth_boxed_851_, v_keys_846_, v_vals_847_, v_heq_848_, v_i_849_, v_entries_850_);
lean_dec_ref(v_vals_847_);
lean_dec_ref(v_keys_846_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12(lean_object* v_00_u03b2_853_, lean_object* v_x_854_, lean_object* v_x_855_, lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12___redArg(v_x_854_, v_x_855_, v_x_856_, v_x_857_);
return v___x_858_;
}
}
lean_object* runtime_initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Meta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
