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
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
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
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
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
lean_object* l_Lean_Elab_runTactic___lam__0(lean_object* v_tacticCode_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
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
LEAN_EXPORT void l_Lean_Elab_runTactic___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticCode_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v___y_9_ = stack[8].m_obj;
lean_object* v_res_13_;
v_res_13_ = l_Lean_Elab_runTactic___lam__0(v_tacticCode_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
stack->m_obj
 = v_res_13_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic___lam__0___boxed(lean_object* v_tacticCode_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Elab_runTactic___lam__0(v_tacticCode_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
return v_res_24_;
}
}
lean_object* l_Lean_Elab_runTactic___lam__1(lean_object* v___x_25_, uint8_t v___x_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_25_, v___x_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
return v___x_34_;
}
}
LEAN_EXPORT void l_Lean_Elab_runTactic___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_25_ = stack[0].m_obj;
uint8_t v___x_26_ = stack[1].m_num;
lean_object* v___y_27_ = stack[2].m_obj;
lean_object* v___y_28_ = stack[3].m_obj;
lean_object* v___y_29_ = stack[4].m_obj;
lean_object* v___y_30_ = stack[5].m_obj;
lean_object* v___y_31_ = stack[6].m_obj;
lean_object* v___y_32_ = stack[7].m_obj;
lean_object* v_res_35_;
v_res_35_ = l_Lean_Elab_runTactic___lam__1(v___x_25_, v___x_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
stack->m_obj
 = v_res_35_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic___lam__1___boxed(lean_object* v___x_36_, lean_object* v___x_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
uint8_t v___x_4861__boxed_45_; lean_object* v_res_46_; 
v___x_4861__boxed_45_ = lean_unbox(v___x_37_);
v_res_46_ = l_Lean_Elab_runTactic___lam__1(v___x_36_, v___x_4861__boxed_45_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
return v_res_46_;
}
}
static lean_object* _init_l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_instMonadEIO___redArg();
return v___x_47_;
}
}
lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2(lean_object* v_msg_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v_toApplicative_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_121_; 
v___x_58_ = lean_obj_once(&l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__0, &l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__0_once, _init_l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__0);
v___x_59_ = l_StateRefT_x27_instMonad___redArg(v___x_58_);
v_toApplicative_60_ = lean_ctor_get(v___x_59_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_121_ == 0)
{
lean_object* v_unused_122_; 
v_unused_122_ = lean_ctor_get(v___x_59_, 1);
lean_dec(v_unused_122_);
v___x_62_ = v___x_59_;
v_isShared_63_ = v_isSharedCheck_121_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_toApplicative_60_);
lean_dec(v___x_59_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_121_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v_toFunctor_64_; lean_object* v_toSeq_65_; lean_object* v_toSeqLeft_66_; lean_object* v_toSeqRight_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_119_; 
v_toFunctor_64_ = lean_ctor_get(v_toApplicative_60_, 0);
v_toSeq_65_ = lean_ctor_get(v_toApplicative_60_, 2);
v_toSeqLeft_66_ = lean_ctor_get(v_toApplicative_60_, 3);
v_toSeqRight_67_ = lean_ctor_get(v_toApplicative_60_, 4);
v_isSharedCheck_119_ = !lean_is_exclusive(v_toApplicative_60_);
if (v_isSharedCheck_119_ == 0)
{
lean_object* v_unused_120_; 
v_unused_120_ = lean_ctor_get(v_toApplicative_60_, 1);
lean_dec(v_unused_120_);
v___x_69_ = v_toApplicative_60_;
v_isShared_70_ = v_isSharedCheck_119_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_toSeqRight_67_);
lean_inc(v_toSeqLeft_66_);
lean_inc(v_toSeq_65_);
lean_inc(v_toFunctor_64_);
lean_dec(v_toApplicative_60_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_119_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___f_71_; lean_object* v___f_72_; lean_object* v___f_73_; lean_object* v___f_74_; lean_object* v___x_75_; lean_object* v___f_76_; lean_object* v___f_77_; lean_object* v___f_78_; lean_object* v___x_80_; 
v___f_71_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__1));
v___f_72_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__2));
lean_inc_ref(v_toFunctor_64_);
v___f_73_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_73_, 0, v_toFunctor_64_);
v___f_74_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_74_, 0, v_toFunctor_64_);
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v___f_73_);
lean_ctor_set(v___x_75_, 1, v___f_74_);
v___f_76_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_76_, 0, v_toSeqRight_67_);
v___f_77_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_77_, 0, v_toSeqLeft_66_);
v___f_78_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_78_, 0, v_toSeq_65_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 4, v___f_76_);
lean_ctor_set(v___x_69_, 3, v___f_77_);
lean_ctor_set(v___x_69_, 2, v___f_78_);
lean_ctor_set(v___x_69_, 1, v___f_71_);
lean_ctor_set(v___x_69_, 0, v___x_75_);
v___x_80_ = v___x_69_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_75_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v___f_71_);
lean_ctor_set(v_reuseFailAlloc_118_, 2, v___f_78_);
lean_ctor_set(v_reuseFailAlloc_118_, 3, v___f_77_);
lean_ctor_set(v_reuseFailAlloc_118_, 4, v___f_76_);
v___x_80_ = v_reuseFailAlloc_118_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
lean_object* v___x_82_; 
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 1, v___f_72_);
lean_ctor_set(v___x_62_, 0, v___x_80_);
v___x_82_ = v___x_62_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_80_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v___f_72_);
v___x_82_ = v_reuseFailAlloc_117_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_object* v___x_83_; lean_object* v_toApplicative_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_115_; 
v___x_83_ = l_StateRefT_x27_instMonad___redArg(v___x_82_);
v_toApplicative_84_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_115_ == 0)
{
lean_object* v_unused_116_; 
v_unused_116_ = lean_ctor_get(v___x_83_, 1);
lean_dec(v_unused_116_);
v___x_86_ = v___x_83_;
v_isShared_87_ = v_isSharedCheck_115_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_toApplicative_84_);
lean_dec(v___x_83_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_115_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v_toFunctor_88_; lean_object* v_toSeq_89_; lean_object* v_toSeqLeft_90_; lean_object* v_toSeqRight_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_113_; 
v_toFunctor_88_ = lean_ctor_get(v_toApplicative_84_, 0);
v_toSeq_89_ = lean_ctor_get(v_toApplicative_84_, 2);
v_toSeqLeft_90_ = lean_ctor_get(v_toApplicative_84_, 3);
v_toSeqRight_91_ = lean_ctor_get(v_toApplicative_84_, 4);
v_isSharedCheck_113_ = !lean_is_exclusive(v_toApplicative_84_);
if (v_isSharedCheck_113_ == 0)
{
lean_object* v_unused_114_; 
v_unused_114_ = lean_ctor_get(v_toApplicative_84_, 1);
lean_dec(v_unused_114_);
v___x_93_ = v_toApplicative_84_;
v_isShared_94_ = v_isSharedCheck_113_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_toSeqRight_91_);
lean_inc(v_toSeqLeft_90_);
lean_inc(v_toSeq_89_);
lean_inc(v_toFunctor_88_);
lean_dec(v_toApplicative_84_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_113_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___f_95_; lean_object* v___f_96_; lean_object* v___f_97_; lean_object* v___f_98_; lean_object* v___x_99_; lean_object* v___f_100_; lean_object* v___f_101_; lean_object* v___f_102_; lean_object* v___x_104_; 
v___f_95_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__3));
v___f_96_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__4));
lean_inc_ref(v_toFunctor_88_);
v___f_97_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_97_, 0, v_toFunctor_88_);
v___f_98_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_98_, 0, v_toFunctor_88_);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v___f_97_);
lean_ctor_set(v___x_99_, 1, v___f_98_);
v___f_100_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_100_, 0, v_toSeqRight_91_);
v___f_101_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_101_, 0, v_toSeqLeft_90_);
v___f_102_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_102_, 0, v_toSeq_89_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 4, v___f_100_);
lean_ctor_set(v___x_93_, 3, v___f_101_);
lean_ctor_set(v___x_93_, 2, v___f_102_);
lean_ctor_set(v___x_93_, 1, v___f_95_);
lean_ctor_set(v___x_93_, 0, v___x_99_);
v___x_104_ = v___x_93_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_99_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v___f_95_);
lean_ctor_set(v_reuseFailAlloc_112_, 2, v___f_102_);
lean_ctor_set(v_reuseFailAlloc_112_, 3, v___f_101_);
lean_ctor_set(v_reuseFailAlloc_112_, 4, v___f_100_);
v___x_104_ = v_reuseFailAlloc_112_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_106_; 
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 1, v___f_96_);
lean_ctor_set(v___x_86_, 0, v___x_104_);
v___x_106_ = v___x_86_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_104_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v___f_96_);
v___x_106_ = v_reuseFailAlloc_111_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_2573__overap_109_; lean_object* v___x_110_; 
v___x_107_ = l_Lean_instInhabitedLocalContext_default;
v___x_108_ = l_instInhabitedOfMonad___redArg(v___x_106_, v___x_107_);
v___x_2573__overap_109_ = lean_panic_fn_borrowed(v___x_108_, v_msg_52_);
lean_dec(v___x_108_);
lean_inc(v___y_56_);
lean_inc_ref(v___y_55_);
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
v___x_110_ = lean_apply_5(v___x_2573__overap_109_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, lean_box(0));
return v___x_110_;
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
LEAN_EXPORT void l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_52_ = stack[0].m_obj;
lean_object* v___y_53_ = stack[1].m_obj;
lean_object* v___y_54_ = stack[2].m_obj;
lean_object* v___y_55_ = stack[3].m_obj;
lean_object* v___y_56_ = stack[4].m_obj;
lean_object* v_res_123_;
v_res_123_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2(v_msg_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
stack->m_obj
 = v_res_123_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___boxed(lean_object* v_msg_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2(v_msg_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
return v_res_130_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(lean_object* v_e_131_, lean_object* v___y_132_){
_start:
{
uint8_t v___x_134_; 
v___x_134_ = l_Lean_Expr_hasMVar(v_e_131_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; 
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v_e_131_);
return v___x_135_;
}
else
{
lean_object* v___x_136_; lean_object* v_mctx_137_; lean_object* v___x_138_; lean_object* v_fst_139_; lean_object* v_snd_140_; lean_object* v___x_141_; lean_object* v_cache_142_; lean_object* v_zetaDeltaFVarIds_143_; lean_object* v_postponed_144_; lean_object* v_diag_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_154_; 
v___x_136_ = lean_st_ref_get(v___y_132_);
v_mctx_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc_ref(v_mctx_137_);
lean_dec(v___x_136_);
v___x_138_ = l_Lean_instantiateMVarsCore(v_mctx_137_, v_e_131_);
v_fst_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_fst_139_);
v_snd_140_ = lean_ctor_get(v___x_138_, 1);
lean_inc(v_snd_140_);
lean_dec_ref(v___x_138_);
v___x_141_ = lean_st_ref_take(v___y_132_);
v_cache_142_ = lean_ctor_get(v___x_141_, 1);
v_zetaDeltaFVarIds_143_ = lean_ctor_get(v___x_141_, 2);
v_postponed_144_ = lean_ctor_get(v___x_141_, 3);
v_diag_145_ = lean_ctor_get(v___x_141_, 4);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_154_ == 0)
{
lean_object* v_unused_155_; 
v_unused_155_ = lean_ctor_get(v___x_141_, 0);
lean_dec(v_unused_155_);
v___x_147_ = v___x_141_;
v_isShared_148_ = v_isSharedCheck_154_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_diag_145_);
lean_inc(v_postponed_144_);
lean_inc(v_zetaDeltaFVarIds_143_);
lean_inc(v_cache_142_);
lean_dec(v___x_141_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_154_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v_snd_140_);
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_snd_140_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_cache_142_);
lean_ctor_set(v_reuseFailAlloc_153_, 2, v_zetaDeltaFVarIds_143_);
lean_ctor_set(v_reuseFailAlloc_153_, 3, v_postponed_144_);
lean_ctor_set(v_reuseFailAlloc_153_, 4, v_diag_145_);
v___x_150_ = v_reuseFailAlloc_153_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_st_ref_put(v___y_132_, v___x_150_);
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v_fst_139_);
return v___x_152_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_131_ = stack[0].m_obj;
lean_object* v___y_132_ = stack[1].m_obj;
lean_object* v_res_156_;
v_res_156_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_e_131_, v___y_132_);
stack->m_obj
 = v_res_156_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg___boxed(lean_object* v_e_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_e_157_, v___y_158_);
lean_dec(v___y_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg(lean_object* v_t_161_, lean_object* v_k_162_){
_start:
{
if (lean_obj_tag(v_t_161_) == 0)
{
lean_object* v_k_163_; lean_object* v_v_164_; lean_object* v_l_165_; lean_object* v_r_166_; uint8_t v___x_167_; 
v_k_163_ = lean_ctor_get(v_t_161_, 1);
v_v_164_ = lean_ctor_get(v_t_161_, 2);
v_l_165_ = lean_ctor_get(v_t_161_, 3);
v_r_166_ = lean_ctor_get(v_t_161_, 4);
v___x_167_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_162_, v_k_163_);
switch(v___x_167_)
{
case 0:
{
v_t_161_ = v_l_165_;
goto _start;
}
case 1:
{
lean_object* v___x_169_; 
lean_inc(v_v_164_);
v___x_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_169_, 0, v_v_164_);
return v___x_169_;
}
default: 
{
v_t_161_ = v_r_166_;
goto _start;
}
}
}
else
{
lean_object* v___x_171_; 
v___x_171_ = lean_box(0);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_t_172_, lean_object* v_k_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg(v_t_172_, v_k_173_);
lean_dec(v_k_173_);
lean_dec(v_t_172_);
return v_res_174_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(lean_object* v_auxDeclToFullName_179_, lean_object* v_as_180_, size_t v_i_181_, size_t v_stop_182_, lean_object* v_b_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_a_190_; uint8_t v___x_194_; 
v___x_194_ = lean_usize_dec_eq(v_i_181_, v_stop_182_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
v___x_195_ = lean_array_uget_borrowed(v_as_180_, v_i_181_);
if (lean_obj_tag(v___x_195_) == 0)
{
v_a_190_ = v_b_183_;
goto v___jp_189_;
}
else
{
lean_object* v_val_196_; 
v_val_196_ = lean_ctor_get(v___x_195_, 0);
if (lean_obj_tag(v_val_196_) == 0)
{
uint8_t v_kind_197_; 
v_kind_197_ = lean_ctor_get_uint8(v_val_196_, sizeof(void*)*4 + 1);
if (v_kind_197_ == 2)
{
lean_object* v_fvarId_198_; lean_object* v_userName_199_; lean_object* v_type_200_; lean_object* v___x_201_; 
v_fvarId_198_ = lean_ctor_get(v_val_196_, 1);
v_userName_199_ = lean_ctor_get(v_val_196_, 2);
v_type_200_ = lean_ctor_get(v_val_196_, 3);
lean_inc_ref(v_type_200_);
v___x_201_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_type_200_, v___y_185_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_203_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_a_202_);
lean_dec_ref_known(v___x_201_, 1);
v___x_203_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg(v_auxDeclToFullName_179_, v_fvarId_198_);
if (lean_obj_tag(v___x_203_) == 1)
{
lean_object* v_val_204_; lean_object* v___x_205_; 
v_val_204_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_val_204_);
lean_dec_ref_known(v___x_203_, 1);
lean_inc(v_userName_199_);
lean_inc(v_fvarId_198_);
v___x_205_ = l_Lean_LocalContext_mkAuxDecl(v_b_183_, v_fvarId_198_, v_userName_199_, v_a_202_, v_val_204_);
v_a_190_ = v___x_205_;
goto v___jp_189_;
}
else
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec(v___x_203_);
lean_dec(v_a_202_);
lean_dec_ref(v_b_183_);
v___x_206_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__0));
v___x_207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__1));
v___x_208_ = lean_unsigned_to_nat(674u);
v___x_209_ = lean_unsigned_to_nat(12u);
v___x_210_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__2));
v___x_211_ = 1;
lean_inc(v_userName_199_);
v___x_212_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_199_, v___x_211_);
v___x_213_ = lean_string_append(v___x_210_, v___x_212_);
lean_dec_ref(v___x_212_);
v___x_214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__3));
v___x_215_ = lean_string_append(v___x_213_, v___x_214_);
v___x_216_ = l_mkPanicMessageWithDecl(v___x_206_, v___x_207_, v___x_208_, v___x_209_, v___x_215_);
lean_dec_ref(v___x_215_);
v___x_217_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2(v___x_216_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_a_218_);
lean_dec_ref_known(v___x_217_, 1);
v_a_190_ = v_a_218_;
goto v___jp_189_;
}
else
{
return v___x_217_;
}
}
}
else
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
lean_dec_ref(v_b_183_);
v_a_219_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_201_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_201_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_219_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
else
{
lean_object* v_fvarId_227_; lean_object* v_userName_228_; lean_object* v_type_229_; uint8_t v_bi_230_; lean_object* v___x_231_; 
v_fvarId_227_ = lean_ctor_get(v_val_196_, 1);
v_userName_228_ = lean_ctor_get(v_val_196_, 2);
v_type_229_ = lean_ctor_get(v_val_196_, 3);
v_bi_230_ = lean_ctor_get_uint8(v_val_196_, sizeof(void*)*4);
lean_inc_ref(v_type_229_);
v___x_231_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_type_229_, v___y_185_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_233_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref_known(v___x_231_, 1);
lean_inc(v_userName_228_);
lean_inc(v_fvarId_227_);
v___x_233_ = l_Lean_LocalContext_mkLocalDecl(v_b_183_, v_fvarId_227_, v_userName_228_, v_a_232_, v_bi_230_, v_kind_197_);
v_a_190_ = v___x_233_;
goto v___jp_189_;
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_dec_ref(v_b_183_);
v_a_234_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_231_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_231_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
else
{
lean_object* v_fvarId_242_; lean_object* v_userName_243_; lean_object* v_type_244_; lean_object* v_value_245_; uint8_t v_nondep_246_; uint8_t v_kind_247_; lean_object* v___x_248_; 
v_fvarId_242_ = lean_ctor_get(v_val_196_, 1);
v_userName_243_ = lean_ctor_get(v_val_196_, 2);
v_type_244_ = lean_ctor_get(v_val_196_, 3);
v_value_245_ = lean_ctor_get(v_val_196_, 4);
v_nondep_246_ = lean_ctor_get_uint8(v_val_196_, sizeof(void*)*5);
v_kind_247_ = lean_ctor_get_uint8(v_val_196_, sizeof(void*)*5 + 1);
lean_inc_ref(v_type_244_);
v___x_248_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_type_244_, v___y_185_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_250_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v___x_248_, 1);
lean_inc_ref(v_value_245_);
v___x_250_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_value_245_, v___y_185_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_252_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v___x_250_, 1);
lean_inc(v_userName_243_);
lean_inc(v_fvarId_242_);
v___x_252_ = l_Lean_LocalContext_mkLetDecl(v_b_183_, v_fvarId_242_, v_userName_243_, v_a_249_, v_a_251_, v_nondep_246_, v_kind_247_);
v_a_190_ = v___x_252_;
goto v___jp_189_;
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec(v_a_249_);
lean_dec_ref(v_b_183_);
v_a_253_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_250_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_250_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec_ref(v_b_183_);
v_a_261_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_248_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_248_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
}
else
{
lean_object* v___x_269_; 
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v_b_183_);
return v___x_269_;
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
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_auxDeclToFullName_179_ = stack[0].m_obj;
lean_object* v_as_180_ = stack[1].m_obj;
size_t v_i_181_ = stack[2].m_num;
size_t v_stop_182_ = stack[3].m_num;
lean_object* v_b_183_ = stack[4].m_obj;
lean_object* v___y_184_ = stack[5].m_obj;
lean_object* v___y_185_ = stack[6].m_obj;
lean_object* v___y_186_ = stack[7].m_obj;
lean_object* v___y_187_ = stack[8].m_obj;
lean_object* v_res_270_;
v_res_270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_179_, v_as_180_, v_i_181_, v_stop_182_, v_b_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
stack->m_obj
 = v_res_270_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___boxed(lean_object* v_auxDeclToFullName_271_, lean_object* v_as_272_, lean_object* v_i_273_, lean_object* v_stop_274_, lean_object* v_b_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
size_t v_i_boxed_281_; size_t v_stop_boxed_282_; lean_object* v_res_283_; 
v_i_boxed_281_ = lean_unbox_usize(v_i_273_);
lean_dec(v_i_273_);
v_stop_boxed_282_ = lean_unbox_usize(v_stop_274_);
lean_dec(v_stop_274_);
v_res_283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_271_, v_as_272_, v_i_boxed_281_, v_stop_boxed_282_, v_b_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec_ref(v_as_272_);
lean_dec(v_auxDeclToFullName_271_);
return v_res_283_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(lean_object* v_auxDeclToFullName_284_, lean_object* v_x_285_, lean_object* v_x_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
if (lean_obj_tag(v_x_285_) == 0)
{
lean_object* v_cs_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_305_; 
v_cs_292_ = lean_ctor_get(v_x_285_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v_x_285_);
if (v_isSharedCheck_305_ == 0)
{
v___x_294_ = v_x_285_;
v_isShared_295_ = v_isSharedCheck_305_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_cs_292_);
lean_dec(v_x_285_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_305_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_array_get_size(v_cs_292_);
v___x_298_ = lean_nat_dec_lt(v___x_296_, v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_300_; 
lean_dec_ref(v_cs_292_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v_x_286_);
v___x_300_ = v___x_294_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_x_286_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
else
{
size_t v___x_302_; size_t v___x_303_; lean_object* v___x_304_; 
lean_del_object(v___x_294_);
v___x_302_ = ((size_t)0ULL);
v___x_303_ = lean_usize_of_nat(v___x_297_);
v___x_304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_284_, v_cs_292_, v___x_302_, v___x_303_, v_x_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
lean_dec_ref(v_cs_292_);
return v___x_304_;
}
}
}
else
{
lean_object* v_vs_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_319_; 
v_vs_306_ = lean_ctor_get(v_x_285_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v_x_285_);
if (v_isSharedCheck_319_ == 0)
{
v___x_308_ = v_x_285_;
v_isShared_309_ = v_isSharedCheck_319_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_vs_306_);
lean_dec(v_x_285_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_319_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = lean_array_get_size(v_vs_306_);
v___x_312_ = lean_nat_dec_lt(v___x_310_, v___x_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_314_; 
lean_dec_ref(v_vs_306_);
if (v_isShared_309_ == 0)
{
lean_ctor_set_tag(v___x_308_, 0);
lean_ctor_set(v___x_308_, 0, v_x_286_);
v___x_314_ = v___x_308_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_x_286_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
else
{
size_t v___x_316_; size_t v___x_317_; lean_object* v___x_318_; 
lean_del_object(v___x_308_);
v___x_316_ = ((size_t)0ULL);
v___x_317_ = lean_usize_of_nat(v___x_311_);
v___x_318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_284_, v_vs_306_, v___x_316_, v___x_317_, v_x_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
lean_dec_ref(v_vs_306_);
return v___x_318_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_auxDeclToFullName_284_ = stack[0].m_obj;
lean_object* v_x_285_ = stack[1].m_obj;
lean_object* v_x_286_ = stack[2].m_obj;
lean_object* v___y_287_ = stack[3].m_obj;
lean_object* v___y_288_ = stack[4].m_obj;
lean_object* v___y_289_ = stack[5].m_obj;
lean_object* v___y_290_ = stack[6].m_obj;
lean_object* v_res_320_;
v_res_320_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(v_auxDeclToFullName_284_, v_x_285_, v_x_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
stack->m_obj
 = v_res_320_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(lean_object* v_auxDeclToFullName_321_, lean_object* v_as_322_, size_t v_i_323_, size_t v_stop_324_, lean_object* v_b_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
uint8_t v___x_331_; 
v___x_331_ = lean_usize_dec_eq(v_i_323_, v_stop_324_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_array_uget_borrowed(v_as_322_, v_i_323_);
lean_inc(v___x_332_);
v___x_333_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(v_auxDeclToFullName_321_, v___x_332_, v_b_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; size_t v___x_335_; size_t v___x_336_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
v___x_335_ = ((size_t)1ULL);
v___x_336_ = lean_usize_add(v_i_323_, v___x_335_);
v_i_323_ = v___x_336_;
v_b_325_ = v_a_334_;
goto _start;
}
else
{
return v___x_333_;
}
}
else
{
lean_object* v___x_338_; 
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v_b_325_);
return v___x_338_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_auxDeclToFullName_321_ = stack[0].m_obj;
lean_object* v_as_322_ = stack[1].m_obj;
size_t v_i_323_ = stack[2].m_num;
size_t v_stop_324_ = stack[3].m_num;
lean_object* v_b_325_ = stack[4].m_obj;
lean_object* v___y_326_ = stack[5].m_obj;
lean_object* v___y_327_ = stack[6].m_obj;
lean_object* v___y_328_ = stack[7].m_obj;
lean_object* v___y_329_ = stack[8].m_obj;
lean_object* v_res_339_;
v_res_339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_321_, v_as_322_, v_i_323_, v_stop_324_, v_b_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
stack->m_obj
 = v_res_339_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9___boxed(lean_object* v_auxDeclToFullName_340_, lean_object* v_as_341_, lean_object* v_i_342_, lean_object* v_stop_343_, lean_object* v_b_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
size_t v_i_boxed_350_; size_t v_stop_boxed_351_; lean_object* v_res_352_; 
v_i_boxed_350_ = lean_unbox_usize(v_i_342_);
lean_dec(v_i_342_);
v_stop_boxed_351_ = lean_unbox_usize(v_stop_343_);
lean_dec(v_stop_343_);
v_res_352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_340_, v_as_341_, v_i_boxed_350_, v_stop_boxed_351_, v_b_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec_ref(v_as_341_);
lean_dec(v_auxDeclToFullName_340_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9___boxed(lean_object* v_auxDeclToFullName_353_, lean_object* v_x_354_, lean_object* v_x_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(v_auxDeclToFullName_353_, v_x_354_, v_x_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v_auxDeclToFullName_353_);
return v_res_361_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_362_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(lean_object* v_auxDeclToFullName_363_, lean_object* v_x_364_, size_t v_x_365_, size_t v_x_366_, lean_object* v_x_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
if (lean_obj_tag(v_x_364_) == 0)
{
lean_object* v_cs_373_; lean_object* v___x_374_; size_t v___x_375_; lean_object* v_j_376_; lean_object* v___x_377_; size_t v___x_378_; size_t v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; size_t v___x_383_; lean_object* v___x_384_; 
v_cs_373_ = lean_ctor_get(v_x_364_, 0);
lean_inc_ref(v_cs_373_);
lean_dec_ref_known(v_x_364_, 1);
v___x_374_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0);
v___x_375_ = lean_usize_shift_right(v_x_365_, v_x_366_);
v_j_376_ = lean_usize_to_nat(v___x_375_);
v___x_377_ = lean_array_get_borrowed(v___x_374_, v_cs_373_, v_j_376_);
v___x_378_ = ((size_t)1ULL);
v___x_379_ = lean_usize_shift_left(v___x_378_, v_x_366_);
v___x_380_ = lean_usize_sub(v___x_379_, v___x_378_);
v___x_381_ = lean_usize_land(v_x_365_, v___x_380_);
v___x_382_ = ((size_t)5ULL);
v___x_383_ = lean_usize_sub(v_x_366_, v___x_382_);
lean_inc(v___x_377_);
v___x_384_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(v_auxDeclToFullName_363_, v___x_377_, v___x_381_, v___x_383_, v_x_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_add(v_j_376_, v___x_386_);
lean_dec(v_j_376_);
v___x_388_ = lean_array_get_size(v_cs_373_);
v___x_389_ = lean_nat_dec_lt(v___x_387_, v___x_388_);
if (v___x_389_ == 0)
{
lean_dec(v___x_387_);
lean_dec_ref(v_cs_373_);
return v___x_384_;
}
else
{
size_t v___x_390_; size_t v___x_391_; lean_object* v___x_392_; 
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 1);
v___x_390_ = lean_usize_of_nat(v___x_387_);
lean_dec(v___x_387_);
v___x_391_ = lean_usize_of_nat(v___x_388_);
v___x_392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_363_, v_cs_373_, v___x_390_, v___x_391_, v_a_385_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
lean_dec_ref(v_cs_373_);
return v___x_392_;
}
}
else
{
lean_dec(v_j_376_);
lean_dec_ref(v_cs_373_);
return v___x_384_;
}
}
else
{
lean_object* v_vs_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_406_; 
v_vs_393_ = lean_ctor_get(v_x_364_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v_x_364_);
if (v_isSharedCheck_406_ == 0)
{
v___x_395_ = v_x_364_;
v_isShared_396_ = v_isSharedCheck_406_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_vs_393_);
lean_dec(v_x_364_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_406_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_397_ = lean_usize_to_nat(v_x_365_);
v___x_398_ = lean_array_get_size(v_vs_393_);
v___x_399_ = lean_nat_dec_lt(v___x_397_, v___x_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_401_; 
lean_dec(v___x_397_);
lean_dec_ref(v_vs_393_);
if (v_isShared_396_ == 0)
{
lean_ctor_set_tag(v___x_395_, 0);
lean_ctor_set(v___x_395_, 0, v_x_367_);
v___x_401_ = v___x_395_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_x_367_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
else
{
size_t v___x_403_; size_t v___x_404_; lean_object* v___x_405_; 
lean_del_object(v___x_395_);
v___x_403_ = lean_usize_of_nat(v___x_397_);
lean_dec(v___x_397_);
v___x_404_ = lean_usize_of_nat(v___x_398_);
v___x_405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_363_, v_vs_393_, v___x_403_, v___x_404_, v_x_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
lean_dec_ref(v_vs_393_);
return v___x_405_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_auxDeclToFullName_363_ = stack[0].m_obj;
lean_object* v_x_364_ = stack[1].m_obj;
size_t v_x_365_ = stack[2].m_num;
size_t v_x_366_ = stack[3].m_num;
lean_object* v_x_367_ = stack[4].m_obj;
lean_object* v___y_368_ = stack[5].m_obj;
lean_object* v___y_369_ = stack[6].m_obj;
lean_object* v___y_370_ = stack[7].m_obj;
lean_object* v___y_371_ = stack[8].m_obj;
lean_object* v_res_407_;
v_res_407_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(v_auxDeclToFullName_363_, v_x_364_, v_x_365_, v_x_366_, v_x_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
stack->m_obj
 = v_res_407_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___boxed(lean_object* v_auxDeclToFullName_408_, lean_object* v_x_409_, lean_object* v_x_410_, lean_object* v_x_411_, lean_object* v_x_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
size_t v_x_5662__boxed_418_; size_t v_x_5663__boxed_419_; lean_object* v_res_420_; 
v_x_5662__boxed_418_ = lean_unbox_usize(v_x_410_);
lean_dec(v_x_410_);
v_x_5663__boxed_419_ = lean_unbox_usize(v_x_411_);
lean_dec(v_x_411_);
v_res_420_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(v_auxDeclToFullName_408_, v_x_409_, v_x_5662__boxed_418_, v_x_5663__boxed_419_, v_x_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v_auxDeclToFullName_408_);
return v_res_420_;
}
}
lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5(lean_object* v_auxDeclToFullName_421_, lean_object* v_t_422_, lean_object* v_init_423_, lean_object* v_start_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = lean_nat_dec_eq(v_start_424_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v_root_432_; lean_object* v_tail_433_; size_t v_shift_434_; lean_object* v_tailOff_435_; uint8_t v___x_436_; 
v_root_432_ = lean_ctor_get(v_t_422_, 0);
lean_inc_ref(v_root_432_);
v_tail_433_ = lean_ctor_get(v_t_422_, 1);
lean_inc_ref(v_tail_433_);
v_shift_434_ = lean_ctor_get_usize(v_t_422_, 4);
v_tailOff_435_ = lean_ctor_get(v_t_422_, 3);
lean_inc(v_tailOff_435_);
lean_dec_ref(v_t_422_);
v___x_436_ = lean_nat_dec_le(v_tailOff_435_, v_start_424_);
if (v___x_436_ == 0)
{
size_t v___x_437_; lean_object* v___x_438_; 
lean_dec(v_tailOff_435_);
v___x_437_ = lean_usize_of_nat(v_start_424_);
v___x_438_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(v_auxDeclToFullName_421_, v_root_432_, v___x_437_, v_shift_434_, v_init_423_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v___x_440_ = lean_array_get_size(v_tail_433_);
v___x_441_ = lean_nat_dec_lt(v___x_430_, v___x_440_);
if (v___x_441_ == 0)
{
lean_dec_ref(v_tail_433_);
return v___x_438_;
}
else
{
size_t v___x_442_; size_t v___x_443_; lean_object* v___x_444_; 
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
v___x_442_ = ((size_t)0ULL);
v___x_443_ = lean_usize_of_nat(v___x_440_);
v___x_444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_421_, v_tail_433_, v___x_442_, v___x_443_, v_a_439_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
lean_dec_ref(v_tail_433_);
return v___x_444_;
}
}
else
{
lean_dec_ref(v_tail_433_);
return v___x_438_;
}
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
lean_dec_ref(v_root_432_);
v___x_445_ = lean_nat_sub(v_start_424_, v_tailOff_435_);
lean_dec(v_tailOff_435_);
v___x_446_ = lean_array_get_size(v_tail_433_);
v___x_447_ = lean_nat_dec_lt(v___x_445_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; 
lean_dec(v___x_445_);
lean_dec_ref(v_tail_433_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v_init_423_);
return v___x_448_;
}
else
{
size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; 
v___x_449_ = lean_usize_of_nat(v___x_445_);
lean_dec(v___x_445_);
v___x_450_ = lean_usize_of_nat(v___x_446_);
v___x_451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_421_, v_tail_433_, v___x_449_, v___x_450_, v_init_423_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
lean_dec_ref(v_tail_433_);
return v___x_451_;
}
}
}
else
{
lean_object* v_root_452_; lean_object* v_tail_453_; lean_object* v___x_454_; 
v_root_452_ = lean_ctor_get(v_t_422_, 0);
lean_inc_ref(v_root_452_);
v_tail_453_ = lean_ctor_get(v_t_422_, 1);
lean_inc_ref(v_tail_453_);
lean_dec_ref(v_t_422_);
v___x_454_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(v_auxDeclToFullName_421_, v_root_452_, v_init_423_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
v___x_456_ = lean_array_get_size(v_tail_453_);
v___x_457_ = lean_nat_dec_lt(v___x_430_, v___x_456_);
if (v___x_457_ == 0)
{
lean_dec_ref(v_tail_453_);
return v___x_454_;
}
else
{
size_t v___x_458_; size_t v___x_459_; lean_object* v___x_460_; 
lean_inc(v_a_455_);
lean_dec_ref_known(v___x_454_, 1);
v___x_458_ = ((size_t)0ULL);
v___x_459_ = lean_usize_of_nat(v___x_456_);
v___x_460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_421_, v_tail_453_, v___x_458_, v___x_459_, v_a_455_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
lean_dec_ref(v_tail_453_);
return v___x_460_;
}
}
else
{
lean_dec_ref(v_tail_453_);
return v___x_454_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_auxDeclToFullName_421_ = stack[0].m_obj;
lean_object* v_t_422_ = stack[1].m_obj;
lean_object* v_init_423_ = stack[2].m_obj;
lean_object* v_start_424_ = stack[3].m_obj;
lean_object* v___y_425_ = stack[4].m_obj;
lean_object* v___y_426_ = stack[5].m_obj;
lean_object* v___y_427_ = stack[6].m_obj;
lean_object* v___y_428_ = stack[7].m_obj;
lean_object* v_res_461_;
v_res_461_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5(v_auxDeclToFullName_421_, v_t_422_, v_init_423_, v_start_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5___boxed(lean_object* v_auxDeclToFullName_462_, lean_object* v_t_463_, lean_object* v_init_464_, lean_object* v_start_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5(v_auxDeclToFullName_462_, v_t_463_, v_init_464_, v_start_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v_start_465_);
lean_dec(v_auxDeclToFullName_462_);
return v_res_471_;
}
}
lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3(lean_object* v_auxDeclToFullName_472_, lean_object* v_lctx_473_, lean_object* v_init_474_, lean_object* v_start_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_decls_481_; lean_object* v___x_482_; 
v_decls_481_ = lean_ctor_get(v_lctx_473_, 1);
lean_inc_ref(v_decls_481_);
lean_dec_ref(v_lctx_473_);
v___x_482_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5(v_auxDeclToFullName_472_, v_decls_481_, v_init_474_, v_start_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
return v___x_482_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_auxDeclToFullName_472_ = stack[0].m_obj;
lean_object* v_lctx_473_ = stack[1].m_obj;
lean_object* v_init_474_ = stack[2].m_obj;
lean_object* v_start_475_ = stack[3].m_obj;
lean_object* v___y_476_ = stack[4].m_obj;
lean_object* v___y_477_ = stack[5].m_obj;
lean_object* v___y_478_ = stack[6].m_obj;
lean_object* v___y_479_ = stack[7].m_obj;
lean_object* v_res_483_;
v_res_483_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3(v_auxDeclToFullName_472_, v_lctx_473_, v_init_474_, v_start_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
stack->m_obj
 = v_res_483_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3___boxed(lean_object* v_auxDeclToFullName_484_, lean_object* v_lctx_485_, lean_object* v_init_486_, lean_object* v_start_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3(v_auxDeclToFullName_484_, v_lctx_485_, v_init_486_, v_start_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v_start_487_);
lean_dec(v_auxDeclToFullName_484_);
return v_res_493_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_494_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_unsigned_to_nat(32u);
v___x_498_ = lean_mk_empty_array_with_capacity(v___x_497_);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_500_ = ((size_t)5ULL);
v___x_501_ = lean_unsigned_to_nat(0u);
v___x_502_ = lean_unsigned_to_nat(32u);
v___x_503_ = lean_mk_empty_array_with_capacity(v___x_502_);
v___x_504_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2);
v___x_505_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v___x_503_);
lean_ctor_set(v___x_505_, 2, v___x_501_);
lean_ctor_set(v___x_505_, 3, v___x_501_);
lean_ctor_set_usize(v___x_505_, 4, v___x_500_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_506_ = lean_box(1);
v___x_507_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3);
v___x_508_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1);
v___x_509_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v___x_507_);
lean_ctor_set(v___x_509_, 2, v___x_506_);
return v___x_509_;
}
}
lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0(lean_object* v_lctx_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_auxDeclToFullName_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_auxDeclToFullName_516_ = lean_ctor_get(v_lctx_510_, 2);
lean_inc(v_auxDeclToFullName_516_);
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4);
v___x_519_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3(v_auxDeclToFullName_516_, v_lctx_510_, v___x_518_, v___x_517_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
lean_dec(v_auxDeclToFullName_516_);
return v___x_519_;
}
}
LEAN_EXPORT void l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_510_ = stack[0].m_obj;
lean_object* v___y_511_ = stack[1].m_obj;
lean_object* v___y_512_ = stack[2].m_obj;
lean_object* v___y_513_ = stack[3].m_obj;
lean_object* v___y_514_ = stack[4].m_obj;
lean_object* v_res_520_;
v_res_520_ = l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0(v_lctx_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
stack->m_obj
 = v_res_520_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___boxed(lean_object* v_lctx_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0(v_lctx_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12___redArg(lean_object* v_x_528_, lean_object* v_x_529_, lean_object* v_x_530_, lean_object* v_x_531_){
_start:
{
lean_object* v_ks_532_; lean_object* v_vs_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_557_; 
v_ks_532_ = lean_ctor_get(v_x_528_, 0);
v_vs_533_ = lean_ctor_get(v_x_528_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_x_528_);
if (v_isSharedCheck_557_ == 0)
{
v___x_535_ = v_x_528_;
v_isShared_536_ = v_isSharedCheck_557_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_vs_533_);
lean_inc(v_ks_532_);
lean_dec(v_x_528_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_557_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_537_ = lean_array_get_size(v_ks_532_);
v___x_538_ = lean_nat_dec_lt(v_x_529_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
lean_dec(v_x_529_);
v___x_539_ = lean_array_push(v_ks_532_, v_x_530_);
v___x_540_ = lean_array_push(v_vs_533_, v_x_531_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 1, v___x_540_);
lean_ctor_set(v___x_535_, 0, v___x_539_);
v___x_542_ = v___x_535_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
else
{
lean_object* v_k_x27_544_; uint8_t v___x_545_; 
v_k_x27_544_ = lean_array_fget_borrowed(v_ks_532_, v_x_529_);
v___x_545_ = l_Lean_instBEqMVarId_beq(v_x_530_, v_k_x27_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_547_; 
if (v_isShared_536_ == 0)
{
v___x_547_ = v___x_535_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_ks_532_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_vs_533_);
v___x_547_ = v_reuseFailAlloc_551_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_unsigned_to_nat(1u);
v___x_549_ = lean_nat_add(v_x_529_, v___x_548_);
lean_dec(v_x_529_);
v_x_528_ = v___x_547_;
v_x_529_ = v___x_549_;
goto _start;
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_552_ = lean_array_fset(v_ks_532_, v_x_529_, v_x_530_);
v___x_553_ = lean_array_fset(v_vs_533_, v_x_529_, v_x_531_);
lean_dec(v_x_529_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 1, v___x_553_);
lean_ctor_set(v___x_535_, 0, v___x_552_);
v___x_555_ = v___x_535_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8___redArg(lean_object* v_n_558_, lean_object* v_k_559_, lean_object* v_v_560_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12___redArg(v_n_558_, v___x_561_, v_k_559_, v_v_560_);
return v___x_562_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_563_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(lean_object* v_x_564_, size_t v_x_565_, size_t v_x_566_, lean_object* v_x_567_, lean_object* v_x_568_){
_start:
{
if (lean_obj_tag(v_x_564_) == 0)
{
lean_object* v_es_569_; size_t v___x_570_; size_t v___x_571_; lean_object* v_j_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v_es_569_ = lean_ctor_get(v_x_564_, 0);
v___x_570_ = ((size_t)31ULL);
v___x_571_ = lean_usize_land(v_x_565_, v___x_570_);
v_j_572_ = lean_usize_to_nat(v___x_571_);
v___x_573_ = lean_array_get_size(v_es_569_);
v___x_574_ = lean_nat_dec_lt(v_j_572_, v___x_573_);
if (v___x_574_ == 0)
{
lean_dec(v_j_572_);
lean_dec(v_x_568_);
lean_dec(v_x_567_);
return v_x_564_;
}
else
{
lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_613_; 
lean_inc_ref(v_es_569_);
v_isSharedCheck_613_ = !lean_is_exclusive(v_x_564_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; 
v_unused_614_ = lean_ctor_get(v_x_564_, 0);
lean_dec(v_unused_614_);
v___x_576_ = v_x_564_;
v_isShared_577_ = v_isSharedCheck_613_;
goto v_resetjp_575_;
}
else
{
lean_dec(v_x_564_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_613_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v_v_578_; lean_object* v___x_579_; lean_object* v_xs_x27_580_; lean_object* v___y_582_; 
v_v_578_ = lean_array_fget(v_es_569_, v_j_572_);
v___x_579_ = lean_box(0);
v_xs_x27_580_ = lean_array_fset(v_es_569_, v_j_572_, v___x_579_);
switch(lean_obj_tag(v_v_578_))
{
case 0:
{
lean_object* v_key_587_; lean_object* v_val_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_598_; 
v_key_587_ = lean_ctor_get(v_v_578_, 0);
v_val_588_ = lean_ctor_get(v_v_578_, 1);
v_isSharedCheck_598_ = !lean_is_exclusive(v_v_578_);
if (v_isSharedCheck_598_ == 0)
{
v___x_590_ = v_v_578_;
v_isShared_591_ = v_isSharedCheck_598_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_val_588_);
lean_inc(v_key_587_);
lean_dec(v_v_578_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_598_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
uint8_t v___x_592_; 
v___x_592_ = l_Lean_instBEqMVarId_beq(v_x_567_, v_key_587_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_del_object(v___x_590_);
v___x_593_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_587_, v_val_588_, v_x_567_, v_x_568_);
v___x_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
v___y_582_ = v___x_594_;
goto v___jp_581_;
}
else
{
lean_object* v___x_596_; 
lean_dec(v_val_588_);
lean_dec(v_key_587_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v_x_568_);
lean_ctor_set(v___x_590_, 0, v_x_567_);
v___x_596_ = v___x_590_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_x_567_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_x_568_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
v___y_582_ = v___x_596_;
goto v___jp_581_;
}
}
}
}
case 1:
{
lean_object* v_node_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_611_; 
v_node_599_ = lean_ctor_get(v_v_578_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v_v_578_);
if (v_isSharedCheck_611_ == 0)
{
v___x_601_ = v_v_578_;
v_isShared_602_ = v_isSharedCheck_611_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_node_599_);
lean_dec(v_v_578_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_611_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
size_t v___x_603_; size_t v___x_604_; size_t v___x_605_; size_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_603_ = ((size_t)5ULL);
v___x_604_ = lean_usize_shift_right(v_x_565_, v___x_603_);
v___x_605_ = ((size_t)1ULL);
v___x_606_ = lean_usize_add(v_x_566_, v___x_605_);
v___x_607_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_node_599_, v___x_604_, v___x_606_, v_x_567_, v_x_568_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_607_);
v___x_609_ = v___x_601_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
v___y_582_ = v___x_609_;
goto v___jp_581_;
}
}
}
default: 
{
lean_object* v___x_612_; 
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v_x_567_);
lean_ctor_set(v___x_612_, 1, v_x_568_);
v___y_582_ = v___x_612_;
goto v___jp_581_;
}
}
v___jp_581_:
{
lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_583_ = lean_array_fset(v_xs_x27_580_, v_j_572_, v___y_582_);
lean_dec(v_j_572_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_583_);
v___x_585_ = v___x_576_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
else
{
lean_object* v_ks_615_; lean_object* v_vs_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_634_; 
v_ks_615_ = lean_ctor_get(v_x_564_, 0);
v_vs_616_ = lean_ctor_get(v_x_564_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_x_564_);
if (v_isSharedCheck_634_ == 0)
{
v___x_618_ = v_x_564_;
v_isShared_619_ = v_isSharedCheck_634_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_vs_616_);
lean_inc(v_ks_615_);
lean_dec(v_x_564_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_634_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_ks_615_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_vs_616_);
v___x_621_ = v_reuseFailAlloc_633_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v_newNode_622_; size_t v___x_623_; uint8_t v___x_624_; 
v_newNode_622_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8___redArg(v___x_621_, v_x_567_, v_x_568_);
v___x_623_ = ((size_t)7ULL);
v___x_624_ = lean_usize_dec_le(v___x_623_, v_x_566_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_625_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_622_);
v___x_626_ = lean_unsigned_to_nat(4u);
v___x_627_ = lean_nat_dec_lt(v___x_625_, v___x_626_);
lean_dec(v___x_625_);
if (v___x_627_ == 0)
{
lean_object* v_ks_628_; lean_object* v_vs_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_ks_628_ = lean_ctor_get(v_newNode_622_, 0);
lean_inc_ref(v_ks_628_);
v_vs_629_ = lean_ctor_get(v_newNode_622_, 1);
lean_inc_ref(v_vs_629_);
lean_dec_ref(v_newNode_622_);
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0);
v___x_632_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(v_x_566_, v_ks_628_, v_vs_629_, v___x_630_, v___x_631_);
lean_dec_ref(v_vs_629_);
lean_dec_ref(v_ks_628_);
return v___x_632_;
}
else
{
return v_newNode_622_;
}
}
else
{
return v_newNode_622_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_564_ = stack[0].m_obj;
size_t v_x_565_ = stack[1].m_num;
size_t v_x_566_ = stack[2].m_num;
lean_object* v_x_567_ = stack[3].m_obj;
lean_object* v_x_568_ = stack[4].m_obj;
lean_object* v_res_635_;
v_res_635_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_x_564_, v_x_565_, v_x_566_, v_x_567_, v_x_568_);
stack->m_obj
 = v_res_635_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(size_t v_depth_636_, lean_object* v_keys_637_, lean_object* v_vals_638_, lean_object* v_i_639_, lean_object* v_entries_640_){
_start:
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_array_get_size(v_keys_637_);
v___x_642_ = lean_nat_dec_lt(v_i_639_, v___x_641_);
if (v___x_642_ == 0)
{
lean_dec(v_i_639_);
return v_entries_640_;
}
else
{
lean_object* v_k_643_; lean_object* v_v_644_; uint64_t v___x_645_; size_t v_h_646_; size_t v___x_647_; lean_object* v___x_648_; size_t v___x_649_; size_t v___x_650_; size_t v___x_651_; size_t v_h_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_k_643_ = lean_array_fget_borrowed(v_keys_637_, v_i_639_);
v_v_644_ = lean_array_fget_borrowed(v_vals_638_, v_i_639_);
v___x_645_ = l_Lean_instHashableMVarId_hash(v_k_643_);
v_h_646_ = lean_uint64_to_usize(v___x_645_);
v___x_647_ = ((size_t)5ULL);
v___x_648_ = lean_unsigned_to_nat(1u);
v___x_649_ = ((size_t)1ULL);
v___x_650_ = lean_usize_sub(v_depth_636_, v___x_649_);
v___x_651_ = lean_usize_mul(v___x_647_, v___x_650_);
v_h_652_ = lean_usize_shift_right(v_h_646_, v___x_651_);
v___x_653_ = lean_nat_add(v_i_639_, v___x_648_);
lean_dec(v_i_639_);
lean_inc(v_v_644_);
lean_inc(v_k_643_);
v___x_654_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_entries_640_, v_h_652_, v_depth_636_, v_k_643_, v_v_644_);
v_i_639_ = v___x_653_;
v_entries_640_ = v___x_654_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_636_ = stack[0].m_num;
lean_object* v_keys_637_ = stack[1].m_obj;
lean_object* v_vals_638_ = stack[2].m_obj;
lean_object* v_i_639_ = stack[3].m_obj;
lean_object* v_entries_640_ = stack[4].m_obj;
lean_object* v_res_656_;
v_res_656_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(v_depth_636_, v_keys_637_, v_vals_638_, v_i_639_, v_entries_640_);
stack->m_obj
 = v_res_656_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg___boxed(lean_object* v_depth_657_, lean_object* v_keys_658_, lean_object* v_vals_659_, lean_object* v_i_660_, lean_object* v_entries_661_){
_start:
{
size_t v_depth_boxed_662_; lean_object* v_res_663_; 
v_depth_boxed_662_ = lean_unbox_usize(v_depth_657_);
lean_dec(v_depth_657_);
v_res_663_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(v_depth_boxed_662_, v_keys_658_, v_vals_659_, v_i_660_, v_entries_661_);
lean_dec_ref(v_vals_659_);
lean_dec_ref(v_keys_658_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_x_664_, lean_object* v_x_665_, lean_object* v_x_666_, lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
size_t v_x_6146__boxed_669_; size_t v_x_6147__boxed_670_; lean_object* v_res_671_; 
v_x_6146__boxed_669_ = lean_unbox_usize(v_x_665_);
lean_dec(v_x_665_);
v_x_6147__boxed_670_ = lean_unbox_usize(v_x_666_);
lean_dec(v_x_666_);
v_res_671_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_x_664_, v_x_6146__boxed_669_, v_x_6147__boxed_670_, v_x_667_, v_x_668_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2___redArg(lean_object* v_x_672_, lean_object* v_x_673_, lean_object* v_x_674_){
_start:
{
uint64_t v___x_675_; size_t v___x_676_; size_t v___x_677_; lean_object* v___x_678_; 
v___x_675_ = l_Lean_instHashableMVarId_hash(v_x_673_);
v___x_676_ = lean_uint64_to_usize(v___x_675_);
v___x_677_ = ((size_t)1ULL);
v___x_678_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_x_672_, v___x_676_, v___x_677_, v_x_673_, v_x_674_);
return v___x_678_;
}
}
lean_object* l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0(lean_object* v_mvarId_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v___x_685_; lean_object* v_mctx_686_; lean_object* v_mvarDecl_687_; lean_object* v_userName_688_; lean_object* v_lctx_689_; lean_object* v_type_690_; lean_object* v_depth_691_; lean_object* v_localInstances_692_; uint8_t v_kind_693_; lean_object* v_numScopeArgs_694_; lean_object* v_index_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_760_; 
v___x_685_ = lean_st_ref_get(v___y_681_);
v_mctx_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc_ref(v_mctx_686_);
lean_dec(v___x_685_);
lean_inc(v_mvarId_679_);
v_mvarDecl_687_ = l_Lean_MetavarContext_getDecl(v_mctx_686_, v_mvarId_679_);
lean_dec_ref(v_mctx_686_);
v_userName_688_ = lean_ctor_get(v_mvarDecl_687_, 0);
v_lctx_689_ = lean_ctor_get(v_mvarDecl_687_, 1);
v_type_690_ = lean_ctor_get(v_mvarDecl_687_, 2);
v_depth_691_ = lean_ctor_get(v_mvarDecl_687_, 3);
v_localInstances_692_ = lean_ctor_get(v_mvarDecl_687_, 4);
v_kind_693_ = lean_ctor_get_uint8(v_mvarDecl_687_, sizeof(void*)*7);
v_numScopeArgs_694_ = lean_ctor_get(v_mvarDecl_687_, 5);
v_index_695_ = lean_ctor_get(v_mvarDecl_687_, 6);
v_isSharedCheck_760_ = !lean_is_exclusive(v_mvarDecl_687_);
if (v_isSharedCheck_760_ == 0)
{
v___x_697_ = v_mvarDecl_687_;
v_isShared_698_ = v_isSharedCheck_760_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_index_695_);
lean_inc(v_numScopeArgs_694_);
lean_inc(v_localInstances_692_);
lean_inc(v_depth_691_);
lean_inc(v_type_690_);
lean_inc(v_lctx_689_);
lean_inc(v_userName_688_);
lean_dec(v_mvarDecl_687_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_760_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0(v_lctx_689_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_701_; lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_751_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_699_, 1);
v___x_701_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_type_690_, v___y_681_);
v_a_702_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_751_ == 0)
{
v___x_704_ = v___x_701_;
v_isShared_705_ = v_isSharedCheck_751_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_701_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_751_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v_fst_708_; lean_object* v_snd_709_; lean_object* v___x_710_; lean_object* v_mctx_711_; lean_object* v_cache_712_; lean_object* v_zetaDeltaFVarIds_713_; lean_object* v_postponed_714_; lean_object* v_diag_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_750_; 
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v_a_700_);
lean_ctor_set(v___x_706_, 1, v_a_702_);
v___x_707_ = lean_sharecommon_quick(v___x_706_);
lean_dec_ref_known(v___x_706_, 2);
v_fst_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_fst_708_);
v_snd_709_ = lean_ctor_get(v___x_707_, 1);
lean_inc(v_snd_709_);
lean_dec(v___x_707_);
v___x_710_ = lean_st_ref_take(v___y_681_);
v_mctx_711_ = lean_ctor_get(v___x_710_, 0);
v_cache_712_ = lean_ctor_get(v___x_710_, 1);
v_zetaDeltaFVarIds_713_ = lean_ctor_get(v___x_710_, 2);
v_postponed_714_ = lean_ctor_get(v___x_710_, 3);
v_diag_715_ = lean_ctor_get(v___x_710_, 4);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_750_ == 0)
{
v___x_717_ = v___x_710_;
v_isShared_718_ = v_isSharedCheck_750_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_diag_715_);
lean_inc(v_postponed_714_);
lean_inc(v_zetaDeltaFVarIds_713_);
lean_inc(v_cache_712_);
lean_inc(v_mctx_711_);
lean_dec(v___x_710_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_750_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v_depth_719_; lean_object* v_levelAssignDepth_720_; lean_object* v_lmvarCounter_721_; lean_object* v_mvarCounter_722_; lean_object* v_lDecls_723_; lean_object* v_decls_724_; lean_object* v_userNames_725_; lean_object* v_lAssignment_726_; lean_object* v_eAssignment_727_; lean_object* v_dAssignment_728_; lean_object* v_instanceTypedMVars_729_; lean_object* v_synthNormMemo_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_749_; 
v_depth_719_ = lean_ctor_get(v_mctx_711_, 0);
v_levelAssignDepth_720_ = lean_ctor_get(v_mctx_711_, 1);
v_lmvarCounter_721_ = lean_ctor_get(v_mctx_711_, 2);
v_mvarCounter_722_ = lean_ctor_get(v_mctx_711_, 3);
v_lDecls_723_ = lean_ctor_get(v_mctx_711_, 4);
v_decls_724_ = lean_ctor_get(v_mctx_711_, 5);
v_userNames_725_ = lean_ctor_get(v_mctx_711_, 6);
v_lAssignment_726_ = lean_ctor_get(v_mctx_711_, 7);
v_eAssignment_727_ = lean_ctor_get(v_mctx_711_, 8);
v_dAssignment_728_ = lean_ctor_get(v_mctx_711_, 9);
v_instanceTypedMVars_729_ = lean_ctor_get(v_mctx_711_, 10);
v_synthNormMemo_730_ = lean_ctor_get(v_mctx_711_, 11);
v_isSharedCheck_749_ = !lean_is_exclusive(v_mctx_711_);
if (v_isSharedCheck_749_ == 0)
{
v___x_732_ = v_mctx_711_;
v_isShared_733_ = v_isSharedCheck_749_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_synthNormMemo_730_);
lean_inc(v_instanceTypedMVars_729_);
lean_inc(v_dAssignment_728_);
lean_inc(v_eAssignment_727_);
lean_inc(v_lAssignment_726_);
lean_inc(v_userNames_725_);
lean_inc(v_decls_724_);
lean_inc(v_lDecls_723_);
lean_inc(v_mvarCounter_722_);
lean_inc(v_lmvarCounter_721_);
lean_inc(v_levelAssignDepth_720_);
lean_inc(v_depth_719_);
lean_dec(v_mctx_711_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_749_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_734_ = lean_box(0);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 2, v_snd_709_);
lean_ctor_set(v___x_697_, 1, v_fst_708_);
v___x_736_ = v___x_697_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_userName_688_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_fst_708_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_snd_709_);
lean_ctor_set(v_reuseFailAlloc_748_, 3, v_depth_691_);
lean_ctor_set(v_reuseFailAlloc_748_, 4, v_localInstances_692_);
lean_ctor_set(v_reuseFailAlloc_748_, 5, v_numScopeArgs_694_);
lean_ctor_set(v_reuseFailAlloc_748_, 6, v_index_695_);
lean_ctor_set_uint8(v_reuseFailAlloc_748_, sizeof(void*)*7, v_kind_693_);
v___x_736_ = v_reuseFailAlloc_748_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2___redArg(v_decls_724_, v_mvarId_679_, v___x_736_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 5, v___x_737_);
v___x_739_ = v___x_732_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_depth_719_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_levelAssignDepth_720_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_lmvarCounter_721_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v_mvarCounter_722_);
lean_ctor_set(v_reuseFailAlloc_747_, 4, v_lDecls_723_);
lean_ctor_set(v_reuseFailAlloc_747_, 5, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_747_, 6, v_userNames_725_);
lean_ctor_set(v_reuseFailAlloc_747_, 7, v_lAssignment_726_);
lean_ctor_set(v_reuseFailAlloc_747_, 8, v_eAssignment_727_);
lean_ctor_set(v_reuseFailAlloc_747_, 9, v_dAssignment_728_);
lean_ctor_set(v_reuseFailAlloc_747_, 10, v_instanceTypedMVars_729_);
lean_ctor_set(v_reuseFailAlloc_747_, 11, v_synthNormMemo_730_);
v___x_739_ = v_reuseFailAlloc_747_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___x_741_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_739_);
v___x_741_ = v___x_717_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_cache_712_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_zetaDeltaFVarIds_713_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v_postponed_714_);
lean_ctor_set(v_reuseFailAlloc_746_, 4, v_diag_715_);
v___x_741_ = v_reuseFailAlloc_746_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_742_ = lean_st_ref_put(v___y_681_, v___x_741_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_734_);
v___x_744_ = v___x_704_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_734_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
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
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_del_object(v___x_697_);
lean_dec(v_index_695_);
lean_dec(v_numScopeArgs_694_);
lean_dec_ref(v_localInstances_692_);
lean_dec(v_depth_691_);
lean_dec_ref(v_type_690_);
lean_dec(v_userName_688_);
lean_dec(v_mvarId_679_);
v_a_752_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_699_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_699_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_679_ = stack[0].m_obj;
lean_object* v___y_680_ = stack[1].m_obj;
lean_object* v___y_681_ = stack[2].m_obj;
lean_object* v___y_682_ = stack[3].m_obj;
lean_object* v___y_683_ = stack[4].m_obj;
lean_object* v_res_761_;
v_res_761_ = l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0(v_mvarId_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
stack->m_obj
 = v_res_761_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0___boxed(lean_object* v_mvarId_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0(v_mvarId_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
return v_res_768_;
}
}
lean_object* l_Lean_Elab_runTactic(lean_object* v_mvarId_769_, lean_object* v_tacticCode_770_, lean_object* v_ctx_771_, lean_object* v_s_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v___f_778_; lean_object* v___x_779_; 
v___f_778_ = lean_alloc_closure((void*)(l_Lean_Elab_runTactic___lam__0___boxed), 10, 1);
lean_closure_set(v___f_778_, 0, v_tacticCode_770_);
lean_inc(v_mvarId_769_);
v___x_779_ = l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0(v_mvarId_769_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v___x_780_; uint8_t v___x_781_; lean_object* v___x_782_; lean_object* v___f_783_; lean_object* v___x_784_; 
lean_dec_ref_known(v___x_779_, 1);
v___x_780_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_780_, 0, v_mvarId_769_);
lean_closure_set(v___x_780_, 1, v___f_778_);
v___x_781_ = 1;
v___x_782_ = lean_box(v___x_781_);
v___f_783_ = lean_alloc_closure((void*)(l_Lean_Elab_runTactic___lam__1___boxed), 9, 2);
lean_closure_set(v___f_783_, 0, v___x_780_);
lean_closure_set(v___f_783_, 1, v___x_782_);
v___x_784_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_783_, v_ctx_771_, v_s_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
return v___x_784_;
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec_ref(v___f_778_);
lean_dec_ref(v_s_772_);
lean_dec_ref(v_ctx_771_);
lean_dec(v_mvarId_769_);
v_a_785_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_779_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_779_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_runTactic_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_769_ = stack[0].m_obj;
lean_object* v_tacticCode_770_ = stack[1].m_obj;
lean_object* v_ctx_771_ = stack[2].m_obj;
lean_object* v_s_772_ = stack[3].m_obj;
lean_object* v_a_773_ = stack[4].m_obj;
lean_object* v_a_774_ = stack[5].m_obj;
lean_object* v_a_775_ = stack[6].m_obj;
lean_object* v_a_776_ = stack[7].m_obj;
lean_object* v_res_793_;
v_res_793_ = l_Lean_Elab_runTactic(v_mvarId_769_, v_tacticCode_770_, v_ctx_771_, v_s_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
stack->m_obj
 = v_res_793_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic___boxed(lean_object* v_mvarId_794_, lean_object* v_tacticCode_795_, lean_object* v_ctx_796_, lean_object* v_s_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_Elab_runTactic(v_mvarId_794_, v_tacticCode_795_, v_ctx_796_, v_s_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
return v_res_803_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1(lean_object* v_e_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_e_804_, v___y_806_);
return v___x_810_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_804_ = stack[0].m_obj;
lean_object* v___y_805_ = stack[1].m_obj;
lean_object* v___y_806_ = stack[2].m_obj;
lean_object* v___y_807_ = stack[3].m_obj;
lean_object* v___y_808_ = stack[4].m_obj;
lean_object* v_res_811_;
v_res_811_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1(v_e_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
stack->m_obj
 = v_res_811_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___boxed(lean_object* v_e_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1(v_e_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2(lean_object* v_00_u03b2_819_, lean_object* v_x_820_, lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2___redArg(v_x_820_, v_x_821_, v_x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1(lean_object* v_00_u03b4_824_, lean_object* v_t_825_, lean_object* v_k_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg(v_t_825_, v_k_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b4_828_, lean_object* v_t_829_, lean_object* v_k_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1(v_00_u03b4_828_, v_t_829_, v_k_830_);
lean_dec(v_k_830_);
lean_dec(v_t_829_);
return v_res_831_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_832_, lean_object* v_x_833_, size_t v_x_834_, size_t v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_x_833_, v_x_834_, v_x_835_, v_x_836_, v_x_837_);
return v___x_838_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_833_ = stack[1].m_obj;
size_t v_x_834_ = stack[2].m_num;
size_t v_x_835_ = stack[3].m_num;
lean_object* v_x_836_ = stack[4].m_obj;
lean_object* v_x_837_ = stack[5].m_obj;
lean_object* v_res_839_;
v_res_839_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6(lean_box(0), v_x_833_, v_x_834_, v_x_835_, v_x_836_, v_x_837_);
stack->m_obj
 = v_res_839_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
size_t v_x_6670__boxed_846_; size_t v_x_6671__boxed_847_; lean_object* v_res_848_; 
v_x_6670__boxed_846_ = lean_unbox_usize(v_x_842_);
lean_dec(v_x_842_);
v_x_6671__boxed_847_ = lean_unbox_usize(v_x_843_);
lean_dec(v_x_843_);
v_res_848_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6(v_00_u03b2_840_, v_x_841_, v_x_6670__boxed_846_, v_x_6671__boxed_847_, v_x_844_, v_x_845_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8(lean_object* v_00_u03b2_849_, lean_object* v_n_850_, lean_object* v_k_851_, lean_object* v_v_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8___redArg(v_n_850_, v_k_851_, v_v_852_);
return v___x_853_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9(lean_object* v_00_u03b2_854_, size_t v_depth_855_, lean_object* v_keys_856_, lean_object* v_vals_857_, lean_object* v_heq_858_, lean_object* v_i_859_, lean_object* v_entries_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(v_depth_855_, v_keys_856_, v_vals_857_, v_i_859_, v_entries_860_);
return v___x_861_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_depth_855_ = stack[1].m_num;
lean_object* v_keys_856_ = stack[2].m_obj;
lean_object* v_vals_857_ = stack[3].m_obj;
lean_object* v_i_859_ = stack[5].m_obj;
lean_object* v_entries_860_ = stack[6].m_obj;
lean_object* v_res_862_;
v_res_862_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9(lean_box(0), v_depth_855_, v_keys_856_, v_vals_857_, lean_box(0), v_i_859_, v_entries_860_);
stack->m_obj
 = v_res_862_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___boxed(lean_object* v_00_u03b2_863_, lean_object* v_depth_864_, lean_object* v_keys_865_, lean_object* v_vals_866_, lean_object* v_heq_867_, lean_object* v_i_868_, lean_object* v_entries_869_){
_start:
{
size_t v_depth_boxed_870_; lean_object* v_res_871_; 
v_depth_boxed_870_ = lean_unbox_usize(v_depth_864_);
lean_dec(v_depth_864_);
v_res_871_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9(v_00_u03b2_863_, v_depth_boxed_870_, v_keys_865_, v_vals_866_, v_heq_867_, v_i_868_, v_entries_869_);
lean_dec_ref(v_vals_866_);
lean_dec_ref(v_keys_865_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12(lean_object* v_00_u03b2_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12___redArg(v_x_873_, v_x_874_, v_x_875_, v_x_876_);
return v___x_877_;
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
