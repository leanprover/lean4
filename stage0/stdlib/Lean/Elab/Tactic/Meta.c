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
uint8_t lean_bool_not(uint8_t);
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
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_2500__overap_107_; lean_object* v___x_108_; 
v___x_105_ = l_Lean_instInhabitedLocalContext_default;
v___x_106_ = l_instInhabitedOfMonad___redArg(v___x_104_, v___x_105_);
v___x_2500__overap_107_ = lean_panic_fn_borrowed(v___x_106_, v_msg_50_);
lean_dec(v___x_106_);
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
v___x_108_ = lean_apply_5(v___x_2500__overap_107_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, lean_box(0));
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
uint8_t v___x_131_; uint8_t v___x_132_; 
v___x_131_ = l_Lean_Expr_hasMVar(v_e_128_);
v___x_132_ = lean_bool_not(v___x_131_);
if (v___x_132_ == 0)
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
else
{
lean_object* v___x_153_; 
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v_e_128_);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg___boxed(lean_object* v_e_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_e_154_, v___y_155_);
lean_dec(v___y_155_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg(lean_object* v_t_158_, lean_object* v_k_159_){
_start:
{
if (lean_obj_tag(v_t_158_) == 0)
{
lean_object* v_k_160_; lean_object* v_v_161_; lean_object* v_l_162_; lean_object* v_r_163_; uint8_t v___x_164_; 
v_k_160_ = lean_ctor_get(v_t_158_, 1);
v_v_161_ = lean_ctor_get(v_t_158_, 2);
v_l_162_ = lean_ctor_get(v_t_158_, 3);
v_r_163_ = lean_ctor_get(v_t_158_, 4);
v___x_164_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_159_, v_k_160_);
switch(v___x_164_)
{
case 0:
{
v_t_158_ = v_l_162_;
goto _start;
}
case 1:
{
lean_object* v___x_166_; 
lean_inc(v_v_161_);
v___x_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_166_, 0, v_v_161_);
return v___x_166_;
}
default: 
{
v_t_158_ = v_r_163_;
goto _start;
}
}
}
else
{
lean_object* v___x_168_; 
v___x_168_ = lean_box(0);
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_t_169_, lean_object* v_k_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg(v_t_169_, v_k_170_);
lean_dec(v_k_170_);
lean_dec(v_t_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(lean_object* v_auxDeclToFullName_176_, lean_object* v_as_177_, size_t v_i_178_, size_t v_stop_179_, lean_object* v_b_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_a_187_; uint8_t v___x_191_; 
v___x_191_ = lean_usize_dec_eq(v_i_178_, v_stop_179_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; 
v___x_192_ = lean_array_uget_borrowed(v_as_177_, v_i_178_);
if (lean_obj_tag(v___x_192_) == 0)
{
v_a_187_ = v_b_180_;
goto v___jp_186_;
}
else
{
lean_object* v_val_193_; 
v_val_193_ = lean_ctor_get(v___x_192_, 0);
if (lean_obj_tag(v_val_193_) == 0)
{
uint8_t v_kind_194_; 
v_kind_194_ = lean_ctor_get_uint8(v_val_193_, sizeof(void*)*4 + 1);
if (v_kind_194_ == 2)
{
lean_object* v_fvarId_195_; lean_object* v_userName_196_; lean_object* v_type_197_; lean_object* v___x_198_; 
v_fvarId_195_ = lean_ctor_get(v_val_193_, 1);
v_userName_196_ = lean_ctor_get(v_val_193_, 2);
v_type_197_ = lean_ctor_get(v_val_193_, 3);
lean_inc_ref(v_type_197_);
v___x_198_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_type_197_, v___y_182_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_200_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
lean_dec_ref_known(v___x_198_, 1);
v___x_200_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg(v_auxDeclToFullName_176_, v_fvarId_195_);
if (lean_obj_tag(v___x_200_) == 1)
{
lean_object* v_val_201_; lean_object* v___x_202_; 
v_val_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_val_201_);
lean_dec_ref_known(v___x_200_, 1);
lean_inc(v_userName_196_);
lean_inc(v_fvarId_195_);
v___x_202_ = l_Lean_LocalContext_mkAuxDecl(v_b_180_, v_fvarId_195_, v_userName_196_, v_a_199_, v_val_201_);
v_a_187_ = v___x_202_;
goto v___jp_186_;
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec(v___x_200_);
lean_dec(v_a_199_);
lean_dec_ref(v_b_180_);
v___x_203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__0));
v___x_204_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__1));
v___x_205_ = lean_unsigned_to_nat(635u);
v___x_206_ = lean_unsigned_to_nat(12u);
v___x_207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__2));
v___x_208_ = 1;
lean_inc(v_userName_196_);
v___x_209_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_196_, v___x_208_);
v___x_210_ = lean_string_append(v___x_207_, v___x_209_);
lean_dec_ref(v___x_209_);
v___x_211_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__3));
v___x_212_ = lean_string_append(v___x_210_, v___x_211_);
v___x_213_ = l_mkPanicMessageWithDecl(v___x_203_, v___x_204_, v___x_205_, v___x_206_, v___x_212_);
lean_dec_ref(v___x_212_);
v___x_214_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2(v___x_213_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_a_215_);
lean_dec_ref_known(v___x_214_, 1);
v_a_187_ = v_a_215_;
goto v___jp_186_;
}
else
{
return v___x_214_;
}
}
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_dec_ref(v_b_180_);
v_a_216_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_198_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_198_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
else
{
lean_object* v_fvarId_224_; lean_object* v_userName_225_; lean_object* v_type_226_; uint8_t v_bi_227_; lean_object* v___x_228_; 
v_fvarId_224_ = lean_ctor_get(v_val_193_, 1);
v_userName_225_ = lean_ctor_get(v_val_193_, 2);
v_type_226_ = lean_ctor_get(v_val_193_, 3);
v_bi_227_ = lean_ctor_get_uint8(v_val_193_, sizeof(void*)*4);
lean_inc_ref(v_type_226_);
v___x_228_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_type_226_, v___y_182_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_230_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref_known(v___x_228_, 1);
lean_inc(v_userName_225_);
lean_inc(v_fvarId_224_);
v___x_230_ = l_Lean_LocalContext_mkLocalDecl(v_b_180_, v_fvarId_224_, v_userName_225_, v_a_229_, v_bi_227_, v_kind_194_);
v_a_187_ = v___x_230_;
goto v___jp_186_;
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_dec_ref(v_b_180_);
v_a_231_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_228_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_228_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
else
{
lean_object* v_fvarId_239_; lean_object* v_userName_240_; lean_object* v_type_241_; lean_object* v_value_242_; uint8_t v_nondep_243_; uint8_t v_kind_244_; lean_object* v___x_245_; 
v_fvarId_239_ = lean_ctor_get(v_val_193_, 1);
v_userName_240_ = lean_ctor_get(v_val_193_, 2);
v_type_241_ = lean_ctor_get(v_val_193_, 3);
v_value_242_ = lean_ctor_get(v_val_193_, 4);
v_nondep_243_ = lean_ctor_get_uint8(v_val_193_, sizeof(void*)*5);
v_kind_244_ = lean_ctor_get_uint8(v_val_193_, sizeof(void*)*5 + 1);
lean_inc_ref(v_type_241_);
v___x_245_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_type_241_, v___y_182_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_247_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_246_);
lean_dec_ref_known(v___x_245_, 1);
lean_inc_ref(v_value_242_);
v___x_247_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_value_242_, v___y_182_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_249_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_a_248_);
lean_dec_ref_known(v___x_247_, 1);
lean_inc(v_userName_240_);
lean_inc(v_fvarId_239_);
v___x_249_ = l_Lean_LocalContext_mkLetDecl(v_b_180_, v_fvarId_239_, v_userName_240_, v_a_246_, v_a_248_, v_nondep_243_, v_kind_244_);
v_a_187_ = v___x_249_;
goto v___jp_186_;
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
lean_dec(v_a_246_);
lean_dec_ref(v_b_180_);
v_a_250_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_247_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_247_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
else
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
lean_dec_ref(v_b_180_);
v_a_258_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_245_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_245_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
}
else
{
lean_object* v___x_266_; 
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v_b_180_);
return v___x_266_;
}
v___jp_186_:
{
size_t v___x_188_; size_t v___x_189_; 
v___x_188_ = ((size_t)1ULL);
v___x_189_ = lean_usize_add(v_i_178_, v___x_188_);
v_i_178_ = v___x_189_;
v_b_180_ = v_a_187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___boxed(lean_object* v_auxDeclToFullName_267_, lean_object* v_as_268_, lean_object* v_i_269_, lean_object* v_stop_270_, lean_object* v_b_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
size_t v_i_boxed_277_; size_t v_stop_boxed_278_; lean_object* v_res_279_; 
v_i_boxed_277_ = lean_unbox_usize(v_i_269_);
lean_dec(v_i_269_);
v_stop_boxed_278_ = lean_unbox_usize(v_stop_270_);
lean_dec(v_stop_270_);
v_res_279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_267_, v_as_268_, v_i_boxed_277_, v_stop_boxed_278_, v_b_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec_ref(v_as_268_);
lean_dec(v_auxDeclToFullName_267_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(lean_object* v_auxDeclToFullName_280_, lean_object* v_x_281_, lean_object* v_x_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
if (lean_obj_tag(v_x_281_) == 0)
{
lean_object* v_cs_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_308_; 
v_cs_288_ = lean_ctor_get(v_x_281_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_308_ == 0)
{
v___x_290_ = v_x_281_;
v_isShared_291_ = v_isSharedCheck_308_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_cs_288_);
lean_dec(v_x_281_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_308_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_array_get_size(v_cs_288_);
v___x_294_ = lean_nat_dec_lt(v___x_292_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_296_; 
lean_dec_ref(v_cs_288_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v_x_282_);
v___x_296_ = v___x_290_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_x_282_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
else
{
uint8_t v___x_298_; 
v___x_298_ = lean_nat_dec_le(v___x_293_, v___x_293_);
if (v___x_298_ == 0)
{
if (v___x_294_ == 0)
{
lean_object* v___x_300_; 
lean_dec_ref(v_cs_288_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v_x_282_);
v___x_300_ = v___x_290_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_x_282_);
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
lean_del_object(v___x_290_);
v___x_302_ = ((size_t)0ULL);
v___x_303_ = lean_usize_of_nat(v___x_293_);
v___x_304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_280_, v_cs_288_, v___x_302_, v___x_303_, v_x_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec_ref(v_cs_288_);
return v___x_304_;
}
}
else
{
size_t v___x_305_; size_t v___x_306_; lean_object* v___x_307_; 
lean_del_object(v___x_290_);
v___x_305_ = ((size_t)0ULL);
v___x_306_ = lean_usize_of_nat(v___x_293_);
v___x_307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_280_, v_cs_288_, v___x_305_, v___x_306_, v_x_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec_ref(v_cs_288_);
return v___x_307_;
}
}
}
}
else
{
lean_object* v_vs_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_329_; 
v_vs_309_ = lean_ctor_get(v_x_281_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_329_ == 0)
{
v___x_311_ = v_x_281_;
v_isShared_312_ = v_isSharedCheck_329_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_vs_309_);
lean_dec(v_x_281_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_329_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_array_get_size(v_vs_309_);
v___x_315_ = lean_nat_dec_lt(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_317_; 
lean_dec_ref(v_vs_309_);
if (v_isShared_312_ == 0)
{
lean_ctor_set_tag(v___x_311_, 0);
lean_ctor_set(v___x_311_, 0, v_x_282_);
v___x_317_ = v___x_311_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_x_282_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
else
{
uint8_t v___x_319_; 
v___x_319_ = lean_nat_dec_le(v___x_314_, v___x_314_);
if (v___x_319_ == 0)
{
if (v___x_315_ == 0)
{
lean_object* v___x_321_; 
lean_dec_ref(v_vs_309_);
if (v_isShared_312_ == 0)
{
lean_ctor_set_tag(v___x_311_, 0);
lean_ctor_set(v___x_311_, 0, v_x_282_);
v___x_321_ = v___x_311_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_x_282_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
else
{
size_t v___x_323_; size_t v___x_324_; lean_object* v___x_325_; 
lean_del_object(v___x_311_);
v___x_323_ = ((size_t)0ULL);
v___x_324_ = lean_usize_of_nat(v___x_314_);
v___x_325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_280_, v_vs_309_, v___x_323_, v___x_324_, v_x_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec_ref(v_vs_309_);
return v___x_325_;
}
}
else
{
size_t v___x_326_; size_t v___x_327_; lean_object* v___x_328_; 
lean_del_object(v___x_311_);
v___x_326_ = ((size_t)0ULL);
v___x_327_ = lean_usize_of_nat(v___x_314_);
v___x_328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_280_, v_vs_309_, v___x_326_, v___x_327_, v_x_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec_ref(v_vs_309_);
return v___x_328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(lean_object* v_auxDeclToFullName_330_, lean_object* v_as_331_, size_t v_i_332_, size_t v_stop_333_, lean_object* v_b_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
uint8_t v___x_340_; 
v___x_340_ = lean_usize_dec_eq(v_i_332_, v_stop_333_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_array_uget_borrowed(v_as_331_, v_i_332_);
lean_inc(v___x_341_);
v___x_342_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(v_auxDeclToFullName_330_, v___x_341_, v_b_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; size_t v___x_344_; size_t v___x_345_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 1);
v___x_344_ = ((size_t)1ULL);
v___x_345_ = lean_usize_add(v_i_332_, v___x_344_);
v_i_332_ = v___x_345_;
v_b_334_ = v_a_343_;
goto _start;
}
else
{
return v___x_342_;
}
}
else
{
lean_object* v___x_347_; 
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v_b_334_);
return v___x_347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9___boxed(lean_object* v_auxDeclToFullName_348_, lean_object* v_as_349_, lean_object* v_i_350_, lean_object* v_stop_351_, lean_object* v_b_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
size_t v_i_boxed_358_; size_t v_stop_boxed_359_; lean_object* v_res_360_; 
v_i_boxed_358_ = lean_unbox_usize(v_i_350_);
lean_dec(v_i_350_);
v_stop_boxed_359_ = lean_unbox_usize(v_stop_351_);
lean_dec(v_stop_351_);
v_res_360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_348_, v_as_349_, v_i_boxed_358_, v_stop_boxed_359_, v_b_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec_ref(v_as_349_);
lean_dec(v_auxDeclToFullName_348_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9___boxed(lean_object* v_auxDeclToFullName_361_, lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(v_auxDeclToFullName_361_, v_x_362_, v_x_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v_auxDeclToFullName_361_);
return v_res_369_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(lean_object* v_auxDeclToFullName_371_, lean_object* v_x_372_, size_t v_x_373_, size_t v_x_374_, lean_object* v_x_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
if (lean_obj_tag(v_x_372_) == 0)
{
lean_object* v_cs_381_; lean_object* v___x_382_; size_t v___x_383_; lean_object* v_j_384_; lean_object* v___x_385_; size_t v___x_386_; size_t v___x_387_; size_t v___x_388_; size_t v___x_389_; size_t v___x_390_; size_t v___x_391_; lean_object* v___x_392_; 
v_cs_381_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_cs_381_);
lean_dec_ref_known(v_x_372_, 1);
v___x_382_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0);
v___x_383_ = lean_usize_shift_right(v_x_373_, v_x_374_);
v_j_384_ = lean_usize_to_nat(v___x_383_);
v___x_385_ = lean_array_get_borrowed(v___x_382_, v_cs_381_, v_j_384_);
v___x_386_ = ((size_t)1ULL);
v___x_387_ = lean_usize_shift_left(v___x_386_, v_x_374_);
v___x_388_ = lean_usize_sub(v___x_387_, v___x_386_);
v___x_389_ = lean_usize_land(v_x_373_, v___x_388_);
v___x_390_ = ((size_t)5ULL);
v___x_391_ = lean_usize_sub(v_x_374_, v___x_390_);
lean_inc(v___x_385_);
v___x_392_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(v_auxDeclToFullName_371_, v___x_385_, v___x_389_, v___x_391_, v_x_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_a_393_);
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_nat_add(v_j_384_, v___x_394_);
lean_dec(v_j_384_);
v___x_396_ = lean_array_get_size(v_cs_381_);
v___x_397_ = lean_nat_dec_lt(v___x_395_, v___x_396_);
if (v___x_397_ == 0)
{
lean_dec(v___x_395_);
lean_dec(v_a_393_);
lean_dec_ref(v_cs_381_);
return v___x_392_;
}
else
{
uint8_t v___x_398_; 
v___x_398_ = lean_nat_dec_le(v___x_396_, v___x_396_);
if (v___x_398_ == 0)
{
if (v___x_397_ == 0)
{
lean_dec(v___x_395_);
lean_dec(v_a_393_);
lean_dec_ref(v_cs_381_);
return v___x_392_;
}
else
{
size_t v___x_399_; size_t v___x_400_; lean_object* v___x_401_; 
lean_dec_ref_known(v___x_392_, 1);
v___x_399_ = lean_usize_of_nat(v___x_395_);
lean_dec(v___x_395_);
v___x_400_ = lean_usize_of_nat(v___x_396_);
v___x_401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_371_, v_cs_381_, v___x_399_, v___x_400_, v_a_393_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
lean_dec_ref(v_cs_381_);
return v___x_401_;
}
}
else
{
size_t v___x_402_; size_t v___x_403_; lean_object* v___x_404_; 
lean_dec_ref_known(v___x_392_, 1);
v___x_402_ = lean_usize_of_nat(v___x_395_);
lean_dec(v___x_395_);
v___x_403_ = lean_usize_of_nat(v___x_396_);
v___x_404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_371_, v_cs_381_, v___x_402_, v___x_403_, v_a_393_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
lean_dec_ref(v_cs_381_);
return v___x_404_;
}
}
}
else
{
lean_dec(v_j_384_);
lean_dec_ref(v_cs_381_);
return v___x_392_;
}
}
else
{
lean_object* v_vs_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_425_; 
v_vs_405_ = lean_ctor_get(v_x_372_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v_x_372_);
if (v_isSharedCheck_425_ == 0)
{
v___x_407_ = v_x_372_;
v_isShared_408_ = v_isSharedCheck_425_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_vs_405_);
lean_dec(v_x_372_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_425_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_409_ = lean_usize_to_nat(v_x_373_);
v___x_410_ = lean_array_get_size(v_vs_405_);
v___x_411_ = lean_nat_dec_lt(v___x_409_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_413_; 
lean_dec(v___x_409_);
lean_dec_ref(v_vs_405_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 0);
lean_ctor_set(v___x_407_, 0, v_x_375_);
v___x_413_ = v___x_407_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_x_375_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
else
{
uint8_t v___x_415_; 
v___x_415_ = lean_nat_dec_le(v___x_410_, v___x_410_);
if (v___x_415_ == 0)
{
if (v___x_411_ == 0)
{
lean_object* v___x_417_; 
lean_dec(v___x_409_);
lean_dec_ref(v_vs_405_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 0);
lean_ctor_set(v___x_407_, 0, v_x_375_);
v___x_417_ = v___x_407_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_x_375_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
else
{
size_t v___x_419_; size_t v___x_420_; lean_object* v___x_421_; 
lean_del_object(v___x_407_);
v___x_419_ = lean_usize_of_nat(v___x_409_);
lean_dec(v___x_409_);
v___x_420_ = lean_usize_of_nat(v___x_410_);
v___x_421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_371_, v_vs_405_, v___x_419_, v___x_420_, v_x_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
lean_dec_ref(v_vs_405_);
return v___x_421_;
}
}
else
{
size_t v___x_422_; size_t v___x_423_; lean_object* v___x_424_; 
lean_del_object(v___x_407_);
v___x_422_ = lean_usize_of_nat(v___x_409_);
lean_dec(v___x_409_);
v___x_423_ = lean_usize_of_nat(v___x_410_);
v___x_424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_371_, v_vs_405_, v___x_422_, v___x_423_, v_x_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
lean_dec_ref(v_vs_405_);
return v___x_424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___boxed(lean_object* v_auxDeclToFullName_426_, lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v_x_429_, lean_object* v_x_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
size_t v_x_5754__boxed_436_; size_t v_x_5755__boxed_437_; lean_object* v_res_438_; 
v_x_5754__boxed_436_ = lean_unbox_usize(v_x_428_);
lean_dec(v_x_428_);
v_x_5755__boxed_437_ = lean_unbox_usize(v_x_429_);
lean_dec(v_x_429_);
v_res_438_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(v_auxDeclToFullName_426_, v_x_427_, v_x_5754__boxed_436_, v_x_5755__boxed_437_, v_x_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v_auxDeclToFullName_426_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5(lean_object* v_auxDeclToFullName_439_, lean_object* v_t_440_, lean_object* v_init_441_, lean_object* v_start_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_nat_dec_eq(v_start_442_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v_root_450_; lean_object* v_tail_451_; size_t v_shift_452_; lean_object* v_tailOff_453_; uint8_t v___x_454_; 
v_root_450_ = lean_ctor_get(v_t_440_, 0);
lean_inc_ref(v_root_450_);
v_tail_451_ = lean_ctor_get(v_t_440_, 1);
lean_inc_ref(v_tail_451_);
v_shift_452_ = lean_ctor_get_usize(v_t_440_, 4);
v_tailOff_453_ = lean_ctor_get(v_t_440_, 3);
lean_inc(v_tailOff_453_);
lean_dec_ref(v_t_440_);
v___x_454_ = lean_nat_dec_le(v_tailOff_453_, v_start_442_);
if (v___x_454_ == 0)
{
size_t v___x_455_; lean_object* v___x_456_; 
lean_dec(v_tailOff_453_);
v___x_455_ = lean_usize_of_nat(v_start_442_);
v___x_456_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(v_auxDeclToFullName_439_, v_root_450_, v___x_455_, v_shift_452_, v_init_441_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
v___x_458_ = lean_array_get_size(v_tail_451_);
v___x_459_ = lean_nat_dec_lt(v___x_448_, v___x_458_);
if (v___x_459_ == 0)
{
lean_dec(v_a_457_);
lean_dec_ref(v_tail_451_);
return v___x_456_;
}
else
{
uint8_t v___x_460_; 
v___x_460_ = lean_nat_dec_le(v___x_458_, v___x_458_);
if (v___x_460_ == 0)
{
if (v___x_459_ == 0)
{
lean_dec(v_a_457_);
lean_dec_ref(v_tail_451_);
return v___x_456_;
}
else
{
size_t v___x_461_; size_t v___x_462_; lean_object* v___x_463_; 
lean_dec_ref_known(v___x_456_, 1);
v___x_461_ = ((size_t)0ULL);
v___x_462_ = lean_usize_of_nat(v___x_458_);
v___x_463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_439_, v_tail_451_, v___x_461_, v___x_462_, v_a_457_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec_ref(v_tail_451_);
return v___x_463_;
}
}
else
{
size_t v___x_464_; size_t v___x_465_; lean_object* v___x_466_; 
lean_dec_ref_known(v___x_456_, 1);
v___x_464_ = ((size_t)0ULL);
v___x_465_ = lean_usize_of_nat(v___x_458_);
v___x_466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_439_, v_tail_451_, v___x_464_, v___x_465_, v_a_457_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec_ref(v_tail_451_);
return v___x_466_;
}
}
}
else
{
lean_dec_ref(v_tail_451_);
return v___x_456_;
}
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
lean_dec_ref(v_root_450_);
v___x_467_ = lean_nat_sub(v_start_442_, v_tailOff_453_);
lean_dec(v_tailOff_453_);
v___x_468_ = lean_array_get_size(v_tail_451_);
v___x_469_ = lean_nat_dec_lt(v___x_467_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; 
lean_dec(v___x_467_);
lean_dec_ref(v_tail_451_);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v_init_441_);
return v___x_470_;
}
else
{
uint8_t v___x_471_; 
v___x_471_ = lean_nat_dec_le(v___x_468_, v___x_468_);
if (v___x_471_ == 0)
{
if (v___x_469_ == 0)
{
lean_object* v___x_472_; 
lean_dec(v___x_467_);
lean_dec_ref(v_tail_451_);
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v_init_441_);
return v___x_472_;
}
else
{
size_t v___x_473_; size_t v___x_474_; lean_object* v___x_475_; 
v___x_473_ = lean_usize_of_nat(v___x_467_);
lean_dec(v___x_467_);
v___x_474_ = lean_usize_of_nat(v___x_468_);
v___x_475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_439_, v_tail_451_, v___x_473_, v___x_474_, v_init_441_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec_ref(v_tail_451_);
return v___x_475_;
}
}
else
{
size_t v___x_476_; size_t v___x_477_; lean_object* v___x_478_; 
v___x_476_ = lean_usize_of_nat(v___x_467_);
lean_dec(v___x_467_);
v___x_477_ = lean_usize_of_nat(v___x_468_);
v___x_478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_439_, v_tail_451_, v___x_476_, v___x_477_, v_init_441_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec_ref(v_tail_451_);
return v___x_478_;
}
}
}
}
else
{
lean_object* v_root_479_; lean_object* v_tail_480_; lean_object* v___x_481_; 
v_root_479_ = lean_ctor_get(v_t_440_, 0);
lean_inc_ref(v_root_479_);
v_tail_480_ = lean_ctor_get(v_t_440_, 1);
lean_inc_ref(v_tail_480_);
lean_dec_ref(v_t_440_);
v___x_481_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(v_auxDeclToFullName_439_, v_root_479_, v_init_441_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_482_);
v___x_483_ = lean_array_get_size(v_tail_480_);
v___x_484_ = lean_nat_dec_lt(v___x_448_, v___x_483_);
if (v___x_484_ == 0)
{
lean_dec(v_a_482_);
lean_dec_ref(v_tail_480_);
return v___x_481_;
}
else
{
uint8_t v___x_485_; 
v___x_485_ = lean_nat_dec_le(v___x_483_, v___x_483_);
if (v___x_485_ == 0)
{
if (v___x_484_ == 0)
{
lean_dec(v_a_482_);
lean_dec_ref(v_tail_480_);
return v___x_481_;
}
else
{
size_t v___x_486_; size_t v___x_487_; lean_object* v___x_488_; 
lean_dec_ref_known(v___x_481_, 1);
v___x_486_ = ((size_t)0ULL);
v___x_487_ = lean_usize_of_nat(v___x_483_);
v___x_488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_439_, v_tail_480_, v___x_486_, v___x_487_, v_a_482_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec_ref(v_tail_480_);
return v___x_488_;
}
}
else
{
size_t v___x_489_; size_t v___x_490_; lean_object* v___x_491_; 
lean_dec_ref_known(v___x_481_, 1);
v___x_489_ = ((size_t)0ULL);
v___x_490_ = lean_usize_of_nat(v___x_483_);
v___x_491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_439_, v_tail_480_, v___x_489_, v___x_490_, v_a_482_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec_ref(v_tail_480_);
return v___x_491_;
}
}
}
else
{
lean_dec_ref(v_tail_480_);
return v___x_481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5___boxed(lean_object* v_auxDeclToFullName_492_, lean_object* v_t_493_, lean_object* v_init_494_, lean_object* v_start_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5(v_auxDeclToFullName_492_, v_t_493_, v_init_494_, v_start_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v_start_495_);
lean_dec(v_auxDeclToFullName_492_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3(lean_object* v_auxDeclToFullName_502_, lean_object* v_lctx_503_, lean_object* v_init_504_, lean_object* v_start_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_decls_511_; lean_object* v___x_512_; 
v_decls_511_ = lean_ctor_get(v_lctx_503_, 1);
lean_inc_ref(v_decls_511_);
lean_dec_ref(v_lctx_503_);
v___x_512_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5(v_auxDeclToFullName_502_, v_decls_511_, v_init_504_, v_start_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3___boxed(lean_object* v_auxDeclToFullName_513_, lean_object* v_lctx_514_, lean_object* v_init_515_, lean_object* v_start_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3(v_auxDeclToFullName_513_, v_lctx_514_, v_init_515_, v_start_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v_start_516_);
lean_dec(v_auxDeclToFullName_513_);
return v_res_522_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_523_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_unsigned_to_nat(32u);
v___x_527_ = lean_mk_empty_array_with_capacity(v___x_526_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_529_ = ((size_t)5ULL);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_unsigned_to_nat(32u);
v___x_532_ = lean_mk_empty_array_with_capacity(v___x_531_);
v___x_533_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2);
v___x_534_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v___x_532_);
lean_ctor_set(v___x_534_, 2, v___x_530_);
lean_ctor_set(v___x_534_, 3, v___x_530_);
lean_ctor_set_usize(v___x_534_, 4, v___x_529_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_535_ = lean_box(1);
v___x_536_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3);
v___x_537_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1);
v___x_538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___x_536_);
lean_ctor_set(v___x_538_, 2, v___x_535_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0(lean_object* v_lctx_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_auxDeclToFullName_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_auxDeclToFullName_545_ = lean_ctor_get(v_lctx_539_, 2);
lean_inc(v_auxDeclToFullName_545_);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4, &l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4);
v___x_548_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3(v_auxDeclToFullName_545_, v_lctx_539_, v___x_547_, v___x_546_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec(v_auxDeclToFullName_545_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___boxed(lean_object* v_lctx_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0(v_lctx_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12___redArg(lean_object* v_x_556_, lean_object* v_x_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
lean_object* v_ks_560_; lean_object* v_vs_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_585_; 
v_ks_560_ = lean_ctor_get(v_x_556_, 0);
v_vs_561_ = lean_ctor_get(v_x_556_, 1);
v_isSharedCheck_585_ = !lean_is_exclusive(v_x_556_);
if (v_isSharedCheck_585_ == 0)
{
v___x_563_ = v_x_556_;
v_isShared_564_ = v_isSharedCheck_585_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_vs_561_);
lean_inc(v_ks_560_);
lean_dec(v_x_556_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_585_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_565_ = lean_array_get_size(v_ks_560_);
v___x_566_ = lean_nat_dec_lt(v_x_557_, v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
lean_dec(v_x_557_);
v___x_567_ = lean_array_push(v_ks_560_, v_x_558_);
v___x_568_ = lean_array_push(v_vs_561_, v_x_559_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v___x_568_);
lean_ctor_set(v___x_563_, 0, v___x_567_);
v___x_570_ = v___x_563_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
else
{
lean_object* v_k_x27_572_; uint8_t v___x_573_; 
v_k_x27_572_ = lean_array_fget_borrowed(v_ks_560_, v_x_557_);
v___x_573_ = l_Lean_instBEqMVarId_beq(v_x_558_, v_k_x27_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_575_; 
if (v_isShared_564_ == 0)
{
v___x_575_ = v___x_563_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_ks_560_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_vs_561_);
v___x_575_ = v_reuseFailAlloc_579_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_nat_add(v_x_557_, v___x_576_);
lean_dec(v_x_557_);
v_x_556_ = v___x_575_;
v_x_557_ = v___x_577_;
goto _start;
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_580_ = lean_array_fset(v_ks_560_, v_x_557_, v_x_558_);
v___x_581_ = lean_array_fset(v_vs_561_, v_x_557_, v_x_559_);
lean_dec(v_x_557_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v___x_581_);
lean_ctor_set(v___x_563_, 0, v___x_580_);
v___x_583_ = v___x_563_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8___redArg(lean_object* v_n_586_, lean_object* v_k_587_, lean_object* v_v_588_){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12___redArg(v_n_586_, v___x_589_, v_k_587_, v_v_588_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(lean_object* v_x_592_, size_t v_x_593_, size_t v_x_594_, lean_object* v_x_595_, lean_object* v_x_596_){
_start:
{
if (lean_obj_tag(v_x_592_) == 0)
{
lean_object* v_es_597_; size_t v___x_598_; size_t v___x_599_; lean_object* v_j_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v_es_597_ = lean_ctor_get(v_x_592_, 0);
v___x_598_ = ((size_t)31ULL);
v___x_599_ = lean_usize_land(v_x_593_, v___x_598_);
v_j_600_ = lean_usize_to_nat(v___x_599_);
v___x_601_ = lean_array_get_size(v_es_597_);
v___x_602_ = lean_nat_dec_lt(v_j_600_, v___x_601_);
if (v___x_602_ == 0)
{
lean_dec(v_j_600_);
lean_dec(v_x_596_);
lean_dec(v_x_595_);
return v_x_592_;
}
else
{
lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_641_; 
lean_inc_ref(v_es_597_);
v_isSharedCheck_641_ = !lean_is_exclusive(v_x_592_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; 
v_unused_642_ = lean_ctor_get(v_x_592_, 0);
lean_dec(v_unused_642_);
v___x_604_ = v_x_592_;
v_isShared_605_ = v_isSharedCheck_641_;
goto v_resetjp_603_;
}
else
{
lean_dec(v_x_592_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_641_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v_v_606_; lean_object* v___x_607_; lean_object* v_xs_x27_608_; lean_object* v___y_610_; 
v_v_606_ = lean_array_fget(v_es_597_, v_j_600_);
v___x_607_ = lean_box(0);
v_xs_x27_608_ = lean_array_fset(v_es_597_, v_j_600_, v___x_607_);
switch(lean_obj_tag(v_v_606_))
{
case 0:
{
lean_object* v_key_615_; lean_object* v_val_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_626_; 
v_key_615_ = lean_ctor_get(v_v_606_, 0);
v_val_616_ = lean_ctor_get(v_v_606_, 1);
v_isSharedCheck_626_ = !lean_is_exclusive(v_v_606_);
if (v_isSharedCheck_626_ == 0)
{
v___x_618_ = v_v_606_;
v_isShared_619_ = v_isSharedCheck_626_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_val_616_);
lean_inc(v_key_615_);
lean_dec(v_v_606_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_626_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
uint8_t v___x_620_; 
v___x_620_ = l_Lean_instBEqMVarId_beq(v_x_595_, v_key_615_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
lean_del_object(v___x_618_);
v___x_621_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_615_, v_val_616_, v_x_595_, v_x_596_);
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
v___y_610_ = v___x_622_;
goto v___jp_609_;
}
else
{
lean_object* v___x_624_; 
lean_dec(v_val_616_);
lean_dec(v_key_615_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 1, v_x_596_);
lean_ctor_set(v___x_618_, 0, v_x_595_);
v___x_624_ = v___x_618_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_x_595_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_x_596_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
v___y_610_ = v___x_624_;
goto v___jp_609_;
}
}
}
}
case 1:
{
lean_object* v_node_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_639_; 
v_node_627_ = lean_ctor_get(v_v_606_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v_v_606_);
if (v_isSharedCheck_639_ == 0)
{
v___x_629_ = v_v_606_;
v_isShared_630_ = v_isSharedCheck_639_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_node_627_);
lean_dec(v_v_606_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_639_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
size_t v___x_631_; size_t v___x_632_; size_t v___x_633_; size_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_631_ = ((size_t)5ULL);
v___x_632_ = lean_usize_shift_right(v_x_593_, v___x_631_);
v___x_633_ = ((size_t)1ULL);
v___x_634_ = lean_usize_add(v_x_594_, v___x_633_);
v___x_635_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_node_627_, v___x_632_, v___x_634_, v_x_595_, v_x_596_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_635_);
v___x_637_ = v___x_629_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
v___y_610_ = v___x_637_;
goto v___jp_609_;
}
}
}
default: 
{
lean_object* v___x_640_; 
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v_x_595_);
lean_ctor_set(v___x_640_, 1, v_x_596_);
v___y_610_ = v___x_640_;
goto v___jp_609_;
}
}
v___jp_609_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = lean_array_fset(v_xs_x27_608_, v_j_600_, v___y_610_);
lean_dec(v_j_600_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_611_);
v___x_613_ = v___x_604_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
else
{
lean_object* v_ks_643_; lean_object* v_vs_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_664_; 
v_ks_643_ = lean_ctor_get(v_x_592_, 0);
v_vs_644_ = lean_ctor_get(v_x_592_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v_x_592_);
if (v_isSharedCheck_664_ == 0)
{
v___x_646_ = v_x_592_;
v_isShared_647_ = v_isSharedCheck_664_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_vs_644_);
lean_inc(v_ks_643_);
lean_dec(v_x_592_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_664_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_ks_643_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_vs_644_);
v___x_649_ = v_reuseFailAlloc_663_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v_newNode_650_; uint8_t v___y_652_; size_t v___x_658_; uint8_t v___x_659_; 
v_newNode_650_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8___redArg(v___x_649_, v_x_595_, v_x_596_);
v___x_658_ = ((size_t)7ULL);
v___x_659_ = lean_usize_dec_le(v___x_658_, v_x_594_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_660_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_650_);
v___x_661_ = lean_unsigned_to_nat(4u);
v___x_662_ = lean_nat_dec_lt(v___x_660_, v___x_661_);
lean_dec(v___x_660_);
v___y_652_ = v___x_662_;
goto v___jp_651_;
}
else
{
v___y_652_ = v___x_659_;
goto v___jp_651_;
}
v___jp_651_:
{
if (v___y_652_ == 0)
{
lean_object* v_ks_653_; lean_object* v_vs_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_ks_653_ = lean_ctor_get(v_newNode_650_, 0);
lean_inc_ref(v_ks_653_);
v_vs_654_ = lean_ctor_get(v_newNode_650_, 1);
lean_inc_ref(v_vs_654_);
lean_dec_ref(v_newNode_650_);
v___x_655_ = lean_unsigned_to_nat(0u);
v___x_656_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0);
v___x_657_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(v_x_594_, v_ks_653_, v_vs_654_, v___x_655_, v___x_656_);
lean_dec_ref(v_vs_654_);
lean_dec_ref(v_ks_653_);
return v___x_657_;
}
else
{
return v_newNode_650_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(size_t v_depth_665_, lean_object* v_keys_666_, lean_object* v_vals_667_, lean_object* v_i_668_, lean_object* v_entries_669_){
_start:
{
lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_670_ = lean_array_get_size(v_keys_666_);
v___x_671_ = lean_nat_dec_lt(v_i_668_, v___x_670_);
if (v___x_671_ == 0)
{
lean_dec(v_i_668_);
return v_entries_669_;
}
else
{
lean_object* v_k_672_; lean_object* v_v_673_; uint64_t v___x_674_; size_t v_h_675_; size_t v___x_676_; lean_object* v___x_677_; size_t v___x_678_; size_t v___x_679_; size_t v___x_680_; size_t v_h_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_k_672_ = lean_array_fget_borrowed(v_keys_666_, v_i_668_);
v_v_673_ = lean_array_fget_borrowed(v_vals_667_, v_i_668_);
v___x_674_ = l_Lean_instHashableMVarId_hash(v_k_672_);
v_h_675_ = lean_uint64_to_usize(v___x_674_);
v___x_676_ = ((size_t)5ULL);
v___x_677_ = lean_unsigned_to_nat(1u);
v___x_678_ = ((size_t)1ULL);
v___x_679_ = lean_usize_sub(v_depth_665_, v___x_678_);
v___x_680_ = lean_usize_mul(v___x_676_, v___x_679_);
v_h_681_ = lean_usize_shift_right(v_h_675_, v___x_680_);
v___x_682_ = lean_nat_add(v_i_668_, v___x_677_);
lean_dec(v_i_668_);
lean_inc(v_v_673_);
lean_inc(v_k_672_);
v___x_683_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_entries_669_, v_h_681_, v_depth_665_, v_k_672_, v_v_673_);
v_i_668_ = v___x_682_;
v_entries_669_ = v___x_683_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg___boxed(lean_object* v_depth_685_, lean_object* v_keys_686_, lean_object* v_vals_687_, lean_object* v_i_688_, lean_object* v_entries_689_){
_start:
{
size_t v_depth_boxed_690_; lean_object* v_res_691_; 
v_depth_boxed_690_ = lean_unbox_usize(v_depth_685_);
lean_dec(v_depth_685_);
v_res_691_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(v_depth_boxed_690_, v_keys_686_, v_vals_687_, v_i_688_, v_entries_689_);
lean_dec_ref(v_vals_687_);
lean_dec_ref(v_keys_686_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
size_t v_x_6128__boxed_697_; size_t v_x_6129__boxed_698_; lean_object* v_res_699_; 
v_x_6128__boxed_697_ = lean_unbox_usize(v_x_693_);
lean_dec(v_x_693_);
v_x_6129__boxed_698_ = lean_unbox_usize(v_x_694_);
lean_dec(v_x_694_);
v_res_699_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_x_692_, v_x_6128__boxed_697_, v_x_6129__boxed_698_, v_x_695_, v_x_696_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2___redArg(lean_object* v_x_700_, lean_object* v_x_701_, lean_object* v_x_702_){
_start:
{
uint64_t v___x_703_; size_t v___x_704_; size_t v___x_705_; lean_object* v___x_706_; 
v___x_703_ = l_Lean_instHashableMVarId_hash(v_x_701_);
v___x_704_ = lean_uint64_to_usize(v___x_703_);
v___x_705_ = ((size_t)1ULL);
v___x_706_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_x_700_, v___x_704_, v___x_705_, v_x_701_, v_x_702_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0(lean_object* v_mvarId_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___x_713_; lean_object* v_mctx_714_; lean_object* v_mvarDecl_715_; lean_object* v_userName_716_; lean_object* v_lctx_717_; lean_object* v_type_718_; lean_object* v_depth_719_; lean_object* v_localInstances_720_; uint8_t v_kind_721_; lean_object* v_numScopeArgs_722_; lean_object* v_index_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_786_; 
v___x_713_ = lean_st_ref_get(v___y_709_);
v_mctx_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc_ref(v_mctx_714_);
lean_dec(v___x_713_);
lean_inc(v_mvarId_707_);
v_mvarDecl_715_ = l_Lean_MetavarContext_getDecl(v_mctx_714_, v_mvarId_707_);
lean_dec_ref(v_mctx_714_);
v_userName_716_ = lean_ctor_get(v_mvarDecl_715_, 0);
v_lctx_717_ = lean_ctor_get(v_mvarDecl_715_, 1);
v_type_718_ = lean_ctor_get(v_mvarDecl_715_, 2);
v_depth_719_ = lean_ctor_get(v_mvarDecl_715_, 3);
v_localInstances_720_ = lean_ctor_get(v_mvarDecl_715_, 4);
v_kind_721_ = lean_ctor_get_uint8(v_mvarDecl_715_, sizeof(void*)*7);
v_numScopeArgs_722_ = lean_ctor_get(v_mvarDecl_715_, 5);
v_index_723_ = lean_ctor_get(v_mvarDecl_715_, 6);
v_isSharedCheck_786_ = !lean_is_exclusive(v_mvarDecl_715_);
if (v_isSharedCheck_786_ == 0)
{
v___x_725_ = v_mvarDecl_715_;
v_isShared_726_ = v_isSharedCheck_786_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_index_723_);
lean_inc(v_numScopeArgs_722_);
lean_inc(v_localInstances_720_);
lean_inc(v_depth_719_);
lean_inc(v_type_718_);
lean_inc(v_lctx_717_);
lean_inc(v_userName_716_);
lean_dec(v_mvarDecl_715_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_786_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0(v_lctx_717_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_729_; lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_777_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_727_, 1);
v___x_729_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_type_718_, v___y_709_);
v_a_730_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_777_ == 0)
{
v___x_732_ = v___x_729_;
v_isShared_733_ = v_isSharedCheck_777_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_777_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v_fst_736_; lean_object* v_snd_737_; lean_object* v___x_738_; lean_object* v_mctx_739_; lean_object* v_cache_740_; lean_object* v_zetaDeltaFVarIds_741_; lean_object* v_postponed_742_; lean_object* v_diag_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_776_; 
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v_a_728_);
lean_ctor_set(v___x_734_, 1, v_a_730_);
v___x_735_ = lean_sharecommon_quick(v___x_734_);
lean_dec_ref_known(v___x_734_, 2);
v_fst_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_fst_736_);
v_snd_737_ = lean_ctor_get(v___x_735_, 1);
lean_inc(v_snd_737_);
lean_dec(v___x_735_);
v___x_738_ = lean_st_ref_take(v___y_709_);
v_mctx_739_ = lean_ctor_get(v___x_738_, 0);
v_cache_740_ = lean_ctor_get(v___x_738_, 1);
v_zetaDeltaFVarIds_741_ = lean_ctor_get(v___x_738_, 2);
v_postponed_742_ = lean_ctor_get(v___x_738_, 3);
v_diag_743_ = lean_ctor_get(v___x_738_, 4);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_776_ == 0)
{
v___x_745_ = v___x_738_;
v_isShared_746_ = v_isSharedCheck_776_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_diag_743_);
lean_inc(v_postponed_742_);
lean_inc(v_zetaDeltaFVarIds_741_);
lean_inc(v_cache_740_);
lean_inc(v_mctx_739_);
lean_dec(v___x_738_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_776_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v_depth_747_; lean_object* v_levelAssignDepth_748_; lean_object* v_lmvarCounter_749_; lean_object* v_mvarCounter_750_; lean_object* v_lDecls_751_; lean_object* v_decls_752_; lean_object* v_userNames_753_; lean_object* v_lAssignment_754_; lean_object* v_eAssignment_755_; lean_object* v_dAssignment_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_775_; 
v_depth_747_ = lean_ctor_get(v_mctx_739_, 0);
v_levelAssignDepth_748_ = lean_ctor_get(v_mctx_739_, 1);
v_lmvarCounter_749_ = lean_ctor_get(v_mctx_739_, 2);
v_mvarCounter_750_ = lean_ctor_get(v_mctx_739_, 3);
v_lDecls_751_ = lean_ctor_get(v_mctx_739_, 4);
v_decls_752_ = lean_ctor_get(v_mctx_739_, 5);
v_userNames_753_ = lean_ctor_get(v_mctx_739_, 6);
v_lAssignment_754_ = lean_ctor_get(v_mctx_739_, 7);
v_eAssignment_755_ = lean_ctor_get(v_mctx_739_, 8);
v_dAssignment_756_ = lean_ctor_get(v_mctx_739_, 9);
v_isSharedCheck_775_ = !lean_is_exclusive(v_mctx_739_);
if (v_isSharedCheck_775_ == 0)
{
v___x_758_ = v_mctx_739_;
v_isShared_759_ = v_isSharedCheck_775_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_dAssignment_756_);
lean_inc(v_eAssignment_755_);
lean_inc(v_lAssignment_754_);
lean_inc(v_userNames_753_);
lean_inc(v_decls_752_);
lean_inc(v_lDecls_751_);
lean_inc(v_mvarCounter_750_);
lean_inc(v_lmvarCounter_749_);
lean_inc(v_levelAssignDepth_748_);
lean_inc(v_depth_747_);
lean_dec(v_mctx_739_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_775_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 2, v_snd_737_);
lean_ctor_set(v___x_725_, 1, v_fst_736_);
v___x_761_ = v___x_725_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_userName_716_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_fst_736_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_snd_737_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v_depth_719_);
lean_ctor_set(v_reuseFailAlloc_774_, 4, v_localInstances_720_);
lean_ctor_set(v_reuseFailAlloc_774_, 5, v_numScopeArgs_722_);
lean_ctor_set(v_reuseFailAlloc_774_, 6, v_index_723_);
lean_ctor_set_uint8(v_reuseFailAlloc_774_, sizeof(void*)*7, v_kind_721_);
v___x_761_ = v_reuseFailAlloc_774_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_762_ = l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2___redArg(v_decls_752_, v_mvarId_707_, v___x_761_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 5, v___x_762_);
v___x_764_ = v___x_758_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_depth_747_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_levelAssignDepth_748_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v_lmvarCounter_749_);
lean_ctor_set(v_reuseFailAlloc_773_, 3, v_mvarCounter_750_);
lean_ctor_set(v_reuseFailAlloc_773_, 4, v_lDecls_751_);
lean_ctor_set(v_reuseFailAlloc_773_, 5, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_773_, 6, v_userNames_753_);
lean_ctor_set(v_reuseFailAlloc_773_, 7, v_lAssignment_754_);
lean_ctor_set(v_reuseFailAlloc_773_, 8, v_eAssignment_755_);
lean_ctor_set(v_reuseFailAlloc_773_, 9, v_dAssignment_756_);
v___x_764_ = v_reuseFailAlloc_773_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_766_; 
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_764_);
v___x_766_ = v___x_745_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_cache_740_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_zetaDeltaFVarIds_741_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v_postponed_742_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v_diag_743_);
v___x_766_ = v_reuseFailAlloc_772_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_767_ = lean_st_ref_set(v___y_709_, v___x_766_);
v___x_768_ = lean_box(0);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_768_);
v___x_770_ = v___x_732_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
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
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_del_object(v___x_725_);
lean_dec(v_index_723_);
lean_dec(v_numScopeArgs_722_);
lean_dec_ref(v_localInstances_720_);
lean_dec(v_depth_719_);
lean_dec_ref(v_type_718_);
lean_dec(v_userName_716_);
lean_dec(v_mvarId_707_);
v_a_778_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_727_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_727_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0___boxed(lean_object* v_mvarId_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0(v_mvarId_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic(lean_object* v_mvarId_794_, lean_object* v_tacticCode_795_, lean_object* v_ctx_796_, lean_object* v_s_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v___x_803_; 
lean_inc(v_mvarId_794_);
v___x_803_ = l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0(v_mvarId_794_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v___f_804_; lean_object* v___x_805_; uint8_t v___x_806_; lean_object* v___x_807_; lean_object* v___f_808_; lean_object* v___x_809_; 
lean_dec_ref_known(v___x_803_, 1);
v___f_804_ = lean_alloc_closure((void*)(l_Lean_Elab_runTactic___lam__0___boxed), 10, 1);
lean_closure_set(v___f_804_, 0, v_tacticCode_795_);
v___x_805_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_805_, 0, v_mvarId_794_);
lean_closure_set(v___x_805_, 1, v___f_804_);
v___x_806_ = 1;
v___x_807_ = lean_box(v___x_806_);
v___f_808_ = lean_alloc_closure((void*)(l_Lean_Elab_runTactic___lam__1___boxed), 9, 2);
lean_closure_set(v___f_808_, 0, v___x_805_);
lean_closure_set(v___f_808_, 1, v___x_807_);
v___x_809_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_808_, v_ctx_796_, v_s_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
return v___x_809_;
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v_s_797_);
lean_dec_ref(v_ctx_796_);
lean_dec(v_tacticCode_795_);
lean_dec(v_mvarId_794_);
v_a_810_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_803_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_803_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic___boxed(lean_object* v_mvarId_818_, lean_object* v_tacticCode_819_, lean_object* v_ctx_820_, lean_object* v_s_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_Elab_runTactic(v_mvarId_818_, v_tacticCode_819_, v_ctx_820_, v_s_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1(lean_object* v_e_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_e_828_, v___y_830_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___boxed(lean_object* v_e_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1(v_e_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2(lean_object* v_00_u03b2_842_, lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2___redArg(v_x_843_, v_x_844_, v_x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1(lean_object* v_00_u03b4_847_, lean_object* v_t_848_, lean_object* v_k_849_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg(v_t_848_, v_k_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b4_851_, lean_object* v_t_852_, lean_object* v_k_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1(v_00_u03b4_851_, v_t_852_, v_k_853_);
lean_dec(v_k_853_);
lean_dec(v_t_852_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_855_, lean_object* v_x_856_, size_t v_x_857_, size_t v_x_858_, lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_x_856_, v_x_857_, v_x_858_, v_x_859_, v_x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_862_, lean_object* v_x_863_, lean_object* v_x_864_, lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v_x_867_){
_start:
{
size_t v_x_6473__boxed_868_; size_t v_x_6474__boxed_869_; lean_object* v_res_870_; 
v_x_6473__boxed_868_ = lean_unbox_usize(v_x_864_);
lean_dec(v_x_864_);
v_x_6474__boxed_869_ = lean_unbox_usize(v_x_865_);
lean_dec(v_x_865_);
v_res_870_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6(v_00_u03b2_862_, v_x_863_, v_x_6473__boxed_868_, v_x_6474__boxed_869_, v_x_866_, v_x_867_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8(lean_object* v_00_u03b2_871_, lean_object* v_n_872_, lean_object* v_k_873_, lean_object* v_v_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8___redArg(v_n_872_, v_k_873_, v_v_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9(lean_object* v_00_u03b2_876_, size_t v_depth_877_, lean_object* v_keys_878_, lean_object* v_vals_879_, lean_object* v_heq_880_, lean_object* v_i_881_, lean_object* v_entries_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(v_depth_877_, v_keys_878_, v_vals_879_, v_i_881_, v_entries_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___boxed(lean_object* v_00_u03b2_884_, lean_object* v_depth_885_, lean_object* v_keys_886_, lean_object* v_vals_887_, lean_object* v_heq_888_, lean_object* v_i_889_, lean_object* v_entries_890_){
_start:
{
size_t v_depth_boxed_891_; lean_object* v_res_892_; 
v_depth_boxed_891_ = lean_unbox_usize(v_depth_885_);
lean_dec(v_depth_885_);
v_res_892_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9(v_00_u03b2_884_, v_depth_boxed_891_, v_keys_886_, v_vals_887_, v_heq_888_, v_i_889_, v_entries_890_);
lean_dec_ref(v_vals_887_);
lean_dec_ref(v_keys_886_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12(lean_object* v_00_u03b2_893_, lean_object* v_x_894_, lean_object* v_x_895_, lean_object* v_x_896_, lean_object* v_x_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12___redArg(v_x_894_, v_x_895_, v_x_896_, v_x_897_);
return v___x_898_;
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
