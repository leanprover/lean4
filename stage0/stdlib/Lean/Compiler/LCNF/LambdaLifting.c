// Lean compiler output
// Module: Lean.Compiler.LCNF.LambdaLifting
// Imports: Lean.Meta.Instances Lean.Compiler.InlineAttrs Lean.Compiler.LCNF.Closure Lean.Compiler.LCNF.Types Lean.Compiler.LCNF.MonadScope Lean.Compiler.LCNF.Internalize Lean.Compiler.LCNF.Level Lean.Compiler.LCNF.AuxDeclCache
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
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
static lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstance___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__1;
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__4;
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
static lean_object* l_Lean_Compiler_LCNF_lambdaLifting___closed__1;
static lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0(lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_lambdaLifting_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lambdaLifting;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lambdaLifting___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
static lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1;
lean_object* l_Lean_Compiler_LCNF_Code_size(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lambdaLifting___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
static lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__19____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_LambdaLifting_main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
static lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__2;
uint8_t l_Lean_Compiler_LCNF_Decl_inlineAttr(lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__2;
lean_object* l_Lean_Compiler_LCNF_Decl_save___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_lambdaLifting_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___closed__0;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_lambdaLifting___closed__0;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
static lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Closure_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
static lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__5;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(size_t, size_t, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1(uint8_t, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
static lean_object* l_Lean_Compiler_LCNF_LambdaLifting_main___closed__0;
static lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__0;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instFVarIdSetEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_eagerLambdaLifting_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Closure_collectFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(x_8, x_4, x_5);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = 1;
if (lean_obj_tag(x_11) == 0)
{
if (x_6 == 0)
{
size_t x_14; size_t x_15; 
lean_free_object(x_9);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_5 = x_12;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_box(x_13);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
}
else
{
lean_object* x_18; 
lean_dec_ref(x_11);
x_18 = lean_box(x_13);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = 1;
if (lean_obj_tag(x_19) == 0)
{
if (x_6 == 0)
{
size_t x_22; size_t x_23; 
x_22 = 1;
x_23 = lean_usize_add(x_2, x_22);
x_2 = x_23;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(x_21);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_19);
x_27 = lean_box(x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_20);
return x_28;
}
}
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(x_1, x_2, x_3, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
if (x_10 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
x_13 = lean_box(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_17 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(x_7, x_15, x_16, x_5, x_6);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_LambdaLifting_hasInstParam_spec__0(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_1, 4);
x_11 = l_Lean_Compiler_LCNF_Code_size(x_10);
x_12 = lean_nat_dec_lt(x_11, x_9);
lean_dec(x_11);
if (x_12 == 0)
{
if (x_8 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Compiler_LCNF_LambdaLifting_hasInstParam(x_1, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_take(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_10, x_11);
lean_ctor_set(x_7, 1, x_12);
x_13 = lean_st_ref_set(x_2, x_7, x_8);
x_14 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec_ref(x_14);
x_18 = lean_name_append_index_after(x_16, x_10);
x_19 = l_Lean_Name_append(x_17, x_18);
lean_inc(x_19);
x_20 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_19, x_3, x_4, x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec_ref(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; 
lean_dec_ref(x_21);
lean_dec(x_19);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec_ref(x_20);
x_5 = x_26;
goto _start;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_7);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_29, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_st_ref_set(x_2, x_32, x_8);
x_34 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec_ref(x_34);
x_38 = lean_name_append_index_after(x_36, x_29);
x_39 = l_Lean_Name_append(x_37, x_38);
lean_inc(x_39);
x_40 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_39, x_3, x_4, x_35);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_1);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
else
{
lean_object* x_45; 
lean_dec_ref(x_41);
lean_dec(x_39);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec_ref(x_40);
x_5 = x_45;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(x_1, x_2, x_4, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_12, x_4, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_17, x_2, x_14);
x_2 = x_19;
x_3 = x_20;
x_9 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = lean_array_size(x_1);
x_13 = 0;
x_14 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(x_12, x_13, x_1, x_6, x_7, x_8, x_9, x_10, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_18);
lean_dec_ref(x_2);
x_19 = lean_array_size(x_17);
x_20 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(x_19, x_13, x_17, x_6, x_7, x_8, x_9, x_10, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_18, x_6, x_7, x_8, x_9, x_10, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
lean_inc(x_24);
x_26 = l_Lean_Compiler_LCNF_Code_inferType(x_24, x_7, x_8, x_9, x_10, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l_Array_append___redArg(x_15, x_21);
lean_dec(x_21);
lean_inc_ref(x_29);
x_30 = l_Lean_Compiler_LCNF_mkForallParams(x_29, x_27, x_7, x_8, x_9, x_10, x_28);
lean_dec(x_27);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_24);
x_34 = lean_box(0);
x_35 = 0;
x_36 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_32);
lean_ctor_set(x_36, 3, x_29);
lean_ctor_set(x_36, 4, x_33);
lean_ctor_set(x_36, 5, x_5);
lean_ctor_set_uint8(x_36, sizeof(void*)*6, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*6 + 1, x_4);
x_37 = l_Lean_Compiler_LCNF_Decl_setLevelParams(x_36);
lean_ctor_set(x_30, 0, x_37);
return x_30;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_30, 0);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_30);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_24);
x_41 = lean_box(0);
x_42 = 0;
x_43 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_38);
lean_ctor_set(x_43, 3, x_29);
lean_ctor_set(x_43, 4, x_40);
lean_ctor_set(x_43, 5, x_5);
lean_ctor_set_uint8(x_43, sizeof(void*)*6, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*6 + 1, x_4);
x_44 = l_Lean_Compiler_LCNF_Decl_setLevelParams(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec_ref(x_29);
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_30);
if (x_46 == 0)
{
return x_30;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_30, 0);
x_48 = lean_ctor_get(x_30, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_30);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_26);
if (x_50 == 0)
{
return x_26;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_26, 0);
x_52 = lean_ctor_get(x_26, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_26);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go_spec__0(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_mkLevelParam(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_mkLevelParam(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_8, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_115; 
lean_inc_ref(x_3);
x_53 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDeclName___redArg(x_3, x_4, x_5, x_8, x_9);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_115 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_box(0);
x_56 = x_116;
x_57 = x_3;
x_58 = x_4;
x_59 = x_5;
x_60 = x_6;
x_61 = x_7;
x_62 = x_8;
x_63 = x_55;
goto block_114;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_117, 5);
lean_inc(x_118);
lean_dec_ref(x_117);
x_56 = x_118;
x_57 = x_3;
x_58 = x_4;
x_59 = x_5;
x_60 = x_6;
x_61 = x_7;
x_62 = x_8;
x_63 = x_55;
goto block_114;
}
block_52:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_st_ref_take(x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_19);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_array_size(x_1);
x_23 = 0;
x_24 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(x_22, x_23, x_1);
x_25 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_10);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_19);
lean_ctor_set(x_26, 3, x_25);
lean_inc_ref(x_26);
x_27 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_21, x_26);
lean_ctor_set(x_15, 0, x_27);
x_28 = lean_st_ref_set(x_12, x_15, x_16);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = 1;
x_31 = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(x_2, x_30, x_12, x_29);
lean_dec(x_12);
lean_dec_ref(x_2);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_26);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_36 = lean_ctor_get(x_15, 0);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_15);
x_38 = lean_array_size(x_1);
x_39 = 0;
x_40 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(x_38, x_39, x_1);
x_41 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_41, 0, x_11);
lean_ctor_set(x_41, 1, x_10);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_17);
lean_ctor_set(x_42, 1, x_18);
lean_ctor_set(x_42, 2, x_19);
lean_ctor_set(x_42, 3, x_41);
lean_inc_ref(x_42);
x_43 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_36, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_37);
x_45 = lean_st_ref_set(x_12, x_44, x_16);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = 1;
x_48 = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(x_2, x_47, x_12, x_46);
lean_dec(x_12);
lean_dec_ref(x_2);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
block_114:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_64 = lean_unsigned_to_nat(0u);
x_65 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__4;
x_66 = lean_st_mk_ref(x_65, x_63);
x_67 = lean_ctor_get(x_57, 1);
lean_inc_ref(x_67);
lean_dec_ref(x_57);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec_ref(x_66);
x_70 = lean_ctor_get_uint8(x_67, sizeof(void*)*6 + 1);
lean_dec_ref(x_67);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_71 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_go(x_1, x_2, x_54, x_70, x_56, x_68, x_59, x_60, x_61, x_62, x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = lean_st_ref_get(x_68, x_73);
lean_dec(x_68);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec_ref(x_74);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_72);
x_76 = l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(x_72, x_61, x_62, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec_ref(x_76);
x_79 = lean_ctor_get(x_72, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_72, 1);
lean_inc(x_80);
x_81 = lean_box(0);
x_82 = l_List_mapTR_loop___at___Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__0(x_80, x_81);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec_ref(x_61);
lean_inc(x_72);
x_83 = l_Lean_Compiler_LCNF_Decl_save___redArg(x_72, x_59, x_62, x_78);
lean_dec(x_62);
lean_dec_ref(x_59);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = lean_st_ref_take(x_58, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec_ref(x_85);
x_88 = !lean_is_exclusive(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_86, 0);
x_90 = lean_ctor_get(x_86, 1);
lean_dec(x_90);
x_91 = lean_array_push(x_89, x_72);
lean_ctor_set(x_86, 1, x_64);
lean_ctor_set(x_86, 0, x_91);
x_92 = lean_st_ref_set(x_58, x_86, x_87);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec_ref(x_92);
x_10 = x_82;
x_11 = x_79;
x_12 = x_60;
x_13 = x_93;
goto block_52;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
lean_dec(x_86);
x_95 = lean_array_push(x_94, x_72);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_64);
x_97 = lean_st_ref_set(x_58, x_96, x_87);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec_ref(x_97);
x_10 = x_82;
x_11 = x_79;
x_12 = x_60;
x_13 = x_98;
goto block_52;
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_79);
x_99 = lean_ctor_get(x_77, 0);
lean_inc(x_99);
lean_dec_ref(x_77);
lean_inc(x_60);
x_100 = l_Lean_Compiler_LCNF_eraseDecl(x_72, x_59, x_60, x_61, x_62, x_78);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec_ref(x_100);
x_10 = x_82;
x_11 = x_99;
x_12 = x_60;
x_13 = x_101;
goto block_52;
}
else
{
uint8_t x_102; 
lean_dec(x_99);
lean_dec(x_82);
lean_dec(x_60);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_102 = !lean_is_exclusive(x_100);
if (x_102 == 0)
{
return x_100;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_100, 0);
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_100);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_72);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_106 = !lean_is_exclusive(x_76);
if (x_106 == 0)
{
return x_76;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_76, 0);
x_108 = lean_ctor_get(x_76, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_76);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_68);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_110 = !lean_is_exclusive(x_71);
if (x_110 == 0)
{
return x_71;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_71, 0);
x_112 = lean_ctor_get(x_71, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_71);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_FVarIdSet_insert(x_4, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_12);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_10);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_23);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_25 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_13 = x_25;
goto block_21;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_23, x_23);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_23);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_27 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_13 = x_27;
goto block_21;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_30 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(x_10, x_28, x_29, x_4);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_31 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_12, x_2, x_3, x_30, x_5, x_6, x_7, x_8, x_9);
x_13 = x_31;
goto block_21;
}
}
block_21:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_11, x_10, x_14, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l_Lean_Name_quickCmp(x_1, x_3);
switch (x_6) {
case 0:
{
x_2 = x_4;
goto _start;
}
case 1:
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
default: 
{
x_2 = x_5;
goto _start;
}
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__0___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_16);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_15);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec_ref(x_15);
x_20 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_22);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec_ref(x_1);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_18, x_18);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_18);
lean_dec_ref(x_15);
x_33 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_10 = x_34;
x_11 = x_35;
goto block_14;
}
else
{
uint8_t x_36; 
lean_dec_ref(x_1);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_42 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(x_15, x_40, x_41, x_4);
lean_dec_ref(x_15);
x_43 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_16, x_2, x_3, x_42, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_10 = x_44;
x_11 = x_45;
goto block_14;
}
else
{
uint8_t x_46; 
lean_dec_ref(x_1);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_50);
x_51 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_53);
lean_ctor_set(x_51, 0, x_54);
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_51, 0);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_51);
x_57 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec_ref(x_1);
x_59 = !lean_is_exclusive(x_51);
if (x_59 == 0)
{
return x_51;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_51, 0);
x_61 = lean_ctor_get(x_51, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_51);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__0;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__1;
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_19 = lean_ctor_get(x_12, 1);
lean_dec(x_19);
x_20 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__2;
x_21 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__3;
lean_inc_ref(x_15);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_18);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_17);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_27, 0, x_16);
lean_ctor_set(x_12, 4, x_25);
lean_ctor_set(x_12, 3, x_26);
lean_ctor_set(x_12, 2, x_27);
lean_ctor_set(x_12, 1, x_20);
lean_ctor_set(x_12, 0, x_24);
lean_ctor_set(x_10, 1, x_21);
x_28 = l_ReaderT_instMonad___redArg(x_10);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 2);
x_35 = lean_ctor_get(x_30, 3);
x_36 = lean_ctor_get(x_30, 4);
x_37 = lean_ctor_get(x_30, 1);
lean_dec(x_37);
x_38 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__4;
x_39 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__5;
lean_inc_ref(x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_40, 0, x_33);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_33);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_36);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_45, 0, x_34);
lean_ctor_set(x_30, 4, x_43);
lean_ctor_set(x_30, 3, x_44);
lean_ctor_set(x_30, 2, x_45);
lean_ctor_set(x_30, 1, x_38);
lean_ctor_set(x_30, 0, x_42);
lean_ctor_set(x_28, 1, x_39);
x_46 = l_ReaderT_instMonad___redArg(x_28);
x_47 = l_ReaderT_instMonad___redArg(x_46);
x_48 = l_ReaderT_instMonad___redArg(x_47);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_48);
x_49 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = l_Lean_FVarIdSet_insert(x_4, x_51);
x_53 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_50, x_2, x_3, x_52, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_1, x_49, x_55);
lean_dec_ref(x_1);
lean_ctor_set(x_53, 0, x_56);
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_53);
x_59 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_1, x_49, x_57);
lean_dec_ref(x_1);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_dec_ref(x_49);
lean_dec_ref(x_1);
return x_53;
}
}
case 1:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_48);
x_61 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_62);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_63 = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(x_64, x_2, x_5, x_6, x_7, x_8, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_67);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec_ref(x_66);
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
x_71 = l_Lean_FVarIdSet_insert(x_4, x_70);
x_72 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_62, x_2, x_3, x_71, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_1, x_64, x_74);
lean_dec_ref(x_1);
lean_ctor_set(x_72, 0, x_75);
return x_72;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_72, 0);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_72);
x_78 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_1, x_64, x_76);
lean_dec_ref(x_1);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
lean_dec(x_64);
lean_dec_ref(x_1);
return x_72;
}
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_1);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_ctor_get(x_1, 1);
lean_dec(x_81);
x_82 = lean_ctor_get(x_1, 0);
lean_dec(x_82);
x_83 = lean_ctor_get(x_66, 1);
lean_inc(x_83);
lean_dec_ref(x_66);
lean_inc(x_4);
x_84 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed), 2, 1);
lean_closure_set(x_84, 0, x_4);
x_85 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed), 2, 1);
lean_closure_set(x_85, 0, x_67);
lean_inc(x_64);
x_86 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectFunDecl), 8, 1);
lean_closure_set(x_86, 0, x_64);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_87 = l_Lean_Compiler_LCNF_Closure_run___redArg(x_86, x_84, x_85, x_5, x_6, x_7, x_8, x_83);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec_ref(x_87);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_92 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(x_91, x_64, x_2, x_3, x_5, x_6, x_7, x_8, x_90);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec_ref(x_92);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = l_Lean_FVarIdSet_insert(x_4, x_95);
x_97 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_62, x_2, x_3, x_96, x_5, x_6, x_7, x_8, x_94);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_97, 0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_99);
lean_ctor_set(x_1, 0, x_93);
lean_ctor_set(x_97, 0, x_1);
return x_97;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_97, 0);
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_97);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_93);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_1);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
else
{
lean_dec(x_93);
lean_free_object(x_1);
return x_97;
}
}
else
{
uint8_t x_103; 
lean_free_object(x_1);
lean_dec_ref(x_62);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_103 = !lean_is_exclusive(x_92);
if (x_103 == 0)
{
return x_92;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_92, 0);
x_105 = lean_ctor_get(x_92, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_92);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_free_object(x_1);
lean_dec(x_64);
lean_dec_ref(x_62);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_107 = !lean_is_exclusive(x_87);
if (x_107 == 0)
{
return x_87;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_87, 0);
x_109 = lean_ctor_get(x_87, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_87);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_1);
x_111 = lean_ctor_get(x_66, 1);
lean_inc(x_111);
lean_dec_ref(x_66);
lean_inc(x_4);
x_112 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed), 2, 1);
lean_closure_set(x_112, 0, x_4);
x_113 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed), 2, 1);
lean_closure_set(x_113, 0, x_67);
lean_inc(x_64);
x_114 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectFunDecl), 8, 1);
lean_closure_set(x_114, 0, x_64);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_115 = l_Lean_Compiler_LCNF_Closure_run___redArg(x_114, x_112, x_113, x_5, x_6, x_7, x_8, x_111);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec_ref(x_115);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
lean_dec(x_117);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_120 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(x_119, x_64, x_2, x_3, x_5, x_6, x_7, x_8, x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec_ref(x_120);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
x_124 = l_Lean_FVarIdSet_insert(x_4, x_123);
x_125 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_62, x_2, x_3, x_124, x_5, x_6, x_7, x_8, x_122);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_121);
lean_ctor_set(x_129, 1, x_126);
if (lean_is_scalar(x_128)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_128;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_127);
return x_130;
}
else
{
lean_dec(x_121);
return x_125;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec_ref(x_62);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_131 = lean_ctor_get(x_120, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_120, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_133 = x_120;
} else {
 lean_dec_ref(x_120);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_64);
lean_dec_ref(x_62);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_135 = lean_ctor_get(x_115, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_115, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_137 = x_115;
} else {
 lean_dec_ref(x_115);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
}
}
else
{
uint8_t x_139; 
lean_dec_ref(x_62);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_139 = !lean_is_exclusive(x_63);
if (x_139 == 0)
{
return x_63;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_63, 0);
x_141 = lean_ctor_get(x_63, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_63);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
case 2:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec_ref(x_48);
x_143 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_143);
x_144 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_144);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_145 = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(x_143, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec_ref(x_145);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
x_149 = l_Lean_FVarIdSet_insert(x_4, x_148);
x_150 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_144, x_2, x_3, x_149, x_5, x_6, x_7, x_8, x_147);
if (lean_obj_tag(x_150) == 0)
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_150, 0);
x_153 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_1, x_146, x_152);
lean_dec_ref(x_1);
lean_ctor_set(x_150, 0, x_153);
return x_150;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_150, 0);
x_155 = lean_ctor_get(x_150, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_150);
x_156 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_1, x_146, x_154);
lean_dec_ref(x_1);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
else
{
lean_dec(x_146);
lean_dec_ref(x_1);
return x_150;
}
}
else
{
uint8_t x_158; 
lean_dec_ref(x_144);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_158 = !lean_is_exclusive(x_145);
if (x_158 == 0)
{
return x_145;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_145, 0);
x_160 = lean_ctor_get(x_145, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_145);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
case 4:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_162 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_162);
x_163 = lean_ctor_get(x_162, 3);
lean_inc_ref(x_163);
lean_dec_ref(x_162);
x_164 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__2), 9, 0);
x_165 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_48, x_163, x_164);
x_166 = lean_apply_8(x_165, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_166) == 0)
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_166, 0);
x_169 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp(x_1, x_168);
lean_ctor_set(x_166, 0, x_169);
return x_166;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = lean_ctor_get(x_166, 0);
x_171 = lean_ctor_get(x_166, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_166);
x_172 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp(x_1, x_170);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
uint8_t x_174; 
lean_dec_ref(x_1);
x_174 = !lean_is_exclusive(x_166);
if (x_174 == 0)
{
return x_166;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_166, 0);
x_176 = lean_ctor_get(x_166, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_166);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
default: 
{
lean_object* x_178; 
lean_dec_ref(x_48);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_1);
lean_ctor_set(x_178, 1, x_9);
return x_178;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_179 = lean_ctor_get(x_30, 0);
x_180 = lean_ctor_get(x_30, 2);
x_181 = lean_ctor_get(x_30, 3);
x_182 = lean_ctor_get(x_30, 4);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_30);
x_183 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__4;
x_184 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__5;
lean_inc_ref(x_179);
x_185 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_185, 0, x_179);
x_186 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_186, 0, x_179);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_188, 0, x_182);
x_189 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_189, 0, x_181);
x_190 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_190, 0, x_180);
x_191 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_191, 0, x_187);
lean_ctor_set(x_191, 1, x_183);
lean_ctor_set(x_191, 2, x_190);
lean_ctor_set(x_191, 3, x_189);
lean_ctor_set(x_191, 4, x_188);
lean_ctor_set(x_28, 1, x_184);
lean_ctor_set(x_28, 0, x_191);
x_192 = l_ReaderT_instMonad___redArg(x_28);
x_193 = l_ReaderT_instMonad___redArg(x_192);
x_194 = l_ReaderT_instMonad___redArg(x_193);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec_ref(x_194);
x_195 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_195);
x_196 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_196);
x_197 = lean_ctor_get(x_195, 0);
lean_inc(x_197);
x_198 = l_Lean_FVarIdSet_insert(x_4, x_197);
x_199 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_196, x_2, x_3, x_198, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_202 = x_199;
} else {
 lean_dec_ref(x_199);
 x_202 = lean_box(0);
}
x_203 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_1, x_195, x_200);
lean_dec_ref(x_1);
if (lean_is_scalar(x_202)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_202;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_201);
return x_204;
}
else
{
lean_dec_ref(x_195);
lean_dec_ref(x_1);
return x_199;
}
}
case 1:
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec_ref(x_194);
x_205 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_205);
x_206 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_206);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_207 = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(x_205, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec_ref(x_207);
x_210 = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(x_208, x_2, x_5, x_6, x_7, x_8, x_209);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_unbox(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_211);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
lean_dec_ref(x_210);
x_214 = lean_ctor_get(x_208, 0);
lean_inc(x_214);
x_215 = l_Lean_FVarIdSet_insert(x_4, x_214);
x_216 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_206, x_2, x_3, x_215, x_5, x_6, x_7, x_8, x_213);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_219 = x_216;
} else {
 lean_dec_ref(x_216);
 x_219 = lean_box(0);
}
x_220 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_1, x_208, x_217);
lean_dec_ref(x_1);
if (lean_is_scalar(x_219)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_219;
}
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_218);
return x_221;
}
else
{
lean_dec(x_208);
lean_dec_ref(x_1);
return x_216;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_222 = x_1;
} else {
 lean_dec_ref(x_1);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_210, 1);
lean_inc(x_223);
lean_dec_ref(x_210);
lean_inc(x_4);
x_224 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed), 2, 1);
lean_closure_set(x_224, 0, x_4);
x_225 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed), 2, 1);
lean_closure_set(x_225, 0, x_211);
lean_inc(x_208);
x_226 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectFunDecl), 8, 1);
lean_closure_set(x_226, 0, x_208);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_227 = l_Lean_Compiler_LCNF_Closure_run___redArg(x_226, x_224, x_225, x_5, x_6, x_7, x_8, x_223);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
lean_dec(x_228);
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
lean_dec_ref(x_227);
x_231 = lean_ctor_get(x_229, 0);
lean_inc(x_231);
lean_dec(x_229);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_232 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(x_231, x_208, x_2, x_3, x_5, x_6, x_7, x_8, x_230);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec_ref(x_232);
x_235 = lean_ctor_get(x_233, 0);
lean_inc(x_235);
x_236 = l_Lean_FVarIdSet_insert(x_4, x_235);
x_237 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_206, x_2, x_3, x_236, x_5, x_6, x_7, x_8, x_234);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_240 = x_237;
} else {
 lean_dec_ref(x_237);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_222;
 lean_ctor_set_tag(x_241, 0);
}
lean_ctor_set(x_241, 0, x_233);
lean_ctor_set(x_241, 1, x_238);
if (lean_is_scalar(x_240)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_240;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_239);
return x_242;
}
else
{
lean_dec(x_233);
lean_dec(x_222);
return x_237;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_222);
lean_dec_ref(x_206);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_243 = lean_ctor_get(x_232, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_232, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_245 = x_232;
} else {
 lean_dec_ref(x_232);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_222);
lean_dec(x_208);
lean_dec_ref(x_206);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_247 = lean_ctor_get(x_227, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_227, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_249 = x_227;
} else {
 lean_dec_ref(x_227);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec_ref(x_206);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_251 = lean_ctor_get(x_207, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_207, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_253 = x_207;
} else {
 lean_dec_ref(x_207);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_252);
return x_254;
}
}
case 2:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec_ref(x_194);
x_255 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_255);
x_256 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_256);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_257 = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(x_255, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec_ref(x_257);
x_260 = lean_ctor_get(x_258, 0);
lean_inc(x_260);
x_261 = l_Lean_FVarIdSet_insert(x_4, x_260);
x_262 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_256, x_2, x_3, x_261, x_5, x_6, x_7, x_8, x_259);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_265 = x_262;
} else {
 lean_dec_ref(x_262);
 x_265 = lean_box(0);
}
x_266 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_1, x_258, x_263);
lean_dec_ref(x_1);
if (lean_is_scalar(x_265)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_265;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_264);
return x_267;
}
else
{
lean_dec(x_258);
lean_dec_ref(x_1);
return x_262;
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec_ref(x_256);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_268 = lean_ctor_get(x_257, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_257, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_270 = x_257;
} else {
 lean_dec_ref(x_257);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
}
case 4:
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_272 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_272);
x_273 = lean_ctor_get(x_272, 3);
lean_inc_ref(x_273);
lean_dec_ref(x_272);
x_274 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__2), 9, 0);
x_275 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_194, x_273, x_274);
x_276 = lean_apply_8(x_275, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_279 = x_276;
} else {
 lean_dec_ref(x_276);
 x_279 = lean_box(0);
}
x_280 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp(x_1, x_277);
if (lean_is_scalar(x_279)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_279;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_278);
return x_281;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec_ref(x_1);
x_282 = lean_ctor_get(x_276, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_276, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_284 = x_276;
} else {
 lean_dec_ref(x_276);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(1, 2, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_282);
lean_ctor_set(x_285, 1, x_283);
return x_285;
}
}
default: 
{
lean_object* x_286; 
lean_dec_ref(x_194);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_1);
lean_ctor_set(x_286, 1, x_9);
return x_286;
}
}
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_287 = lean_ctor_get(x_28, 0);
lean_inc(x_287);
lean_dec(x_28);
x_288 = lean_ctor_get(x_287, 0);
lean_inc_ref(x_288);
x_289 = lean_ctor_get(x_287, 2);
lean_inc_ref(x_289);
x_290 = lean_ctor_get(x_287, 3);
lean_inc_ref(x_290);
x_291 = lean_ctor_get(x_287, 4);
lean_inc_ref(x_291);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 lean_ctor_release(x_287, 2);
 lean_ctor_release(x_287, 3);
 lean_ctor_release(x_287, 4);
 x_292 = x_287;
} else {
 lean_dec_ref(x_287);
 x_292 = lean_box(0);
}
x_293 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__4;
x_294 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__5;
lean_inc_ref(x_288);
x_295 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_295, 0, x_288);
x_296 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_296, 0, x_288);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
x_298 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_298, 0, x_291);
x_299 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_299, 0, x_290);
x_300 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_300, 0, x_289);
if (lean_is_scalar(x_292)) {
 x_301 = lean_alloc_ctor(0, 5, 0);
} else {
 x_301 = x_292;
}
lean_ctor_set(x_301, 0, x_297);
lean_ctor_set(x_301, 1, x_293);
lean_ctor_set(x_301, 2, x_300);
lean_ctor_set(x_301, 3, x_299);
lean_ctor_set(x_301, 4, x_298);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_294);
x_303 = l_ReaderT_instMonad___redArg(x_302);
x_304 = l_ReaderT_instMonad___redArg(x_303);
x_305 = l_ReaderT_instMonad___redArg(x_304);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec_ref(x_305);
x_306 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_306);
x_307 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_307);
x_308 = lean_ctor_get(x_306, 0);
lean_inc(x_308);
x_309 = l_Lean_FVarIdSet_insert(x_4, x_308);
x_310 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_307, x_2, x_3, x_309, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_313 = x_310;
} else {
 lean_dec_ref(x_310);
 x_313 = lean_box(0);
}
x_314 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_1, x_306, x_311);
lean_dec_ref(x_1);
if (lean_is_scalar(x_313)) {
 x_315 = lean_alloc_ctor(0, 2, 0);
} else {
 x_315 = x_313;
}
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_312);
return x_315;
}
else
{
lean_dec_ref(x_306);
lean_dec_ref(x_1);
return x_310;
}
}
case 1:
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec_ref(x_305);
x_316 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_316);
x_317 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_317);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_318 = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(x_316, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec_ref(x_318);
x_321 = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(x_319, x_2, x_5, x_6, x_7, x_8, x_320);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_unbox(x_322);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_322);
x_324 = lean_ctor_get(x_321, 1);
lean_inc(x_324);
lean_dec_ref(x_321);
x_325 = lean_ctor_get(x_319, 0);
lean_inc(x_325);
x_326 = l_Lean_FVarIdSet_insert(x_4, x_325);
x_327 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_317, x_2, x_3, x_326, x_5, x_6, x_7, x_8, x_324);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_330 = x_327;
} else {
 lean_dec_ref(x_327);
 x_330 = lean_box(0);
}
x_331 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_1, x_319, x_328);
lean_dec_ref(x_1);
if (lean_is_scalar(x_330)) {
 x_332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_332 = x_330;
}
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_329);
return x_332;
}
else
{
lean_dec(x_319);
lean_dec_ref(x_1);
return x_327;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_333 = x_1;
} else {
 lean_dec_ref(x_1);
 x_333 = lean_box(0);
}
x_334 = lean_ctor_get(x_321, 1);
lean_inc(x_334);
lean_dec_ref(x_321);
lean_inc(x_4);
x_335 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed), 2, 1);
lean_closure_set(x_335, 0, x_4);
x_336 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed), 2, 1);
lean_closure_set(x_336, 0, x_322);
lean_inc(x_319);
x_337 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectFunDecl), 8, 1);
lean_closure_set(x_337, 0, x_319);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_338 = l_Lean_Compiler_LCNF_Closure_run___redArg(x_337, x_335, x_336, x_5, x_6, x_7, x_8, x_334);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_339, 1);
lean_inc(x_340);
lean_dec(x_339);
x_341 = lean_ctor_get(x_338, 1);
lean_inc(x_341);
lean_dec_ref(x_338);
x_342 = lean_ctor_get(x_340, 0);
lean_inc(x_342);
lean_dec(x_340);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_343 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(x_342, x_319, x_2, x_3, x_5, x_6, x_7, x_8, x_341);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec_ref(x_343);
x_346 = lean_ctor_get(x_344, 0);
lean_inc(x_346);
x_347 = l_Lean_FVarIdSet_insert(x_4, x_346);
x_348 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_317, x_2, x_3, x_347, x_5, x_6, x_7, x_8, x_345);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_351 = x_348;
} else {
 lean_dec_ref(x_348);
 x_351 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_333;
 lean_ctor_set_tag(x_352, 0);
}
lean_ctor_set(x_352, 0, x_344);
lean_ctor_set(x_352, 1, x_349);
if (lean_is_scalar(x_351)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_351;
}
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_350);
return x_353;
}
else
{
lean_dec(x_344);
lean_dec(x_333);
return x_348;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_333);
lean_dec_ref(x_317);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_354 = lean_ctor_get(x_343, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_343, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_356 = x_343;
} else {
 lean_dec_ref(x_343);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_354);
lean_ctor_set(x_357, 1, x_355);
return x_357;
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_333);
lean_dec(x_319);
lean_dec_ref(x_317);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_358 = lean_ctor_get(x_338, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_338, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_360 = x_338;
} else {
 lean_dec_ref(x_338);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_359);
return x_361;
}
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec_ref(x_317);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_362 = lean_ctor_get(x_318, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_318, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_364 = x_318;
} else {
 lean_dec_ref(x_318);
 x_364 = lean_box(0);
}
if (lean_is_scalar(x_364)) {
 x_365 = lean_alloc_ctor(1, 2, 0);
} else {
 x_365 = x_364;
}
lean_ctor_set(x_365, 0, x_362);
lean_ctor_set(x_365, 1, x_363);
return x_365;
}
}
case 2:
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_dec_ref(x_305);
x_366 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_366);
x_367 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_367);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_368 = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(x_366, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_368, 1);
lean_inc(x_370);
lean_dec_ref(x_368);
x_371 = lean_ctor_get(x_369, 0);
lean_inc(x_371);
x_372 = l_Lean_FVarIdSet_insert(x_4, x_371);
x_373 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_367, x_2, x_3, x_372, x_5, x_6, x_7, x_8, x_370);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_376 = x_373;
} else {
 lean_dec_ref(x_373);
 x_376 = lean_box(0);
}
x_377 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_1, x_369, x_374);
lean_dec_ref(x_1);
if (lean_is_scalar(x_376)) {
 x_378 = lean_alloc_ctor(0, 2, 0);
} else {
 x_378 = x_376;
}
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_375);
return x_378;
}
else
{
lean_dec(x_369);
lean_dec_ref(x_1);
return x_373;
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec_ref(x_367);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_379 = lean_ctor_get(x_368, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_368, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_381 = x_368;
} else {
 lean_dec_ref(x_368);
 x_381 = lean_box(0);
}
if (lean_is_scalar(x_381)) {
 x_382 = lean_alloc_ctor(1, 2, 0);
} else {
 x_382 = x_381;
}
lean_ctor_set(x_382, 0, x_379);
lean_ctor_set(x_382, 1, x_380);
return x_382;
}
}
case 4:
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_383 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_383);
x_384 = lean_ctor_get(x_383, 3);
lean_inc_ref(x_384);
lean_dec_ref(x_383);
x_385 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__2), 9, 0);
x_386 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_305, x_384, x_385);
x_387 = lean_apply_8(x_386, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_390 = x_387;
} else {
 lean_dec_ref(x_387);
 x_390 = lean_box(0);
}
x_391 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp(x_1, x_388);
if (lean_is_scalar(x_390)) {
 x_392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_392 = x_390;
}
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_389);
return x_392;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec_ref(x_1);
x_393 = lean_ctor_get(x_387, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_387, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_395 = x_387;
} else {
 lean_dec_ref(x_387);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 2, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_393);
lean_ctor_set(x_396, 1, x_394);
return x_396;
}
}
default: 
{
lean_object* x_397; 
lean_dec_ref(x_305);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_1);
lean_ctor_set(x_397, 1, x_9);
return x_397;
}
}
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_398 = lean_ctor_get(x_12, 0);
x_399 = lean_ctor_get(x_12, 2);
x_400 = lean_ctor_get(x_12, 3);
x_401 = lean_ctor_get(x_12, 4);
lean_inc(x_401);
lean_inc(x_400);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_12);
x_402 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__2;
x_403 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__3;
lean_inc_ref(x_398);
x_404 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_404, 0, x_398);
x_405 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_405, 0, x_398);
x_406 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
x_407 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_407, 0, x_401);
x_408 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_408, 0, x_400);
x_409 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_409, 0, x_399);
x_410 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_410, 0, x_406);
lean_ctor_set(x_410, 1, x_402);
lean_ctor_set(x_410, 2, x_409);
lean_ctor_set(x_410, 3, x_408);
lean_ctor_set(x_410, 4, x_407);
lean_ctor_set(x_10, 1, x_403);
lean_ctor_set(x_10, 0, x_410);
x_411 = l_ReaderT_instMonad___redArg(x_10);
x_412 = lean_ctor_get(x_411, 0);
lean_inc_ref(x_412);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_413 = x_411;
} else {
 lean_dec_ref(x_411);
 x_413 = lean_box(0);
}
x_414 = lean_ctor_get(x_412, 0);
lean_inc_ref(x_414);
x_415 = lean_ctor_get(x_412, 2);
lean_inc_ref(x_415);
x_416 = lean_ctor_get(x_412, 3);
lean_inc_ref(x_416);
x_417 = lean_ctor_get(x_412, 4);
lean_inc_ref(x_417);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 lean_ctor_release(x_412, 2);
 lean_ctor_release(x_412, 3);
 lean_ctor_release(x_412, 4);
 x_418 = x_412;
} else {
 lean_dec_ref(x_412);
 x_418 = lean_box(0);
}
x_419 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__4;
x_420 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__5;
lean_inc_ref(x_414);
x_421 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_421, 0, x_414);
x_422 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_422, 0, x_414);
x_423 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_423, 0, x_421);
lean_ctor_set(x_423, 1, x_422);
x_424 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_424, 0, x_417);
x_425 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_425, 0, x_416);
x_426 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_426, 0, x_415);
if (lean_is_scalar(x_418)) {
 x_427 = lean_alloc_ctor(0, 5, 0);
} else {
 x_427 = x_418;
}
lean_ctor_set(x_427, 0, x_423);
lean_ctor_set(x_427, 1, x_419);
lean_ctor_set(x_427, 2, x_426);
lean_ctor_set(x_427, 3, x_425);
lean_ctor_set(x_427, 4, x_424);
if (lean_is_scalar(x_413)) {
 x_428 = lean_alloc_ctor(0, 2, 0);
} else {
 x_428 = x_413;
}
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_420);
x_429 = l_ReaderT_instMonad___redArg(x_428);
x_430 = l_ReaderT_instMonad___redArg(x_429);
x_431 = l_ReaderT_instMonad___redArg(x_430);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec_ref(x_431);
x_432 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_432);
x_433 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_433);
x_434 = lean_ctor_get(x_432, 0);
lean_inc(x_434);
x_435 = l_Lean_FVarIdSet_insert(x_4, x_434);
x_436 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_433, x_2, x_3, x_435, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 lean_ctor_release(x_436, 1);
 x_439 = x_436;
} else {
 lean_dec_ref(x_436);
 x_439 = lean_box(0);
}
x_440 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_1, x_432, x_437);
lean_dec_ref(x_1);
if (lean_is_scalar(x_439)) {
 x_441 = lean_alloc_ctor(0, 2, 0);
} else {
 x_441 = x_439;
}
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_438);
return x_441;
}
else
{
lean_dec_ref(x_432);
lean_dec_ref(x_1);
return x_436;
}
}
case 1:
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec_ref(x_431);
x_442 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_442);
x_443 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_443);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_444 = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(x_442, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; 
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_444, 1);
lean_inc(x_446);
lean_dec_ref(x_444);
x_447 = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(x_445, x_2, x_5, x_6, x_7, x_8, x_446);
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_unbox(x_448);
if (x_449 == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_448);
x_450 = lean_ctor_get(x_447, 1);
lean_inc(x_450);
lean_dec_ref(x_447);
x_451 = lean_ctor_get(x_445, 0);
lean_inc(x_451);
x_452 = l_Lean_FVarIdSet_insert(x_4, x_451);
x_453 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_443, x_2, x_3, x_452, x_5, x_6, x_7, x_8, x_450);
if (lean_obj_tag(x_453) == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_456 = x_453;
} else {
 lean_dec_ref(x_453);
 x_456 = lean_box(0);
}
x_457 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_1, x_445, x_454);
lean_dec_ref(x_1);
if (lean_is_scalar(x_456)) {
 x_458 = lean_alloc_ctor(0, 2, 0);
} else {
 x_458 = x_456;
}
lean_ctor_set(x_458, 0, x_457);
lean_ctor_set(x_458, 1, x_455);
return x_458;
}
else
{
lean_dec(x_445);
lean_dec_ref(x_1);
return x_453;
}
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_459 = x_1;
} else {
 lean_dec_ref(x_1);
 x_459 = lean_box(0);
}
x_460 = lean_ctor_get(x_447, 1);
lean_inc(x_460);
lean_dec_ref(x_447);
lean_inc(x_4);
x_461 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed), 2, 1);
lean_closure_set(x_461, 0, x_4);
x_462 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed), 2, 1);
lean_closure_set(x_462, 0, x_448);
lean_inc(x_445);
x_463 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectFunDecl), 8, 1);
lean_closure_set(x_463, 0, x_445);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_464 = l_Lean_Compiler_LCNF_Closure_run___redArg(x_463, x_461, x_462, x_5, x_6, x_7, x_8, x_460);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_465, 1);
lean_inc(x_466);
lean_dec(x_465);
x_467 = lean_ctor_get(x_464, 1);
lean_inc(x_467);
lean_dec_ref(x_464);
x_468 = lean_ctor_get(x_466, 0);
lean_inc(x_468);
lean_dec(x_466);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_469 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(x_468, x_445, x_2, x_3, x_5, x_6, x_7, x_8, x_467);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
lean_dec_ref(x_469);
x_472 = lean_ctor_get(x_470, 0);
lean_inc(x_472);
x_473 = l_Lean_FVarIdSet_insert(x_4, x_472);
x_474 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_443, x_2, x_3, x_473, x_5, x_6, x_7, x_8, x_471);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_474, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_477 = x_474;
} else {
 lean_dec_ref(x_474);
 x_477 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_478 = lean_alloc_ctor(0, 2, 0);
} else {
 x_478 = x_459;
 lean_ctor_set_tag(x_478, 0);
}
lean_ctor_set(x_478, 0, x_470);
lean_ctor_set(x_478, 1, x_475);
if (lean_is_scalar(x_477)) {
 x_479 = lean_alloc_ctor(0, 2, 0);
} else {
 x_479 = x_477;
}
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_476);
return x_479;
}
else
{
lean_dec(x_470);
lean_dec(x_459);
return x_474;
}
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
lean_dec(x_459);
lean_dec_ref(x_443);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_480 = lean_ctor_get(x_469, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_469, 1);
lean_inc(x_481);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_482 = x_469;
} else {
 lean_dec_ref(x_469);
 x_482 = lean_box(0);
}
if (lean_is_scalar(x_482)) {
 x_483 = lean_alloc_ctor(1, 2, 0);
} else {
 x_483 = x_482;
}
lean_ctor_set(x_483, 0, x_480);
lean_ctor_set(x_483, 1, x_481);
return x_483;
}
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
lean_dec(x_459);
lean_dec(x_445);
lean_dec_ref(x_443);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_484 = lean_ctor_get(x_464, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_464, 1);
lean_inc(x_485);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 x_486 = x_464;
} else {
 lean_dec_ref(x_464);
 x_486 = lean_box(0);
}
if (lean_is_scalar(x_486)) {
 x_487 = lean_alloc_ctor(1, 2, 0);
} else {
 x_487 = x_486;
}
lean_ctor_set(x_487, 0, x_484);
lean_ctor_set(x_487, 1, x_485);
return x_487;
}
}
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
lean_dec_ref(x_443);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_488 = lean_ctor_get(x_444, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_444, 1);
lean_inc(x_489);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_490 = x_444;
} else {
 lean_dec_ref(x_444);
 x_490 = lean_box(0);
}
if (lean_is_scalar(x_490)) {
 x_491 = lean_alloc_ctor(1, 2, 0);
} else {
 x_491 = x_490;
}
lean_ctor_set(x_491, 0, x_488);
lean_ctor_set(x_491, 1, x_489);
return x_491;
}
}
case 2:
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec_ref(x_431);
x_492 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_492);
x_493 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_493);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_494 = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(x_492, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec_ref(x_494);
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
x_498 = l_Lean_FVarIdSet_insert(x_4, x_497);
x_499 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_493, x_2, x_3, x_498, x_5, x_6, x_7, x_8, x_496);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_499, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 x_502 = x_499;
} else {
 lean_dec_ref(x_499);
 x_502 = lean_box(0);
}
x_503 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_1, x_495, x_500);
lean_dec_ref(x_1);
if (lean_is_scalar(x_502)) {
 x_504 = lean_alloc_ctor(0, 2, 0);
} else {
 x_504 = x_502;
}
lean_ctor_set(x_504, 0, x_503);
lean_ctor_set(x_504, 1, x_501);
return x_504;
}
else
{
lean_dec(x_495);
lean_dec_ref(x_1);
return x_499;
}
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec_ref(x_493);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_505 = lean_ctor_get(x_494, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_494, 1);
lean_inc(x_506);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_507 = x_494;
} else {
 lean_dec_ref(x_494);
 x_507 = lean_box(0);
}
if (lean_is_scalar(x_507)) {
 x_508 = lean_alloc_ctor(1, 2, 0);
} else {
 x_508 = x_507;
}
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_506);
return x_508;
}
}
case 4:
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_509 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_509);
x_510 = lean_ctor_get(x_509, 3);
lean_inc_ref(x_510);
lean_dec_ref(x_509);
x_511 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__2), 9, 0);
x_512 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_431, x_510, x_511);
x_513 = lean_apply_8(x_512, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 x_516 = x_513;
} else {
 lean_dec_ref(x_513);
 x_516 = lean_box(0);
}
x_517 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp(x_1, x_514);
if (lean_is_scalar(x_516)) {
 x_518 = lean_alloc_ctor(0, 2, 0);
} else {
 x_518 = x_516;
}
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_515);
return x_518;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_dec_ref(x_1);
x_519 = lean_ctor_get(x_513, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_513, 1);
lean_inc(x_520);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 x_521 = x_513;
} else {
 lean_dec_ref(x_513);
 x_521 = lean_box(0);
}
if (lean_is_scalar(x_521)) {
 x_522 = lean_alloc_ctor(1, 2, 0);
} else {
 x_522 = x_521;
}
lean_ctor_set(x_522, 0, x_519);
lean_ctor_set(x_522, 1, x_520);
return x_522;
}
}
default: 
{
lean_object* x_523; 
lean_dec_ref(x_431);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_523 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_523, 0, x_1);
lean_ctor_set(x_523, 1, x_9);
return x_523;
}
}
}
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_524 = lean_ctor_get(x_10, 0);
lean_inc(x_524);
lean_dec(x_10);
x_525 = lean_ctor_get(x_524, 0);
lean_inc_ref(x_525);
x_526 = lean_ctor_get(x_524, 2);
lean_inc_ref(x_526);
x_527 = lean_ctor_get(x_524, 3);
lean_inc_ref(x_527);
x_528 = lean_ctor_get(x_524, 4);
lean_inc_ref(x_528);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 lean_ctor_release(x_524, 2);
 lean_ctor_release(x_524, 3);
 lean_ctor_release(x_524, 4);
 x_529 = x_524;
} else {
 lean_dec_ref(x_524);
 x_529 = lean_box(0);
}
x_530 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__2;
x_531 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__3;
lean_inc_ref(x_525);
x_532 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_532, 0, x_525);
x_533 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_533, 0, x_525);
x_534 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_534, 0, x_532);
lean_ctor_set(x_534, 1, x_533);
x_535 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_535, 0, x_528);
x_536 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_536, 0, x_527);
x_537 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_537, 0, x_526);
if (lean_is_scalar(x_529)) {
 x_538 = lean_alloc_ctor(0, 5, 0);
} else {
 x_538 = x_529;
}
lean_ctor_set(x_538, 0, x_534);
lean_ctor_set(x_538, 1, x_530);
lean_ctor_set(x_538, 2, x_537);
lean_ctor_set(x_538, 3, x_536);
lean_ctor_set(x_538, 4, x_535);
x_539 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_539, 0, x_538);
lean_ctor_set(x_539, 1, x_531);
x_540 = l_ReaderT_instMonad___redArg(x_539);
x_541 = lean_ctor_get(x_540, 0);
lean_inc_ref(x_541);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 lean_ctor_release(x_540, 1);
 x_542 = x_540;
} else {
 lean_dec_ref(x_540);
 x_542 = lean_box(0);
}
x_543 = lean_ctor_get(x_541, 0);
lean_inc_ref(x_543);
x_544 = lean_ctor_get(x_541, 2);
lean_inc_ref(x_544);
x_545 = lean_ctor_get(x_541, 3);
lean_inc_ref(x_545);
x_546 = lean_ctor_get(x_541, 4);
lean_inc_ref(x_546);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 lean_ctor_release(x_541, 2);
 lean_ctor_release(x_541, 3);
 lean_ctor_release(x_541, 4);
 x_547 = x_541;
} else {
 lean_dec_ref(x_541);
 x_547 = lean_box(0);
}
x_548 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__4;
x_549 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__5;
lean_inc_ref(x_543);
x_550 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_550, 0, x_543);
x_551 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_551, 0, x_543);
x_552 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
x_553 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_553, 0, x_546);
x_554 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_554, 0, x_545);
x_555 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_555, 0, x_544);
if (lean_is_scalar(x_547)) {
 x_556 = lean_alloc_ctor(0, 5, 0);
} else {
 x_556 = x_547;
}
lean_ctor_set(x_556, 0, x_552);
lean_ctor_set(x_556, 1, x_548);
lean_ctor_set(x_556, 2, x_555);
lean_ctor_set(x_556, 3, x_554);
lean_ctor_set(x_556, 4, x_553);
if (lean_is_scalar(x_542)) {
 x_557 = lean_alloc_ctor(0, 2, 0);
} else {
 x_557 = x_542;
}
lean_ctor_set(x_557, 0, x_556);
lean_ctor_set(x_557, 1, x_549);
x_558 = l_ReaderT_instMonad___redArg(x_557);
x_559 = l_ReaderT_instMonad___redArg(x_558);
x_560 = l_ReaderT_instMonad___redArg(x_559);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_dec_ref(x_560);
x_561 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_561);
x_562 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_562);
x_563 = lean_ctor_get(x_561, 0);
lean_inc(x_563);
x_564 = l_Lean_FVarIdSet_insert(x_4, x_563);
x_565 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_562, x_2, x_3, x_564, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_565) == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_566 = lean_ctor_get(x_565, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_565, 1);
lean_inc(x_567);
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 lean_ctor_release(x_565, 1);
 x_568 = x_565;
} else {
 lean_dec_ref(x_565);
 x_568 = lean_box(0);
}
x_569 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_1, x_561, x_566);
lean_dec_ref(x_1);
if (lean_is_scalar(x_568)) {
 x_570 = lean_alloc_ctor(0, 2, 0);
} else {
 x_570 = x_568;
}
lean_ctor_set(x_570, 0, x_569);
lean_ctor_set(x_570, 1, x_567);
return x_570;
}
else
{
lean_dec_ref(x_561);
lean_dec_ref(x_1);
return x_565;
}
}
case 1:
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; 
lean_dec_ref(x_560);
x_571 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_571);
x_572 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_572);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_573 = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(x_571, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; uint8_t x_578; 
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
lean_dec_ref(x_573);
x_576 = l_Lean_Compiler_LCNF_LambdaLifting_shouldLift___redArg(x_574, x_2, x_5, x_6, x_7, x_8, x_575);
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_unbox(x_577);
if (x_578 == 0)
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
lean_dec(x_577);
x_579 = lean_ctor_get(x_576, 1);
lean_inc(x_579);
lean_dec_ref(x_576);
x_580 = lean_ctor_get(x_574, 0);
lean_inc(x_580);
x_581 = l_Lean_FVarIdSet_insert(x_4, x_580);
x_582 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_572, x_2, x_3, x_581, x_5, x_6, x_7, x_8, x_579);
if (lean_obj_tag(x_582) == 0)
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_585 = x_582;
} else {
 lean_dec_ref(x_582);
 x_585 = lean_box(0);
}
x_586 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_1, x_574, x_583);
lean_dec_ref(x_1);
if (lean_is_scalar(x_585)) {
 x_587 = lean_alloc_ctor(0, 2, 0);
} else {
 x_587 = x_585;
}
lean_ctor_set(x_587, 0, x_586);
lean_ctor_set(x_587, 1, x_584);
return x_587;
}
else
{
lean_dec(x_574);
lean_dec_ref(x_1);
return x_582;
}
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_588 = x_1;
} else {
 lean_dec_ref(x_1);
 x_588 = lean_box(0);
}
x_589 = lean_ctor_get(x_576, 1);
lean_inc(x_589);
lean_dec_ref(x_576);
lean_inc(x_4);
x_590 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed), 2, 1);
lean_closure_set(x_590, 0, x_4);
x_591 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed), 2, 1);
lean_closure_set(x_591, 0, x_577);
lean_inc(x_574);
x_592 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectFunDecl), 8, 1);
lean_closure_set(x_592, 0, x_574);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_593 = l_Lean_Compiler_LCNF_Closure_run___redArg(x_592, x_590, x_591, x_5, x_6, x_7, x_8, x_589);
if (lean_obj_tag(x_593) == 0)
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_594 = lean_ctor_get(x_593, 0);
lean_inc(x_594);
x_595 = lean_ctor_get(x_594, 1);
lean_inc(x_595);
lean_dec(x_594);
x_596 = lean_ctor_get(x_593, 1);
lean_inc(x_596);
lean_dec_ref(x_593);
x_597 = lean_ctor_get(x_595, 0);
lean_inc(x_597);
lean_dec(x_595);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_598 = l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg(x_597, x_574, x_2, x_3, x_5, x_6, x_7, x_8, x_596);
if (lean_obj_tag(x_598) == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_598, 1);
lean_inc(x_600);
lean_dec_ref(x_598);
x_601 = lean_ctor_get(x_599, 0);
lean_inc(x_601);
x_602 = l_Lean_FVarIdSet_insert(x_4, x_601);
x_603 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_572, x_2, x_3, x_602, x_5, x_6, x_7, x_8, x_600);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_603, 1);
lean_inc(x_605);
if (lean_is_exclusive(x_603)) {
 lean_ctor_release(x_603, 0);
 lean_ctor_release(x_603, 1);
 x_606 = x_603;
} else {
 lean_dec_ref(x_603);
 x_606 = lean_box(0);
}
if (lean_is_scalar(x_588)) {
 x_607 = lean_alloc_ctor(0, 2, 0);
} else {
 x_607 = x_588;
 lean_ctor_set_tag(x_607, 0);
}
lean_ctor_set(x_607, 0, x_599);
lean_ctor_set(x_607, 1, x_604);
if (lean_is_scalar(x_606)) {
 x_608 = lean_alloc_ctor(0, 2, 0);
} else {
 x_608 = x_606;
}
lean_ctor_set(x_608, 0, x_607);
lean_ctor_set(x_608, 1, x_605);
return x_608;
}
else
{
lean_dec(x_599);
lean_dec(x_588);
return x_603;
}
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_dec(x_588);
lean_dec_ref(x_572);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_609 = lean_ctor_get(x_598, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_598, 1);
lean_inc(x_610);
if (lean_is_exclusive(x_598)) {
 lean_ctor_release(x_598, 0);
 lean_ctor_release(x_598, 1);
 x_611 = x_598;
} else {
 lean_dec_ref(x_598);
 x_611 = lean_box(0);
}
if (lean_is_scalar(x_611)) {
 x_612 = lean_alloc_ctor(1, 2, 0);
} else {
 x_612 = x_611;
}
lean_ctor_set(x_612, 0, x_609);
lean_ctor_set(x_612, 1, x_610);
return x_612;
}
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
lean_dec(x_588);
lean_dec(x_574);
lean_dec_ref(x_572);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_613 = lean_ctor_get(x_593, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_593, 1);
lean_inc(x_614);
if (lean_is_exclusive(x_593)) {
 lean_ctor_release(x_593, 0);
 lean_ctor_release(x_593, 1);
 x_615 = x_593;
} else {
 lean_dec_ref(x_593);
 x_615 = lean_box(0);
}
if (lean_is_scalar(x_615)) {
 x_616 = lean_alloc_ctor(1, 2, 0);
} else {
 x_616 = x_615;
}
lean_ctor_set(x_616, 0, x_613);
lean_ctor_set(x_616, 1, x_614);
return x_616;
}
}
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
lean_dec_ref(x_572);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_617 = lean_ctor_get(x_573, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_573, 1);
lean_inc(x_618);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 lean_ctor_release(x_573, 1);
 x_619 = x_573;
} else {
 lean_dec_ref(x_573);
 x_619 = lean_box(0);
}
if (lean_is_scalar(x_619)) {
 x_620 = lean_alloc_ctor(1, 2, 0);
} else {
 x_620 = x_619;
}
lean_ctor_set(x_620, 0, x_617);
lean_ctor_set(x_620, 1, x_618);
return x_620;
}
}
case 2:
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; 
lean_dec_ref(x_560);
x_621 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_621);
x_622 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_622);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_623 = l_Lean_Compiler_LCNF_LambdaLifting_visitFunDecl(x_621, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_623) == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_624 = lean_ctor_get(x_623, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_623, 1);
lean_inc(x_625);
lean_dec_ref(x_623);
x_626 = lean_ctor_get(x_624, 0);
lean_inc(x_626);
x_627 = l_Lean_FVarIdSet_insert(x_4, x_626);
x_628 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode(x_622, x_2, x_3, x_627, x_5, x_6, x_7, x_8, x_625);
if (lean_obj_tag(x_628) == 0)
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_629 = lean_ctor_get(x_628, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_628, 1);
lean_inc(x_630);
if (lean_is_exclusive(x_628)) {
 lean_ctor_release(x_628, 0);
 lean_ctor_release(x_628, 1);
 x_631 = x_628;
} else {
 lean_dec_ref(x_628);
 x_631 = lean_box(0);
}
x_632 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_1, x_624, x_629);
lean_dec_ref(x_1);
if (lean_is_scalar(x_631)) {
 x_633 = lean_alloc_ctor(0, 2, 0);
} else {
 x_633 = x_631;
}
lean_ctor_set(x_633, 0, x_632);
lean_ctor_set(x_633, 1, x_630);
return x_633;
}
else
{
lean_dec(x_624);
lean_dec_ref(x_1);
return x_628;
}
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; 
lean_dec_ref(x_622);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_634 = lean_ctor_get(x_623, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_623, 1);
lean_inc(x_635);
if (lean_is_exclusive(x_623)) {
 lean_ctor_release(x_623, 0);
 lean_ctor_release(x_623, 1);
 x_636 = x_623;
} else {
 lean_dec_ref(x_623);
 x_636 = lean_box(0);
}
if (lean_is_scalar(x_636)) {
 x_637 = lean_alloc_ctor(1, 2, 0);
} else {
 x_637 = x_636;
}
lean_ctor_set(x_637, 0, x_634);
lean_ctor_set(x_637, 1, x_635);
return x_637;
}
}
case 4:
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_638 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_638);
x_639 = lean_ctor_get(x_638, 3);
lean_inc_ref(x_639);
lean_dec_ref(x_638);
x_640 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__2), 9, 0);
x_641 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_560, x_639, x_640);
x_642 = lean_apply_8(x_641, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_642) == 0)
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_643 = lean_ctor_get(x_642, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_642, 1);
lean_inc(x_644);
if (lean_is_exclusive(x_642)) {
 lean_ctor_release(x_642, 0);
 lean_ctor_release(x_642, 1);
 x_645 = x_642;
} else {
 lean_dec_ref(x_642);
 x_645 = lean_box(0);
}
x_646 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp(x_1, x_643);
if (lean_is_scalar(x_645)) {
 x_647 = lean_alloc_ctor(0, 2, 0);
} else {
 x_647 = x_645;
}
lean_ctor_set(x_647, 0, x_646);
lean_ctor_set(x_647, 1, x_644);
return x_647;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
lean_dec_ref(x_1);
x_648 = lean_ctor_get(x_642, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_642, 1);
lean_inc(x_649);
if (lean_is_exclusive(x_642)) {
 lean_ctor_release(x_642, 0);
 lean_ctor_release(x_642, 1);
 x_650 = x_642;
} else {
 lean_dec_ref(x_642);
 x_650 = lean_box(0);
}
if (lean_is_scalar(x_650)) {
 x_651 = lean_alloc_ctor(1, 2, 0);
} else {
 x_651 = x_650;
}
lean_ctor_set(x_651, 0, x_648);
lean_ctor_set(x_651, 1, x_649);
return x_651;
}
}
default: 
{
lean_object* x_652; 
lean_dec_ref(x_560);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_652 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_652, 0, x_1);
lean_ctor_set(x_652, 1, x_9);
return x_652;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_LambdaLifting_visitCode_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_LambdaLifting_visitCode___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_LambdaLifting_main_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_apply_9(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_2, 0, x_15);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_free_object(x_2);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_apply_9(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_32 = x_24;
} else {
 lean_dec_ref(x_24);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_10);
return x_34;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LambdaLifting_main___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LambdaLifting_visitCode), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LambdaLifting_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_14);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_17 = lean_ctor_get(x_1, 5);
lean_inc(x_17);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 x_18 = x_1;
} else {
 lean_dec_ref(x_1);
 x_18 = lean_box(0);
}
x_32 = l_Lean_Compiler_LCNF_LambdaLifting_main___closed__0;
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_array_get_size(x_13);
x_35 = lean_nat_dec_lt(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_34);
x_36 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_LambdaLifting_main_spec__0(x_32, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_19 = x_36;
goto block_31;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_34, x_34);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_34);
x_38 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_LambdaLifting_main_spec__0(x_32, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_19 = x_38;
goto block_31;
}
else
{
size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; 
x_39 = 0;
x_40 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_41 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LambdaLifting_visitFunDecl_spec__0(x_13, x_39, x_40, x_4);
x_42 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_LambdaLifting_main_spec__0(x_32, x_14, x_2, x_3, x_41, x_5, x_6, x_7, x_8, x_9);
x_19 = x_42;
goto block_31;
}
}
block_31:
{
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
if (lean_is_scalar(x_18)) {
 x_22 = lean_alloc_ctor(0, 6, 2);
} else {
 x_22 = x_18;
}
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_12);
lean_ctor_set(x_22, 3, x_13);
lean_ctor_set(x_22, 4, x_21);
lean_ctor_set(x_22, 5, x_17);
lean_ctor_set_uint8(x_22, sizeof(void*)*6, x_15);
lean_ctor_set_uint8(x_22, sizeof(void*)*6 + 1, x_16);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
if (lean_is_scalar(x_18)) {
 x_25 = lean_alloc_ctor(0, 6, 2);
} else {
 x_25 = x_18;
}
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_11);
lean_ctor_set(x_25, 2, x_12);
lean_ctor_set(x_25, 3, x_13);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set(x_25, 5, x_17);
lean_ctor_set_uint8(x_25, sizeof(void*)*6, x_15);
lean_ctor_set_uint8(x_25, sizeof(void*)*6 + 1, x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1;
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Lean_instFVarIdSetEmptyCollection;
lean_inc_ref(x_1);
x_16 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_16, 2, x_5);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_2);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 1, x_4);
lean_inc(x_13);
x_17 = l_Lean_Compiler_LCNF_LambdaLifting_main(x_1, x_16, x_13, x_15, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_st_ref_get(x_13, x_19);
lean_dec(x_13);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_23);
lean_dec(x_22);
x_24 = lean_array_push(x_23, x_18);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_27);
lean_dec(x_25);
x_28 = lean_array_push(x_27, x_18);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_lambdaLifting___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_4);
x_13 = l_Lean_Compiler_LCNF_Decl_lambdaLifting(x_1, x_11, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_lam", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_lambdaLifting_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_eq(x_4, x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_array_uget(x_3, x_4);
x_20 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__1;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_21 = l_Lean_Compiler_LCNF_Decl_lambdaLifting(x_19, x_1, x_20, x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = l_Array_append___redArg(x_6, x_22);
lean_dec(x_22);
x_12 = x_24;
x_13 = x_23;
goto block_17;
}
else
{
lean_dec_ref(x_6);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec_ref(x_21);
x_12 = x_25;
x_13 = x_26;
goto block_17;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
return x_21;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_11);
return x_27;
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
x_6 = x_12;
x_11 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lambdaLifting___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_mk_empty_array_with_capacity(x_1);
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_10, x_10);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_17 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_lambdaLifting_spec__0(x_2, x_1, x_3, x_15, x_16, x_9, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_lambdaLifting___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lambdaLifting", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_lambdaLifting___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_lambdaLifting___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_lambdaLifting() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 1;
x_3 = 0;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_lambdaLifting___lam__0___boxed), 8, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
x_6 = l_Lean_Compiler_LCNF_lambdaLifting___closed__1;
x_7 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*3, x_2);
lean_ctor_set_uint8(x_7, sizeof(void*)*3 + 1, x_2);
lean_ctor_set_uint8(x_7, sizeof(void*)*3 + 2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_lambdaLifting_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_lambdaLifting_spec__0(x_12, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lambdaLifting___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Compiler_LCNF_lambdaLifting___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
return x_10;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_elam", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_eagerLambdaLifting_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_eq(x_4, x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_35; 
x_19 = lean_array_uget(x_3, x_4);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = l_Lean_Meta_isInstance___redArg(x_20, x_10, x_11);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_35 = l_Lean_Compiler_LCNF_Decl_inlineAttr(x_19);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = lean_unbox(x_22);
lean_dec(x_22);
x_24 = x_36;
goto block_34;
}
else
{
lean_dec(x_22);
x_24 = x_35;
goto block_34;
}
block_34:
{
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_25 = 1;
x_26 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___closed__1;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_27 = l_Lean_Compiler_LCNF_Decl_lambdaLifting(x_19, x_25, x_26, x_1, x_2, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = l_Array_append___redArg(x_6, x_28);
lean_dec(x_28);
x_12 = x_30;
x_13 = x_29;
goto block_17;
}
else
{
lean_dec_ref(x_6);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec_ref(x_27);
x_12 = x_31;
x_13 = x_32;
goto block_17;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
return x_27;
}
}
}
else
{
lean_object* x_33; 
x_33 = lean_array_push(x_6, x_19);
x_12 = x_33;
x_13 = x_23;
goto block_17;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_6);
lean_ctor_set(x_37, 1, x_11);
return x_37;
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
x_6 = x_12;
x_11 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_mk_empty_array_with_capacity(x_1);
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_10, x_10);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_17 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_eagerLambdaLifting_spec__0(x_2, x_1, x_3, x_15, x_16, x_9, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eagerLambdaLifting", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_eagerLambdaLifting() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = 0;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0___boxed), 8, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
x_6 = l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__1;
x_7 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*3, x_2);
lean_ctor_set_uint8(x_7, sizeof(void*)*3 + 1, x_2);
lean_ctor_set_uint8(x_7, sizeof(void*)*3 + 2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_eagerLambdaLifting_spec__0(x_12, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Compiler_LCNF_eagerLambdaLifting___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__0;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LCNF", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LambdaLifting", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1700u);
x_2 = l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__19____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_lambdaLifting___closed__0;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_Compiler_LCNF_initFn___closed__19____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_;
x_8 = l_Lean_registerTraceClass(x_7, x_3, x_4, x_6);
return x_8;
}
else
{
return x_5;
}
}
}
lean_object* initialize_Lean_Meta_Instances(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_InlineAttrs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Closure(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_MonadScope(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Level(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_AuxDeclCache(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_LambdaLifting(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Instances(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InlineAttrs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Closure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_MonadScope(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Level(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_AuxDeclCache(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0 = _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__0);
l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1 = _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__1);
l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__2 = _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__2);
l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__3 = _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__3);
l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__4 = _init_l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_LambdaLifting_mkAuxDecl___redArg___closed__4);
l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__0 = _init_l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__0);
l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__1 = _init_l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__1);
l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__2 = _init_l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__2);
l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__3 = _init_l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__3);
l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__4 = _init_l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__4);
l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__5 = _init_l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_LambdaLifting_visitCode___closed__5);
l_Lean_Compiler_LCNF_LambdaLifting_main___closed__0 = _init_l_Lean_Compiler_LCNF_LambdaLifting_main___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_LambdaLifting_main___closed__0);
l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0 = _init_l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__0);
l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1 = _init_l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_lambdaLifting___closed__1);
l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__0 = _init_l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__0();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__0);
l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__1 = _init_l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_lambdaLifting_spec__0___closed__1);
l_Lean_Compiler_LCNF_lambdaLifting___closed__0 = _init_l_Lean_Compiler_LCNF_lambdaLifting___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_lambdaLifting___closed__0);
l_Lean_Compiler_LCNF_lambdaLifting___closed__1 = _init_l_Lean_Compiler_LCNF_lambdaLifting___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_lambdaLifting___closed__1);
l_Lean_Compiler_LCNF_lambdaLifting = _init_l_Lean_Compiler_LCNF_lambdaLifting();
lean_mark_persistent(l_Lean_Compiler_LCNF_lambdaLifting);
l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___closed__0 = _init_l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___closed__0();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___closed__0);
l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___closed__1 = _init_l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_eagerLambdaLifting_spec__0___closed__1);
l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__0 = _init_l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__0);
l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__1 = _init_l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_eagerLambdaLifting___closed__1);
l_Lean_Compiler_LCNF_eagerLambdaLifting = _init_l_Lean_Compiler_LCNF_eagerLambdaLifting();
lean_mark_persistent(l_Lean_Compiler_LCNF_eagerLambdaLifting);
l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
l_Lean_Compiler_LCNF_initFn___closed__19____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_ = _init_l_Lean_Compiler_LCNF_initFn___closed__19____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__19____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_LambdaLifting___hyg_1700_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
