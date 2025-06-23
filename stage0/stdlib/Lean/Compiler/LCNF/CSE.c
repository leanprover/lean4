// Lean compiler output
// Module: Lean.Compiler.LCNF.CSE
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.ToExpr Lean.Compiler.LCNF.PassManager
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_cse_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__7;
lean_object* l_StateRefT_x27_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___redArg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__13;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Code_cse_go_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__16;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0;
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__12;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__3;
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
static lean_object* l_Lean_Compiler_LCNF_cse___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDecl_toExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_goFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Code_cse_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Code_cse_go_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__6;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftBaseIOEIO___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Code_cse_go___closed__0;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__10;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Code_cse_go_spec__2(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__7;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__0;
static lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__0;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__1;
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_goFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1129_(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5;
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__17;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
static lean_object* l_Lean_Compiler_LCNF_cse___closed__0;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__15;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__4;
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__14;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__11;
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__0;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_liftIOCore___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadLiftBaseIOEIO___lam__0), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_instMonadLiftSTRealWorldBaseIO___lam__0), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadLiftT___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__10;
x_2 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__11;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__9;
x_2 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__12;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__8;
x_2 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__13;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__7;
x_2 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__14;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__6;
x_2 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__15;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__16;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_get), 5, 4);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, lean_box(0));
lean_closure_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1;
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
x_9 = lean_ctor_get(x_3, 4);
x_10 = lean_ctor_get(x_3, 1);
lean_dec(x_10);
x_11 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2;
x_12 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__3;
lean_inc(x_6);
x_13 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_13, 0, x_6);
x_14 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_14, 0, x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_16, 0, x_9);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_17, 0, x_8);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_18, 0, x_7);
lean_ctor_set(x_3, 4, x_16);
lean_ctor_set(x_3, 3, x_17);
lean_ctor_set(x_3, 2, x_18);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_15);
lean_ctor_set(x_1, 1, x_12);
x_19 = l_ReaderT_instMonad___redArg(x_1);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 2);
x_26 = lean_ctor_get(x_21, 3);
x_27 = lean_ctor_get(x_21, 4);
x_28 = lean_ctor_get(x_21, 1);
lean_dec(x_28);
x_29 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lam__0___boxed), 7, 0);
x_30 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4;
x_31 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5;
lean_inc(x_24);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_32, 0, x_24);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_33, 0, x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_35, 0, x_27);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_36, 0, x_26);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_37, 0, x_25);
lean_ctor_set(x_21, 4, x_35);
lean_ctor_set(x_21, 3, x_36);
lean_ctor_set(x_21, 2, x_37);
lean_ctor_set(x_21, 1, x_30);
lean_ctor_set(x_21, 0, x_34);
lean_ctor_set(x_19, 1, x_31);
x_38 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__17;
x_39 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_39, 0, lean_box(0));
lean_closure_set(x_39, 1, lean_box(0));
lean_closure_set(x_39, 2, x_19);
lean_closure_set(x_39, 3, lean_box(0));
lean_closure_set(x_39, 4, lean_box(0));
lean_closure_set(x_39, 5, x_38);
lean_closure_set(x_39, 6, x_29);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get(x_21, 2);
x_42 = lean_ctor_get(x_21, 3);
x_43 = lean_ctor_get(x_21, 4);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_21);
x_44 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lam__0___boxed), 7, 0);
x_45 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4;
x_46 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5;
lean_inc(x_40);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_47, 0, x_40);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_48, 0, x_40);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_50, 0, x_43);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_51, 0, x_42);
x_52 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_52, 0, x_41);
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_45);
lean_ctor_set(x_53, 2, x_52);
lean_ctor_set(x_53, 3, x_51);
lean_ctor_set(x_53, 4, x_50);
lean_ctor_set(x_19, 1, x_46);
lean_ctor_set(x_19, 0, x_53);
x_54 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__17;
x_55 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_55, 0, lean_box(0));
lean_closure_set(x_55, 1, lean_box(0));
lean_closure_set(x_55, 2, x_19);
lean_closure_set(x_55, 3, lean_box(0));
lean_closure_set(x_55, 4, lean_box(0));
lean_closure_set(x_55, 5, x_54);
lean_closure_set(x_55, 6, x_44);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_56 = lean_ctor_get(x_19, 0);
lean_inc(x_56);
lean_dec(x_19);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 4);
lean_inc(x_60);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 lean_ctor_release(x_56, 4);
 x_61 = x_56;
} else {
 lean_dec_ref(x_56);
 x_61 = lean_box(0);
}
x_62 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lam__0___boxed), 7, 0);
x_63 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4;
x_64 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5;
lean_inc(x_57);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_65, 0, x_57);
x_66 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_66, 0, x_57);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_68, 0, x_60);
x_69 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_69, 0, x_59);
x_70 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_70, 0, x_58);
if (lean_is_scalar(x_61)) {
 x_71 = lean_alloc_ctor(0, 5, 0);
} else {
 x_71 = x_61;
}
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_63);
lean_ctor_set(x_71, 2, x_70);
lean_ctor_set(x_71, 3, x_69);
lean_ctor_set(x_71, 4, x_68);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_64);
x_73 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__17;
x_74 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_74, 0, lean_box(0));
lean_closure_set(x_74, 1, lean_box(0));
lean_closure_set(x_74, 2, x_72);
lean_closure_set(x_74, 3, lean_box(0));
lean_closure_set(x_74, 4, lean_box(0));
lean_closure_set(x_74, 5, x_73);
lean_closure_set(x_74, 6, x_62);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_75 = lean_ctor_get(x_3, 0);
x_76 = lean_ctor_get(x_3, 2);
x_77 = lean_ctor_get(x_3, 3);
x_78 = lean_ctor_get(x_3, 4);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_3);
x_79 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2;
x_80 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__3;
lean_inc(x_75);
x_81 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_81, 0, x_75);
x_82 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_82, 0, x_75);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_84, 0, x_78);
x_85 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_85, 0, x_77);
x_86 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_86, 0, x_76);
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_79);
lean_ctor_set(x_87, 2, x_86);
lean_ctor_set(x_87, 3, x_85);
lean_ctor_set(x_87, 4, x_84);
lean_ctor_set(x_1, 1, x_80);
lean_ctor_set(x_1, 0, x_87);
x_88 = l_ReaderT_instMonad___redArg(x_1);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_89, 3);
lean_inc(x_93);
x_94 = lean_ctor_get(x_89, 4);
lean_inc(x_94);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 lean_ctor_release(x_89, 4);
 x_95 = x_89;
} else {
 lean_dec_ref(x_89);
 x_95 = lean_box(0);
}
x_96 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lam__0___boxed), 7, 0);
x_97 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4;
x_98 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5;
lean_inc(x_91);
x_99 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_99, 0, x_91);
x_100 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_100, 0, x_91);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_102, 0, x_94);
x_103 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_103, 0, x_93);
x_104 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_104, 0, x_92);
if (lean_is_scalar(x_95)) {
 x_105 = lean_alloc_ctor(0, 5, 0);
} else {
 x_105 = x_95;
}
lean_ctor_set(x_105, 0, x_101);
lean_ctor_set(x_105, 1, x_97);
lean_ctor_set(x_105, 2, x_104);
lean_ctor_set(x_105, 3, x_103);
lean_ctor_set(x_105, 4, x_102);
if (lean_is_scalar(x_90)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_90;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_98);
x_107 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__17;
x_108 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_108, 0, lean_box(0));
lean_closure_set(x_108, 1, lean_box(0));
lean_closure_set(x_108, 2, x_106);
lean_closure_set(x_108, 3, lean_box(0));
lean_closure_set(x_108, 4, lean_box(0));
lean_closure_set(x_108, 5, x_107);
lean_closure_set(x_108, 6, x_96);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_109 = lean_ctor_get(x_1, 0);
lean_inc(x_109);
lean_dec(x_1);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_109, 4);
lean_inc(x_113);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 lean_ctor_release(x_109, 2);
 lean_ctor_release(x_109, 3);
 lean_ctor_release(x_109, 4);
 x_114 = x_109;
} else {
 lean_dec_ref(x_109);
 x_114 = lean_box(0);
}
x_115 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2;
x_116 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__3;
lean_inc(x_110);
x_117 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_117, 0, x_110);
x_118 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_118, 0, x_110);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_120, 0, x_113);
x_121 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_121, 0, x_112);
x_122 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_122, 0, x_111);
if (lean_is_scalar(x_114)) {
 x_123 = lean_alloc_ctor(0, 5, 0);
} else {
 x_123 = x_114;
}
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_115);
lean_ctor_set(x_123, 2, x_122);
lean_ctor_set(x_123, 3, x_121);
lean_ctor_set(x_123, 4, x_120);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_116);
x_125 = l_ReaderT_instMonad___redArg(x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_126, 3);
lean_inc(x_130);
x_131 = lean_ctor_get(x_126, 4);
lean_inc(x_131);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 lean_ctor_release(x_126, 2);
 lean_ctor_release(x_126, 3);
 lean_ctor_release(x_126, 4);
 x_132 = x_126;
} else {
 lean_dec_ref(x_126);
 x_132 = lean_box(0);
}
x_133 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lam__0___boxed), 7, 0);
x_134 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4;
x_135 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5;
lean_inc(x_128);
x_136 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_136, 0, x_128);
x_137 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_137, 0, x_128);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_139, 0, x_131);
x_140 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_140, 0, x_130);
x_141 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_141, 0, x_129);
if (lean_is_scalar(x_132)) {
 x_142 = lean_alloc_ctor(0, 5, 0);
} else {
 x_142 = x_132;
}
lean_ctor_set(x_142, 0, x_138);
lean_ctor_set(x_142, 1, x_134);
lean_ctor_set(x_142, 2, x_141);
lean_ctor_set(x_142, 3, x_140);
lean_ctor_set(x_142, 4, x_139);
if (lean_is_scalar(x_127)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_127;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_135);
x_144 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__17;
x_145 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_145, 0, lean_box(0));
lean_closure_set(x_145, 1, lean_box(0));
lean_closure_set(x_145, 2, x_143);
lean_closure_set(x_145, 3, lean_box(0));
lean_closure_set(x_145, 4, lean_box(0));
lean_closure_set(x_145, 5, x_144);
lean_closure_set(x_145, 6, x_133);
return x_145;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_apply_1(x_1, x_12);
lean_ctor_set(x_9, 1, x_13);
x_14 = lean_st_ref_set(x_2, x_9, x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = lean_apply_1(x_1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_st_ref_set(x_2, x_24, x_10);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM___lam__0___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_CSE_getSubst___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_CSE_getSubst(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_eqv___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_hash___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0;
x_11 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1;
x_12 = l_Lean_PersistentHashMap_insert___redArg(x_10, x_11, x_9, x_1, x_2);
lean_ctor_set(x_6, 0, x_12);
x_13 = lean_st_ref_set(x_3, x_6, x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_22 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0;
x_23 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1;
x_24 = l_Lean_PersistentHashMap_insert___redArg(x_22, x_23, x_20, x_1, x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
x_26 = lean_st_ref_set(x_3, x_25, x_7);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0;
x_15 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1;
x_16 = l_Lean_PersistentHashMap_insert___redArg(x_14, x_15, x_13, x_1, x_2);
lean_ctor_set(x_10, 0, x_16);
x_17 = lean_st_ref_set(x_3, x_10, x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0;
x_27 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1;
x_28 = l_Lean_PersistentHashMap_insert___redArg(x_26, x_27, x_24, x_1, x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
x_30 = lean_st_ref_set(x_3, x_29, x_11);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_CSE_addEntry(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_2);
x_10 = lean_st_ref_set(x_1, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_st_ref_set(x_1, x_18, x_7);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
x_22 = lean_box(0);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_st_ref_get(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_2);
x_12 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(x_2, x_11, x_15, x_14);
lean_dec(x_15);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_box(0);
x_24 = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(x_2, x_11, x_23, x_22);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_21);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_3);
x_13 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(x_3, x_12, x_16, x_15);
lean_dec(x_16);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_14);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_box(0);
x_25 = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(x_3, x_12, x_24, x_23);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 0, x_22);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_24; 
x_6 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_st_ref_take(x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_13 = x_9;
} else {
 lean_dec_ref(x_9);
 x_13 = lean_box(0);
}
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; lean_object* x_42; uint8_t x_43; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_2);
x_29 = lean_array_get_size(x_26);
x_30 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_27);
x_31 = 32;
x_32 = lean_uint64_shift_right(x_30, x_31);
x_33 = lean_uint64_xor(x_30, x_32);
x_34 = 16;
x_35 = lean_uint64_shift_right(x_33, x_34);
x_36 = lean_uint64_xor(x_33, x_35);
x_37 = lean_uint64_to_usize(x_36);
x_38 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_39 = 1;
x_40 = lean_usize_sub(x_38, x_39);
x_41 = lean_usize_land(x_37, x_40);
x_42 = lean_array_uget(x_26, x_41);
x_43 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_27, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_25, x_44);
lean_dec(x_25);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_27);
lean_ctor_set(x_46, 1, x_28);
lean_ctor_set(x_46, 2, x_42);
x_47 = lean_array_uset(x_26, x_41, x_46);
x_48 = lean_unsigned_to_nat(4u);
x_49 = lean_nat_mul(x_45, x_48);
x_50 = lean_unsigned_to_nat(3u);
x_51 = lean_nat_div(x_49, x_50);
lean_dec(x_49);
x_52 = lean_array_get_size(x_47);
x_53 = lean_nat_dec_le(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_47);
lean_ctor_set(x_12, 1, x_54);
lean_ctor_set(x_12, 0, x_45);
x_14 = x_12;
goto block_23;
}
else
{
lean_ctor_set(x_12, 1, x_47);
lean_ctor_set(x_12, 0, x_45);
x_14 = x_12;
goto block_23;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_box(0);
x_56 = lean_array_uset(x_26, x_41, x_55);
x_57 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_27, x_28, x_42);
x_58 = lean_array_uset(x_56, x_41, x_57);
lean_ctor_set(x_12, 1, x_58);
x_14 = x_12;
goto block_23;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; size_t x_71; size_t x_72; size_t x_73; size_t x_74; size_t x_75; lean_object* x_76; uint8_t x_77; 
x_59 = lean_ctor_get(x_12, 0);
x_60 = lean_ctor_get(x_12, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_12);
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
lean_dec(x_1);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_2);
x_63 = lean_array_get_size(x_60);
x_64 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_61);
x_65 = 32;
x_66 = lean_uint64_shift_right(x_64, x_65);
x_67 = lean_uint64_xor(x_64, x_66);
x_68 = 16;
x_69 = lean_uint64_shift_right(x_67, x_68);
x_70 = lean_uint64_xor(x_67, x_69);
x_71 = lean_uint64_to_usize(x_70);
x_72 = lean_usize_of_nat(x_63);
lean_dec(x_63);
x_73 = 1;
x_74 = lean_usize_sub(x_72, x_73);
x_75 = lean_usize_land(x_71, x_74);
x_76 = lean_array_uget(x_60, x_75);
x_77 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_61, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_nat_add(x_59, x_78);
lean_dec(x_59);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_61);
lean_ctor_set(x_80, 1, x_62);
lean_ctor_set(x_80, 2, x_76);
x_81 = lean_array_uset(x_60, x_75, x_80);
x_82 = lean_unsigned_to_nat(4u);
x_83 = lean_nat_mul(x_79, x_82);
x_84 = lean_unsigned_to_nat(3u);
x_85 = lean_nat_div(x_83, x_84);
lean_dec(x_83);
x_86 = lean_array_get_size(x_81);
x_87 = lean_nat_dec_le(x_85, x_86);
lean_dec(x_86);
lean_dec(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_81);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_79);
lean_ctor_set(x_89, 1, x_88);
x_14 = x_89;
goto block_23;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_79);
lean_ctor_set(x_90, 1, x_81);
x_14 = x_90;
goto block_23;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_box(0);
x_92 = lean_array_uset(x_60, x_75, x_91);
x_93 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_61, x_62, x_76);
x_94 = lean_array_uset(x_92, x_75, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_59);
lean_ctor_set(x_95, 1, x_94);
x_14 = x_95;
goto block_23;
}
}
block_23:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
if (lean_is_scalar(x_13)) {
 x_15 = lean_alloc_ctor(0, 2, 0);
} else {
 x_15 = x_13;
}
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_st_ref_set(x_3, x_15, x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(x_1, x_2, x_3, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_CSE_replaceLet(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_26; 
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
x_8 = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(x_1, x_7, x_4, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_15 = x_11;
} else {
 lean_dec_ref(x_11);
 x_15 = lean_box(0);
}
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; size_t x_39; size_t x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; uint8_t x_45; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_2);
x_31 = lean_array_get_size(x_28);
x_32 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_29);
x_33 = 32;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = 16;
x_37 = lean_uint64_shift_right(x_35, x_36);
x_38 = lean_uint64_xor(x_35, x_37);
x_39 = lean_uint64_to_usize(x_38);
x_40 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_41 = 1;
x_42 = lean_usize_sub(x_40, x_41);
x_43 = lean_usize_land(x_39, x_42);
x_44 = lean_array_uget(x_28, x_43);
x_45 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_29, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_27, x_46);
lean_dec(x_27);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_29);
lean_ctor_set(x_48, 1, x_30);
lean_ctor_set(x_48, 2, x_44);
x_49 = lean_array_uset(x_28, x_43, x_48);
x_50 = lean_unsigned_to_nat(4u);
x_51 = lean_nat_mul(x_47, x_50);
x_52 = lean_unsigned_to_nat(3u);
x_53 = lean_nat_div(x_51, x_52);
lean_dec(x_51);
x_54 = lean_array_get_size(x_49);
x_55 = lean_nat_dec_le(x_53, x_54);
lean_dec(x_54);
lean_dec(x_53);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_49);
lean_ctor_set(x_14, 1, x_56);
lean_ctor_set(x_14, 0, x_47);
x_16 = x_14;
goto block_25;
}
else
{
lean_ctor_set(x_14, 1, x_49);
lean_ctor_set(x_14, 0, x_47);
x_16 = x_14;
goto block_25;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_box(0);
x_58 = lean_array_uset(x_28, x_43, x_57);
x_59 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_29, x_30, x_44);
x_60 = lean_array_uset(x_58, x_43, x_59);
lean_ctor_set(x_14, 1, x_60);
x_16 = x_14;
goto block_25;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; size_t x_73; size_t x_74; size_t x_75; size_t x_76; size_t x_77; lean_object* x_78; uint8_t x_79; 
x_61 = lean_ctor_get(x_14, 0);
x_62 = lean_ctor_get(x_14, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_14);
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
lean_dec(x_1);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_2);
x_65 = lean_array_get_size(x_62);
x_66 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_63);
x_67 = 32;
x_68 = lean_uint64_shift_right(x_66, x_67);
x_69 = lean_uint64_xor(x_66, x_68);
x_70 = 16;
x_71 = lean_uint64_shift_right(x_69, x_70);
x_72 = lean_uint64_xor(x_69, x_71);
x_73 = lean_uint64_to_usize(x_72);
x_74 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_75 = 1;
x_76 = lean_usize_sub(x_74, x_75);
x_77 = lean_usize_land(x_73, x_76);
x_78 = lean_array_uget(x_62, x_77);
x_79 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_63, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_61, x_80);
lean_dec(x_61);
x_82 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_82, 0, x_63);
lean_ctor_set(x_82, 1, x_64);
lean_ctor_set(x_82, 2, x_78);
x_83 = lean_array_uset(x_62, x_77, x_82);
x_84 = lean_unsigned_to_nat(4u);
x_85 = lean_nat_mul(x_81, x_84);
x_86 = lean_unsigned_to_nat(3u);
x_87 = lean_nat_div(x_85, x_86);
lean_dec(x_85);
x_88 = lean_array_get_size(x_83);
x_89 = lean_nat_dec_le(x_87, x_88);
lean_dec(x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_83);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_81);
lean_ctor_set(x_91, 1, x_90);
x_16 = x_91;
goto block_25;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_81);
lean_ctor_set(x_92, 1, x_83);
x_16 = x_92;
goto block_25;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_box(0);
x_94 = lean_array_uset(x_62, x_77, x_93);
x_95 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_63, x_64, x_78);
x_96 = lean_array_uset(x_94, x_77, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_61);
lean_ctor_set(x_97, 1, x_96);
x_16 = x_97;
goto block_25;
}
}
block_25:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
if (lean_is_scalar(x_15)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_15;
}
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_st_ref_set(x_3, x_17, x_12);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(x_1, x_2, x_3, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_CSE_replaceFun(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; uint8_t x_22; 
x_10 = lean_array_fget(x_3, x_2);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
x_12 = lean_st_ref_get(x_4, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_15, x_1, x_11);
lean_dec(x_15);
lean_inc(x_10);
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(x_10, x_16, x_5, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_21 = lean_ptr_addr(x_18);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_2, x_23);
x_25 = lean_array_fset(x_3, x_2, x_18);
lean_dec(x_2);
x_2 = x_24;
x_3 = x_25;
x_6 = x_19;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_18);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_2, x_27);
lean_dec(x_2);
x_2 = x_28;
x_6 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(x_1, x_9, x_2, x_3, x_5, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_2);
x_10 = lean_st_ref_set(x_1, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_st_ref_set(x_1, x_18, x_7);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
x_22 = lean_box(0);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_goFunDecl(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 4);
lean_inc(x_14);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(x_16, x_12, x_3, x_4, x_5, x_6, x_7, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_3, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_25);
x_28 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(x_3, x_23, x_27, x_26);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_dec(x_10);
x_31 = lean_unbox(x_15);
x_32 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_30, x_31, x_13);
lean_dec(x_30);
x_33 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_2, x_32, x_18, x_25, x_5, x_29);
return x_33;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_st_ref_get(x_3, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_11, x_1, x_6);
lean_dec(x_11);
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(x_15, x_7, x_1);
lean_dec(x_15);
x_18 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(x_2, x_16, x_17, x_4, x_14);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0___redArg(x_1, x_2, x_3, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(x_8, x_2, x_1);
lean_dec(x_8);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(x_12, x_2, x_1);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1___redArg(x_1, x_2, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Code_cse_go_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_2);
x_10 = lean_st_ref_set(x_1, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_st_ref_set(x_1, x_18, x_7);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
x_22 = lean_box(0);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Code_cse_go_spec__2(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_4);
x_12 = lean_nat_dec_lt(x_3, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_fget(x_4, x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_14, 2);
lean_inc(x_29);
x_30 = lean_st_ref_get(x_5, x_10);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(x_1, x_28, x_5, x_6, x_7, x_8, x_9, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Compiler_LCNF_Code_cse_go(x_2, x_29, x_5, x_6, x_7, x_8, x_9, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_14);
x_40 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(x_14, x_35, x_38);
lean_inc(x_40);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Code_cse_go_spec__2___lam__0(x_5, x_33, x_41, x_39);
lean_dec(x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_15 = x_40;
x_16 = x_43;
goto block_27;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_44 = lean_ctor_get(x_14, 0);
lean_inc(x_44);
x_45 = lean_st_ref_get(x_5, x_10);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Compiler_LCNF_Code_cse_go(x_2, x_44, x_5, x_6, x_7, x_8, x_9, x_47);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_14);
x_52 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_14, x_50);
lean_inc(x_52);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Code_cse_go_spec__2___lam__0(x_5, x_48, x_53, x_51);
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_15 = x_52;
x_16 = x_55;
goto block_27;
}
block_27:
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = lean_ptr_addr(x_14);
lean_dec(x_14);
x_18 = lean_ptr_addr(x_15);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_3, x_20);
x_22 = lean_array_fset(x_4, x_3, x_15);
lean_dec(x_3);
x_3 = x_21;
x_4 = x_22;
x_10 = x_16;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_3, x_24);
lean_dec(x_3);
x_3 = x_25;
x_10 = x_16;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse_go___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
lean_inc(x_9);
x_13 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0___redArg(x_12, x_9, x_3, x_5, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_3, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_20);
lean_inc(x_22);
x_23 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__0___redArg(x_21, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_st_ref_take(x_3, x_18);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; size_t x_45; size_t x_46; uint8_t x_47; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_28, x_22, x_19);
lean_ctor_set(x_25, 0, x_29);
x_30 = lean_st_ref_set(x_3, x_25, x_26);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_10);
x_32 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_45 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_46 = lean_ptr_addr(x_33);
x_47 = lean_usize_dec_eq(x_45, x_46);
if (x_47 == 0)
{
lean_dec(x_9);
x_36 = x_47;
goto block_44;
}
else
{
size_t x_48; size_t x_49; uint8_t x_50; 
x_48 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_49 = lean_ptr_addr(x_14);
x_50 = lean_usize_dec_eq(x_48, x_49);
x_36 = x_50;
goto block_44;
}
block_44:
{
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_2);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_2, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_2, 0);
lean_dec(x_39);
lean_ctor_set(x_2, 1, x_33);
lean_ctor_set(x_2, 0, x_14);
if (lean_is_scalar(x_35)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_35;
}
lean_ctor_set(x_40, 0, x_2);
lean_ctor_set(x_40, 1, x_34);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_14);
lean_ctor_set(x_41, 1, x_33);
if (lean_is_scalar(x_35)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_35;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_34);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_33);
lean_dec(x_14);
if (lean_is_scalar(x_35)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_35;
}
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_34);
return x_43;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; size_t x_67; size_t x_68; uint8_t x_69; 
x_51 = lean_ctor_get(x_25, 0);
x_52 = lean_ctor_get(x_25, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_25);
x_53 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_51, x_22, x_19);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_st_ref_set(x_3, x_54, x_26);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
lean_inc(x_10);
x_57 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_67 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_68 = lean_ptr_addr(x_58);
x_69 = lean_usize_dec_eq(x_67, x_68);
if (x_69 == 0)
{
lean_dec(x_9);
x_61 = x_69;
goto block_66;
}
else
{
size_t x_70; size_t x_71; uint8_t x_72; 
x_70 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_71 = lean_ptr_addr(x_14);
x_72 = lean_usize_dec_eq(x_70, x_71);
x_61 = x_72;
goto block_66;
}
block_66:
{
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_62 = x_2;
} else {
 lean_dec_ref(x_2);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_14);
lean_ctor_set(x_63, 1, x_58);
if (lean_is_scalar(x_60)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_60;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_59);
return x_64;
}
else
{
lean_object* x_65; 
lean_dec(x_58);
lean_dec(x_14);
if (lean_is_scalar(x_60)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_60;
}
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_59);
return x_65;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_2);
x_73 = lean_ctor_get(x_23, 0);
lean_inc(x_73);
lean_dec(x_23);
x_74 = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(x_14, x_73, x_3, x_5, x_18);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_2 = x_10;
x_8 = x_75;
goto _start;
}
}
case 1:
{
if (x_1 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; size_t x_95; size_t x_96; uint8_t x_97; 
x_77 = lean_ctor_get(x_2, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 1);
lean_inc(x_78);
lean_inc(x_77);
x_79 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_1, x_77, x_3, x_4, x_5, x_6, x_7, x_8);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_78);
x_82 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_78, x_3, x_4, x_5, x_6, x_7, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_95 = lean_ptr_addr(x_78);
lean_dec(x_78);
x_96 = lean_ptr_addr(x_83);
x_97 = lean_usize_dec_eq(x_95, x_96);
if (x_97 == 0)
{
lean_dec(x_77);
x_86 = x_97;
goto block_94;
}
else
{
size_t x_98; size_t x_99; uint8_t x_100; 
x_98 = lean_ptr_addr(x_77);
lean_dec(x_77);
x_99 = lean_ptr_addr(x_80);
x_100 = lean_usize_dec_eq(x_98, x_99);
x_86 = x_100;
goto block_94;
}
block_94:
{
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_2);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_2, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_2, 0);
lean_dec(x_89);
lean_ctor_set(x_2, 1, x_83);
lean_ctor_set(x_2, 0, x_80);
if (lean_is_scalar(x_85)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_85;
}
lean_ctor_set(x_90, 0, x_2);
lean_ctor_set(x_90, 1, x_84);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_2);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_80);
lean_ctor_set(x_91, 1, x_83);
if (lean_is_scalar(x_85)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_85;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_84);
return x_92;
}
}
else
{
lean_object* x_93; 
lean_dec(x_83);
lean_dec(x_80);
if (lean_is_scalar(x_85)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_85;
}
lean_ctor_set(x_93, 0, x_2);
lean_ctor_set(x_93, 1, x_84);
return x_93;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_101 = lean_ctor_get(x_2, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_2, 1);
lean_inc(x_102);
lean_inc(x_101);
x_103 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_1, x_101, x_3, x_4, x_5, x_6, x_7, x_8);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_st_ref_get(x_3, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Compiler_LCNF_Code_cse_go___closed__0;
lean_inc(x_104);
x_111 = l_Lean_Compiler_LCNF_FunDecl_toExpr(x_104, x_110);
lean_inc(x_111);
x_112 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__0___redArg(x_109, x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_113 = lean_st_ref_take(x_3, x_108);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_ctor_get(x_104, 0);
lean_inc(x_116);
x_117 = !lean_is_exclusive(x_114);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; size_t x_135; size_t x_136; uint8_t x_137; 
x_118 = lean_ctor_get(x_114, 0);
x_119 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_118, x_111, x_116);
lean_ctor_set(x_114, 0, x_119);
x_120 = lean_st_ref_set(x_3, x_114, x_115);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
lean_inc(x_102);
x_122 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_102, x_3, x_4, x_5, x_6, x_7, x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
x_135 = lean_ptr_addr(x_102);
lean_dec(x_102);
x_136 = lean_ptr_addr(x_123);
x_137 = lean_usize_dec_eq(x_135, x_136);
if (x_137 == 0)
{
lean_dec(x_101);
x_126 = x_137;
goto block_134;
}
else
{
size_t x_138; size_t x_139; uint8_t x_140; 
x_138 = lean_ptr_addr(x_101);
lean_dec(x_101);
x_139 = lean_ptr_addr(x_104);
x_140 = lean_usize_dec_eq(x_138, x_139);
x_126 = x_140;
goto block_134;
}
block_134:
{
if (x_126 == 0)
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_2);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_2, 1);
lean_dec(x_128);
x_129 = lean_ctor_get(x_2, 0);
lean_dec(x_129);
lean_ctor_set(x_2, 1, x_123);
lean_ctor_set(x_2, 0, x_104);
if (lean_is_scalar(x_125)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_125;
}
lean_ctor_set(x_130, 0, x_2);
lean_ctor_set(x_130, 1, x_124);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_2);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_104);
lean_ctor_set(x_131, 1, x_123);
if (lean_is_scalar(x_125)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_125;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_124);
return x_132;
}
}
else
{
lean_object* x_133; 
lean_dec(x_123);
lean_dec(x_104);
if (lean_is_scalar(x_125)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_125;
}
lean_ctor_set(x_133, 0, x_2);
lean_ctor_set(x_133, 1, x_124);
return x_133;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; size_t x_157; size_t x_158; uint8_t x_159; 
x_141 = lean_ctor_get(x_114, 0);
x_142 = lean_ctor_get(x_114, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_114);
x_143 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_141, x_111, x_116);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = lean_st_ref_set(x_3, x_144, x_115);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
lean_inc(x_102);
x_147 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_102, x_3, x_4, x_5, x_6, x_7, x_146);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_157 = lean_ptr_addr(x_102);
lean_dec(x_102);
x_158 = lean_ptr_addr(x_148);
x_159 = lean_usize_dec_eq(x_157, x_158);
if (x_159 == 0)
{
lean_dec(x_101);
x_151 = x_159;
goto block_156;
}
else
{
size_t x_160; size_t x_161; uint8_t x_162; 
x_160 = lean_ptr_addr(x_101);
lean_dec(x_101);
x_161 = lean_ptr_addr(x_104);
x_162 = lean_usize_dec_eq(x_160, x_161);
x_151 = x_162;
goto block_156;
}
block_156:
{
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_152 = x_2;
} else {
 lean_dec_ref(x_2);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_104);
lean_ctor_set(x_153, 1, x_148);
if (lean_is_scalar(x_150)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_150;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_149);
return x_154;
}
else
{
lean_object* x_155; 
lean_dec(x_148);
lean_dec(x_104);
if (lean_is_scalar(x_150)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_150;
}
lean_ctor_set(x_155, 0, x_2);
lean_ctor_set(x_155, 1, x_149);
return x_155;
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_111);
lean_dec(x_101);
lean_dec(x_2);
x_163 = lean_ctor_get(x_112, 0);
lean_inc(x_163);
lean_dec(x_112);
x_164 = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(x_104, x_163, x_3, x_5, x_108);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_2 = x_102;
x_8 = x_165;
goto _start;
}
}
}
case 2:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; size_t x_185; size_t x_186; uint8_t x_187; 
x_167 = lean_ctor_get(x_2, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_2, 1);
lean_inc(x_168);
lean_inc(x_167);
x_169 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_1, x_167, x_3, x_4, x_5, x_6, x_7, x_8);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
lean_inc(x_168);
x_172 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_168, x_3, x_4, x_5, x_6, x_7, x_171);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_175 = x_172;
} else {
 lean_dec_ref(x_172);
 x_175 = lean_box(0);
}
x_185 = lean_ptr_addr(x_168);
lean_dec(x_168);
x_186 = lean_ptr_addr(x_173);
x_187 = lean_usize_dec_eq(x_185, x_186);
if (x_187 == 0)
{
lean_dec(x_167);
x_176 = x_187;
goto block_184;
}
else
{
size_t x_188; size_t x_189; uint8_t x_190; 
x_188 = lean_ptr_addr(x_167);
lean_dec(x_167);
x_189 = lean_ptr_addr(x_170);
x_190 = lean_usize_dec_eq(x_188, x_189);
x_176 = x_190;
goto block_184;
}
block_184:
{
if (x_176 == 0)
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_2);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_2, 1);
lean_dec(x_178);
x_179 = lean_ctor_get(x_2, 0);
lean_dec(x_179);
lean_ctor_set(x_2, 1, x_173);
lean_ctor_set(x_2, 0, x_170);
if (lean_is_scalar(x_175)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_175;
}
lean_ctor_set(x_180, 0, x_2);
lean_ctor_set(x_180, 1, x_174);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_2);
x_181 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_181, 0, x_170);
lean_ctor_set(x_181, 1, x_173);
if (lean_is_scalar(x_175)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_175;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_174);
return x_182;
}
}
else
{
lean_object* x_183; 
lean_dec(x_173);
lean_dec(x_170);
if (lean_is_scalar(x_175)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_175;
}
lean_ctor_set(x_183, 0, x_2);
lean_ctor_set(x_183, 1, x_174);
return x_183;
}
}
}
case 3:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; 
x_191 = lean_ctor_get(x_2, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_2, 1);
lean_inc(x_192);
x_193 = lean_st_ref_get(x_3, x_8);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_box(0);
x_198 = lean_unbox(x_197);
lean_inc(x_191);
x_199 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_196, x_191, x_198);
lean_dec(x_196);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; uint8_t x_215; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
lean_dec(x_199);
x_201 = lean_unbox(x_197);
lean_inc(x_192);
x_202 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1___redArg(x_201, x_192, x_3, x_195);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_205 = x_202;
} else {
 lean_dec_ref(x_202);
 x_205 = lean_box(0);
}
x_215 = lean_name_eq(x_191, x_200);
lean_dec(x_191);
if (x_215 == 0)
{
lean_dec(x_192);
x_206 = x_215;
goto block_214;
}
else
{
size_t x_216; size_t x_217; uint8_t x_218; 
x_216 = lean_ptr_addr(x_192);
lean_dec(x_192);
x_217 = lean_ptr_addr(x_203);
x_218 = lean_usize_dec_eq(x_216, x_217);
x_206 = x_218;
goto block_214;
}
block_214:
{
if (x_206 == 0)
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_2);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_2, 1);
lean_dec(x_208);
x_209 = lean_ctor_get(x_2, 0);
lean_dec(x_209);
lean_ctor_set(x_2, 1, x_203);
lean_ctor_set(x_2, 0, x_200);
if (lean_is_scalar(x_205)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_205;
}
lean_ctor_set(x_210, 0, x_2);
lean_ctor_set(x_210, 1, x_204);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_2);
x_211 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_211, 0, x_200);
lean_ctor_set(x_211, 1, x_203);
if (lean_is_scalar(x_205)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_205;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_204);
return x_212;
}
}
else
{
lean_object* x_213; 
lean_dec(x_203);
lean_dec(x_200);
if (lean_is_scalar(x_205)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_205;
}
lean_ctor_set(x_213, 0, x_2);
lean_ctor_set(x_213, 1, x_204);
return x_213;
}
}
}
else
{
lean_object* x_219; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_2);
x_219 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_195);
return x_219;
}
}
case 4:
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; 
x_220 = lean_ctor_get(x_2, 0);
lean_inc(x_220);
x_221 = lean_st_ref_get(x_3, x_8);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_ctor_get(x_220, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_220, 1);
lean_inc(x_225);
x_226 = lean_ctor_get(x_220, 2);
lean_inc(x_226);
x_227 = lean_ctor_get(x_220, 3);
lean_inc(x_227);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 lean_ctor_release(x_220, 2);
 lean_ctor_release(x_220, 3);
 x_228 = x_220;
} else {
 lean_dec_ref(x_220);
 x_228 = lean_box(0);
}
x_229 = lean_ctor_get(x_222, 1);
lean_inc(x_229);
lean_dec(x_222);
x_230 = lean_box(0);
x_231 = lean_unbox(x_230);
lean_inc(x_226);
x_232 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_229, x_226, x_231);
lean_dec(x_229);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; uint8_t x_252; size_t x_256; size_t x_257; uint8_t x_258; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 x_234 = x_232;
} else {
 lean_dec_ref(x_232);
 x_234 = lean_box(0);
}
x_235 = lean_st_ref_get(x_3, x_223);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_238 = x_235;
} else {
 lean_dec_ref(x_235);
 x_238 = lean_box(0);
}
x_239 = lean_unsigned_to_nat(0u);
x_240 = lean_unbox(x_230);
lean_inc(x_227);
x_241 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Code_cse_go_spec__2(x_240, x_1, x_239, x_227, x_3, x_4, x_5, x_6, x_7, x_237);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_244 = x_241;
} else {
 lean_dec_ref(x_241);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_236, 1);
lean_inc(x_245);
lean_dec(x_236);
x_246 = lean_unbox(x_230);
lean_inc(x_225);
x_247 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_245, x_246, x_225);
lean_dec(x_245);
x_256 = lean_ptr_addr(x_227);
lean_dec(x_227);
x_257 = lean_ptr_addr(x_242);
x_258 = lean_usize_dec_eq(x_256, x_257);
if (x_258 == 0)
{
lean_dec(x_225);
x_252 = x_258;
goto block_255;
}
else
{
size_t x_259; size_t x_260; uint8_t x_261; 
x_259 = lean_ptr_addr(x_225);
lean_dec(x_225);
x_260 = lean_ptr_addr(x_247);
x_261 = lean_usize_dec_eq(x_259, x_260);
x_252 = x_261;
goto block_255;
}
block_251:
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
if (lean_is_scalar(x_228)) {
 x_248 = lean_alloc_ctor(0, 4, 0);
} else {
 x_248 = x_228;
}
lean_ctor_set(x_248, 0, x_224);
lean_ctor_set(x_248, 1, x_247);
lean_ctor_set(x_248, 2, x_233);
lean_ctor_set(x_248, 3, x_242);
if (lean_is_scalar(x_234)) {
 x_249 = lean_alloc_ctor(4, 1, 0);
} else {
 x_249 = x_234;
 lean_ctor_set_tag(x_249, 4);
}
lean_ctor_set(x_249, 0, x_248);
if (lean_is_scalar(x_244)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_244;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_243);
return x_250;
}
block_255:
{
if (x_252 == 0)
{
lean_dec(x_238);
lean_dec(x_226);
lean_dec(x_2);
goto block_251;
}
else
{
uint8_t x_253; 
x_253 = lean_name_eq(x_226, x_233);
lean_dec(x_226);
if (x_253 == 0)
{
lean_dec(x_238);
lean_dec(x_2);
goto block_251;
}
else
{
lean_object* x_254; 
lean_dec(x_247);
lean_dec(x_244);
lean_dec(x_242);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_228);
lean_dec(x_224);
if (lean_is_scalar(x_238)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_238;
}
lean_ctor_set(x_254, 0, x_2);
lean_ctor_set(x_254, 1, x_243);
return x_254;
}
}
}
}
else
{
lean_object* x_262; 
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_2);
x_262 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_223);
return x_262;
}
}
case 5:
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_263 = lean_ctor_get(x_2, 0);
lean_inc(x_263);
x_264 = lean_st_ref_get(x_3, x_8);
x_265 = !lean_is_exclusive(x_264);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; 
x_266 = lean_ctor_get(x_264, 0);
x_267 = lean_ctor_get(x_264, 1);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = lean_box(0);
x_270 = lean_unbox(x_269);
lean_inc(x_263);
x_271 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_268, x_263, x_270);
lean_dec(x_268);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; uint8_t x_273; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
lean_dec(x_271);
x_273 = lean_name_eq(x_263, x_272);
lean_dec(x_263);
if (x_273 == 0)
{
uint8_t x_274; 
x_274 = !lean_is_exclusive(x_2);
if (x_274 == 0)
{
lean_object* x_275; 
x_275 = lean_ctor_get(x_2, 0);
lean_dec(x_275);
lean_ctor_set(x_2, 0, x_272);
lean_ctor_set(x_264, 0, x_2);
return x_264;
}
else
{
lean_object* x_276; 
lean_dec(x_2);
x_276 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_276, 0, x_272);
lean_ctor_set(x_264, 0, x_276);
return x_264;
}
}
else
{
lean_dec(x_272);
lean_ctor_set(x_264, 0, x_2);
return x_264;
}
}
else
{
lean_object* x_277; 
lean_free_object(x_264);
lean_dec(x_263);
lean_dec(x_2);
x_277 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_267);
return x_277;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; lean_object* x_283; 
x_278 = lean_ctor_get(x_264, 0);
x_279 = lean_ctor_get(x_264, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_264);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec(x_278);
x_281 = lean_box(0);
x_282 = lean_unbox(x_281);
lean_inc(x_263);
x_283 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_280, x_263, x_282);
lean_dec(x_280);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; uint8_t x_285; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
lean_dec(x_283);
x_285 = lean_name_eq(x_263, x_284);
lean_dec(x_263);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_286 = x_2;
} else {
 lean_dec_ref(x_2);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(5, 1, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_284);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_279);
return x_288;
}
else
{
lean_object* x_289; 
lean_dec(x_284);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_2);
lean_ctor_set(x_289, 1, x_279);
return x_289;
}
}
else
{
lean_object* x_290; 
lean_dec(x_263);
lean_dec(x_2);
x_290 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_279);
return x_290;
}
}
}
default: 
{
lean_object* x_291; 
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_2);
lean_ctor_set(x_291, 1, x_8);
return x_291;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_goFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1___redArg(x_5, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Code_cse_go_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Code_cse_go_spec__2___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Code_cse_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Code_cse_go_spec__2(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_Code_cse_go(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Code_cse___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Compiler_LCNF_Code_cse___closed__2;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Code_cse___closed__3;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Code_cse___closed__4;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Code_cse___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Code_cse___closed__6;
x_2 = l_Lean_Compiler_LCNF_Code_cse___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = l_Lean_Compiler_LCNF_Code_cse___closed__7;
x_9 = lean_st_mk_ref(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_2, x_10, x_3, x_4, x_5, x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_10, x_14);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_13);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Compiler_LCNF_Code_cse(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_cse_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_apply_6(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_ctor_set(x_2, 0, x_12);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_2, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_free_object(x_2);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_apply_6(x_1, x_20, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_29 = x_21;
} else {
 lean_dec_ref(x_21);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(1, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Code_cse(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
x_13 = lean_ctor_get(x_2, 4);
x_14 = lean_ctor_get(x_2, 5);
x_15 = lean_box(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_cse___lam__0___boxed), 7, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_cse_spec__0(x_16, x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_2, 4, x_19);
lean_ctor_set(x_17, 0, x_2);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_2, 4, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_2);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get(x_2, 2);
x_30 = lean_ctor_get(x_2, 3);
x_31 = lean_ctor_get(x_2, 4);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
x_34 = lean_ctor_get(x_2, 5);
lean_inc(x_34);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
x_35 = lean_box(x_1);
x_36 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_cse___lam__0___boxed), 7, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_cse_spec__0(x_36, x_31, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_41, 0, x_27);
lean_ctor_set(x_41, 1, x_28);
lean_ctor_set(x_41, 2, x_29);
lean_ctor_set(x_41, 3, x_30);
lean_ctor_set(x_41, 4, x_38);
lean_ctor_set(x_41, 5, x_34);
lean_ctor_set_uint8(x_41, sizeof(void*)*6, x_32);
lean_ctor_set_uint8(x_41, sizeof(void*)*6 + 1, x_33);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Compiler_LCNF_Decl_cse___lam__0(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Compiler_LCNF_Decl_cse(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cse___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cse", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_cse___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Compiler_LCNF_cse___closed__1;
x_5 = lean_box(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_cse___boxed), 7, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_4, x_6, x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_LCNF_cse(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1129_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_CSE___hyg_1129_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_cse___closed__0;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1129_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_CSE___hyg_1129_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_CSE___hyg_1129_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1129_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LCNF", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_CSE___hyg_1129_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_CSE___hyg_1129_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_CSE___hyg_1129_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_CSE___hyg_1129_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_CSE___hyg_1129_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_CSE___hyg_1129_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_CSE___hyg_1129_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_CSE___hyg_1129_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_CSE___hyg_1129_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("CSE", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_CSE___hyg_1129_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_CSE___hyg_1129_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_CSE___hyg_1129_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_CSE___hyg_1129_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1129u);
x_2 = l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1129_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_3 = lean_box(1);
x_4 = l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_CSE___hyg_1129_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ToExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_CSE(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__0 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__0);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__3 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__3);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__6 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__6);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__7 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__7);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__8 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__8);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__9 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__9);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__10 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__10);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__11 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__11);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__12 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__12);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__13 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__13);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__14 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__14);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__15 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__15);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__16 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__16);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__17 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__17);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM);
l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0 = _init_l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0);
l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1 = _init_l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1);
l_Lean_Compiler_LCNF_Code_cse_go___closed__0 = _init_l_Lean_Compiler_LCNF_Code_cse_go___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Code_cse_go___closed__0);
l_Lean_Compiler_LCNF_Code_cse___closed__0 = _init_l_Lean_Compiler_LCNF_Code_cse___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Code_cse___closed__0);
l_Lean_Compiler_LCNF_Code_cse___closed__1 = _init_l_Lean_Compiler_LCNF_Code_cse___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Code_cse___closed__1);
l_Lean_Compiler_LCNF_Code_cse___closed__2 = _init_l_Lean_Compiler_LCNF_Code_cse___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Code_cse___closed__2);
l_Lean_Compiler_LCNF_Code_cse___closed__3 = _init_l_Lean_Compiler_LCNF_Code_cse___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Code_cse___closed__3);
l_Lean_Compiler_LCNF_Code_cse___closed__4 = _init_l_Lean_Compiler_LCNF_Code_cse___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Code_cse___closed__4);
l_Lean_Compiler_LCNF_Code_cse___closed__5 = _init_l_Lean_Compiler_LCNF_Code_cse___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Code_cse___closed__5);
l_Lean_Compiler_LCNF_Code_cse___closed__6 = _init_l_Lean_Compiler_LCNF_Code_cse___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Code_cse___closed__6);
l_Lean_Compiler_LCNF_Code_cse___closed__7 = _init_l_Lean_Compiler_LCNF_Code_cse___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_Code_cse___closed__7);
l_Lean_Compiler_LCNF_cse___closed__0 = _init_l_Lean_Compiler_LCNF_cse___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_cse___closed__0);
l_Lean_Compiler_LCNF_cse___closed__1 = _init_l_Lean_Compiler_LCNF_cse___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_cse___closed__1);
l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1129_ = _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1129_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1129_);
l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_CSE___hyg_1129_ = _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_CSE___hyg_1129_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_CSE___hyg_1129_);
l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1129_ = _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1129_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1129_);
l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_CSE___hyg_1129_ = _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_CSE___hyg_1129_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_CSE___hyg_1129_);
l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_CSE___hyg_1129_ = _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_CSE___hyg_1129_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_CSE___hyg_1129_);
l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1129_ = _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1129_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1129_);
l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_CSE___hyg_1129_ = _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_CSE___hyg_1129_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_CSE___hyg_1129_);
l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_CSE___hyg_1129_ = _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_CSE___hyg_1129_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_CSE___hyg_1129_);
l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_CSE___hyg_1129_ = _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_CSE___hyg_1129_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_CSE___hyg_1129_);
l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_CSE___hyg_1129_ = _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_CSE___hyg_1129_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_CSE___hyg_1129_);
l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_CSE___hyg_1129_ = _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_CSE___hyg_1129_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_CSE___hyg_1129_);
l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_CSE___hyg_1129_ = _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_CSE___hyg_1129_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_CSE___hyg_1129_);
l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_CSE___hyg_1129_ = _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_CSE___hyg_1129_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_CSE___hyg_1129_);
l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_CSE___hyg_1129_ = _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_CSE___hyg_1129_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_CSE___hyg_1129_);
l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_CSE___hyg_1129_ = _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_CSE___hyg_1129_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_CSE___hyg_1129_);
l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_CSE___hyg_1129_ = _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_CSE___hyg_1129_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_CSE___hyg_1129_);
l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_CSE___hyg_1129_ = _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_CSE___hyg_1129_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_CSE___hyg_1129_);
l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_CSE___hyg_1129_ = _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_CSE___hyg_1129_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_CSE___hyg_1129_);
l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_CSE___hyg_1129_ = _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_CSE___hyg_1129_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_CSE___hyg_1129_);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1129_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
