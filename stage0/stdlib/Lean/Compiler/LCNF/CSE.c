// Lean compiler output
// Module: Lean.Compiler.LCNF.CSE
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.ToExpr Lean.Compiler.LCNF.PassManager Lean.Compiler.NeverExtractAttr
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___redArg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__13;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1277_(lean_object*);
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
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__12;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__3;
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_cse___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDecl_toExpr(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_goFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Code_cse_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__6;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftBaseIOEIO___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Code_cse_go___closed__0;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Code_cse_go_spec__2(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__7;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__0;
static lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__0;
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__1;
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_goFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5;
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__17;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_cse___closed__0;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__15;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
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
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
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
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__11;
uint8_t l_Lean_hasNeverExtractAttribute_visit(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_st_ref_get(x_2, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_hasNeverExtractAttribute_visit(x_8, x_4);
x_10 = lean_box(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_hasNeverExtractAttribute_visit(x_13, x_4);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(x_1, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_CSE_hasNeverExtract(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
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
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 3);
lean_inc(x_17);
lean_inc(x_17);
x_18 = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(x_17, x_7, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_st_ref_get(x_3, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_17);
lean_inc(x_26);
x_27 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__0___redArg(x_25, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_st_ref_take(x_3, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; size_t x_49; size_t x_50; uint8_t x_51; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_32, x_26, x_16);
lean_ctor_set(x_29, 0, x_33);
x_34 = lean_st_ref_set(x_3, x_29, x_30);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_10);
x_36 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_49 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_50 = lean_ptr_addr(x_37);
x_51 = lean_usize_dec_eq(x_49, x_50);
if (x_51 == 0)
{
lean_dec(x_9);
x_40 = x_51;
goto block_48;
}
else
{
size_t x_52; size_t x_53; uint8_t x_54; 
x_52 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_53 = lean_ptr_addr(x_14);
x_54 = lean_usize_dec_eq(x_52, x_53);
x_40 = x_54;
goto block_48;
}
block_48:
{
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_2);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_2, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_2, 0);
lean_dec(x_43);
lean_ctor_set(x_2, 1, x_37);
lean_ctor_set(x_2, 0, x_14);
if (lean_is_scalar(x_39)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_39;
}
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_14);
lean_ctor_set(x_45, 1, x_37);
if (lean_is_scalar(x_39)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_39;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_38);
return x_46;
}
}
else
{
lean_object* x_47; 
lean_dec(x_37);
lean_dec(x_14);
if (lean_is_scalar(x_39)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_39;
}
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; size_t x_71; size_t x_72; uint8_t x_73; 
x_55 = lean_ctor_get(x_29, 0);
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_29);
x_57 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_55, x_26, x_16);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_st_ref_set(x_3, x_58, x_30);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
lean_inc(x_10);
x_61 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_71 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_72 = lean_ptr_addr(x_62);
x_73 = lean_usize_dec_eq(x_71, x_72);
if (x_73 == 0)
{
lean_dec(x_9);
x_65 = x_73;
goto block_70;
}
else
{
size_t x_74; size_t x_75; uint8_t x_76; 
x_74 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_75 = lean_ptr_addr(x_14);
x_76 = lean_usize_dec_eq(x_74, x_75);
x_65 = x_76;
goto block_70;
}
block_70:
{
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_66 = x_2;
} else {
 lean_dec_ref(x_2);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_14);
lean_ctor_set(x_67, 1, x_62);
if (lean_is_scalar(x_64)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_64;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
return x_68;
}
else
{
lean_object* x_69; 
lean_dec(x_62);
lean_dec(x_14);
if (lean_is_scalar(x_64)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_64;
}
lean_ctor_set(x_69, 0, x_2);
lean_ctor_set(x_69, 1, x_63);
return x_69;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_26);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_2);
x_77 = lean_ctor_get(x_27, 0);
lean_inc(x_77);
lean_dec(x_27);
x_78 = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(x_14, x_77, x_3, x_5, x_24);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_2 = x_10;
x_8 = x_79;
goto _start;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; size_t x_95; size_t x_96; uint8_t x_97; 
lean_dec(x_17);
lean_dec(x_16);
x_81 = lean_ctor_get(x_18, 1);
lean_inc(x_81);
lean_dec(x_18);
lean_inc(x_10);
x_82 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_81);
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
x_95 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_96 = lean_ptr_addr(x_83);
x_97 = lean_usize_dec_eq(x_95, x_96);
if (x_97 == 0)
{
lean_dec(x_9);
x_86 = x_97;
goto block_94;
}
else
{
size_t x_98; size_t x_99; uint8_t x_100; 
x_98 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_99 = lean_ptr_addr(x_14);
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
lean_ctor_set(x_2, 0, x_14);
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
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_14);
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
lean_dec(x_14);
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
}
case 1:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_2, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_2, 1);
lean_inc(x_102);
lean_inc(x_101);
x_103 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_1, x_101, x_3, x_4, x_5, x_6, x_7, x_8);
if (x_1 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; size_t x_119; size_t x_120; uint8_t x_121; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_102);
x_106 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_102, x_3, x_4, x_5, x_6, x_7, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_119 = lean_ptr_addr(x_102);
lean_dec(x_102);
x_120 = lean_ptr_addr(x_107);
x_121 = lean_usize_dec_eq(x_119, x_120);
if (x_121 == 0)
{
lean_dec(x_101);
x_110 = x_121;
goto block_118;
}
else
{
size_t x_122; size_t x_123; uint8_t x_124; 
x_122 = lean_ptr_addr(x_101);
lean_dec(x_101);
x_123 = lean_ptr_addr(x_104);
x_124 = lean_usize_dec_eq(x_122, x_123);
x_110 = x_124;
goto block_118;
}
block_118:
{
if (x_110 == 0)
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_2);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_2, 1);
lean_dec(x_112);
x_113 = lean_ctor_get(x_2, 0);
lean_dec(x_113);
lean_ctor_set(x_2, 1, x_107);
lean_ctor_set(x_2, 0, x_104);
if (lean_is_scalar(x_109)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_109;
}
lean_ctor_set(x_114, 0, x_2);
lean_ctor_set(x_114, 1, x_108);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_2);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_104);
lean_ctor_set(x_115, 1, x_107);
if (lean_is_scalar(x_109)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_109;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_108);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec(x_107);
lean_dec(x_104);
if (lean_is_scalar(x_109)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_109;
}
lean_ctor_set(x_117, 0, x_2);
lean_ctor_set(x_117, 1, x_108);
return x_117;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_125 = lean_ctor_get(x_103, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_103, 1);
lean_inc(x_126);
lean_dec(x_103);
x_127 = lean_st_ref_get(x_3, x_126);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l_Lean_Compiler_LCNF_Code_cse_go___closed__0;
lean_inc(x_125);
x_132 = l_Lean_Compiler_LCNF_FunDecl_toExpr(x_125, x_131);
lean_inc(x_132);
x_133 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__0___redArg(x_130, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_134 = lean_st_ref_take(x_3, x_129);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get(x_125, 0);
lean_inc(x_137);
x_138 = !lean_is_exclusive(x_135);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; size_t x_156; size_t x_157; uint8_t x_158; 
x_139 = lean_ctor_get(x_135, 0);
x_140 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_139, x_132, x_137);
lean_ctor_set(x_135, 0, x_140);
x_141 = lean_st_ref_set(x_3, x_135, x_136);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
lean_inc(x_102);
x_143 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_102, x_3, x_4, x_5, x_6, x_7, x_142);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_146 = x_143;
} else {
 lean_dec_ref(x_143);
 x_146 = lean_box(0);
}
x_156 = lean_ptr_addr(x_102);
lean_dec(x_102);
x_157 = lean_ptr_addr(x_144);
x_158 = lean_usize_dec_eq(x_156, x_157);
if (x_158 == 0)
{
lean_dec(x_101);
x_147 = x_158;
goto block_155;
}
else
{
size_t x_159; size_t x_160; uint8_t x_161; 
x_159 = lean_ptr_addr(x_101);
lean_dec(x_101);
x_160 = lean_ptr_addr(x_125);
x_161 = lean_usize_dec_eq(x_159, x_160);
x_147 = x_161;
goto block_155;
}
block_155:
{
if (x_147 == 0)
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_2);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_2, 1);
lean_dec(x_149);
x_150 = lean_ctor_get(x_2, 0);
lean_dec(x_150);
lean_ctor_set(x_2, 1, x_144);
lean_ctor_set(x_2, 0, x_125);
if (lean_is_scalar(x_146)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_146;
}
lean_ctor_set(x_151, 0, x_2);
lean_ctor_set(x_151, 1, x_145);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_2);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_125);
lean_ctor_set(x_152, 1, x_144);
if (lean_is_scalar(x_146)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_146;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_145);
return x_153;
}
}
else
{
lean_object* x_154; 
lean_dec(x_144);
lean_dec(x_125);
if (lean_is_scalar(x_146)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_146;
}
lean_ctor_set(x_154, 0, x_2);
lean_ctor_set(x_154, 1, x_145);
return x_154;
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; size_t x_178; size_t x_179; uint8_t x_180; 
x_162 = lean_ctor_get(x_135, 0);
x_163 = lean_ctor_get(x_135, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_135);
x_164 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_162, x_132, x_137);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_163);
x_166 = lean_st_ref_set(x_3, x_165, x_136);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
lean_inc(x_102);
x_168 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_102, x_3, x_4, x_5, x_6, x_7, x_167);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_171 = x_168;
} else {
 lean_dec_ref(x_168);
 x_171 = lean_box(0);
}
x_178 = lean_ptr_addr(x_102);
lean_dec(x_102);
x_179 = lean_ptr_addr(x_169);
x_180 = lean_usize_dec_eq(x_178, x_179);
if (x_180 == 0)
{
lean_dec(x_101);
x_172 = x_180;
goto block_177;
}
else
{
size_t x_181; size_t x_182; uint8_t x_183; 
x_181 = lean_ptr_addr(x_101);
lean_dec(x_101);
x_182 = lean_ptr_addr(x_125);
x_183 = lean_usize_dec_eq(x_181, x_182);
x_172 = x_183;
goto block_177;
}
block_177:
{
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_173 = x_2;
} else {
 lean_dec_ref(x_2);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_125);
lean_ctor_set(x_174, 1, x_169);
if (lean_is_scalar(x_171)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_171;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_170);
return x_175;
}
else
{
lean_object* x_176; 
lean_dec(x_169);
lean_dec(x_125);
if (lean_is_scalar(x_171)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_171;
}
lean_ctor_set(x_176, 0, x_2);
lean_ctor_set(x_176, 1, x_170);
return x_176;
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_132);
lean_dec(x_101);
lean_dec(x_2);
x_184 = lean_ctor_get(x_133, 0);
lean_inc(x_184);
lean_dec(x_133);
x_185 = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(x_125, x_184, x_3, x_5, x_129);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_2 = x_102;
x_8 = x_186;
goto _start;
}
}
}
case 2:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; size_t x_206; size_t x_207; uint8_t x_208; 
x_188 = lean_ctor_get(x_2, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_2, 1);
lean_inc(x_189);
lean_inc(x_188);
x_190 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_1, x_188, x_3, x_4, x_5, x_6, x_7, x_8);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
lean_inc(x_189);
x_193 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_189, x_3, x_4, x_5, x_6, x_7, x_192);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_196 = x_193;
} else {
 lean_dec_ref(x_193);
 x_196 = lean_box(0);
}
x_206 = lean_ptr_addr(x_189);
lean_dec(x_189);
x_207 = lean_ptr_addr(x_194);
x_208 = lean_usize_dec_eq(x_206, x_207);
if (x_208 == 0)
{
lean_dec(x_188);
x_197 = x_208;
goto block_205;
}
else
{
size_t x_209; size_t x_210; uint8_t x_211; 
x_209 = lean_ptr_addr(x_188);
lean_dec(x_188);
x_210 = lean_ptr_addr(x_191);
x_211 = lean_usize_dec_eq(x_209, x_210);
x_197 = x_211;
goto block_205;
}
block_205:
{
if (x_197 == 0)
{
uint8_t x_198; 
x_198 = !lean_is_exclusive(x_2);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_2, 1);
lean_dec(x_199);
x_200 = lean_ctor_get(x_2, 0);
lean_dec(x_200);
lean_ctor_set(x_2, 1, x_194);
lean_ctor_set(x_2, 0, x_191);
if (lean_is_scalar(x_196)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_196;
}
lean_ctor_set(x_201, 0, x_2);
lean_ctor_set(x_201, 1, x_195);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_2);
x_202 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_202, 0, x_191);
lean_ctor_set(x_202, 1, x_194);
if (lean_is_scalar(x_196)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_196;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_195);
return x_203;
}
}
else
{
lean_object* x_204; 
lean_dec(x_194);
lean_dec(x_191);
if (lean_is_scalar(x_196)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_196;
}
lean_ctor_set(x_204, 0, x_2);
lean_ctor_set(x_204, 1, x_195);
return x_204;
}
}
}
case 3:
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; 
x_212 = lean_ctor_get(x_2, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_2, 1);
lean_inc(x_213);
x_214 = lean_st_ref_get(x_3, x_8);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_box(0);
x_219 = lean_unbox(x_218);
lean_inc(x_212);
x_220 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_217, x_212, x_219);
lean_dec(x_217);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; uint8_t x_236; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec(x_220);
x_222 = lean_unbox(x_218);
lean_inc(x_213);
x_223 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1___redArg(x_222, x_213, x_3, x_216);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_226 = x_223;
} else {
 lean_dec_ref(x_223);
 x_226 = lean_box(0);
}
x_236 = lean_name_eq(x_212, x_221);
lean_dec(x_212);
if (x_236 == 0)
{
lean_dec(x_213);
x_227 = x_236;
goto block_235;
}
else
{
size_t x_237; size_t x_238; uint8_t x_239; 
x_237 = lean_ptr_addr(x_213);
lean_dec(x_213);
x_238 = lean_ptr_addr(x_224);
x_239 = lean_usize_dec_eq(x_237, x_238);
x_227 = x_239;
goto block_235;
}
block_235:
{
if (x_227 == 0)
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_2);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_2, 1);
lean_dec(x_229);
x_230 = lean_ctor_get(x_2, 0);
lean_dec(x_230);
lean_ctor_set(x_2, 1, x_224);
lean_ctor_set(x_2, 0, x_221);
if (lean_is_scalar(x_226)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_226;
}
lean_ctor_set(x_231, 0, x_2);
lean_ctor_set(x_231, 1, x_225);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_2);
x_232 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_232, 0, x_221);
lean_ctor_set(x_232, 1, x_224);
if (lean_is_scalar(x_226)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_226;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_225);
return x_233;
}
}
else
{
lean_object* x_234; 
lean_dec(x_224);
lean_dec(x_221);
if (lean_is_scalar(x_226)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_226;
}
lean_ctor_set(x_234, 0, x_2);
lean_ctor_set(x_234, 1, x_225);
return x_234;
}
}
}
else
{
lean_object* x_240; 
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_2);
x_240 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_216);
return x_240;
}
}
case 4:
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; 
x_241 = lean_ctor_get(x_2, 0);
lean_inc(x_241);
x_242 = lean_st_ref_get(x_3, x_8);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_ctor_get(x_241, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_241, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_241, 2);
lean_inc(x_247);
x_248 = lean_ctor_get(x_241, 3);
lean_inc(x_248);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 lean_ctor_release(x_241, 2);
 lean_ctor_release(x_241, 3);
 x_249 = x_241;
} else {
 lean_dec_ref(x_241);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_243, 1);
lean_inc(x_250);
lean_dec(x_243);
x_251 = lean_box(0);
x_252 = lean_unbox(x_251);
lean_inc(x_247);
x_253 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_250, x_247, x_252);
lean_dec(x_250);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; uint8_t x_273; size_t x_277; size_t x_278; uint8_t x_279; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 x_255 = x_253;
} else {
 lean_dec_ref(x_253);
 x_255 = lean_box(0);
}
x_256 = lean_st_ref_get(x_3, x_244);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_259 = x_256;
} else {
 lean_dec_ref(x_256);
 x_259 = lean_box(0);
}
x_260 = lean_unsigned_to_nat(0u);
x_261 = lean_unbox(x_251);
lean_inc(x_248);
x_262 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Code_cse_go_spec__2(x_261, x_1, x_260, x_248, x_3, x_4, x_5, x_6, x_7, x_258);
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
x_266 = lean_ctor_get(x_257, 1);
lean_inc(x_266);
lean_dec(x_257);
x_267 = lean_unbox(x_251);
lean_inc(x_246);
x_268 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_266, x_267, x_246);
lean_dec(x_266);
x_277 = lean_ptr_addr(x_248);
lean_dec(x_248);
x_278 = lean_ptr_addr(x_263);
x_279 = lean_usize_dec_eq(x_277, x_278);
if (x_279 == 0)
{
lean_dec(x_246);
x_273 = x_279;
goto block_276;
}
else
{
size_t x_280; size_t x_281; uint8_t x_282; 
x_280 = lean_ptr_addr(x_246);
lean_dec(x_246);
x_281 = lean_ptr_addr(x_268);
x_282 = lean_usize_dec_eq(x_280, x_281);
x_273 = x_282;
goto block_276;
}
block_272:
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
if (lean_is_scalar(x_249)) {
 x_269 = lean_alloc_ctor(0, 4, 0);
} else {
 x_269 = x_249;
}
lean_ctor_set(x_269, 0, x_245);
lean_ctor_set(x_269, 1, x_268);
lean_ctor_set(x_269, 2, x_254);
lean_ctor_set(x_269, 3, x_263);
if (lean_is_scalar(x_255)) {
 x_270 = lean_alloc_ctor(4, 1, 0);
} else {
 x_270 = x_255;
 lean_ctor_set_tag(x_270, 4);
}
lean_ctor_set(x_270, 0, x_269);
if (lean_is_scalar(x_265)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_265;
}
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_264);
return x_271;
}
block_276:
{
if (x_273 == 0)
{
lean_dec(x_259);
lean_dec(x_247);
lean_dec(x_2);
goto block_272;
}
else
{
uint8_t x_274; 
x_274 = lean_name_eq(x_247, x_254);
lean_dec(x_247);
if (x_274 == 0)
{
lean_dec(x_259);
lean_dec(x_2);
goto block_272;
}
else
{
lean_object* x_275; 
lean_dec(x_268);
lean_dec(x_265);
lean_dec(x_263);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_249);
lean_dec(x_245);
if (lean_is_scalar(x_259)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_259;
}
lean_ctor_set(x_275, 0, x_2);
lean_ctor_set(x_275, 1, x_264);
return x_275;
}
}
}
}
else
{
lean_object* x_283; 
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_2);
x_283 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_244);
return x_283;
}
}
case 5:
{
lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_284 = lean_ctor_get(x_2, 0);
lean_inc(x_284);
x_285 = lean_st_ref_get(x_3, x_8);
x_286 = !lean_is_exclusive(x_285);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; 
x_287 = lean_ctor_get(x_285, 0);
x_288 = lean_ctor_get(x_285, 1);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
x_290 = lean_box(0);
x_291 = lean_unbox(x_290);
lean_inc(x_284);
x_292 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_289, x_284, x_291);
lean_dec(x_289);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; uint8_t x_294; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
lean_dec(x_292);
x_294 = lean_name_eq(x_284, x_293);
lean_dec(x_284);
if (x_294 == 0)
{
uint8_t x_295; 
x_295 = !lean_is_exclusive(x_2);
if (x_295 == 0)
{
lean_object* x_296; 
x_296 = lean_ctor_get(x_2, 0);
lean_dec(x_296);
lean_ctor_set(x_2, 0, x_293);
lean_ctor_set(x_285, 0, x_2);
return x_285;
}
else
{
lean_object* x_297; 
lean_dec(x_2);
x_297 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_297, 0, x_293);
lean_ctor_set(x_285, 0, x_297);
return x_285;
}
}
else
{
lean_dec(x_293);
lean_ctor_set(x_285, 0, x_2);
return x_285;
}
}
else
{
lean_object* x_298; 
lean_free_object(x_285);
lean_dec(x_284);
lean_dec(x_2);
x_298 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_288);
return x_298;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; 
x_299 = lean_ctor_get(x_285, 0);
x_300 = lean_ctor_get(x_285, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_285);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_box(0);
x_303 = lean_unbox(x_302);
lean_inc(x_284);
x_304 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_301, x_284, x_303);
lean_dec(x_301);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; uint8_t x_306; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
lean_dec(x_304);
x_306 = lean_name_eq(x_284, x_305);
lean_dec(x_284);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_307 = x_2;
} else {
 lean_dec_ref(x_2);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(5, 1, 0);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_305);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_300);
return x_309;
}
else
{
lean_object* x_310; 
lean_dec(x_305);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_2);
lean_ctor_set(x_310, 1, x_300);
return x_310;
}
}
else
{
lean_object* x_311; 
lean_dec(x_284);
lean_dec(x_2);
x_311 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_300);
return x_311;
}
}
}
default: 
{
lean_object* x_312; 
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_2);
lean_ctor_set(x_312, 1, x_8);
return x_312;
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
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1277_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_CSE___hyg_1277_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_cse___closed__0;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1277_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_CSE___hyg_1277_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_CSE___hyg_1277_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1277_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LCNF", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_CSE___hyg_1277_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_CSE___hyg_1277_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_CSE___hyg_1277_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_CSE___hyg_1277_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_CSE___hyg_1277_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_CSE___hyg_1277_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_CSE___hyg_1277_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_CSE___hyg_1277_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_CSE___hyg_1277_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("CSE", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_CSE___hyg_1277_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_CSE___hyg_1277_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_CSE___hyg_1277_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_CSE___hyg_1277_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1277u);
x_2 = l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1277_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_3 = lean_box(1);
x_4 = l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_CSE___hyg_1277_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ToExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_NeverExtractAttr(uint8_t builtin, lean_object*);
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
res = initialize_Lean_Compiler_NeverExtractAttr(builtin, lean_io_mk_world());
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
l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1277_ = _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1277_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1277_);
l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_CSE___hyg_1277_ = _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_CSE___hyg_1277_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_CSE___hyg_1277_);
l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1277_ = _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1277_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1277_);
l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_CSE___hyg_1277_ = _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_CSE___hyg_1277_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_CSE___hyg_1277_);
l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_CSE___hyg_1277_ = _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_CSE___hyg_1277_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_CSE___hyg_1277_);
l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1277_ = _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1277_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1277_);
l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_CSE___hyg_1277_ = _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_CSE___hyg_1277_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_CSE___hyg_1277_);
l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_CSE___hyg_1277_ = _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_CSE___hyg_1277_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_CSE___hyg_1277_);
l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_CSE___hyg_1277_ = _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_CSE___hyg_1277_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_CSE___hyg_1277_);
l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_CSE___hyg_1277_ = _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_CSE___hyg_1277_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_CSE___hyg_1277_);
l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_CSE___hyg_1277_ = _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_CSE___hyg_1277_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_CSE___hyg_1277_);
l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_CSE___hyg_1277_ = _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_CSE___hyg_1277_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_CSE___hyg_1277_);
l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_CSE___hyg_1277_ = _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_CSE___hyg_1277_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_CSE___hyg_1277_);
l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_CSE___hyg_1277_ = _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_CSE___hyg_1277_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_CSE___hyg_1277_);
l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_CSE___hyg_1277_ = _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_CSE___hyg_1277_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_CSE___hyg_1277_);
l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_CSE___hyg_1277_ = _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_CSE___hyg_1277_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_CSE___hyg_1277_);
l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_CSE___hyg_1277_ = _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_CSE___hyg_1277_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_CSE___hyg_1277_);
l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_CSE___hyg_1277_ = _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_CSE___hyg_1277_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_CSE___hyg_1277_);
l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_CSE___hyg_1277_ = _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_CSE___hyg_1277_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_CSE___hyg_1277_);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1277_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
