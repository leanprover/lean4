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
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___redArg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__13;
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__16;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__2;
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0;
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__4___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__12;
uint8_t l_Lean_beqFVarId____x40_Lean_Expr___hyg_1504_(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__3;
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_cse___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDecl_toExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_goFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_hasNeverExtractAttribute(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__6;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1(lean_object*, lean_object*);
lean_object* l_instMonadLiftBaseIOEIO___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Code_cse_go___closed__0;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__7;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__0;
static lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__0;
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_goFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5;
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__17;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1___redArg(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_cse___closed__0;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint64_t l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__15;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go___lam__2(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__11;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1278_(lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref(x_6);
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
lean_inc_ref(x_24);
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
lean_inc_ref(x_40);
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
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_56, 2);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_56, 3);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_56, 4);
lean_inc_ref(x_60);
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
lean_inc_ref(x_57);
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
lean_inc_ref(x_75);
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
lean_inc_ref(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_89, 0);
lean_inc_ref(x_91);
x_92 = lean_ctor_get(x_89, 2);
lean_inc_ref(x_92);
x_93 = lean_ctor_get(x_89, 3);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_89, 4);
lean_inc_ref(x_94);
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
lean_inc_ref(x_91);
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
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_109, 2);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_109, 3);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_109, 4);
lean_inc_ref(x_113);
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
lean_inc_ref(x_110);
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
lean_inc_ref(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_126, 0);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_126, 2);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_126, 3);
lean_inc_ref(x_130);
x_131 = lean_ctor_get(x_126, 4);
lean_inc_ref(x_131);
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
lean_inc_ref(x_128);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_8);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_inc_ref(x_6);
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
lean_inc_ref(x_9);
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
lean_inc_ref(x_10);
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
lean_inc_ref(x_13);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_5);
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
lean_dec_ref(x_9);
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
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
lean_dec_ref(x_5);
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
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
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
lean_dec_ref(x_12);
lean_inc(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(x_2, x_11, x_15, x_14);
lean_dec_ref(x_15);
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
lean_dec_ref(x_12);
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
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_12);
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
lean_dec_ref(x_13);
lean_inc(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(x_3, x_12, x_16, x_15);
lean_dec_ref(x_16);
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
lean_dec_ref(x_13);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_beqFVarId____x40_Lean_Expr___hyg_1504_(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1_spec__1_spec__1___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = l_Lean_beqFVarId____x40_Lean_Expr___hyg_1504_(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__4___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = l_Lean_beqFVarId____x40_Lean_Expr___hyg_1504_(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__4___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__4___redArg(x_2, x_3, x_4);
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
lean_dec_ref(x_6);
x_8 = lean_st_ref_take(x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_12);
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
lean_dec_ref(x_1);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_2);
x_29 = lean_array_get_size(x_26);
x_30 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_27);
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
x_43 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(x_27, x_42);
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
x_54 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1___redArg(x_47);
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
x_57 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__4___redArg(x_27, x_28, x_42);
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
lean_dec_ref(x_1);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_2);
x_63 = lean_array_get_size(x_60);
x_64 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_61);
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
x_77 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(x_61, x_76);
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
x_88 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1___redArg(x_81);
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
x_93 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__4___redArg(x_61, x_62, x_76);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_25; 
x_6 = 1;
x_7 = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(x_1, x_6, x_4, x_5);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_13);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_14 = x_10;
} else {
 lean_dec_ref(x_10);
 x_14 = lean_box(0);
}
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; size_t x_42; lean_object* x_43; uint8_t x_44; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec_ref(x_1);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_2);
x_30 = lean_array_get_size(x_27);
x_31 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_28);
x_32 = 32;
x_33 = lean_uint64_shift_right(x_31, x_32);
x_34 = lean_uint64_xor(x_31, x_33);
x_35 = 16;
x_36 = lean_uint64_shift_right(x_34, x_35);
x_37 = lean_uint64_xor(x_34, x_36);
x_38 = lean_uint64_to_usize(x_37);
x_39 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_40 = 1;
x_41 = lean_usize_sub(x_39, x_40);
x_42 = lean_usize_land(x_38, x_41);
x_43 = lean_array_uget(x_27, x_42);
x_44 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(x_28, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_26, x_45);
lean_dec(x_26);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_28);
lean_ctor_set(x_47, 1, x_29);
lean_ctor_set(x_47, 2, x_43);
x_48 = lean_array_uset(x_27, x_42, x_47);
x_49 = lean_unsigned_to_nat(4u);
x_50 = lean_nat_mul(x_46, x_49);
x_51 = lean_unsigned_to_nat(3u);
x_52 = lean_nat_div(x_50, x_51);
lean_dec(x_50);
x_53 = lean_array_get_size(x_48);
x_54 = lean_nat_dec_le(x_52, x_53);
lean_dec(x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1___redArg(x_48);
lean_ctor_set(x_13, 1, x_55);
lean_ctor_set(x_13, 0, x_46);
x_15 = x_13;
goto block_24;
}
else
{
lean_ctor_set(x_13, 1, x_48);
lean_ctor_set(x_13, 0, x_46);
x_15 = x_13;
goto block_24;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_box(0);
x_57 = lean_array_uset(x_27, x_42, x_56);
x_58 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__4___redArg(x_28, x_29, x_43);
x_59 = lean_array_uset(x_57, x_42, x_58);
lean_ctor_set(x_13, 1, x_59);
x_15 = x_13;
goto block_24;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; size_t x_72; size_t x_73; size_t x_74; size_t x_75; size_t x_76; lean_object* x_77; uint8_t x_78; 
x_60 = lean_ctor_get(x_13, 0);
x_61 = lean_ctor_get(x_13, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_13);
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
lean_dec_ref(x_1);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_2);
x_64 = lean_array_get_size(x_61);
x_65 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_62);
x_66 = 32;
x_67 = lean_uint64_shift_right(x_65, x_66);
x_68 = lean_uint64_xor(x_65, x_67);
x_69 = 16;
x_70 = lean_uint64_shift_right(x_68, x_69);
x_71 = lean_uint64_xor(x_68, x_70);
x_72 = lean_uint64_to_usize(x_71);
x_73 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_74 = 1;
x_75 = lean_usize_sub(x_73, x_74);
x_76 = lean_usize_land(x_72, x_75);
x_77 = lean_array_uget(x_61, x_76);
x_78 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(x_62, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_60, x_79);
lean_dec(x_60);
x_81 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_81, 0, x_62);
lean_ctor_set(x_81, 1, x_63);
lean_ctor_set(x_81, 2, x_77);
x_82 = lean_array_uset(x_61, x_76, x_81);
x_83 = lean_unsigned_to_nat(4u);
x_84 = lean_nat_mul(x_80, x_83);
x_85 = lean_unsigned_to_nat(3u);
x_86 = lean_nat_div(x_84, x_85);
lean_dec(x_84);
x_87 = lean_array_get_size(x_82);
x_88 = lean_nat_dec_le(x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__1___redArg(x_82);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_80);
lean_ctor_set(x_90, 1, x_89);
x_15 = x_90;
goto block_24;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_80);
lean_ctor_set(x_91, 1, x_82);
x_15 = x_91;
goto block_24;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_box(0);
x_93 = lean_array_uset(x_61, x_76, x_92);
x_94 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_CSE_replaceLet_spec__4___redArg(x_62, x_63, x_77);
x_95 = lean_array_uset(x_93, x_76, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_60);
lean_ctor_set(x_96, 1, x_95);
x_15 = x_96;
goto block_24;
}
}
block_24:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
if (lean_is_scalar(x_14)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_14;
}
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_st_ref_set(x_3, x_16, x_11);
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
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
lean_dec_ref(x_1);
x_5 = lean_st_ref_get(x_2, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = l_Lean_hasNeverExtractAttribute(x_8, x_4);
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
lean_inc_ref(x_13);
lean_dec(x_11);
x_14 = l_Lean_hasNeverExtractAttribute(x_13, x_4);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_9);
x_10 = lean_st_ref_get(x_3, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_13, x_1, x_9);
lean_dec_ref(x_13);
x_15 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(x_2, x_14, x_4, x_5, x_6, x_7, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1;
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_ctor_get(x_11, 3);
x_17 = lean_ctor_get(x_11, 4);
x_18 = lean_ctor_get(x_11, 1);
lean_dec(x_18);
x_19 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2;
x_20 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__3;
lean_inc_ref(x_14);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_21, 0, x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_17);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_16);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_26, 0, x_15);
lean_ctor_set(x_11, 4, x_24);
lean_ctor_set(x_11, 3, x_25);
lean_ctor_set(x_11, 2, x_26);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_11, 0, x_23);
lean_ctor_set(x_9, 1, x_20);
x_27 = l_ReaderT_instMonad___redArg(x_9);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 2);
x_34 = lean_ctor_get(x_29, 3);
x_35 = lean_ctor_get(x_29, 4);
x_36 = lean_ctor_get(x_29, 1);
lean_dec(x_36);
x_37 = lean_box(x_1);
x_38 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___lam__0___boxed), 8, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4;
x_40 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5;
lean_inc_ref(x_32);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_41, 0, x_32);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_32);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_45, 0, x_34);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_46, 0, x_33);
lean_ctor_set(x_29, 4, x_44);
lean_ctor_set(x_29, 3, x_45);
lean_ctor_set(x_29, 2, x_46);
lean_ctor_set(x_29, 1, x_39);
lean_ctor_set(x_29, 0, x_43);
lean_ctor_set(x_27, 1, x_40);
x_47 = l_ReaderT_instMonad___redArg(x_27);
x_48 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_47, x_2, x_38);
x_49 = lean_apply_6(x_48, x_3, x_4, x_5, x_6, x_7, x_8);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_50 = lean_ctor_get(x_29, 0);
x_51 = lean_ctor_get(x_29, 2);
x_52 = lean_ctor_get(x_29, 3);
x_53 = lean_ctor_get(x_29, 4);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_29);
x_54 = lean_box(x_1);
x_55 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___lam__0___boxed), 8, 1);
lean_closure_set(x_55, 0, x_54);
x_56 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4;
x_57 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5;
lean_inc_ref(x_50);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_58, 0, x_50);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_50);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_61, 0, x_53);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_62, 0, x_52);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_63, 0, x_51);
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_56);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_64, 3, x_62);
lean_ctor_set(x_64, 4, x_61);
lean_ctor_set(x_27, 1, x_57);
lean_ctor_set(x_27, 0, x_64);
x_65 = l_ReaderT_instMonad___redArg(x_27);
x_66 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_65, x_2, x_55);
x_67 = lean_apply_6(x_66, x_3, x_4, x_5, x_6, x_7, x_8);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_68 = lean_ctor_get(x_27, 0);
lean_inc(x_68);
lean_dec(x_27);
x_69 = lean_ctor_get(x_68, 0);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_68, 2);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_68, 3);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_68, 4);
lean_inc_ref(x_72);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 lean_ctor_release(x_68, 2);
 lean_ctor_release(x_68, 3);
 lean_ctor_release(x_68, 4);
 x_73 = x_68;
} else {
 lean_dec_ref(x_68);
 x_73 = lean_box(0);
}
x_74 = lean_box(x_1);
x_75 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___lam__0___boxed), 8, 1);
lean_closure_set(x_75, 0, x_74);
x_76 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4;
x_77 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5;
lean_inc_ref(x_69);
x_78 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_78, 0, x_69);
x_79 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_79, 0, x_69);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_81, 0, x_72);
x_82 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_82, 0, x_71);
x_83 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_83, 0, x_70);
if (lean_is_scalar(x_73)) {
 x_84 = lean_alloc_ctor(0, 5, 0);
} else {
 x_84 = x_73;
}
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_76);
lean_ctor_set(x_84, 2, x_83);
lean_ctor_set(x_84, 3, x_82);
lean_ctor_set(x_84, 4, x_81);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_77);
x_86 = l_ReaderT_instMonad___redArg(x_85);
x_87 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_86, x_2, x_75);
x_88 = lean_apply_6(x_87, x_3, x_4, x_5, x_6, x_7, x_8);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_89 = lean_ctor_get(x_11, 0);
x_90 = lean_ctor_get(x_11, 2);
x_91 = lean_ctor_get(x_11, 3);
x_92 = lean_ctor_get(x_11, 4);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_11);
x_93 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2;
x_94 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__3;
lean_inc_ref(x_89);
x_95 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_95, 0, x_89);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_96, 0, x_89);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_98, 0, x_92);
x_99 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_99, 0, x_91);
x_100 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_100, 0, x_90);
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_93);
lean_ctor_set(x_101, 2, x_100);
lean_ctor_set(x_101, 3, x_99);
lean_ctor_set(x_101, 4, x_98);
lean_ctor_set(x_9, 1, x_94);
lean_ctor_set(x_9, 0, x_101);
x_102 = l_ReaderT_instMonad___redArg(x_9);
x_103 = lean_ctor_get(x_102, 0);
lean_inc_ref(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_103, 0);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_103, 2);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_103, 3);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_103, 4);
lean_inc_ref(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 lean_ctor_release(x_103, 2);
 lean_ctor_release(x_103, 3);
 lean_ctor_release(x_103, 4);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
x_110 = lean_box(x_1);
x_111 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___lam__0___boxed), 8, 1);
lean_closure_set(x_111, 0, x_110);
x_112 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4;
x_113 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5;
lean_inc_ref(x_105);
x_114 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_114, 0, x_105);
x_115 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_115, 0, x_105);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_117, 0, x_108);
x_118 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_118, 0, x_107);
x_119 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_119, 0, x_106);
if (lean_is_scalar(x_109)) {
 x_120 = lean_alloc_ctor(0, 5, 0);
} else {
 x_120 = x_109;
}
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_112);
lean_ctor_set(x_120, 2, x_119);
lean_ctor_set(x_120, 3, x_118);
lean_ctor_set(x_120, 4, x_117);
if (lean_is_scalar(x_104)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_104;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_113);
x_122 = l_ReaderT_instMonad___redArg(x_121);
x_123 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_122, x_2, x_111);
x_124 = lean_apply_6(x_123, x_3, x_4, x_5, x_6, x_7, x_8);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_125 = lean_ctor_get(x_9, 0);
lean_inc(x_125);
lean_dec(x_9);
x_126 = lean_ctor_get(x_125, 0);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_125, 2);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_125, 3);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_125, 4);
lean_inc_ref(x_129);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 lean_ctor_release(x_125, 3);
 lean_ctor_release(x_125, 4);
 x_130 = x_125;
} else {
 lean_dec_ref(x_125);
 x_130 = lean_box(0);
}
x_131 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2;
x_132 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__3;
lean_inc_ref(x_126);
x_133 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_133, 0, x_126);
x_134 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_134, 0, x_126);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_136, 0, x_129);
x_137 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_137, 0, x_128);
x_138 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_138, 0, x_127);
if (lean_is_scalar(x_130)) {
 x_139 = lean_alloc_ctor(0, 5, 0);
} else {
 x_139 = x_130;
}
lean_ctor_set(x_139, 0, x_135);
lean_ctor_set(x_139, 1, x_131);
lean_ctor_set(x_139, 2, x_138);
lean_ctor_set(x_139, 3, x_137);
lean_ctor_set(x_139, 4, x_136);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_132);
x_141 = l_ReaderT_instMonad___redArg(x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc_ref(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_142, 0);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_142, 2);
lean_inc_ref(x_145);
x_146 = lean_ctor_get(x_142, 3);
lean_inc_ref(x_146);
x_147 = lean_ctor_get(x_142, 4);
lean_inc_ref(x_147);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 lean_ctor_release(x_142, 4);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_box(x_1);
x_150 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___lam__0___boxed), 8, 1);
lean_closure_set(x_150, 0, x_149);
x_151 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4;
x_152 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5;
lean_inc_ref(x_144);
x_153 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_153, 0, x_144);
x_154 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_154, 0, x_144);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_156, 0, x_147);
x_157 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_157, 0, x_146);
x_158 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_158, 0, x_145);
if (lean_is_scalar(x_148)) {
 x_159 = lean_alloc_ctor(0, 5, 0);
} else {
 x_159 = x_148;
}
lean_ctor_set(x_159, 0, x_155);
lean_ctor_set(x_159, 1, x_151);
lean_ctor_set(x_159, 2, x_158);
lean_ctor_set(x_159, 3, x_157);
lean_ctor_set(x_159, 4, x_156);
if (lean_is_scalar(x_143)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_143;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_152);
x_161 = l_ReaderT_instMonad___redArg(x_160);
x_162 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_161, x_2, x_150);
x_163 = lean_apply_6(x_162, x_3, x_4, x_5, x_6, x_7, x_8);
return x_163;
}
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
lean_dec_ref(x_5);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_14);
x_15 = 0;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_16 = l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(x_15, x_12, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_st_ref_get(x_3, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_22);
lean_dec(x_20);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_23 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
lean_inc(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_24);
x_27 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(x_3, x_22, x_26, x_25);
lean_dec_ref(x_26);
lean_dec(x_3);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_29);
lean_dec(x_10);
x_30 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_29, x_15, x_13);
lean_dec_ref(x_29);
x_31 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_2, x_30, x_17, x_24, x_4, x_5, x_6, x_7, x_28);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_17);
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_dec_ref(x_23);
x_34 = lean_box(0);
x_35 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(x_3, x_22, x_34, x_33);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 0, x_32);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_40 = !lean_is_exclusive(x_16);
if (x_40 == 0)
{
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
x_11 = lean_st_ref_get(x_3, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_3, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_14, x_1, x_9);
lean_dec_ref(x_14);
x_20 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(x_18, x_10, x_1);
lean_dec_ref(x_18);
x_21 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(x_2, x_19, x_20, x_4, x_5, x_6, x_7, x_17);
return x_21;
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
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(x_8, x_2, x_1);
lean_dec_ref(x_8);
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
lean_inc_ref(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(x_12, x_2, x_1);
lean_dec_ref(x_12);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go___lam__2(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_25; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_11);
x_12 = lean_st_ref_get(x_4, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
lean_dec(x_13);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_25 = l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(x_1, x_10, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
lean_inc(x_4);
x_28 = l_Lean_Compiler_LCNF_Code_cse_go(x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(x_3, x_26, x_29);
lean_inc_ref(x_31);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_Compiler_LCNF_Code_cse_go___lam__0(x_4, x_15, x_32, x_30);
lean_dec_ref(x_32);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_26);
lean_dec_ref(x_3);
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_dec_ref(x_28);
x_16 = x_38;
x_17 = x_39;
goto block_24;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_40 = lean_ctor_get(x_25, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_25, 1);
lean_inc(x_41);
lean_dec_ref(x_25);
x_16 = x_40;
x_17 = x_41;
goto block_24;
}
block_24:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_box(0);
x_19 = l_Lean_Compiler_LCNF_Code_cse_go___lam__0(x_4, x_15, x_18, x_17);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_16);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_42);
x_43 = lean_st_ref_get(x_4, x_9);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc_ref(x_46);
lean_dec(x_44);
lean_inc(x_4);
x_47 = l_Lean_Compiler_LCNF_Code_cse_go(x_2, x_42, x_4, x_5, x_6, x_7, x_8, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
lean_inc_ref(x_3);
x_50 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_3, x_48);
x_51 = !lean_is_exclusive(x_3);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_3, 0);
lean_dec(x_52);
lean_inc_ref(x_50);
lean_ctor_set(x_3, 0, x_50);
x_53 = l_Lean_Compiler_LCNF_Code_cse_go___lam__0(x_4, x_46, x_3, x_49);
lean_dec_ref(x_3);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_50);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_3);
lean_inc_ref(x_50);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_50);
x_59 = l_Lean_Compiler_LCNF_Code_cse_go___lam__0(x_4, x_46, x_58, x_49);
lean_dec_ref(x_58);
lean_dec(x_4);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_50);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec_ref(x_3);
x_63 = lean_ctor_get(x_47, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_47, 1);
lean_inc(x_64);
lean_dec_ref(x_47);
x_65 = lean_box(0);
x_66 = l_Lean_Compiler_LCNF_Code_cse_go___lam__0(x_4, x_46, x_65, x_64);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set_tag(x_66, 1);
lean_ctor_set(x_66, 0, x_63);
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_69);
return x_70;
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
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1;
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_ctor_get(x_11, 3);
x_17 = lean_ctor_get(x_11, 4);
x_18 = lean_ctor_get(x_11, 1);
lean_dec(x_18);
x_19 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2;
x_20 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__3;
lean_inc_ref(x_14);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_21, 0, x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_17);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_16);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_26, 0, x_15);
lean_ctor_set(x_11, 4, x_24);
lean_ctor_set(x_11, 3, x_25);
lean_ctor_set(x_11, 2, x_26);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_11, 0, x_23);
lean_ctor_set(x_9, 1, x_20);
x_27 = l_ReaderT_instMonad___redArg(x_9);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 2);
x_34 = lean_ctor_get(x_29, 3);
x_35 = lean_ctor_get(x_29, 4);
x_36 = lean_ctor_get(x_29, 1);
lean_dec(x_36);
x_37 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4;
x_38 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5;
lean_inc_ref(x_32);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_39, 0, x_32);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_40, 0, x_32);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_35);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_34);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_44, 0, x_33);
lean_ctor_set(x_29, 4, x_42);
lean_ctor_set(x_29, 3, x_43);
lean_ctor_set(x_29, 2, x_44);
lean_ctor_set(x_29, 1, x_37);
lean_ctor_set(x_29, 0, x_41);
lean_ctor_set(x_27, 1, x_38);
x_45 = l_ReaderT_instMonad___redArg(x_27);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec_ref(x_45);
x_46 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_47);
x_48 = 0;
x_49 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0(x_48, x_46, x_3, x_4, x_5, x_6, x_7, x_8);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 3);
lean_inc(x_53);
lean_inc(x_53);
x_54 = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(x_53, x_7, x_51);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec_ref(x_54);
x_58 = lean_st_ref_get(x_3, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_61);
lean_dec(x_59);
x_62 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_53);
x_63 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0;
x_64 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1;
lean_inc_ref(x_62);
x_65 = l_Lean_PersistentHashMap_find_x3f___redArg(x_63, x_64, x_61, x_62);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_st_ref_take(x_3, x_60);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec_ref(x_66);
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_67, 0);
x_71 = l_Lean_PersistentHashMap_insert___redArg(x_63, x_64, x_70, x_62, x_52);
lean_ctor_set(x_67, 0, x_71);
x_72 = lean_st_ref_set(x_3, x_67, x_68);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_47, x_3, x_4, x_5, x_6, x_7, x_73);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_2, x_50, x_76);
lean_dec_ref(x_2);
lean_ctor_set(x_74, 0, x_77);
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_74, 0);
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_74);
x_80 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_2, x_50, x_78);
lean_dec_ref(x_2);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
else
{
lean_dec(x_50);
lean_dec_ref(x_2);
return x_74;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_82 = lean_ctor_get(x_67, 0);
x_83 = lean_ctor_get(x_67, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_67);
x_84 = l_Lean_PersistentHashMap_insert___redArg(x_63, x_64, x_82, x_62, x_52);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = lean_st_ref_set(x_3, x_85, x_68);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_47, x_3, x_4, x_5, x_6, x_7, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
x_92 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_2, x_50, x_89);
lean_dec_ref(x_2);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_dec(x_50);
lean_dec_ref(x_2);
return x_88;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec_ref(x_62);
lean_dec(x_52);
lean_dec_ref(x_2);
x_94 = lean_ctor_get(x_65, 0);
lean_inc(x_94);
lean_dec_ref(x_65);
x_95 = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(x_50, x_94, x_3, x_5, x_60);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec_ref(x_95);
x_2 = x_47;
x_8 = x_96;
goto _start;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_53);
lean_dec(x_52);
x_98 = lean_ctor_get(x_54, 1);
lean_inc(x_98);
lean_dec_ref(x_54);
x_99 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_47, x_3, x_4, x_5, x_6, x_7, x_98);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_2, x_50, x_101);
lean_dec_ref(x_2);
lean_ctor_set(x_99, 0, x_102);
return x_99;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_99, 0);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_99);
x_105 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_2, x_50, x_103);
lean_dec_ref(x_2);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_dec(x_50);
lean_dec_ref(x_2);
return x_99;
}
}
}
case 1:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec_ref(x_45);
x_107 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_108);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_109 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_1, x_107, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_109) == 0)
{
if (x_1 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec_ref(x_109);
x_112 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_108, x_3, x_4, x_5, x_6, x_7, x_111);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_112, 0);
x_115 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_110, x_114);
lean_dec_ref(x_2);
lean_ctor_set(x_112, 0, x_115);
return x_112;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_112, 0);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_112);
x_118 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_110, x_116);
lean_dec_ref(x_2);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_dec(x_110);
lean_dec_ref(x_2);
return x_112;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_120 = lean_ctor_get(x_109, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_109, 1);
lean_inc(x_121);
lean_dec_ref(x_109);
x_122 = lean_st_ref_get(x_3, x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec_ref(x_122);
x_125 = lean_ctor_get(x_123, 0);
lean_inc_ref(x_125);
lean_dec(x_123);
x_126 = l_Lean_Compiler_LCNF_Code_cse_go___closed__0;
lean_inc(x_120);
x_127 = l_Lean_Compiler_LCNF_FunDecl_toExpr(x_120, x_126);
x_128 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0;
x_129 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1;
lean_inc_ref(x_127);
x_130 = l_Lean_PersistentHashMap_find_x3f___redArg(x_128, x_129, x_125, x_127);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_131 = lean_st_ref_take(x_3, x_124);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec_ref(x_131);
x_134 = lean_ctor_get(x_120, 0);
lean_inc(x_134);
x_135 = !lean_is_exclusive(x_132);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_132, 0);
x_137 = l_Lean_PersistentHashMap_insert___redArg(x_128, x_129, x_136, x_127, x_134);
lean_ctor_set(x_132, 0, x_137);
x_138 = lean_st_ref_set(x_3, x_132, x_133);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec_ref(x_138);
x_140 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_108, x_3, x_4, x_5, x_6, x_7, x_139);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_140, 0);
x_143 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_120, x_142);
lean_dec_ref(x_2);
lean_ctor_set(x_140, 0, x_143);
return x_140;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_140, 0);
x_145 = lean_ctor_get(x_140, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_140);
x_146 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_120, x_144);
lean_dec_ref(x_2);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_dec(x_120);
lean_dec_ref(x_2);
return x_140;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_148 = lean_ctor_get(x_132, 0);
x_149 = lean_ctor_get(x_132, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_132);
x_150 = l_Lean_PersistentHashMap_insert___redArg(x_128, x_129, x_148, x_127, x_134);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_149);
x_152 = lean_st_ref_set(x_3, x_151, x_133);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec_ref(x_152);
x_154 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_108, x_3, x_4, x_5, x_6, x_7, x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_157 = x_154;
} else {
 lean_dec_ref(x_154);
 x_157 = lean_box(0);
}
x_158 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_120, x_155);
lean_dec_ref(x_2);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_156);
return x_159;
}
else
{
lean_dec(x_120);
lean_dec_ref(x_2);
return x_154;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec_ref(x_127);
lean_dec_ref(x_2);
x_160 = lean_ctor_get(x_130, 0);
lean_inc(x_160);
lean_dec_ref(x_130);
x_161 = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(x_120, x_160, x_3, x_5, x_124);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec_ref(x_161);
x_2 = x_108;
x_8 = x_162;
goto _start;
}
}
}
else
{
uint8_t x_164; 
lean_dec_ref(x_108);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_164 = !lean_is_exclusive(x_109);
if (x_164 == 0)
{
return x_109;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_109, 0);
x_166 = lean_ctor_get(x_109, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_109);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
case 2:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec_ref(x_45);
x_168 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_168);
x_169 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_169);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_170 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_1, x_168, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec_ref(x_170);
x_173 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_169, x_3, x_4, x_5, x_6, x_7, x_172);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_173, 0);
x_176 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_171, x_175);
lean_dec_ref(x_2);
lean_ctor_set(x_173, 0, x_176);
return x_173;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_173, 0);
x_178 = lean_ctor_get(x_173, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_173);
x_179 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_171, x_177);
lean_dec_ref(x_2);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
else
{
lean_dec(x_171);
lean_dec_ref(x_2);
return x_173;
}
}
else
{
uint8_t x_181; 
lean_dec_ref(x_169);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_181 = !lean_is_exclusive(x_170);
if (x_181 == 0)
{
return x_170;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_170, 0);
x_183 = lean_ctor_get(x_170, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_170);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
case 3:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; 
lean_dec_ref(x_45);
x_185 = lean_ctor_get(x_2, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_186);
x_187 = lean_st_ref_get(x_3, x_8);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec_ref(x_187);
x_190 = lean_ctor_get(x_188, 1);
lean_inc_ref(x_190);
lean_dec(x_188);
x_191 = 0;
x_192 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_190, x_185, x_191);
lean_dec_ref(x_190);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
lean_dec_ref(x_192);
x_194 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1___redArg(x_191, x_186, x_3, x_189);
lean_dec(x_3);
x_195 = !lean_is_exclusive(x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_194, 0);
x_197 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp(x_2, x_193, x_196);
lean_dec_ref(x_2);
lean_ctor_set(x_194, 0, x_197);
return x_194;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_194, 0);
x_199 = lean_ctor_get(x_194, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_194);
x_200 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp(x_2, x_193, x_198);
lean_dec_ref(x_2);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
else
{
lean_object* x_202; 
lean_dec_ref(x_186);
lean_dec(x_3);
lean_dec_ref(x_2);
x_202 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_189);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_202;
}
}
case 4:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; 
x_203 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_203);
x_204 = lean_st_ref_get(x_3, x_8);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec_ref(x_204);
x_207 = lean_ctor_get(x_203, 1);
lean_inc_ref(x_207);
x_208 = lean_ctor_get(x_203, 2);
lean_inc(x_208);
x_209 = lean_ctor_get(x_203, 3);
lean_inc_ref(x_209);
lean_dec_ref(x_203);
x_210 = lean_ctor_get(x_205, 1);
lean_inc_ref(x_210);
lean_dec(x_205);
x_211 = 0;
x_212 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_210, x_208, x_211);
lean_dec_ref(x_210);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
lean_dec_ref(x_212);
x_214 = lean_st_ref_get(x_3, x_206);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec_ref(x_214);
x_217 = lean_box(x_211);
x_218 = lean_box(x_1);
x_219 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_cse_go___lam__2___boxed), 9, 2);
lean_closure_set(x_219, 0, x_217);
lean_closure_set(x_219, 1, x_218);
x_220 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_45, x_209, x_219);
x_221 = lean_apply_6(x_220, x_3, x_4, x_5, x_6, x_7, x_216);
if (lean_obj_tag(x_221) == 0)
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_223 = lean_ctor_get(x_221, 0);
x_224 = lean_ctor_get(x_215, 1);
lean_inc_ref(x_224);
lean_dec(x_215);
x_225 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_224, x_211, x_207);
lean_dec_ref(x_224);
x_226 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(x_2, x_225, x_213, x_223);
lean_ctor_set(x_221, 0, x_226);
return x_221;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_227 = lean_ctor_get(x_221, 0);
x_228 = lean_ctor_get(x_221, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_221);
x_229 = lean_ctor_get(x_215, 1);
lean_inc_ref(x_229);
lean_dec(x_215);
x_230 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_229, x_211, x_207);
lean_dec_ref(x_229);
x_231 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(x_2, x_230, x_213, x_227);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_228);
return x_232;
}
}
else
{
uint8_t x_233; 
lean_dec(x_215);
lean_dec(x_213);
lean_dec_ref(x_207);
lean_dec_ref(x_2);
x_233 = !lean_is_exclusive(x_221);
if (x_233 == 0)
{
return x_221;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_221, 0);
x_235 = lean_ctor_get(x_221, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_221);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
else
{
lean_object* x_237; 
lean_dec_ref(x_209);
lean_dec_ref(x_207);
lean_dec_ref(x_45);
lean_dec(x_3);
lean_dec_ref(x_2);
x_237 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_206);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_237;
}
}
case 5:
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
lean_dec_ref(x_45);
x_238 = lean_ctor_get(x_2, 0);
lean_inc(x_238);
x_239 = lean_st_ref_get(x_3, x_8);
lean_dec(x_3);
x_240 = !lean_is_exclusive(x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; 
x_241 = lean_ctor_get(x_239, 0);
x_242 = lean_ctor_get(x_239, 1);
x_243 = lean_ctor_get(x_241, 1);
lean_inc_ref(x_243);
lean_dec(x_241);
x_244 = 0;
x_245 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_243, x_238, x_244);
lean_dec_ref(x_243);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec_ref(x_245);
x_247 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(x_2, x_246);
lean_ctor_set(x_239, 0, x_247);
return x_239;
}
else
{
lean_object* x_248; 
lean_free_object(x_239);
lean_dec_ref(x_2);
x_248 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_242);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; 
x_249 = lean_ctor_get(x_239, 0);
x_250 = lean_ctor_get(x_239, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_239);
x_251 = lean_ctor_get(x_249, 1);
lean_inc_ref(x_251);
lean_dec(x_249);
x_252 = 0;
x_253 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_251, x_238, x_252);
lean_dec_ref(x_251);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec_ref(x_253);
x_255 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(x_2, x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_250);
return x_256;
}
else
{
lean_object* x_257; 
lean_dec_ref(x_2);
x_257 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_250);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_257;
}
}
}
default: 
{
lean_object* x_258; 
lean_dec_ref(x_45);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_2);
lean_ctor_set(x_258, 1, x_8);
return x_258;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_259 = lean_ctor_get(x_29, 0);
x_260 = lean_ctor_get(x_29, 2);
x_261 = lean_ctor_get(x_29, 3);
x_262 = lean_ctor_get(x_29, 4);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_29);
x_263 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4;
x_264 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5;
lean_inc_ref(x_259);
x_265 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_265, 0, x_259);
x_266 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_266, 0, x_259);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
x_268 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_268, 0, x_262);
x_269 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_269, 0, x_261);
x_270 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_270, 0, x_260);
x_271 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_271, 0, x_267);
lean_ctor_set(x_271, 1, x_263);
lean_ctor_set(x_271, 2, x_270);
lean_ctor_set(x_271, 3, x_269);
lean_ctor_set(x_271, 4, x_268);
lean_ctor_set(x_27, 1, x_264);
lean_ctor_set(x_27, 0, x_271);
x_272 = l_ReaderT_instMonad___redArg(x_27);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
lean_dec_ref(x_272);
x_273 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_273);
x_274 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_274);
x_275 = 0;
x_276 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0(x_275, x_273, x_3, x_4, x_5, x_6, x_7, x_8);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec_ref(x_276);
x_279 = lean_ctor_get(x_277, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_277, 3);
lean_inc(x_280);
lean_inc(x_280);
x_281 = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(x_280, x_7, x_278);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_unbox(x_282);
lean_dec(x_282);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_284 = lean_ctor_get(x_281, 1);
lean_inc(x_284);
lean_dec_ref(x_281);
x_285 = lean_st_ref_get(x_3, x_284);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec_ref(x_285);
x_288 = lean_ctor_get(x_286, 0);
lean_inc_ref(x_288);
lean_dec(x_286);
x_289 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_280);
x_290 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0;
x_291 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1;
lean_inc_ref(x_289);
x_292 = l_Lean_PersistentHashMap_find_x3f___redArg(x_290, x_291, x_288, x_289);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_293 = lean_st_ref_take(x_3, x_287);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec_ref(x_293);
x_296 = lean_ctor_get(x_294, 0);
lean_inc_ref(x_296);
x_297 = lean_ctor_get(x_294, 1);
lean_inc_ref(x_297);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 lean_ctor_release(x_294, 1);
 x_298 = x_294;
} else {
 lean_dec_ref(x_294);
 x_298 = lean_box(0);
}
x_299 = l_Lean_PersistentHashMap_insert___redArg(x_290, x_291, x_296, x_289, x_279);
if (lean_is_scalar(x_298)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_298;
}
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_297);
x_301 = lean_st_ref_set(x_3, x_300, x_295);
x_302 = lean_ctor_get(x_301, 1);
lean_inc(x_302);
lean_dec_ref(x_301);
x_303 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_274, x_3, x_4, x_5, x_6, x_7, x_302);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_306 = x_303;
} else {
 lean_dec_ref(x_303);
 x_306 = lean_box(0);
}
x_307 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_2, x_277, x_304);
lean_dec_ref(x_2);
if (lean_is_scalar(x_306)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_306;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_305);
return x_308;
}
else
{
lean_dec(x_277);
lean_dec_ref(x_2);
return x_303;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec_ref(x_289);
lean_dec(x_279);
lean_dec_ref(x_2);
x_309 = lean_ctor_get(x_292, 0);
lean_inc(x_309);
lean_dec_ref(x_292);
x_310 = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(x_277, x_309, x_3, x_5, x_287);
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
lean_dec_ref(x_310);
x_2 = x_274;
x_8 = x_311;
goto _start;
}
}
else
{
lean_object* x_313; lean_object* x_314; 
lean_dec(x_280);
lean_dec(x_279);
x_313 = lean_ctor_get(x_281, 1);
lean_inc(x_313);
lean_dec_ref(x_281);
x_314 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_274, x_3, x_4, x_5, x_6, x_7, x_313);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_317 = x_314;
} else {
 lean_dec_ref(x_314);
 x_317 = lean_box(0);
}
x_318 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_2, x_277, x_315);
lean_dec_ref(x_2);
if (lean_is_scalar(x_317)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_317;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_316);
return x_319;
}
else
{
lean_dec(x_277);
lean_dec_ref(x_2);
return x_314;
}
}
}
case 1:
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_dec_ref(x_272);
x_320 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_320);
x_321 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_321);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_322 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_1, x_320, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_322) == 0)
{
if (x_1 == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec_ref(x_322);
x_325 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_321, x_3, x_4, x_5, x_6, x_7, x_324);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_328 = x_325;
} else {
 lean_dec_ref(x_325);
 x_328 = lean_box(0);
}
x_329 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_323, x_326);
lean_dec_ref(x_2);
if (lean_is_scalar(x_328)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_328;
}
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_327);
return x_330;
}
else
{
lean_dec(x_323);
lean_dec_ref(x_2);
return x_325;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_331 = lean_ctor_get(x_322, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_322, 1);
lean_inc(x_332);
lean_dec_ref(x_322);
x_333 = lean_st_ref_get(x_3, x_332);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
lean_dec_ref(x_333);
x_336 = lean_ctor_get(x_334, 0);
lean_inc_ref(x_336);
lean_dec(x_334);
x_337 = l_Lean_Compiler_LCNF_Code_cse_go___closed__0;
lean_inc(x_331);
x_338 = l_Lean_Compiler_LCNF_FunDecl_toExpr(x_331, x_337);
x_339 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0;
x_340 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1;
lean_inc_ref(x_338);
x_341 = l_Lean_PersistentHashMap_find_x3f___redArg(x_339, x_340, x_336, x_338);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_342 = lean_st_ref_take(x_3, x_335);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec_ref(x_342);
x_345 = lean_ctor_get(x_331, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_343, 0);
lean_inc_ref(x_346);
x_347 = lean_ctor_get(x_343, 1);
lean_inc_ref(x_347);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_348 = x_343;
} else {
 lean_dec_ref(x_343);
 x_348 = lean_box(0);
}
x_349 = l_Lean_PersistentHashMap_insert___redArg(x_339, x_340, x_346, x_338, x_345);
if (lean_is_scalar(x_348)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_348;
}
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_347);
x_351 = lean_st_ref_set(x_3, x_350, x_344);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
lean_dec_ref(x_351);
x_353 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_321, x_3, x_4, x_5, x_6, x_7, x_352);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_356 = x_353;
} else {
 lean_dec_ref(x_353);
 x_356 = lean_box(0);
}
x_357 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_331, x_354);
lean_dec_ref(x_2);
if (lean_is_scalar(x_356)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_356;
}
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_355);
return x_358;
}
else
{
lean_dec(x_331);
lean_dec_ref(x_2);
return x_353;
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec_ref(x_338);
lean_dec_ref(x_2);
x_359 = lean_ctor_get(x_341, 0);
lean_inc(x_359);
lean_dec_ref(x_341);
x_360 = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(x_331, x_359, x_3, x_5, x_335);
x_361 = lean_ctor_get(x_360, 1);
lean_inc(x_361);
lean_dec_ref(x_360);
x_2 = x_321;
x_8 = x_361;
goto _start;
}
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec_ref(x_321);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_363 = lean_ctor_get(x_322, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_322, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 x_365 = x_322;
} else {
 lean_dec_ref(x_322);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 2, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_363);
lean_ctor_set(x_366, 1, x_364);
return x_366;
}
}
case 2:
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec_ref(x_272);
x_367 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_367);
x_368 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_368);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_369 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_1, x_367, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec_ref(x_369);
x_372 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_368, x_3, x_4, x_5, x_6, x_7, x_371);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_372, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_375 = x_372;
} else {
 lean_dec_ref(x_372);
 x_375 = lean_box(0);
}
x_376 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_370, x_373);
lean_dec_ref(x_2);
if (lean_is_scalar(x_375)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_375;
}
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_374);
return x_377;
}
else
{
lean_dec(x_370);
lean_dec_ref(x_2);
return x_372;
}
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec_ref(x_368);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_378 = lean_ctor_get(x_369, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_369, 1);
lean_inc(x_379);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_380 = x_369;
} else {
 lean_dec_ref(x_369);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(1, 2, 0);
} else {
 x_381 = x_380;
}
lean_ctor_set(x_381, 0, x_378);
lean_ctor_set(x_381, 1, x_379);
return x_381;
}
}
case 3:
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; 
lean_dec_ref(x_272);
x_382 = lean_ctor_get(x_2, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_383);
x_384 = lean_st_ref_get(x_3, x_8);
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec_ref(x_384);
x_387 = lean_ctor_get(x_385, 1);
lean_inc_ref(x_387);
lean_dec(x_385);
x_388 = 0;
x_389 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_387, x_382, x_388);
lean_dec_ref(x_387);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
lean_dec_ref(x_389);
x_391 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1___redArg(x_388, x_383, x_3, x_386);
lean_dec(x_3);
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_394 = x_391;
} else {
 lean_dec_ref(x_391);
 x_394 = lean_box(0);
}
x_395 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp(x_2, x_390, x_392);
lean_dec_ref(x_2);
if (lean_is_scalar(x_394)) {
 x_396 = lean_alloc_ctor(0, 2, 0);
} else {
 x_396 = x_394;
}
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_393);
return x_396;
}
else
{
lean_object* x_397; 
lean_dec_ref(x_383);
lean_dec(x_3);
lean_dec_ref(x_2);
x_397 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_386);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_397;
}
}
case 4:
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; 
x_398 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_398);
x_399 = lean_st_ref_get(x_3, x_8);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_399, 1);
lean_inc(x_401);
lean_dec_ref(x_399);
x_402 = lean_ctor_get(x_398, 1);
lean_inc_ref(x_402);
x_403 = lean_ctor_get(x_398, 2);
lean_inc(x_403);
x_404 = lean_ctor_get(x_398, 3);
lean_inc_ref(x_404);
lean_dec_ref(x_398);
x_405 = lean_ctor_get(x_400, 1);
lean_inc_ref(x_405);
lean_dec(x_400);
x_406 = 0;
x_407 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_405, x_403, x_406);
lean_dec_ref(x_405);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
lean_dec_ref(x_407);
x_409 = lean_st_ref_get(x_3, x_401);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec_ref(x_409);
x_412 = lean_box(x_406);
x_413 = lean_box(x_1);
x_414 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_cse_go___lam__2___boxed), 9, 2);
lean_closure_set(x_414, 0, x_412);
lean_closure_set(x_414, 1, x_413);
x_415 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_272, x_404, x_414);
x_416 = lean_apply_6(x_415, x_3, x_4, x_5, x_6, x_7, x_411);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_419 = x_416;
} else {
 lean_dec_ref(x_416);
 x_419 = lean_box(0);
}
x_420 = lean_ctor_get(x_410, 1);
lean_inc_ref(x_420);
lean_dec(x_410);
x_421 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_420, x_406, x_402);
lean_dec_ref(x_420);
x_422 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(x_2, x_421, x_408, x_417);
if (lean_is_scalar(x_419)) {
 x_423 = lean_alloc_ctor(0, 2, 0);
} else {
 x_423 = x_419;
}
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_418);
return x_423;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
lean_dec(x_410);
lean_dec(x_408);
lean_dec_ref(x_402);
lean_dec_ref(x_2);
x_424 = lean_ctor_get(x_416, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_416, 1);
lean_inc(x_425);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_426 = x_416;
} else {
 lean_dec_ref(x_416);
 x_426 = lean_box(0);
}
if (lean_is_scalar(x_426)) {
 x_427 = lean_alloc_ctor(1, 2, 0);
} else {
 x_427 = x_426;
}
lean_ctor_set(x_427, 0, x_424);
lean_ctor_set(x_427, 1, x_425);
return x_427;
}
}
else
{
lean_object* x_428; 
lean_dec_ref(x_404);
lean_dec_ref(x_402);
lean_dec_ref(x_272);
lean_dec(x_3);
lean_dec_ref(x_2);
x_428 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_401);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_428;
}
}
case 5:
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; lean_object* x_436; 
lean_dec_ref(x_272);
x_429 = lean_ctor_get(x_2, 0);
lean_inc(x_429);
x_430 = lean_st_ref_get(x_3, x_8);
lean_dec(x_3);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_433 = x_430;
} else {
 lean_dec_ref(x_430);
 x_433 = lean_box(0);
}
x_434 = lean_ctor_get(x_431, 1);
lean_inc_ref(x_434);
lean_dec(x_431);
x_435 = 0;
x_436 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_434, x_429, x_435);
lean_dec_ref(x_434);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
lean_dec_ref(x_436);
x_438 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(x_2, x_437);
if (lean_is_scalar(x_433)) {
 x_439 = lean_alloc_ctor(0, 2, 0);
} else {
 x_439 = x_433;
}
lean_ctor_set(x_439, 0, x_438);
lean_ctor_set(x_439, 1, x_432);
return x_439;
}
else
{
lean_object* x_440; 
lean_dec(x_433);
lean_dec_ref(x_2);
x_440 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_432);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_440;
}
}
default: 
{
lean_object* x_441; 
lean_dec_ref(x_272);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_2);
lean_ctor_set(x_441, 1, x_8);
return x_441;
}
}
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_442 = lean_ctor_get(x_27, 0);
lean_inc(x_442);
lean_dec(x_27);
x_443 = lean_ctor_get(x_442, 0);
lean_inc_ref(x_443);
x_444 = lean_ctor_get(x_442, 2);
lean_inc_ref(x_444);
x_445 = lean_ctor_get(x_442, 3);
lean_inc_ref(x_445);
x_446 = lean_ctor_get(x_442, 4);
lean_inc_ref(x_446);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 lean_ctor_release(x_442, 2);
 lean_ctor_release(x_442, 3);
 lean_ctor_release(x_442, 4);
 x_447 = x_442;
} else {
 lean_dec_ref(x_442);
 x_447 = lean_box(0);
}
x_448 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4;
x_449 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5;
lean_inc_ref(x_443);
x_450 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_450, 0, x_443);
x_451 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_451, 0, x_443);
x_452 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_452, 0, x_450);
lean_ctor_set(x_452, 1, x_451);
x_453 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_453, 0, x_446);
x_454 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_454, 0, x_445);
x_455 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_455, 0, x_444);
if (lean_is_scalar(x_447)) {
 x_456 = lean_alloc_ctor(0, 5, 0);
} else {
 x_456 = x_447;
}
lean_ctor_set(x_456, 0, x_452);
lean_ctor_set(x_456, 1, x_448);
lean_ctor_set(x_456, 2, x_455);
lean_ctor_set(x_456, 3, x_454);
lean_ctor_set(x_456, 4, x_453);
x_457 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_457, 0, x_456);
lean_ctor_set(x_457, 1, x_449);
x_458 = l_ReaderT_instMonad___redArg(x_457);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_459; lean_object* x_460; uint8_t x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; 
lean_dec_ref(x_458);
x_459 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_459);
x_460 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_460);
x_461 = 0;
x_462 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0(x_461, x_459, x_3, x_4, x_5, x_6, x_7, x_8);
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec_ref(x_462);
x_465 = lean_ctor_get(x_463, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_463, 3);
lean_inc(x_466);
lean_inc(x_466);
x_467 = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(x_466, x_7, x_464);
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_unbox(x_468);
lean_dec(x_468);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_470 = lean_ctor_get(x_467, 1);
lean_inc(x_470);
lean_dec_ref(x_467);
x_471 = lean_st_ref_get(x_3, x_470);
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_471, 1);
lean_inc(x_473);
lean_dec_ref(x_471);
x_474 = lean_ctor_get(x_472, 0);
lean_inc_ref(x_474);
lean_dec(x_472);
x_475 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_466);
x_476 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0;
x_477 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1;
lean_inc_ref(x_475);
x_478 = l_Lean_PersistentHashMap_find_x3f___redArg(x_476, x_477, x_474, x_475);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_479 = lean_st_ref_take(x_3, x_473);
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_479, 1);
lean_inc(x_481);
lean_dec_ref(x_479);
x_482 = lean_ctor_get(x_480, 0);
lean_inc_ref(x_482);
x_483 = lean_ctor_get(x_480, 1);
lean_inc_ref(x_483);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 x_484 = x_480;
} else {
 lean_dec_ref(x_480);
 x_484 = lean_box(0);
}
x_485 = l_Lean_PersistentHashMap_insert___redArg(x_476, x_477, x_482, x_475, x_465);
if (lean_is_scalar(x_484)) {
 x_486 = lean_alloc_ctor(0, 2, 0);
} else {
 x_486 = x_484;
}
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_483);
x_487 = lean_st_ref_set(x_3, x_486, x_481);
x_488 = lean_ctor_get(x_487, 1);
lean_inc(x_488);
lean_dec_ref(x_487);
x_489 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_460, x_3, x_4, x_5, x_6, x_7, x_488);
if (lean_obj_tag(x_489) == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_490 = lean_ctor_get(x_489, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_489, 1);
lean_inc(x_491);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 lean_ctor_release(x_489, 1);
 x_492 = x_489;
} else {
 lean_dec_ref(x_489);
 x_492 = lean_box(0);
}
x_493 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_2, x_463, x_490);
lean_dec_ref(x_2);
if (lean_is_scalar(x_492)) {
 x_494 = lean_alloc_ctor(0, 2, 0);
} else {
 x_494 = x_492;
}
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_491);
return x_494;
}
else
{
lean_dec(x_463);
lean_dec_ref(x_2);
return x_489;
}
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
lean_dec_ref(x_475);
lean_dec(x_465);
lean_dec_ref(x_2);
x_495 = lean_ctor_get(x_478, 0);
lean_inc(x_495);
lean_dec_ref(x_478);
x_496 = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(x_463, x_495, x_3, x_5, x_473);
x_497 = lean_ctor_get(x_496, 1);
lean_inc(x_497);
lean_dec_ref(x_496);
x_2 = x_460;
x_8 = x_497;
goto _start;
}
}
else
{
lean_object* x_499; lean_object* x_500; 
lean_dec(x_466);
lean_dec(x_465);
x_499 = lean_ctor_get(x_467, 1);
lean_inc(x_499);
lean_dec_ref(x_467);
x_500 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_460, x_3, x_4, x_5, x_6, x_7, x_499);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 x_503 = x_500;
} else {
 lean_dec_ref(x_500);
 x_503 = lean_box(0);
}
x_504 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_2, x_463, x_501);
lean_dec_ref(x_2);
if (lean_is_scalar(x_503)) {
 x_505 = lean_alloc_ctor(0, 2, 0);
} else {
 x_505 = x_503;
}
lean_ctor_set(x_505, 0, x_504);
lean_ctor_set(x_505, 1, x_502);
return x_505;
}
else
{
lean_dec(x_463);
lean_dec_ref(x_2);
return x_500;
}
}
}
case 1:
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec_ref(x_458);
x_506 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_506);
x_507 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_507);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_508 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_1, x_506, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_508) == 0)
{
if (x_1 == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec_ref(x_508);
x_511 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_507, x_3, x_4, x_5, x_6, x_7, x_510);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_514 = x_511;
} else {
 lean_dec_ref(x_511);
 x_514 = lean_box(0);
}
x_515 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_509, x_512);
lean_dec_ref(x_2);
if (lean_is_scalar(x_514)) {
 x_516 = lean_alloc_ctor(0, 2, 0);
} else {
 x_516 = x_514;
}
lean_ctor_set(x_516, 0, x_515);
lean_ctor_set(x_516, 1, x_513);
return x_516;
}
else
{
lean_dec(x_509);
lean_dec_ref(x_2);
return x_511;
}
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_517 = lean_ctor_get(x_508, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_508, 1);
lean_inc(x_518);
lean_dec_ref(x_508);
x_519 = lean_st_ref_get(x_3, x_518);
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_519, 1);
lean_inc(x_521);
lean_dec_ref(x_519);
x_522 = lean_ctor_get(x_520, 0);
lean_inc_ref(x_522);
lean_dec(x_520);
x_523 = l_Lean_Compiler_LCNF_Code_cse_go___closed__0;
lean_inc(x_517);
x_524 = l_Lean_Compiler_LCNF_FunDecl_toExpr(x_517, x_523);
x_525 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0;
x_526 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1;
lean_inc_ref(x_524);
x_527 = l_Lean_PersistentHashMap_find_x3f___redArg(x_525, x_526, x_522, x_524);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_528 = lean_st_ref_take(x_3, x_521);
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_528, 1);
lean_inc(x_530);
lean_dec_ref(x_528);
x_531 = lean_ctor_get(x_517, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_529, 0);
lean_inc_ref(x_532);
x_533 = lean_ctor_get(x_529, 1);
lean_inc_ref(x_533);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 lean_ctor_release(x_529, 1);
 x_534 = x_529;
} else {
 lean_dec_ref(x_529);
 x_534 = lean_box(0);
}
x_535 = l_Lean_PersistentHashMap_insert___redArg(x_525, x_526, x_532, x_524, x_531);
if (lean_is_scalar(x_534)) {
 x_536 = lean_alloc_ctor(0, 2, 0);
} else {
 x_536 = x_534;
}
lean_ctor_set(x_536, 0, x_535);
lean_ctor_set(x_536, 1, x_533);
x_537 = lean_st_ref_set(x_3, x_536, x_530);
x_538 = lean_ctor_get(x_537, 1);
lean_inc(x_538);
lean_dec_ref(x_537);
x_539 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_507, x_3, x_4, x_5, x_6, x_7, x_538);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 lean_ctor_release(x_539, 1);
 x_542 = x_539;
} else {
 lean_dec_ref(x_539);
 x_542 = lean_box(0);
}
x_543 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_517, x_540);
lean_dec_ref(x_2);
if (lean_is_scalar(x_542)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_542;
}
lean_ctor_set(x_544, 0, x_543);
lean_ctor_set(x_544, 1, x_541);
return x_544;
}
else
{
lean_dec(x_517);
lean_dec_ref(x_2);
return x_539;
}
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; 
lean_dec_ref(x_524);
lean_dec_ref(x_2);
x_545 = lean_ctor_get(x_527, 0);
lean_inc(x_545);
lean_dec_ref(x_527);
x_546 = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(x_517, x_545, x_3, x_5, x_521);
x_547 = lean_ctor_get(x_546, 1);
lean_inc(x_547);
lean_dec_ref(x_546);
x_2 = x_507;
x_8 = x_547;
goto _start;
}
}
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec_ref(x_507);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_549 = lean_ctor_get(x_508, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_508, 1);
lean_inc(x_550);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_551 = x_508;
} else {
 lean_dec_ref(x_508);
 x_551 = lean_box(0);
}
if (lean_is_scalar(x_551)) {
 x_552 = lean_alloc_ctor(1, 2, 0);
} else {
 x_552 = x_551;
}
lean_ctor_set(x_552, 0, x_549);
lean_ctor_set(x_552, 1, x_550);
return x_552;
}
}
case 2:
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
lean_dec_ref(x_458);
x_553 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_553);
x_554 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_554);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_555 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_1, x_553, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
lean_dec_ref(x_555);
x_558 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_554, x_3, x_4, x_5, x_6, x_7, x_557);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_558, 1);
lean_inc(x_560);
if (lean_is_exclusive(x_558)) {
 lean_ctor_release(x_558, 0);
 lean_ctor_release(x_558, 1);
 x_561 = x_558;
} else {
 lean_dec_ref(x_558);
 x_561 = lean_box(0);
}
x_562 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_556, x_559);
lean_dec_ref(x_2);
if (lean_is_scalar(x_561)) {
 x_563 = lean_alloc_ctor(0, 2, 0);
} else {
 x_563 = x_561;
}
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_560);
return x_563;
}
else
{
lean_dec(x_556);
lean_dec_ref(x_2);
return x_558;
}
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
lean_dec_ref(x_554);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_564 = lean_ctor_get(x_555, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_555, 1);
lean_inc(x_565);
if (lean_is_exclusive(x_555)) {
 lean_ctor_release(x_555, 0);
 lean_ctor_release(x_555, 1);
 x_566 = x_555;
} else {
 lean_dec_ref(x_555);
 x_566 = lean_box(0);
}
if (lean_is_scalar(x_566)) {
 x_567 = lean_alloc_ctor(1, 2, 0);
} else {
 x_567 = x_566;
}
lean_ctor_set(x_567, 0, x_564);
lean_ctor_set(x_567, 1, x_565);
return x_567;
}
}
case 3:
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; uint8_t x_574; lean_object* x_575; 
lean_dec_ref(x_458);
x_568 = lean_ctor_get(x_2, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_569);
x_570 = lean_st_ref_get(x_3, x_8);
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_570, 1);
lean_inc(x_572);
lean_dec_ref(x_570);
x_573 = lean_ctor_get(x_571, 1);
lean_inc_ref(x_573);
lean_dec(x_571);
x_574 = 0;
x_575 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_573, x_568, x_574);
lean_dec_ref(x_573);
if (lean_obj_tag(x_575) == 0)
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_576 = lean_ctor_get(x_575, 0);
lean_inc(x_576);
lean_dec_ref(x_575);
x_577 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1___redArg(x_574, x_569, x_3, x_572);
lean_dec(x_3);
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_577, 1);
lean_inc(x_579);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 lean_ctor_release(x_577, 1);
 x_580 = x_577;
} else {
 lean_dec_ref(x_577);
 x_580 = lean_box(0);
}
x_581 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp(x_2, x_576, x_578);
lean_dec_ref(x_2);
if (lean_is_scalar(x_580)) {
 x_582 = lean_alloc_ctor(0, 2, 0);
} else {
 x_582 = x_580;
}
lean_ctor_set(x_582, 0, x_581);
lean_ctor_set(x_582, 1, x_579);
return x_582;
}
else
{
lean_object* x_583; 
lean_dec_ref(x_569);
lean_dec(x_3);
lean_dec_ref(x_2);
x_583 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_572);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_583;
}
}
case 4:
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; uint8_t x_592; lean_object* x_593; 
x_584 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_584);
x_585 = lean_st_ref_get(x_3, x_8);
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
x_587 = lean_ctor_get(x_585, 1);
lean_inc(x_587);
lean_dec_ref(x_585);
x_588 = lean_ctor_get(x_584, 1);
lean_inc_ref(x_588);
x_589 = lean_ctor_get(x_584, 2);
lean_inc(x_589);
x_590 = lean_ctor_get(x_584, 3);
lean_inc_ref(x_590);
lean_dec_ref(x_584);
x_591 = lean_ctor_get(x_586, 1);
lean_inc_ref(x_591);
lean_dec(x_586);
x_592 = 0;
x_593 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_591, x_589, x_592);
lean_dec_ref(x_591);
if (lean_obj_tag(x_593) == 0)
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_594 = lean_ctor_get(x_593, 0);
lean_inc(x_594);
lean_dec_ref(x_593);
x_595 = lean_st_ref_get(x_3, x_587);
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_595, 1);
lean_inc(x_597);
lean_dec_ref(x_595);
x_598 = lean_box(x_592);
x_599 = lean_box(x_1);
x_600 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_cse_go___lam__2___boxed), 9, 2);
lean_closure_set(x_600, 0, x_598);
lean_closure_set(x_600, 1, x_599);
x_601 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_458, x_590, x_600);
x_602 = lean_apply_6(x_601, x_3, x_4, x_5, x_6, x_7, x_597);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_602, 1);
lean_inc(x_604);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 lean_ctor_release(x_602, 1);
 x_605 = x_602;
} else {
 lean_dec_ref(x_602);
 x_605 = lean_box(0);
}
x_606 = lean_ctor_get(x_596, 1);
lean_inc_ref(x_606);
lean_dec(x_596);
x_607 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_606, x_592, x_588);
lean_dec_ref(x_606);
x_608 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(x_2, x_607, x_594, x_603);
if (lean_is_scalar(x_605)) {
 x_609 = lean_alloc_ctor(0, 2, 0);
} else {
 x_609 = x_605;
}
lean_ctor_set(x_609, 0, x_608);
lean_ctor_set(x_609, 1, x_604);
return x_609;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_596);
lean_dec(x_594);
lean_dec_ref(x_588);
lean_dec_ref(x_2);
x_610 = lean_ctor_get(x_602, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_602, 1);
lean_inc(x_611);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 lean_ctor_release(x_602, 1);
 x_612 = x_602;
} else {
 lean_dec_ref(x_602);
 x_612 = lean_box(0);
}
if (lean_is_scalar(x_612)) {
 x_613 = lean_alloc_ctor(1, 2, 0);
} else {
 x_613 = x_612;
}
lean_ctor_set(x_613, 0, x_610);
lean_ctor_set(x_613, 1, x_611);
return x_613;
}
}
else
{
lean_object* x_614; 
lean_dec_ref(x_590);
lean_dec_ref(x_588);
lean_dec_ref(x_458);
lean_dec(x_3);
lean_dec_ref(x_2);
x_614 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_587);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_614;
}
}
case 5:
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; uint8_t x_621; lean_object* x_622; 
lean_dec_ref(x_458);
x_615 = lean_ctor_get(x_2, 0);
lean_inc(x_615);
x_616 = lean_st_ref_get(x_3, x_8);
lean_dec(x_3);
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_616, 1);
lean_inc(x_618);
if (lean_is_exclusive(x_616)) {
 lean_ctor_release(x_616, 0);
 lean_ctor_release(x_616, 1);
 x_619 = x_616;
} else {
 lean_dec_ref(x_616);
 x_619 = lean_box(0);
}
x_620 = lean_ctor_get(x_617, 1);
lean_inc_ref(x_620);
lean_dec(x_617);
x_621 = 0;
x_622 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_620, x_615, x_621);
lean_dec_ref(x_620);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_623 = lean_ctor_get(x_622, 0);
lean_inc(x_623);
lean_dec_ref(x_622);
x_624 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(x_2, x_623);
if (lean_is_scalar(x_619)) {
 x_625 = lean_alloc_ctor(0, 2, 0);
} else {
 x_625 = x_619;
}
lean_ctor_set(x_625, 0, x_624);
lean_ctor_set(x_625, 1, x_618);
return x_625;
}
else
{
lean_object* x_626; 
lean_dec(x_619);
lean_dec_ref(x_2);
x_626 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_618);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_626;
}
}
default: 
{
lean_object* x_627; 
lean_dec_ref(x_458);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_627 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_627, 0, x_2);
lean_ctor_set(x_627, 1, x_8);
return x_627;
}
}
}
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_628 = lean_ctor_get(x_11, 0);
x_629 = lean_ctor_get(x_11, 2);
x_630 = lean_ctor_get(x_11, 3);
x_631 = lean_ctor_get(x_11, 4);
lean_inc(x_631);
lean_inc(x_630);
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_11);
x_632 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2;
x_633 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__3;
lean_inc_ref(x_628);
x_634 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_634, 0, x_628);
x_635 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_635, 0, x_628);
x_636 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_636, 0, x_634);
lean_ctor_set(x_636, 1, x_635);
x_637 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_637, 0, x_631);
x_638 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_638, 0, x_630);
x_639 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_639, 0, x_629);
x_640 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_640, 0, x_636);
lean_ctor_set(x_640, 1, x_632);
lean_ctor_set(x_640, 2, x_639);
lean_ctor_set(x_640, 3, x_638);
lean_ctor_set(x_640, 4, x_637);
lean_ctor_set(x_9, 1, x_633);
lean_ctor_set(x_9, 0, x_640);
x_641 = l_ReaderT_instMonad___redArg(x_9);
x_642 = lean_ctor_get(x_641, 0);
lean_inc_ref(x_642);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_643 = x_641;
} else {
 lean_dec_ref(x_641);
 x_643 = lean_box(0);
}
x_644 = lean_ctor_get(x_642, 0);
lean_inc_ref(x_644);
x_645 = lean_ctor_get(x_642, 2);
lean_inc_ref(x_645);
x_646 = lean_ctor_get(x_642, 3);
lean_inc_ref(x_646);
x_647 = lean_ctor_get(x_642, 4);
lean_inc_ref(x_647);
if (lean_is_exclusive(x_642)) {
 lean_ctor_release(x_642, 0);
 lean_ctor_release(x_642, 1);
 lean_ctor_release(x_642, 2);
 lean_ctor_release(x_642, 3);
 lean_ctor_release(x_642, 4);
 x_648 = x_642;
} else {
 lean_dec_ref(x_642);
 x_648 = lean_box(0);
}
x_649 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4;
x_650 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5;
lean_inc_ref(x_644);
x_651 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_651, 0, x_644);
x_652 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_652, 0, x_644);
x_653 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_653, 0, x_651);
lean_ctor_set(x_653, 1, x_652);
x_654 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_654, 0, x_647);
x_655 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_655, 0, x_646);
x_656 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_656, 0, x_645);
if (lean_is_scalar(x_648)) {
 x_657 = lean_alloc_ctor(0, 5, 0);
} else {
 x_657 = x_648;
}
lean_ctor_set(x_657, 0, x_653);
lean_ctor_set(x_657, 1, x_649);
lean_ctor_set(x_657, 2, x_656);
lean_ctor_set(x_657, 3, x_655);
lean_ctor_set(x_657, 4, x_654);
if (lean_is_scalar(x_643)) {
 x_658 = lean_alloc_ctor(0, 2, 0);
} else {
 x_658 = x_643;
}
lean_ctor_set(x_658, 0, x_657);
lean_ctor_set(x_658, 1, x_650);
x_659 = l_ReaderT_instMonad___redArg(x_658);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_660; lean_object* x_661; uint8_t x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; uint8_t x_670; 
lean_dec_ref(x_659);
x_660 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_660);
x_661 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_661);
x_662 = 0;
x_663 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0(x_662, x_660, x_3, x_4, x_5, x_6, x_7, x_8);
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_663, 1);
lean_inc(x_665);
lean_dec_ref(x_663);
x_666 = lean_ctor_get(x_664, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_664, 3);
lean_inc(x_667);
lean_inc(x_667);
x_668 = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(x_667, x_7, x_665);
x_669 = lean_ctor_get(x_668, 0);
lean_inc(x_669);
x_670 = lean_unbox(x_669);
lean_dec(x_669);
if (x_670 == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_671 = lean_ctor_get(x_668, 1);
lean_inc(x_671);
lean_dec_ref(x_668);
x_672 = lean_st_ref_get(x_3, x_671);
x_673 = lean_ctor_get(x_672, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_672, 1);
lean_inc(x_674);
lean_dec_ref(x_672);
x_675 = lean_ctor_get(x_673, 0);
lean_inc_ref(x_675);
lean_dec(x_673);
x_676 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_667);
x_677 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0;
x_678 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1;
lean_inc_ref(x_676);
x_679 = l_Lean_PersistentHashMap_find_x3f___redArg(x_677, x_678, x_675, x_676);
if (lean_obj_tag(x_679) == 0)
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_680 = lean_st_ref_take(x_3, x_674);
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
lean_dec_ref(x_680);
x_683 = lean_ctor_get(x_681, 0);
lean_inc_ref(x_683);
x_684 = lean_ctor_get(x_681, 1);
lean_inc_ref(x_684);
if (lean_is_exclusive(x_681)) {
 lean_ctor_release(x_681, 0);
 lean_ctor_release(x_681, 1);
 x_685 = x_681;
} else {
 lean_dec_ref(x_681);
 x_685 = lean_box(0);
}
x_686 = l_Lean_PersistentHashMap_insert___redArg(x_677, x_678, x_683, x_676, x_666);
if (lean_is_scalar(x_685)) {
 x_687 = lean_alloc_ctor(0, 2, 0);
} else {
 x_687 = x_685;
}
lean_ctor_set(x_687, 0, x_686);
lean_ctor_set(x_687, 1, x_684);
x_688 = lean_st_ref_set(x_3, x_687, x_682);
x_689 = lean_ctor_get(x_688, 1);
lean_inc(x_689);
lean_dec_ref(x_688);
x_690 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_661, x_3, x_4, x_5, x_6, x_7, x_689);
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_690, 1);
lean_inc(x_692);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 x_693 = x_690;
} else {
 lean_dec_ref(x_690);
 x_693 = lean_box(0);
}
x_694 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_2, x_664, x_691);
lean_dec_ref(x_2);
if (lean_is_scalar(x_693)) {
 x_695 = lean_alloc_ctor(0, 2, 0);
} else {
 x_695 = x_693;
}
lean_ctor_set(x_695, 0, x_694);
lean_ctor_set(x_695, 1, x_692);
return x_695;
}
else
{
lean_dec(x_664);
lean_dec_ref(x_2);
return x_690;
}
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; 
lean_dec_ref(x_676);
lean_dec(x_666);
lean_dec_ref(x_2);
x_696 = lean_ctor_get(x_679, 0);
lean_inc(x_696);
lean_dec_ref(x_679);
x_697 = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(x_664, x_696, x_3, x_5, x_674);
x_698 = lean_ctor_get(x_697, 1);
lean_inc(x_698);
lean_dec_ref(x_697);
x_2 = x_661;
x_8 = x_698;
goto _start;
}
}
else
{
lean_object* x_700; lean_object* x_701; 
lean_dec(x_667);
lean_dec(x_666);
x_700 = lean_ctor_get(x_668, 1);
lean_inc(x_700);
lean_dec_ref(x_668);
x_701 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_661, x_3, x_4, x_5, x_6, x_7, x_700);
if (lean_obj_tag(x_701) == 0)
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_702 = lean_ctor_get(x_701, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_701, 1);
lean_inc(x_703);
if (lean_is_exclusive(x_701)) {
 lean_ctor_release(x_701, 0);
 lean_ctor_release(x_701, 1);
 x_704 = x_701;
} else {
 lean_dec_ref(x_701);
 x_704 = lean_box(0);
}
x_705 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_2, x_664, x_702);
lean_dec_ref(x_2);
if (lean_is_scalar(x_704)) {
 x_706 = lean_alloc_ctor(0, 2, 0);
} else {
 x_706 = x_704;
}
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_703);
return x_706;
}
else
{
lean_dec(x_664);
lean_dec_ref(x_2);
return x_701;
}
}
}
case 1:
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; 
lean_dec_ref(x_659);
x_707 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_707);
x_708 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_708);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_709 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_1, x_707, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_709) == 0)
{
if (x_1 == 0)
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; 
x_710 = lean_ctor_get(x_709, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_709, 1);
lean_inc(x_711);
lean_dec_ref(x_709);
x_712 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_708, x_3, x_4, x_5, x_6, x_7, x_711);
if (lean_obj_tag(x_712) == 0)
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_713 = lean_ctor_get(x_712, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_712, 1);
lean_inc(x_714);
if (lean_is_exclusive(x_712)) {
 lean_ctor_release(x_712, 0);
 lean_ctor_release(x_712, 1);
 x_715 = x_712;
} else {
 lean_dec_ref(x_712);
 x_715 = lean_box(0);
}
x_716 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_710, x_713);
lean_dec_ref(x_2);
if (lean_is_scalar(x_715)) {
 x_717 = lean_alloc_ctor(0, 2, 0);
} else {
 x_717 = x_715;
}
lean_ctor_set(x_717, 0, x_716);
lean_ctor_set(x_717, 1, x_714);
return x_717;
}
else
{
lean_dec(x_710);
lean_dec_ref(x_2);
return x_712;
}
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_718 = lean_ctor_get(x_709, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_709, 1);
lean_inc(x_719);
lean_dec_ref(x_709);
x_720 = lean_st_ref_get(x_3, x_719);
x_721 = lean_ctor_get(x_720, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_720, 1);
lean_inc(x_722);
lean_dec_ref(x_720);
x_723 = lean_ctor_get(x_721, 0);
lean_inc_ref(x_723);
lean_dec(x_721);
x_724 = l_Lean_Compiler_LCNF_Code_cse_go___closed__0;
lean_inc(x_718);
x_725 = l_Lean_Compiler_LCNF_FunDecl_toExpr(x_718, x_724);
x_726 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0;
x_727 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1;
lean_inc_ref(x_725);
x_728 = l_Lean_PersistentHashMap_find_x3f___redArg(x_726, x_727, x_723, x_725);
if (lean_obj_tag(x_728) == 0)
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_729 = lean_st_ref_take(x_3, x_722);
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_729, 1);
lean_inc(x_731);
lean_dec_ref(x_729);
x_732 = lean_ctor_get(x_718, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_730, 0);
lean_inc_ref(x_733);
x_734 = lean_ctor_get(x_730, 1);
lean_inc_ref(x_734);
if (lean_is_exclusive(x_730)) {
 lean_ctor_release(x_730, 0);
 lean_ctor_release(x_730, 1);
 x_735 = x_730;
} else {
 lean_dec_ref(x_730);
 x_735 = lean_box(0);
}
x_736 = l_Lean_PersistentHashMap_insert___redArg(x_726, x_727, x_733, x_725, x_732);
if (lean_is_scalar(x_735)) {
 x_737 = lean_alloc_ctor(0, 2, 0);
} else {
 x_737 = x_735;
}
lean_ctor_set(x_737, 0, x_736);
lean_ctor_set(x_737, 1, x_734);
x_738 = lean_st_ref_set(x_3, x_737, x_731);
x_739 = lean_ctor_get(x_738, 1);
lean_inc(x_739);
lean_dec_ref(x_738);
x_740 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_708, x_3, x_4, x_5, x_6, x_7, x_739);
if (lean_obj_tag(x_740) == 0)
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_741 = lean_ctor_get(x_740, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_740, 1);
lean_inc(x_742);
if (lean_is_exclusive(x_740)) {
 lean_ctor_release(x_740, 0);
 lean_ctor_release(x_740, 1);
 x_743 = x_740;
} else {
 lean_dec_ref(x_740);
 x_743 = lean_box(0);
}
x_744 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_718, x_741);
lean_dec_ref(x_2);
if (lean_is_scalar(x_743)) {
 x_745 = lean_alloc_ctor(0, 2, 0);
} else {
 x_745 = x_743;
}
lean_ctor_set(x_745, 0, x_744);
lean_ctor_set(x_745, 1, x_742);
return x_745;
}
else
{
lean_dec(x_718);
lean_dec_ref(x_2);
return x_740;
}
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; 
lean_dec_ref(x_725);
lean_dec_ref(x_2);
x_746 = lean_ctor_get(x_728, 0);
lean_inc(x_746);
lean_dec_ref(x_728);
x_747 = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(x_718, x_746, x_3, x_5, x_722);
x_748 = lean_ctor_get(x_747, 1);
lean_inc(x_748);
lean_dec_ref(x_747);
x_2 = x_708;
x_8 = x_748;
goto _start;
}
}
}
else
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
lean_dec_ref(x_708);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_750 = lean_ctor_get(x_709, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_709, 1);
lean_inc(x_751);
if (lean_is_exclusive(x_709)) {
 lean_ctor_release(x_709, 0);
 lean_ctor_release(x_709, 1);
 x_752 = x_709;
} else {
 lean_dec_ref(x_709);
 x_752 = lean_box(0);
}
if (lean_is_scalar(x_752)) {
 x_753 = lean_alloc_ctor(1, 2, 0);
} else {
 x_753 = x_752;
}
lean_ctor_set(x_753, 0, x_750);
lean_ctor_set(x_753, 1, x_751);
return x_753;
}
}
case 2:
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; 
lean_dec_ref(x_659);
x_754 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_754);
x_755 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_755);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_756 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_1, x_754, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_756) == 0)
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; 
x_757 = lean_ctor_get(x_756, 0);
lean_inc(x_757);
x_758 = lean_ctor_get(x_756, 1);
lean_inc(x_758);
lean_dec_ref(x_756);
x_759 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_755, x_3, x_4, x_5, x_6, x_7, x_758);
if (lean_obj_tag(x_759) == 0)
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; 
x_760 = lean_ctor_get(x_759, 0);
lean_inc(x_760);
x_761 = lean_ctor_get(x_759, 1);
lean_inc(x_761);
if (lean_is_exclusive(x_759)) {
 lean_ctor_release(x_759, 0);
 lean_ctor_release(x_759, 1);
 x_762 = x_759;
} else {
 lean_dec_ref(x_759);
 x_762 = lean_box(0);
}
x_763 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_757, x_760);
lean_dec_ref(x_2);
if (lean_is_scalar(x_762)) {
 x_764 = lean_alloc_ctor(0, 2, 0);
} else {
 x_764 = x_762;
}
lean_ctor_set(x_764, 0, x_763);
lean_ctor_set(x_764, 1, x_761);
return x_764;
}
else
{
lean_dec(x_757);
lean_dec_ref(x_2);
return x_759;
}
}
else
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
lean_dec_ref(x_755);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_765 = lean_ctor_get(x_756, 0);
lean_inc(x_765);
x_766 = lean_ctor_get(x_756, 1);
lean_inc(x_766);
if (lean_is_exclusive(x_756)) {
 lean_ctor_release(x_756, 0);
 lean_ctor_release(x_756, 1);
 x_767 = x_756;
} else {
 lean_dec_ref(x_756);
 x_767 = lean_box(0);
}
if (lean_is_scalar(x_767)) {
 x_768 = lean_alloc_ctor(1, 2, 0);
} else {
 x_768 = x_767;
}
lean_ctor_set(x_768, 0, x_765);
lean_ctor_set(x_768, 1, x_766);
return x_768;
}
}
case 3:
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; uint8_t x_775; lean_object* x_776; 
lean_dec_ref(x_659);
x_769 = lean_ctor_get(x_2, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_770);
x_771 = lean_st_ref_get(x_3, x_8);
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_771, 1);
lean_inc(x_773);
lean_dec_ref(x_771);
x_774 = lean_ctor_get(x_772, 1);
lean_inc_ref(x_774);
lean_dec(x_772);
x_775 = 0;
x_776 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_774, x_769, x_775);
lean_dec_ref(x_774);
if (lean_obj_tag(x_776) == 0)
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_777 = lean_ctor_get(x_776, 0);
lean_inc(x_777);
lean_dec_ref(x_776);
x_778 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1___redArg(x_775, x_770, x_3, x_773);
lean_dec(x_3);
x_779 = lean_ctor_get(x_778, 0);
lean_inc(x_779);
x_780 = lean_ctor_get(x_778, 1);
lean_inc(x_780);
if (lean_is_exclusive(x_778)) {
 lean_ctor_release(x_778, 0);
 lean_ctor_release(x_778, 1);
 x_781 = x_778;
} else {
 lean_dec_ref(x_778);
 x_781 = lean_box(0);
}
x_782 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp(x_2, x_777, x_779);
lean_dec_ref(x_2);
if (lean_is_scalar(x_781)) {
 x_783 = lean_alloc_ctor(0, 2, 0);
} else {
 x_783 = x_781;
}
lean_ctor_set(x_783, 0, x_782);
lean_ctor_set(x_783, 1, x_780);
return x_783;
}
else
{
lean_object* x_784; 
lean_dec_ref(x_770);
lean_dec(x_3);
lean_dec_ref(x_2);
x_784 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_773);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_784;
}
}
case 4:
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; uint8_t x_793; lean_object* x_794; 
x_785 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_785);
x_786 = lean_st_ref_get(x_3, x_8);
x_787 = lean_ctor_get(x_786, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_786, 1);
lean_inc(x_788);
lean_dec_ref(x_786);
x_789 = lean_ctor_get(x_785, 1);
lean_inc_ref(x_789);
x_790 = lean_ctor_get(x_785, 2);
lean_inc(x_790);
x_791 = lean_ctor_get(x_785, 3);
lean_inc_ref(x_791);
lean_dec_ref(x_785);
x_792 = lean_ctor_get(x_787, 1);
lean_inc_ref(x_792);
lean_dec(x_787);
x_793 = 0;
x_794 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_792, x_790, x_793);
lean_dec_ref(x_792);
if (lean_obj_tag(x_794) == 0)
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; 
x_795 = lean_ctor_get(x_794, 0);
lean_inc(x_795);
lean_dec_ref(x_794);
x_796 = lean_st_ref_get(x_3, x_788);
x_797 = lean_ctor_get(x_796, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_796, 1);
lean_inc(x_798);
lean_dec_ref(x_796);
x_799 = lean_box(x_793);
x_800 = lean_box(x_1);
x_801 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_cse_go___lam__2___boxed), 9, 2);
lean_closure_set(x_801, 0, x_799);
lean_closure_set(x_801, 1, x_800);
x_802 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_659, x_791, x_801);
x_803 = lean_apply_6(x_802, x_3, x_4, x_5, x_6, x_7, x_798);
if (lean_obj_tag(x_803) == 0)
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_804 = lean_ctor_get(x_803, 0);
lean_inc(x_804);
x_805 = lean_ctor_get(x_803, 1);
lean_inc(x_805);
if (lean_is_exclusive(x_803)) {
 lean_ctor_release(x_803, 0);
 lean_ctor_release(x_803, 1);
 x_806 = x_803;
} else {
 lean_dec_ref(x_803);
 x_806 = lean_box(0);
}
x_807 = lean_ctor_get(x_797, 1);
lean_inc_ref(x_807);
lean_dec(x_797);
x_808 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_807, x_793, x_789);
lean_dec_ref(x_807);
x_809 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(x_2, x_808, x_795, x_804);
if (lean_is_scalar(x_806)) {
 x_810 = lean_alloc_ctor(0, 2, 0);
} else {
 x_810 = x_806;
}
lean_ctor_set(x_810, 0, x_809);
lean_ctor_set(x_810, 1, x_805);
return x_810;
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
lean_dec(x_797);
lean_dec(x_795);
lean_dec_ref(x_789);
lean_dec_ref(x_2);
x_811 = lean_ctor_get(x_803, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_803, 1);
lean_inc(x_812);
if (lean_is_exclusive(x_803)) {
 lean_ctor_release(x_803, 0);
 lean_ctor_release(x_803, 1);
 x_813 = x_803;
} else {
 lean_dec_ref(x_803);
 x_813 = lean_box(0);
}
if (lean_is_scalar(x_813)) {
 x_814 = lean_alloc_ctor(1, 2, 0);
} else {
 x_814 = x_813;
}
lean_ctor_set(x_814, 0, x_811);
lean_ctor_set(x_814, 1, x_812);
return x_814;
}
}
else
{
lean_object* x_815; 
lean_dec_ref(x_791);
lean_dec_ref(x_789);
lean_dec_ref(x_659);
lean_dec(x_3);
lean_dec_ref(x_2);
x_815 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_788);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_815;
}
}
case 5:
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; uint8_t x_822; lean_object* x_823; 
lean_dec_ref(x_659);
x_816 = lean_ctor_get(x_2, 0);
lean_inc(x_816);
x_817 = lean_st_ref_get(x_3, x_8);
lean_dec(x_3);
x_818 = lean_ctor_get(x_817, 0);
lean_inc(x_818);
x_819 = lean_ctor_get(x_817, 1);
lean_inc(x_819);
if (lean_is_exclusive(x_817)) {
 lean_ctor_release(x_817, 0);
 lean_ctor_release(x_817, 1);
 x_820 = x_817;
} else {
 lean_dec_ref(x_817);
 x_820 = lean_box(0);
}
x_821 = lean_ctor_get(x_818, 1);
lean_inc_ref(x_821);
lean_dec(x_818);
x_822 = 0;
x_823 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_821, x_816, x_822);
lean_dec_ref(x_821);
if (lean_obj_tag(x_823) == 0)
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_824 = lean_ctor_get(x_823, 0);
lean_inc(x_824);
lean_dec_ref(x_823);
x_825 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(x_2, x_824);
if (lean_is_scalar(x_820)) {
 x_826 = lean_alloc_ctor(0, 2, 0);
} else {
 x_826 = x_820;
}
lean_ctor_set(x_826, 0, x_825);
lean_ctor_set(x_826, 1, x_819);
return x_826;
}
else
{
lean_object* x_827; 
lean_dec(x_820);
lean_dec_ref(x_2);
x_827 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_819);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_827;
}
}
default: 
{
lean_object* x_828; 
lean_dec_ref(x_659);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_828 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_828, 0, x_2);
lean_ctor_set(x_828, 1, x_8);
return x_828;
}
}
}
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; 
x_829 = lean_ctor_get(x_9, 0);
lean_inc(x_829);
lean_dec(x_9);
x_830 = lean_ctor_get(x_829, 0);
lean_inc_ref(x_830);
x_831 = lean_ctor_get(x_829, 2);
lean_inc_ref(x_831);
x_832 = lean_ctor_get(x_829, 3);
lean_inc_ref(x_832);
x_833 = lean_ctor_get(x_829, 4);
lean_inc_ref(x_833);
if (lean_is_exclusive(x_829)) {
 lean_ctor_release(x_829, 0);
 lean_ctor_release(x_829, 1);
 lean_ctor_release(x_829, 2);
 lean_ctor_release(x_829, 3);
 lean_ctor_release(x_829, 4);
 x_834 = x_829;
} else {
 lean_dec_ref(x_829);
 x_834 = lean_box(0);
}
x_835 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2;
x_836 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__3;
lean_inc_ref(x_830);
x_837 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_837, 0, x_830);
x_838 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_838, 0, x_830);
x_839 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_839, 0, x_837);
lean_ctor_set(x_839, 1, x_838);
x_840 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_840, 0, x_833);
x_841 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_841, 0, x_832);
x_842 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_842, 0, x_831);
if (lean_is_scalar(x_834)) {
 x_843 = lean_alloc_ctor(0, 5, 0);
} else {
 x_843 = x_834;
}
lean_ctor_set(x_843, 0, x_839);
lean_ctor_set(x_843, 1, x_835);
lean_ctor_set(x_843, 2, x_842);
lean_ctor_set(x_843, 3, x_841);
lean_ctor_set(x_843, 4, x_840);
x_844 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_844, 0, x_843);
lean_ctor_set(x_844, 1, x_836);
x_845 = l_ReaderT_instMonad___redArg(x_844);
x_846 = lean_ctor_get(x_845, 0);
lean_inc_ref(x_846);
if (lean_is_exclusive(x_845)) {
 lean_ctor_release(x_845, 0);
 lean_ctor_release(x_845, 1);
 x_847 = x_845;
} else {
 lean_dec_ref(x_845);
 x_847 = lean_box(0);
}
x_848 = lean_ctor_get(x_846, 0);
lean_inc_ref(x_848);
x_849 = lean_ctor_get(x_846, 2);
lean_inc_ref(x_849);
x_850 = lean_ctor_get(x_846, 3);
lean_inc_ref(x_850);
x_851 = lean_ctor_get(x_846, 4);
lean_inc_ref(x_851);
if (lean_is_exclusive(x_846)) {
 lean_ctor_release(x_846, 0);
 lean_ctor_release(x_846, 1);
 lean_ctor_release(x_846, 2);
 lean_ctor_release(x_846, 3);
 lean_ctor_release(x_846, 4);
 x_852 = x_846;
} else {
 lean_dec_ref(x_846);
 x_852 = lean_box(0);
}
x_853 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__4;
x_854 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__5;
lean_inc_ref(x_848);
x_855 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_855, 0, x_848);
x_856 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_856, 0, x_848);
x_857 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_857, 0, x_855);
lean_ctor_set(x_857, 1, x_856);
x_858 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_858, 0, x_851);
x_859 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_859, 0, x_850);
x_860 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_860, 0, x_849);
if (lean_is_scalar(x_852)) {
 x_861 = lean_alloc_ctor(0, 5, 0);
} else {
 x_861 = x_852;
}
lean_ctor_set(x_861, 0, x_857);
lean_ctor_set(x_861, 1, x_853);
lean_ctor_set(x_861, 2, x_860);
lean_ctor_set(x_861, 3, x_859);
lean_ctor_set(x_861, 4, x_858);
if (lean_is_scalar(x_847)) {
 x_862 = lean_alloc_ctor(0, 2, 0);
} else {
 x_862 = x_847;
}
lean_ctor_set(x_862, 0, x_861);
lean_ctor_set(x_862, 1, x_854);
x_863 = l_ReaderT_instMonad___redArg(x_862);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_864; lean_object* x_865; uint8_t x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; uint8_t x_874; 
lean_dec_ref(x_863);
x_864 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_864);
x_865 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_865);
x_866 = 0;
x_867 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0(x_866, x_864, x_3, x_4, x_5, x_6, x_7, x_8);
x_868 = lean_ctor_get(x_867, 0);
lean_inc(x_868);
x_869 = lean_ctor_get(x_867, 1);
lean_inc(x_869);
lean_dec_ref(x_867);
x_870 = lean_ctor_get(x_868, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_868, 3);
lean_inc(x_871);
lean_inc(x_871);
x_872 = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(x_871, x_7, x_869);
x_873 = lean_ctor_get(x_872, 0);
lean_inc(x_873);
x_874 = lean_unbox(x_873);
lean_dec(x_873);
if (x_874 == 0)
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_875 = lean_ctor_get(x_872, 1);
lean_inc(x_875);
lean_dec_ref(x_872);
x_876 = lean_st_ref_get(x_3, x_875);
x_877 = lean_ctor_get(x_876, 0);
lean_inc(x_877);
x_878 = lean_ctor_get(x_876, 1);
lean_inc(x_878);
lean_dec_ref(x_876);
x_879 = lean_ctor_get(x_877, 0);
lean_inc_ref(x_879);
lean_dec(x_877);
x_880 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_871);
x_881 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0;
x_882 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1;
lean_inc_ref(x_880);
x_883 = l_Lean_PersistentHashMap_find_x3f___redArg(x_881, x_882, x_879, x_880);
if (lean_obj_tag(x_883) == 0)
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_884 = lean_st_ref_take(x_3, x_878);
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_884, 1);
lean_inc(x_886);
lean_dec_ref(x_884);
x_887 = lean_ctor_get(x_885, 0);
lean_inc_ref(x_887);
x_888 = lean_ctor_get(x_885, 1);
lean_inc_ref(x_888);
if (lean_is_exclusive(x_885)) {
 lean_ctor_release(x_885, 0);
 lean_ctor_release(x_885, 1);
 x_889 = x_885;
} else {
 lean_dec_ref(x_885);
 x_889 = lean_box(0);
}
x_890 = l_Lean_PersistentHashMap_insert___redArg(x_881, x_882, x_887, x_880, x_870);
if (lean_is_scalar(x_889)) {
 x_891 = lean_alloc_ctor(0, 2, 0);
} else {
 x_891 = x_889;
}
lean_ctor_set(x_891, 0, x_890);
lean_ctor_set(x_891, 1, x_888);
x_892 = lean_st_ref_set(x_3, x_891, x_886);
x_893 = lean_ctor_get(x_892, 1);
lean_inc(x_893);
lean_dec_ref(x_892);
x_894 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_865, x_3, x_4, x_5, x_6, x_7, x_893);
if (lean_obj_tag(x_894) == 0)
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; 
x_895 = lean_ctor_get(x_894, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_894, 1);
lean_inc(x_896);
if (lean_is_exclusive(x_894)) {
 lean_ctor_release(x_894, 0);
 lean_ctor_release(x_894, 1);
 x_897 = x_894;
} else {
 lean_dec_ref(x_894);
 x_897 = lean_box(0);
}
x_898 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_2, x_868, x_895);
lean_dec_ref(x_2);
if (lean_is_scalar(x_897)) {
 x_899 = lean_alloc_ctor(0, 2, 0);
} else {
 x_899 = x_897;
}
lean_ctor_set(x_899, 0, x_898);
lean_ctor_set(x_899, 1, x_896);
return x_899;
}
else
{
lean_dec(x_868);
lean_dec_ref(x_2);
return x_894;
}
}
else
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; 
lean_dec_ref(x_880);
lean_dec(x_870);
lean_dec_ref(x_2);
x_900 = lean_ctor_get(x_883, 0);
lean_inc(x_900);
lean_dec_ref(x_883);
x_901 = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(x_868, x_900, x_3, x_5, x_878);
x_902 = lean_ctor_get(x_901, 1);
lean_inc(x_902);
lean_dec_ref(x_901);
x_2 = x_865;
x_8 = x_902;
goto _start;
}
}
else
{
lean_object* x_904; lean_object* x_905; 
lean_dec(x_871);
lean_dec(x_870);
x_904 = lean_ctor_get(x_872, 1);
lean_inc(x_904);
lean_dec_ref(x_872);
x_905 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_865, x_3, x_4, x_5, x_6, x_7, x_904);
if (lean_obj_tag(x_905) == 0)
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; 
x_906 = lean_ctor_get(x_905, 0);
lean_inc(x_906);
x_907 = lean_ctor_get(x_905, 1);
lean_inc(x_907);
if (lean_is_exclusive(x_905)) {
 lean_ctor_release(x_905, 0);
 lean_ctor_release(x_905, 1);
 x_908 = x_905;
} else {
 lean_dec_ref(x_905);
 x_908 = lean_box(0);
}
x_909 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_2, x_868, x_906);
lean_dec_ref(x_2);
if (lean_is_scalar(x_908)) {
 x_910 = lean_alloc_ctor(0, 2, 0);
} else {
 x_910 = x_908;
}
lean_ctor_set(x_910, 0, x_909);
lean_ctor_set(x_910, 1, x_907);
return x_910;
}
else
{
lean_dec(x_868);
lean_dec_ref(x_2);
return x_905;
}
}
}
case 1:
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; 
lean_dec_ref(x_863);
x_911 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_911);
x_912 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_912);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_913 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_1, x_911, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_913) == 0)
{
if (x_1 == 0)
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; 
x_914 = lean_ctor_get(x_913, 0);
lean_inc(x_914);
x_915 = lean_ctor_get(x_913, 1);
lean_inc(x_915);
lean_dec_ref(x_913);
x_916 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_912, x_3, x_4, x_5, x_6, x_7, x_915);
if (lean_obj_tag(x_916) == 0)
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; 
x_917 = lean_ctor_get(x_916, 0);
lean_inc(x_917);
x_918 = lean_ctor_get(x_916, 1);
lean_inc(x_918);
if (lean_is_exclusive(x_916)) {
 lean_ctor_release(x_916, 0);
 lean_ctor_release(x_916, 1);
 x_919 = x_916;
} else {
 lean_dec_ref(x_916);
 x_919 = lean_box(0);
}
x_920 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_914, x_917);
lean_dec_ref(x_2);
if (lean_is_scalar(x_919)) {
 x_921 = lean_alloc_ctor(0, 2, 0);
} else {
 x_921 = x_919;
}
lean_ctor_set(x_921, 0, x_920);
lean_ctor_set(x_921, 1, x_918);
return x_921;
}
else
{
lean_dec(x_914);
lean_dec_ref(x_2);
return x_916;
}
}
else
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; 
x_922 = lean_ctor_get(x_913, 0);
lean_inc(x_922);
x_923 = lean_ctor_get(x_913, 1);
lean_inc(x_923);
lean_dec_ref(x_913);
x_924 = lean_st_ref_get(x_3, x_923);
x_925 = lean_ctor_get(x_924, 0);
lean_inc(x_925);
x_926 = lean_ctor_get(x_924, 1);
lean_inc(x_926);
lean_dec_ref(x_924);
x_927 = lean_ctor_get(x_925, 0);
lean_inc_ref(x_927);
lean_dec(x_925);
x_928 = l_Lean_Compiler_LCNF_Code_cse_go___closed__0;
lean_inc(x_922);
x_929 = l_Lean_Compiler_LCNF_FunDecl_toExpr(x_922, x_928);
x_930 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0;
x_931 = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1;
lean_inc_ref(x_929);
x_932 = l_Lean_PersistentHashMap_find_x3f___redArg(x_930, x_931, x_927, x_929);
if (lean_obj_tag(x_932) == 0)
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; 
x_933 = lean_st_ref_take(x_3, x_926);
x_934 = lean_ctor_get(x_933, 0);
lean_inc(x_934);
x_935 = lean_ctor_get(x_933, 1);
lean_inc(x_935);
lean_dec_ref(x_933);
x_936 = lean_ctor_get(x_922, 0);
lean_inc(x_936);
x_937 = lean_ctor_get(x_934, 0);
lean_inc_ref(x_937);
x_938 = lean_ctor_get(x_934, 1);
lean_inc_ref(x_938);
if (lean_is_exclusive(x_934)) {
 lean_ctor_release(x_934, 0);
 lean_ctor_release(x_934, 1);
 x_939 = x_934;
} else {
 lean_dec_ref(x_934);
 x_939 = lean_box(0);
}
x_940 = l_Lean_PersistentHashMap_insert___redArg(x_930, x_931, x_937, x_929, x_936);
if (lean_is_scalar(x_939)) {
 x_941 = lean_alloc_ctor(0, 2, 0);
} else {
 x_941 = x_939;
}
lean_ctor_set(x_941, 0, x_940);
lean_ctor_set(x_941, 1, x_938);
x_942 = lean_st_ref_set(x_3, x_941, x_935);
x_943 = lean_ctor_get(x_942, 1);
lean_inc(x_943);
lean_dec_ref(x_942);
x_944 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_912, x_3, x_4, x_5, x_6, x_7, x_943);
if (lean_obj_tag(x_944) == 0)
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; 
x_945 = lean_ctor_get(x_944, 0);
lean_inc(x_945);
x_946 = lean_ctor_get(x_944, 1);
lean_inc(x_946);
if (lean_is_exclusive(x_944)) {
 lean_ctor_release(x_944, 0);
 lean_ctor_release(x_944, 1);
 x_947 = x_944;
} else {
 lean_dec_ref(x_944);
 x_947 = lean_box(0);
}
x_948 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_922, x_945);
lean_dec_ref(x_2);
if (lean_is_scalar(x_947)) {
 x_949 = lean_alloc_ctor(0, 2, 0);
} else {
 x_949 = x_947;
}
lean_ctor_set(x_949, 0, x_948);
lean_ctor_set(x_949, 1, x_946);
return x_949;
}
else
{
lean_dec(x_922);
lean_dec_ref(x_2);
return x_944;
}
}
else
{
lean_object* x_950; lean_object* x_951; lean_object* x_952; 
lean_dec_ref(x_929);
lean_dec_ref(x_2);
x_950 = lean_ctor_get(x_932, 0);
lean_inc(x_950);
lean_dec_ref(x_932);
x_951 = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(x_922, x_950, x_3, x_5, x_926);
x_952 = lean_ctor_get(x_951, 1);
lean_inc(x_952);
lean_dec_ref(x_951);
x_2 = x_912;
x_8 = x_952;
goto _start;
}
}
}
else
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; 
lean_dec_ref(x_912);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_954 = lean_ctor_get(x_913, 0);
lean_inc(x_954);
x_955 = lean_ctor_get(x_913, 1);
lean_inc(x_955);
if (lean_is_exclusive(x_913)) {
 lean_ctor_release(x_913, 0);
 lean_ctor_release(x_913, 1);
 x_956 = x_913;
} else {
 lean_dec_ref(x_913);
 x_956 = lean_box(0);
}
if (lean_is_scalar(x_956)) {
 x_957 = lean_alloc_ctor(1, 2, 0);
} else {
 x_957 = x_956;
}
lean_ctor_set(x_957, 0, x_954);
lean_ctor_set(x_957, 1, x_955);
return x_957;
}
}
case 2:
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; 
lean_dec_ref(x_863);
x_958 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_958);
x_959 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_959);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_960 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_1, x_958, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_960) == 0)
{
lean_object* x_961; lean_object* x_962; lean_object* x_963; 
x_961 = lean_ctor_get(x_960, 0);
lean_inc(x_961);
x_962 = lean_ctor_get(x_960, 1);
lean_inc(x_962);
lean_dec_ref(x_960);
x_963 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_959, x_3, x_4, x_5, x_6, x_7, x_962);
if (lean_obj_tag(x_963) == 0)
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; 
x_964 = lean_ctor_get(x_963, 0);
lean_inc(x_964);
x_965 = lean_ctor_get(x_963, 1);
lean_inc(x_965);
if (lean_is_exclusive(x_963)) {
 lean_ctor_release(x_963, 0);
 lean_ctor_release(x_963, 1);
 x_966 = x_963;
} else {
 lean_dec_ref(x_963);
 x_966 = lean_box(0);
}
x_967 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_961, x_964);
lean_dec_ref(x_2);
if (lean_is_scalar(x_966)) {
 x_968 = lean_alloc_ctor(0, 2, 0);
} else {
 x_968 = x_966;
}
lean_ctor_set(x_968, 0, x_967);
lean_ctor_set(x_968, 1, x_965);
return x_968;
}
else
{
lean_dec(x_961);
lean_dec_ref(x_2);
return x_963;
}
}
else
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; 
lean_dec_ref(x_959);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_969 = lean_ctor_get(x_960, 0);
lean_inc(x_969);
x_970 = lean_ctor_get(x_960, 1);
lean_inc(x_970);
if (lean_is_exclusive(x_960)) {
 lean_ctor_release(x_960, 0);
 lean_ctor_release(x_960, 1);
 x_971 = x_960;
} else {
 lean_dec_ref(x_960);
 x_971 = lean_box(0);
}
if (lean_is_scalar(x_971)) {
 x_972 = lean_alloc_ctor(1, 2, 0);
} else {
 x_972 = x_971;
}
lean_ctor_set(x_972, 0, x_969);
lean_ctor_set(x_972, 1, x_970);
return x_972;
}
}
case 3:
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; uint8_t x_979; lean_object* x_980; 
lean_dec_ref(x_863);
x_973 = lean_ctor_get(x_2, 0);
lean_inc(x_973);
x_974 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_974);
x_975 = lean_st_ref_get(x_3, x_8);
x_976 = lean_ctor_get(x_975, 0);
lean_inc(x_976);
x_977 = lean_ctor_get(x_975, 1);
lean_inc(x_977);
lean_dec_ref(x_975);
x_978 = lean_ctor_get(x_976, 1);
lean_inc_ref(x_978);
lean_dec(x_976);
x_979 = 0;
x_980 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_978, x_973, x_979);
lean_dec_ref(x_978);
if (lean_obj_tag(x_980) == 0)
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_981 = lean_ctor_get(x_980, 0);
lean_inc(x_981);
lean_dec_ref(x_980);
x_982 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1___redArg(x_979, x_974, x_3, x_977);
lean_dec(x_3);
x_983 = lean_ctor_get(x_982, 0);
lean_inc(x_983);
x_984 = lean_ctor_get(x_982, 1);
lean_inc(x_984);
if (lean_is_exclusive(x_982)) {
 lean_ctor_release(x_982, 0);
 lean_ctor_release(x_982, 1);
 x_985 = x_982;
} else {
 lean_dec_ref(x_982);
 x_985 = lean_box(0);
}
x_986 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp(x_2, x_981, x_983);
lean_dec_ref(x_2);
if (lean_is_scalar(x_985)) {
 x_987 = lean_alloc_ctor(0, 2, 0);
} else {
 x_987 = x_985;
}
lean_ctor_set(x_987, 0, x_986);
lean_ctor_set(x_987, 1, x_984);
return x_987;
}
else
{
lean_object* x_988; 
lean_dec_ref(x_974);
lean_dec(x_3);
lean_dec_ref(x_2);
x_988 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_977);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_988;
}
}
case 4:
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; uint8_t x_997; lean_object* x_998; 
x_989 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_989);
x_990 = lean_st_ref_get(x_3, x_8);
x_991 = lean_ctor_get(x_990, 0);
lean_inc(x_991);
x_992 = lean_ctor_get(x_990, 1);
lean_inc(x_992);
lean_dec_ref(x_990);
x_993 = lean_ctor_get(x_989, 1);
lean_inc_ref(x_993);
x_994 = lean_ctor_get(x_989, 2);
lean_inc(x_994);
x_995 = lean_ctor_get(x_989, 3);
lean_inc_ref(x_995);
lean_dec_ref(x_989);
x_996 = lean_ctor_get(x_991, 1);
lean_inc_ref(x_996);
lean_dec(x_991);
x_997 = 0;
x_998 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_996, x_994, x_997);
lean_dec_ref(x_996);
if (lean_obj_tag(x_998) == 0)
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; 
x_999 = lean_ctor_get(x_998, 0);
lean_inc(x_999);
lean_dec_ref(x_998);
x_1000 = lean_st_ref_get(x_3, x_992);
x_1001 = lean_ctor_get(x_1000, 0);
lean_inc(x_1001);
x_1002 = lean_ctor_get(x_1000, 1);
lean_inc(x_1002);
lean_dec_ref(x_1000);
x_1003 = lean_box(x_997);
x_1004 = lean_box(x_1);
x_1005 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_cse_go___lam__2___boxed), 9, 2);
lean_closure_set(x_1005, 0, x_1003);
lean_closure_set(x_1005, 1, x_1004);
x_1006 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_863, x_995, x_1005);
x_1007 = lean_apply_6(x_1006, x_3, x_4, x_5, x_6, x_7, x_1002);
if (lean_obj_tag(x_1007) == 0)
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; 
x_1008 = lean_ctor_get(x_1007, 0);
lean_inc(x_1008);
x_1009 = lean_ctor_get(x_1007, 1);
lean_inc(x_1009);
if (lean_is_exclusive(x_1007)) {
 lean_ctor_release(x_1007, 0);
 lean_ctor_release(x_1007, 1);
 x_1010 = x_1007;
} else {
 lean_dec_ref(x_1007);
 x_1010 = lean_box(0);
}
x_1011 = lean_ctor_get(x_1001, 1);
lean_inc_ref(x_1011);
lean_dec(x_1001);
x_1012 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1011, x_997, x_993);
lean_dec_ref(x_1011);
x_1013 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(x_2, x_1012, x_999, x_1008);
if (lean_is_scalar(x_1010)) {
 x_1014 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1014 = x_1010;
}
lean_ctor_set(x_1014, 0, x_1013);
lean_ctor_set(x_1014, 1, x_1009);
return x_1014;
}
else
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; 
lean_dec(x_1001);
lean_dec(x_999);
lean_dec_ref(x_993);
lean_dec_ref(x_2);
x_1015 = lean_ctor_get(x_1007, 0);
lean_inc(x_1015);
x_1016 = lean_ctor_get(x_1007, 1);
lean_inc(x_1016);
if (lean_is_exclusive(x_1007)) {
 lean_ctor_release(x_1007, 0);
 lean_ctor_release(x_1007, 1);
 x_1017 = x_1007;
} else {
 lean_dec_ref(x_1007);
 x_1017 = lean_box(0);
}
if (lean_is_scalar(x_1017)) {
 x_1018 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1018 = x_1017;
}
lean_ctor_set(x_1018, 0, x_1015);
lean_ctor_set(x_1018, 1, x_1016);
return x_1018;
}
}
else
{
lean_object* x_1019; 
lean_dec_ref(x_995);
lean_dec_ref(x_993);
lean_dec_ref(x_863);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1019 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_992);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_1019;
}
}
case 5:
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; uint8_t x_1026; lean_object* x_1027; 
lean_dec_ref(x_863);
x_1020 = lean_ctor_get(x_2, 0);
lean_inc(x_1020);
x_1021 = lean_st_ref_get(x_3, x_8);
lean_dec(x_3);
x_1022 = lean_ctor_get(x_1021, 0);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_1021, 1);
lean_inc(x_1023);
if (lean_is_exclusive(x_1021)) {
 lean_ctor_release(x_1021, 0);
 lean_ctor_release(x_1021, 1);
 x_1024 = x_1021;
} else {
 lean_dec_ref(x_1021);
 x_1024 = lean_box(0);
}
x_1025 = lean_ctor_get(x_1022, 1);
lean_inc_ref(x_1025);
lean_dec(x_1022);
x_1026 = 0;
x_1027 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_1025, x_1020, x_1026);
lean_dec_ref(x_1025);
if (lean_obj_tag(x_1027) == 0)
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_1028 = lean_ctor_get(x_1027, 0);
lean_inc(x_1028);
lean_dec_ref(x_1027);
x_1029 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(x_2, x_1028);
if (lean_is_scalar(x_1024)) {
 x_1030 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1030 = x_1024;
}
lean_ctor_set(x_1030, 0, x_1029);
lean_ctor_set(x_1030, 1, x_1023);
return x_1030;
}
else
{
lean_object* x_1031; 
lean_dec(x_1024);
lean_dec_ref(x_2);
x_1031 = l_Lean_Compiler_LCNF_mkReturnErased(x_4, x_5, x_6, x_7, x_1023);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_1031;
}
}
default: 
{
lean_object* x_1032; 
lean_dec_ref(x_863);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_1032 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1032, 0, x_2);
lean_ctor_set(x_1032, 1, x_8);
return x_1032;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___lam__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_10 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Code_cse_go_spec__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
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
x_10 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Code_cse_go_spec__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Code_cse_go___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_2);
x_12 = l_Lean_Compiler_LCNF_Code_cse_go___lam__2(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_Code_cse_go(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Compiler_LCNF_Code_cse___closed__7;
x_9 = lean_st_mk_ref(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
lean_inc(x_10);
x_12 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_2, x_10, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
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
else
{
lean_dec(x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l_Lean_Compiler_LCNF_Code_cse(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
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
lean_dec_ref(x_12);
lean_dec_ref(x_11);
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
lean_dec_ref(x_30);
lean_dec_ref(x_29);
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
x_9 = l_Lean_Compiler_LCNF_Decl_cse___lam__0(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
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
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Compiler_LCNF_cse(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1278_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_CSE___hyg_1278_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_cse___closed__0;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1278_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_CSE___hyg_1278_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_CSE___hyg_1278_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1278_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LCNF", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_CSE___hyg_1278_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_CSE___hyg_1278_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_CSE___hyg_1278_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_CSE___hyg_1278_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_CSE___hyg_1278_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_CSE___hyg_1278_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_CSE___hyg_1278_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_CSE___hyg_1278_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_CSE___hyg_1278_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("CSE", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_CSE___hyg_1278_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_CSE___hyg_1278_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_CSE___hyg_1278_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_CSE___hyg_1278_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1278u);
x_2 = l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1278_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_CSE___hyg_1278_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
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
l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1278_ = _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1278_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_CSE___hyg_1278_);
l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_CSE___hyg_1278_ = _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_CSE___hyg_1278_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_CSE___hyg_1278_);
l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1278_ = _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1278_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_CSE___hyg_1278_);
l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_CSE___hyg_1278_ = _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_CSE___hyg_1278_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_CSE___hyg_1278_);
l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_CSE___hyg_1278_ = _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_CSE___hyg_1278_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_CSE___hyg_1278_);
l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1278_ = _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1278_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_CSE___hyg_1278_);
l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_CSE___hyg_1278_ = _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_CSE___hyg_1278_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_CSE___hyg_1278_);
l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_CSE___hyg_1278_ = _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_CSE___hyg_1278_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_CSE___hyg_1278_);
l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_CSE___hyg_1278_ = _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_CSE___hyg_1278_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_CSE___hyg_1278_);
l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_CSE___hyg_1278_ = _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_CSE___hyg_1278_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_CSE___hyg_1278_);
l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_CSE___hyg_1278_ = _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_CSE___hyg_1278_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_CSE___hyg_1278_);
l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_CSE___hyg_1278_ = _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_CSE___hyg_1278_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_CSE___hyg_1278_);
l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_CSE___hyg_1278_ = _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_CSE___hyg_1278_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_CSE___hyg_1278_);
l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_CSE___hyg_1278_ = _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_CSE___hyg_1278_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_CSE___hyg_1278_);
l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_CSE___hyg_1278_ = _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_CSE___hyg_1278_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_CSE___hyg_1278_);
l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_CSE___hyg_1278_ = _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_CSE___hyg_1278_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_CSE___hyg_1278_);
l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_CSE___hyg_1278_ = _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_CSE___hyg_1278_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_CSE___hyg_1278_);
l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_CSE___hyg_1278_ = _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_CSE___hyg_1278_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_CSE___hyg_1278_);
l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_CSE___hyg_1278_ = _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_CSE___hyg_1278_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_CSE___hyg_1278_);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1278_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
