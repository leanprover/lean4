// Lean compiler output
// Module: Lean.Compiler.LCNF.Internalize
// Imports: public import Lean.Compiler.LCNF.Bind
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Purity_ctorIdx(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_anyExpr;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftBaseIOEIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* l_instMonadStateOfOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadStateOfOfMonadLift___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadStateOfMonadStateOf___redArg(lean_object*);
lean_object* l_modify(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_liftIOCore___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftBaseIOEIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__3_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__5_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__5_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__4_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__6_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__6_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__3_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__7_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__7_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__8_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__8_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__9_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__9_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__10_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "_private.Lean.Compiler.LCNF.Internalize.0.Lean.Compiler.LCNF.Internalize.internalizeExpr.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Compiler.LCNF.Internalize"};
static const lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(uint8_t, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(uint8_t, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(uint8_t, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "Lean.Compiler.LCNF.Internalize.internalizeCodeDecl"};
static const lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_cleanup___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_cleanup___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_cleanup___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_cleanup___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_normalizeFVarIds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_normalizeFVarIds___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_normalizeFVarIds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___redArg(lean_object* v_x_1_, lean_object* v_state_2_, uint8_t v_ctx_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = lean_st_mk_ref(v_state_2_);
v___x_10_ = lean_box(v_ctx_3_);
lean_inc(v_a_7_);
lean_inc_ref(v_a_6_);
lean_inc(v_a_5_);
lean_inc_ref(v_a_4_);
lean_inc(v___x_9_);
v___x_11_ = lean_apply_7(v_x_1_, v___x_10_, v___x_9_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, lean_box(0));
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v_a_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_21_; 
v_a_12_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_21_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_21_ == 0)
{
v___x_14_ = v___x_11_;
v_isShared_15_ = v_isSharedCheck_21_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_a_12_);
lean_dec(v___x_11_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_21_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_19_; 
v___x_16_ = lean_st_ref_get(v___x_9_);
lean_dec(v___x_9_);
v___x_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_17_, 0, v_a_12_);
lean_ctor_set(v___x_17_, 1, v___x_16_);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 0, v___x_17_);
v___x_19_ = v___x_14_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_17_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
else
{
lean_object* v_a_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
lean_dec(v___x_9_);
v_a_22_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v___x_11_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_a_22_);
lean_dec(v___x_11_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_a_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___redArg___boxed(lean_object* v_x_30_, lean_object* v_state_31_, lean_object* v_ctx_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
uint8_t v_ctx_boxed_38_; lean_object* v_res_39_; 
v_ctx_boxed_38_ = lean_unbox(v_ctx_32_);
v_res_39_ = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___redArg(v_x_30_, v_state_31_, v_ctx_boxed_38_, v_a_33_, v_a_34_, v_a_35_, v_a_36_);
lean_dec(v_a_36_);
lean_dec_ref(v_a_35_);
lean_dec(v_a_34_);
lean_dec_ref(v_a_33_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run(uint8_t v_pu_40_, lean_object* v_00_u03b1_41_, lean_object* v_x_42_, lean_object* v_state_43_, uint8_t v_ctx_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_st_mk_ref(v_state_43_);
v___x_51_ = lean_box(v_ctx_44_);
lean_inc(v_a_48_);
lean_inc_ref(v_a_47_);
lean_inc(v_a_46_);
lean_inc_ref(v_a_45_);
lean_inc(v___x_50_);
v___x_52_ = lean_apply_7(v_x_42_, v___x_51_, v___x_50_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, lean_box(0));
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_62_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_62_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_62_ == 0)
{
v___x_55_ = v___x_52_;
v_isShared_56_ = v_isSharedCheck_62_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_a_53_);
lean_dec(v___x_52_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_62_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_60_; 
v___x_57_ = lean_st_ref_get(v___x_50_);
lean_dec(v___x_50_);
v___x_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_58_, 0, v_a_53_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 0, v___x_58_);
v___x_60_ = v___x_55_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_58_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
else
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_70_; 
lean_dec(v___x_50_);
v_a_63_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_70_ == 0)
{
v___x_65_ = v___x_52_;
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_52_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
if (v_isShared_66_ == 0)
{
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_a_63_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___boxed(lean_object* v_pu_71_, lean_object* v_00_u03b1_72_, lean_object* v_x_73_, lean_object* v_state_74_, lean_object* v_ctx_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
uint8_t v_pu_boxed_81_; uint8_t v_ctx_boxed_82_; lean_object* v_res_83_; 
v_pu_boxed_81_ = lean_unbox(v_pu_71_);
v_ctx_boxed_82_ = lean_unbox(v_ctx_75_);
v_res_83_ = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run(v_pu_boxed_81_, v_00_u03b1_72_, v_x_73_, v_state_74_, v_ctx_boxed_82_, v_a_76_, v_a_77_, v_a_78_, v_a_79_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___redArg(lean_object* v_x_84_, lean_object* v_state_85_, uint8_t v_ctx_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = lean_st_mk_ref(v_state_85_);
v___x_93_ = lean_box(v_ctx_86_);
lean_inc(v_a_90_);
lean_inc_ref(v_a_89_);
lean_inc(v_a_88_);
lean_inc_ref(v_a_87_);
lean_inc(v___x_92_);
v___x_94_ = lean_apply_7(v_x_84_, v___x_93_, v___x_92_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, lean_box(0));
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_103_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_103_ == 0)
{
v___x_97_ = v___x_94_;
v_isShared_98_ = v_isSharedCheck_103_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_94_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_103_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_99_; lean_object* v___x_101_; 
v___x_99_ = lean_st_ref_get(v___x_92_);
lean_dec(v___x_92_);
lean_dec(v___x_99_);
if (v_isShared_98_ == 0)
{
v___x_101_ = v___x_97_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_95_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
else
{
lean_dec(v___x_92_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___redArg___boxed(lean_object* v_x_104_, lean_object* v_state_105_, lean_object* v_ctx_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
uint8_t v_ctx_boxed_112_; lean_object* v_res_113_; 
v_ctx_boxed_112_ = lean_unbox(v_ctx_106_);
v_res_113_ = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___redArg(v_x_104_, v_state_105_, v_ctx_boxed_112_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27(uint8_t v_pu_114_, lean_object* v_00_u03b1_115_, lean_object* v_x_116_, lean_object* v_state_117_, uint8_t v_ctx_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lean_st_mk_ref(v_state_117_);
v___x_125_ = lean_box(v_ctx_118_);
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
lean_inc(v_a_120_);
lean_inc_ref(v_a_119_);
lean_inc(v___x_124_);
v___x_126_ = lean_apply_7(v_x_116_, v___x_125_, v___x_124_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, lean_box(0));
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_135_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_135_ == 0)
{
v___x_129_ = v___x_126_;
v_isShared_130_ = v_isSharedCheck_135_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_126_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_135_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_131_ = lean_st_ref_get(v___x_124_);
lean_dec(v___x_124_);
lean_dec(v___x_131_);
if (v_isShared_130_ == 0)
{
v___x_133_ = v___x_129_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_a_127_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
else
{
lean_dec(v___x_124_);
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___boxed(lean_object* v_pu_136_, lean_object* v_00_u03b1_137_, lean_object* v_x_138_, lean_object* v_state_139_, lean_object* v_ctx_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
uint8_t v_pu_boxed_146_; uint8_t v_ctx_boxed_147_; lean_object* v_res_148_; 
v_pu_boxed_146_ = lean_unbox(v_pu_136_);
v_ctx_boxed_147_ = lean_unbox(v_ctx_140_);
v_res_148_ = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27(v_pu_boxed_146_, v_00_u03b1_137_, v_x_138_, v_state_139_, v_ctx_boxed_147_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(lean_object* v_binderName_149_, uint8_t v_a_150_, lean_object* v_a_151_){
_start:
{
if (lean_obj_tag(v_binderName_149_) == 2)
{
lean_object* v_pre_153_; lean_object* v___x_154_; lean_object* v_lctx_155_; lean_object* v_nextIdx_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_168_; 
v_pre_153_ = lean_ctor_get(v_binderName_149_, 0);
lean_inc(v_pre_153_);
lean_dec_ref_known(v_binderName_149_, 2);
v___x_154_ = lean_st_ref_take(v_a_151_);
v_lctx_155_ = lean_ctor_get(v___x_154_, 0);
v_nextIdx_156_ = lean_ctor_get(v___x_154_, 1);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_168_ == 0)
{
v___x_158_ = v___x_154_;
v_isShared_159_ = v_isSharedCheck_168_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_nextIdx_156_);
lean_inc(v_lctx_155_);
lean_dec(v___x_154_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_168_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_160_ = lean_unsigned_to_nat(1u);
v___x_161_ = lean_nat_add(v_nextIdx_156_, v___x_160_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v___x_161_);
v___x_163_ = v___x_158_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_lctx_155_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v___x_161_);
v___x_163_ = v_reuseFailAlloc_167_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_st_ref_put(v_a_151_, v___x_163_);
v___x_165_ = l_Lean_Name_num___override(v_pre_153_, v_nextIdx_156_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
}
}
else
{
if (v_a_150_ == 0)
{
lean_object* v___x_169_; 
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v_binderName_149_);
return v___x_169_;
}
else
{
lean_object* v___x_170_; lean_object* v_lctx_171_; lean_object* v_nextIdx_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_184_; 
v___x_170_ = lean_st_ref_take(v_a_151_);
v_lctx_171_ = lean_ctor_get(v___x_170_, 0);
v_nextIdx_172_ = lean_ctor_get(v___x_170_, 1);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_184_ == 0)
{
v___x_174_ = v___x_170_;
v_isShared_175_ = v_isSharedCheck_184_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_nextIdx_172_);
lean_inc(v_lctx_171_);
lean_dec(v___x_170_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_184_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_176_ = lean_unsigned_to_nat(1u);
v___x_177_ = lean_nat_add(v_nextIdx_172_, v___x_176_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v___x_177_);
v___x_179_ = v___x_174_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_lctx_171_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_177_);
v___x_179_ = v_reuseFailAlloc_183_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_st_ref_put(v_a_151_, v___x_179_);
v___x_181_ = l_Lean_Name_num___override(v_binderName_149_, v_nextIdx_172_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg___boxed(lean_object* v_binderName_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
uint8_t v_a_boxed_189_; lean_object* v_res_190_; 
v_a_boxed_189_ = lean_unbox(v_a_186_);
v_res_190_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_185_, v_a_boxed_189_, v_a_187_);
lean_dec(v_a_187_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName(uint8_t v_pu_191_, lean_object* v_binderName_192_, uint8_t v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_192_, v_a_193_, v_a_196_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___boxed(lean_object* v_pu_201_, lean_object* v_binderName_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
uint8_t v_pu_boxed_210_; uint8_t v_a_boxed_211_; lean_object* v_res_212_; 
v_pu_boxed_210_ = lean_unbox(v_pu_201_);
v_a_boxed_211_ = lean_unbox(v_a_203_);
v_res_212_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName(v_pu_boxed_210_, v_binderName_202_, v_a_boxed_211_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_204_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___lam__0(uint8_t v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_st_ref_get(v___y_214_);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___lam__0___boxed(lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
uint8_t v___y_198__boxed_229_; lean_object* v_res_230_; 
v___y_198__boxed_229_ = lean_unbox(v___y_222_);
v_res_230_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___lam__0(v___y_198__boxed_229_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue(uint8_t v_pu_232_){
_start:
{
lean_object* v___f_233_; 
v___f_233_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0));
return v___f_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___boxed(lean_object* v_pu_234_){
_start:
{
uint8_t v_pu_boxed_235_; lean_object* v_res_236_; 
v_pu_boxed_235_ = lean_unbox(v_pu_234_);
v_res_236_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue(v_pu_boxed_235_);
return v_res_236_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11(void){
_start:
{
lean_object* v___f_258_; lean_object* v___x_259_; 
v___f_258_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__10));
v___x_259_ = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(v___f_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM(uint8_t v_pu_260_){
_start:
{
lean_object* v___f_261_; lean_object* v___x_262_; lean_object* v_get_263_; lean_object* v_set_264_; lean_object* v_modifyGet_265_; lean_object* v___f_266_; lean_object* v___f_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___f_261_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0));
v___x_262_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11, &l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11_once, _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11);
v_get_263_ = lean_ctor_get(v___x_262_, 0);
v_set_264_ = lean_ctor_get(v___x_262_, 1);
v_modifyGet_265_ = lean_ctor_get(v___x_262_, 2);
lean_inc(v_set_264_);
v___f_266_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_266_, 0, v_set_264_);
lean_closure_set(v___f_266_, 1, v___f_261_);
lean_inc(v_modifyGet_265_);
v___f_267_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_267_, 0, v_modifyGet_265_);
lean_closure_set(v___f_267_, 1, v___f_261_);
lean_inc(v_get_263_);
v___x_268_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_268_, 0, lean_box(0));
lean_closure_set(v___x_268_, 1, v_get_263_);
v___x_269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___f_266_);
lean_ctor_set(v___x_269_, 2, v___f_267_);
v___x_270_ = l_instMonadStateOfMonadStateOf___redArg(v___x_269_);
v___x_271_ = lean_alloc_closure((void*)(l_modify), 4, 3);
lean_closure_set(v___x_271_, 0, lean_box(0));
lean_closure_set(v___x_271_, 1, lean_box(0));
lean_closure_set(v___x_271_, 2, v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___boxed(lean_object* v_pu_272_){
_start:
{
uint8_t v_pu_boxed_273_; lean_object* v_res_274_; 
v_pu_boxed_273_ = lean_unbox(v_pu_272_);
v_res_274_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM(v_pu_boxed_273_);
return v_res_274_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(lean_object* v_a_275_, lean_object* v_x_276_){
_start:
{
if (lean_obj_tag(v_x_276_) == 0)
{
uint8_t v___x_277_; 
v___x_277_ = 0;
return v___x_277_;
}
else
{
lean_object* v_key_278_; lean_object* v_tail_279_; uint8_t v___x_280_; 
v_key_278_ = lean_ctor_get(v_x_276_, 0);
v_tail_279_ = lean_ctor_get(v_x_276_, 2);
v___x_280_ = l_Lean_instBEqFVarId_beq(v_key_278_, v_a_275_);
if (v___x_280_ == 0)
{
v_x_276_ = v_tail_279_;
goto _start;
}
else
{
return v___x_280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg___boxed(lean_object* v_a_282_, lean_object* v_x_283_){
_start:
{
uint8_t v_res_284_; lean_object* v_r_285_; 
v_res_284_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_a_282_, v_x_283_);
lean_dec(v_x_283_);
lean_dec(v_a_282_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(lean_object* v_a_286_, lean_object* v_b_287_, lean_object* v_x_288_){
_start:
{
if (lean_obj_tag(v_x_288_) == 0)
{
lean_dec(v_b_287_);
lean_dec(v_a_286_);
return v_x_288_;
}
else
{
lean_object* v_key_289_; lean_object* v_value_290_; lean_object* v_tail_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_303_; 
v_key_289_ = lean_ctor_get(v_x_288_, 0);
v_value_290_ = lean_ctor_get(v_x_288_, 1);
v_tail_291_ = lean_ctor_get(v_x_288_, 2);
v_isSharedCheck_303_ = !lean_is_exclusive(v_x_288_);
if (v_isSharedCheck_303_ == 0)
{
v___x_293_ = v_x_288_;
v_isShared_294_ = v_isSharedCheck_303_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_tail_291_);
lean_inc(v_value_290_);
lean_inc(v_key_289_);
lean_dec(v_x_288_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_303_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
uint8_t v___x_295_; 
v___x_295_ = l_Lean_instBEqFVarId_beq(v_key_289_, v_a_286_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_296_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(v_a_286_, v_b_287_, v_tail_291_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 2, v___x_296_);
v___x_298_ = v___x_293_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_key_289_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_value_290_);
lean_ctor_set(v_reuseFailAlloc_299_, 2, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
else
{
lean_object* v___x_301_; 
lean_dec(v_value_290_);
lean_dec(v_key_289_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v_b_287_);
lean_ctor_set(v___x_293_, 0, v_a_286_);
v___x_301_ = v___x_293_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_286_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_b_287_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_tail_291_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
if (lean_obj_tag(v_x_305_) == 0)
{
return v_x_304_;
}
else
{
lean_object* v_key_306_; lean_object* v_value_307_; lean_object* v_tail_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_331_; 
v_key_306_ = lean_ctor_get(v_x_305_, 0);
v_value_307_ = lean_ctor_get(v_x_305_, 1);
v_tail_308_ = lean_ctor_get(v_x_305_, 2);
v_isSharedCheck_331_ = !lean_is_exclusive(v_x_305_);
if (v_isSharedCheck_331_ == 0)
{
v___x_310_ = v_x_305_;
v_isShared_311_ = v_isSharedCheck_331_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_tail_308_);
lean_inc(v_value_307_);
lean_inc(v_key_306_);
lean_dec(v_x_305_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_331_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; uint64_t v___x_313_; uint64_t v___x_314_; uint64_t v___x_315_; uint64_t v_fold_316_; uint64_t v___x_317_; uint64_t v___x_318_; uint64_t v___x_319_; size_t v___x_320_; size_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_312_ = lean_array_get_size(v_x_304_);
v___x_313_ = l_Lean_instHashableFVarId_hash(v_key_306_);
v___x_314_ = 32ULL;
v___x_315_ = lean_uint64_shift_right(v___x_313_, v___x_314_);
v_fold_316_ = lean_uint64_xor(v___x_313_, v___x_315_);
v___x_317_ = 16ULL;
v___x_318_ = lean_uint64_shift_right(v_fold_316_, v___x_317_);
v___x_319_ = lean_uint64_xor(v_fold_316_, v___x_318_);
v___x_320_ = lean_uint64_to_usize(v___x_319_);
v___x_321_ = lean_usize_of_nat(v___x_312_);
v___x_322_ = ((size_t)1ULL);
v___x_323_ = lean_usize_sub(v___x_321_, v___x_322_);
v___x_324_ = lean_usize_land(v___x_320_, v___x_323_);
v___x_325_ = lean_array_uget_borrowed(v_x_304_, v___x_324_);
lean_inc(v___x_325_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 2, v___x_325_);
v___x_327_ = v___x_310_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_key_306_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_value_307_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v___x_325_);
v___x_327_ = v_reuseFailAlloc_330_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; 
v___x_328_ = lean_array_uset(v_x_304_, v___x_324_, v___x_327_);
v_x_304_ = v___x_328_;
v_x_305_ = v_tail_308_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(lean_object* v_i_332_, lean_object* v_source_333_, lean_object* v_target_334_){
_start:
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = lean_array_get_size(v_source_333_);
v___x_336_ = lean_nat_dec_lt(v_i_332_, v___x_335_);
if (v___x_336_ == 0)
{
lean_dec_ref(v_source_333_);
lean_dec(v_i_332_);
return v_target_334_;
}
else
{
lean_object* v_es_337_; lean_object* v___x_338_; lean_object* v_source_339_; lean_object* v_target_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_es_337_ = lean_array_fget(v_source_333_, v_i_332_);
v___x_338_ = lean_box(0);
v_source_339_ = lean_array_fset(v_source_333_, v_i_332_, v___x_338_);
v_target_340_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(v_target_334_, v_es_337_);
v___x_341_ = lean_unsigned_to_nat(1u);
v___x_342_ = lean_nat_add(v_i_332_, v___x_341_);
lean_dec(v_i_332_);
v_i_332_ = v___x_342_;
v_source_333_ = v_source_339_;
v_target_334_ = v_target_340_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(lean_object* v_data_344_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v_nbuckets_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_345_ = lean_array_get_size(v_data_344_);
v___x_346_ = lean_unsigned_to_nat(2u);
v_nbuckets_347_ = lean_nat_mul(v___x_345_, v___x_346_);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_box(0);
v___x_350_ = lean_mk_array(v_nbuckets_347_, v___x_349_);
v___x_351_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(v___x_348_, v_data_344_, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(lean_object* v_m_352_, lean_object* v_a_353_, lean_object* v_b_354_){
_start:
{
lean_object* v_size_355_; lean_object* v_buckets_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_399_; 
v_size_355_ = lean_ctor_get(v_m_352_, 0);
v_buckets_356_ = lean_ctor_get(v_m_352_, 1);
v_isSharedCheck_399_ = !lean_is_exclusive(v_m_352_);
if (v_isSharedCheck_399_ == 0)
{
v___x_358_ = v_m_352_;
v_isShared_359_ = v_isSharedCheck_399_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_buckets_356_);
lean_inc(v_size_355_);
lean_dec(v_m_352_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_399_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; uint64_t v___x_361_; uint64_t v___x_362_; uint64_t v___x_363_; uint64_t v_fold_364_; uint64_t v___x_365_; uint64_t v___x_366_; uint64_t v___x_367_; size_t v___x_368_; size_t v___x_369_; size_t v___x_370_; size_t v___x_371_; size_t v___x_372_; lean_object* v_bkt_373_; uint8_t v___x_374_; 
v___x_360_ = lean_array_get_size(v_buckets_356_);
v___x_361_ = l_Lean_instHashableFVarId_hash(v_a_353_);
v___x_362_ = 32ULL;
v___x_363_ = lean_uint64_shift_right(v___x_361_, v___x_362_);
v_fold_364_ = lean_uint64_xor(v___x_361_, v___x_363_);
v___x_365_ = 16ULL;
v___x_366_ = lean_uint64_shift_right(v_fold_364_, v___x_365_);
v___x_367_ = lean_uint64_xor(v_fold_364_, v___x_366_);
v___x_368_ = lean_uint64_to_usize(v___x_367_);
v___x_369_ = lean_usize_of_nat(v___x_360_);
v___x_370_ = ((size_t)1ULL);
v___x_371_ = lean_usize_sub(v___x_369_, v___x_370_);
v___x_372_ = lean_usize_land(v___x_368_, v___x_371_);
v_bkt_373_ = lean_array_uget_borrowed(v_buckets_356_, v___x_372_);
v___x_374_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_a_353_, v_bkt_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v_size_x27_376_; lean_object* v___x_377_; lean_object* v_buckets_x27_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_375_ = lean_unsigned_to_nat(1u);
v_size_x27_376_ = lean_nat_add(v_size_355_, v___x_375_);
lean_dec(v_size_355_);
lean_inc(v_bkt_373_);
v___x_377_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_377_, 0, v_a_353_);
lean_ctor_set(v___x_377_, 1, v_b_354_);
lean_ctor_set(v___x_377_, 2, v_bkt_373_);
v_buckets_x27_378_ = lean_array_uset(v_buckets_356_, v___x_372_, v___x_377_);
v___x_379_ = lean_unsigned_to_nat(4u);
v___x_380_ = lean_nat_mul(v_size_x27_376_, v___x_379_);
v___x_381_ = lean_unsigned_to_nat(3u);
v___x_382_ = lean_nat_div(v___x_380_, v___x_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_array_get_size(v_buckets_x27_378_);
v___x_384_ = lean_nat_dec_le(v___x_382_, v___x_383_);
lean_dec(v___x_382_);
if (v___x_384_ == 0)
{
lean_object* v_val_385_; lean_object* v___x_387_; 
v_val_385_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(v_buckets_x27_378_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 1, v_val_385_);
lean_ctor_set(v___x_358_, 0, v_size_x27_376_);
v___x_387_ = v___x_358_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_size_x27_376_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_val_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
else
{
lean_object* v___x_390_; 
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 1, v_buckets_x27_378_);
lean_ctor_set(v___x_358_, 0, v_size_x27_376_);
v___x_390_ = v___x_358_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_size_x27_376_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_buckets_x27_378_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
else
{
lean_object* v___x_392_; lean_object* v_buckets_x27_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
lean_inc(v_bkt_373_);
v___x_392_ = lean_box(0);
v_buckets_x27_393_ = lean_array_uset(v_buckets_356_, v___x_372_, v___x_392_);
v___x_394_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(v_a_353_, v_b_354_, v_bkt_373_);
v___x_395_ = lean_array_uset(v_buckets_x27_393_, v___x_372_, v___x_394_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 1, v___x_395_);
v___x_397_ = v___x_358_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_size_355_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v___x_395_);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; lean_object* v_ngen_403_; lean_object* v_namePrefix_404_; lean_object* v_idx_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_434_; 
v___x_402_ = lean_st_ref_get(v___y_400_);
v_ngen_403_ = lean_ctor_get(v___x_402_, 2);
lean_inc_ref(v_ngen_403_);
lean_dec(v___x_402_);
v_namePrefix_404_ = lean_ctor_get(v_ngen_403_, 0);
v_idx_405_ = lean_ctor_get(v_ngen_403_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_ngen_403_);
if (v_isSharedCheck_434_ == 0)
{
v___x_407_ = v_ngen_403_;
v_isShared_408_ = v_isSharedCheck_434_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_idx_405_);
lean_inc(v_namePrefix_404_);
lean_dec(v_ngen_403_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_434_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v_env_410_; lean_object* v_nextMacroScope_411_; lean_object* v_auxDeclNGen_412_; lean_object* v_traceState_413_; lean_object* v_cache_414_; lean_object* v_messages_415_; lean_object* v_infoState_416_; lean_object* v_snapshotTasks_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_432_; 
v___x_409_ = lean_st_ref_take(v___y_400_);
v_env_410_ = lean_ctor_get(v___x_409_, 0);
v_nextMacroScope_411_ = lean_ctor_get(v___x_409_, 1);
v_auxDeclNGen_412_ = lean_ctor_get(v___x_409_, 3);
v_traceState_413_ = lean_ctor_get(v___x_409_, 4);
v_cache_414_ = lean_ctor_get(v___x_409_, 5);
v_messages_415_ = lean_ctor_get(v___x_409_, 6);
v_infoState_416_ = lean_ctor_get(v___x_409_, 7);
v_snapshotTasks_417_ = lean_ctor_get(v___x_409_, 8);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; 
v_unused_433_ = lean_ctor_get(v___x_409_, 2);
lean_dec(v_unused_433_);
v___x_419_ = v___x_409_;
v_isShared_420_ = v_isSharedCheck_432_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_snapshotTasks_417_);
lean_inc(v_infoState_416_);
lean_inc(v_messages_415_);
lean_inc(v_cache_414_);
lean_inc(v_traceState_413_);
lean_inc(v_auxDeclNGen_412_);
lean_inc(v_nextMacroScope_411_);
lean_inc(v_env_410_);
lean_dec(v___x_409_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_432_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v_r_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
lean_inc(v_idx_405_);
lean_inc(v_namePrefix_404_);
v_r_421_ = l_Lean_Name_num___override(v_namePrefix_404_, v_idx_405_);
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_nat_add(v_idx_405_, v___x_422_);
lean_dec(v_idx_405_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 1, v___x_423_);
v___x_425_ = v___x_407_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_namePrefix_404_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v___x_423_);
v___x_425_ = v_reuseFailAlloc_431_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_427_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 2, v___x_425_);
v___x_427_ = v___x_419_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_env_410_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_nextMacroScope_411_);
lean_ctor_set(v_reuseFailAlloc_430_, 2, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_430_, 3, v_auxDeclNGen_412_);
lean_ctor_set(v_reuseFailAlloc_430_, 4, v_traceState_413_);
lean_ctor_set(v_reuseFailAlloc_430_, 5, v_cache_414_);
lean_ctor_set(v_reuseFailAlloc_430_, 6, v_messages_415_);
lean_ctor_set(v_reuseFailAlloc_430_, 7, v_infoState_416_);
lean_ctor_set(v_reuseFailAlloc_430_, 8, v_snapshotTasks_417_);
v___x_427_ = v_reuseFailAlloc_430_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_st_ref_put(v___y_400_, v___x_427_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v_r_421_);
return v___x_429_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg___boxed(lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_435_);
lean_dec(v___y_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(uint8_t v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v___x_445_; lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
v___x_445_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_443_);
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0___boxed(lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
uint8_t v___y_3107__boxed_461_; lean_object* v_res_462_; 
v___y_3107__boxed_461_ = lean_unbox(v___y_454_);
v_res_462_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(v___y_3107__boxed_461_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(lean_object* v_fvarId_463_, uint8_t v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_483_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_483_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_483_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_483_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_476_ = lean_st_ref_take(v_a_465_);
lean_inc(v_a_472_);
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v_a_472_);
v___x_478_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v___x_476_, v_fvarId_463_, v___x_477_);
v___x_479_ = lean_st_ref_put(v_a_465_, v___x_478_);
if (v_isShared_475_ == 0)
{
v___x_481_ = v___x_474_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_472_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
else
{
lean_dec(v_fvarId_463_);
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg___boxed(lean_object* v_fvarId_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
uint8_t v_a_boxed_492_; lean_object* v_res_493_; 
v_a_boxed_492_ = lean_unbox(v_a_485_);
v_res_493_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_484_, v_a_boxed_492_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(uint8_t v_pu_494_, lean_object* v_fvarId_495_, uint8_t v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___boxed(lean_object* v_pu_504_, lean_object* v_fvarId_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
uint8_t v_pu_boxed_513_; uint8_t v_a_boxed_514_; lean_object* v_res_515_; 
v_pu_boxed_513_ = lean_unbox(v_pu_504_);
v_a_boxed_514_ = lean_unbox(v_a_506_);
v_res_515_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(v_pu_boxed_513_, v_fvarId_505_, v_a_boxed_514_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_507_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(uint8_t v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_521_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___boxed(lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
uint8_t v___y_3182__boxed_531_; lean_object* v_res_532_; 
v___y_3182__boxed_531_ = lean_unbox(v___y_524_);
v_res_532_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(v___y_3182__boxed_531_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1(lean_object* v_00_u03b2_533_, lean_object* v_m_534_, lean_object* v_a_535_, lean_object* v_b_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v_m_534_, v_a_535_, v_b_536_);
return v___x_537_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(lean_object* v_00_u03b2_538_, lean_object* v_a_539_, lean_object* v_x_540_){
_start:
{
uint8_t v___x_541_; 
v___x_541_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_a_539_, v_x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___boxed(lean_object* v_00_u03b2_542_, lean_object* v_a_543_, lean_object* v_x_544_){
_start:
{
uint8_t v_res_545_; lean_object* v_r_546_; 
v_res_545_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(v_00_u03b2_542_, v_a_543_, v_x_544_);
lean_dec(v_x_544_);
lean_dec(v_a_543_);
v_r_546_ = lean_box(v_res_545_);
return v_r_546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3(lean_object* v_00_u03b2_547_, lean_object* v_data_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(v_data_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4(lean_object* v_00_u03b2_550_, lean_object* v_a_551_, lean_object* v_b_552_, lean_object* v_x_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(v_a_551_, v_b_552_, v_x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_555_, lean_object* v_i_556_, lean_object* v_source_557_, lean_object* v_target_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(v_i_556_, v_source_557_, v_target_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_560_, lean_object* v_x_561_, lean_object* v_x_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(v_x_561_, v_x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(lean_object* v_a_564_, lean_object* v_x_565_){
_start:
{
if (lean_obj_tag(v_x_565_) == 0)
{
lean_object* v___x_566_; 
v___x_566_ = lean_box(0);
return v___x_566_;
}
else
{
lean_object* v_key_567_; lean_object* v_value_568_; lean_object* v_tail_569_; uint8_t v___x_570_; 
v_key_567_ = lean_ctor_get(v_x_565_, 0);
v_value_568_ = lean_ctor_get(v_x_565_, 1);
v_tail_569_ = lean_ctor_get(v_x_565_, 2);
v___x_570_ = l_Lean_instBEqFVarId_beq(v_key_567_, v_a_564_);
if (v___x_570_ == 0)
{
v_x_565_ = v_tail_569_;
goto _start;
}
else
{
lean_object* v___x_572_; 
lean_inc(v_value_568_);
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v_value_568_);
return v___x_572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_573_, lean_object* v_x_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_573_, v_x_574_);
lean_dec(v_x_574_);
lean_dec(v_a_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(lean_object* v_m_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_buckets_578_; lean_object* v___x_579_; uint64_t v___x_580_; uint64_t v___x_581_; uint64_t v___x_582_; uint64_t v_fold_583_; uint64_t v___x_584_; uint64_t v___x_585_; uint64_t v___x_586_; size_t v___x_587_; size_t v___x_588_; size_t v___x_589_; size_t v___x_590_; size_t v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_buckets_578_ = lean_ctor_get(v_m_576_, 1);
v___x_579_ = lean_array_get_size(v_buckets_578_);
v___x_580_ = l_Lean_instHashableFVarId_hash(v_a_577_);
v___x_581_ = 32ULL;
v___x_582_ = lean_uint64_shift_right(v___x_580_, v___x_581_);
v_fold_583_ = lean_uint64_xor(v___x_580_, v___x_582_);
v___x_584_ = 16ULL;
v___x_585_ = lean_uint64_shift_right(v_fold_583_, v___x_584_);
v___x_586_ = lean_uint64_xor(v_fold_583_, v___x_585_);
v___x_587_ = lean_uint64_to_usize(v___x_586_);
v___x_588_ = lean_usize_of_nat(v___x_579_);
v___x_589_ = ((size_t)1ULL);
v___x_590_ = lean_usize_sub(v___x_588_, v___x_589_);
v___x_591_ = lean_usize_land(v___x_587_, v___x_590_);
v___x_592_ = lean_array_uget_borrowed(v_buckets_578_, v___x_591_);
v___x_593_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_577_, v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg___boxed(lean_object* v_m_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v_m_594_, v_a_595_);
lean_dec(v_a_595_);
lean_dec_ref(v_m_594_);
return v_res_596_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_instMonadEIO(lean_box(0));
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(lean_object* v_msg_602_, uint8_t v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v_toApplicative_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_676_; 
v___x_610_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
v___x_611_ = l_StateRefT_x27_instMonad___redArg(v___x_610_);
v_toApplicative_612_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; 
v_unused_677_ = lean_ctor_get(v___x_611_, 1);
lean_dec(v_unused_677_);
v___x_614_ = v___x_611_;
v_isShared_615_ = v_isSharedCheck_676_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_toApplicative_612_);
lean_dec(v___x_611_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_676_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_toFunctor_616_; lean_object* v_toSeq_617_; lean_object* v_toSeqLeft_618_; lean_object* v_toSeqRight_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_674_; 
v_toFunctor_616_ = lean_ctor_get(v_toApplicative_612_, 0);
v_toSeq_617_ = lean_ctor_get(v_toApplicative_612_, 2);
v_toSeqLeft_618_ = lean_ctor_get(v_toApplicative_612_, 3);
v_toSeqRight_619_ = lean_ctor_get(v_toApplicative_612_, 4);
v_isSharedCheck_674_ = !lean_is_exclusive(v_toApplicative_612_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; 
v_unused_675_ = lean_ctor_get(v_toApplicative_612_, 1);
lean_dec(v_unused_675_);
v___x_621_ = v_toApplicative_612_;
v_isShared_622_ = v_isSharedCheck_674_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_toSeqRight_619_);
lean_inc(v_toSeqLeft_618_);
lean_inc(v_toSeq_617_);
lean_inc(v_toFunctor_616_);
lean_dec(v_toApplicative_612_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_674_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___f_623_; lean_object* v___f_624_; lean_object* v___f_625_; lean_object* v___f_626_; lean_object* v___x_627_; lean_object* v___f_628_; lean_object* v___f_629_; lean_object* v___f_630_; lean_object* v___x_632_; 
v___f_623_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
v___f_624_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_616_);
v___f_625_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_625_, 0, v_toFunctor_616_);
v___f_626_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_626_, 0, v_toFunctor_616_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___f_625_);
lean_ctor_set(v___x_627_, 1, v___f_626_);
v___f_628_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_628_, 0, v_toSeqRight_619_);
v___f_629_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_629_, 0, v_toSeqLeft_618_);
v___f_630_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_630_, 0, v_toSeq_617_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 4, v___f_628_);
lean_ctor_set(v___x_621_, 3, v___f_629_);
lean_ctor_set(v___x_621_, 2, v___f_630_);
lean_ctor_set(v___x_621_, 1, v___f_623_);
lean_ctor_set(v___x_621_, 0, v___x_627_);
v___x_632_ = v___x_621_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v___f_623_);
lean_ctor_set(v_reuseFailAlloc_673_, 2, v___f_630_);
lean_ctor_set(v_reuseFailAlloc_673_, 3, v___f_629_);
lean_ctor_set(v_reuseFailAlloc_673_, 4, v___f_628_);
v___x_632_ = v_reuseFailAlloc_673_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_634_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v___f_624_);
lean_ctor_set(v___x_614_, 0, v___x_632_);
v___x_634_ = v___x_614_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v___f_624_);
v___x_634_ = v_reuseFailAlloc_672_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; lean_object* v_toApplicative_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_670_; 
v___x_635_ = l_StateRefT_x27_instMonad___redArg(v___x_634_);
v_toApplicative_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; 
v_unused_671_ = lean_ctor_get(v___x_635_, 1);
lean_dec(v_unused_671_);
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_670_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_toApplicative_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_670_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v_toFunctor_640_; lean_object* v_toSeq_641_; lean_object* v_toSeqLeft_642_; lean_object* v_toSeqRight_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_668_; 
v_toFunctor_640_ = lean_ctor_get(v_toApplicative_636_, 0);
v_toSeq_641_ = lean_ctor_get(v_toApplicative_636_, 2);
v_toSeqLeft_642_ = lean_ctor_get(v_toApplicative_636_, 3);
v_toSeqRight_643_ = lean_ctor_get(v_toApplicative_636_, 4);
v_isSharedCheck_668_ = !lean_is_exclusive(v_toApplicative_636_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; 
v_unused_669_ = lean_ctor_get(v_toApplicative_636_, 1);
lean_dec(v_unused_669_);
v___x_645_ = v_toApplicative_636_;
v_isShared_646_ = v_isSharedCheck_668_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_toSeqRight_643_);
lean_inc(v_toSeqLeft_642_);
lean_inc(v_toSeq_641_);
lean_inc(v_toFunctor_640_);
lean_dec(v_toApplicative_636_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_668_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___f_647_; lean_object* v___f_648_; lean_object* v___f_649_; lean_object* v___f_650_; lean_object* v___x_651_; lean_object* v___f_652_; lean_object* v___f_653_; lean_object* v___f_654_; lean_object* v___x_656_; 
v___f_647_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
v___f_648_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(v_toFunctor_640_);
v___f_649_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_649_, 0, v_toFunctor_640_);
v___f_650_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_650_, 0, v_toFunctor_640_);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___f_649_);
lean_ctor_set(v___x_651_, 1, v___f_650_);
v___f_652_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_652_, 0, v_toSeqRight_643_);
v___f_653_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_653_, 0, v_toSeqLeft_642_);
v___f_654_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_654_, 0, v_toSeq_641_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 4, v___f_652_);
lean_ctor_set(v___x_645_, 3, v___f_653_);
lean_ctor_set(v___x_645_, 2, v___f_654_);
lean_ctor_set(v___x_645_, 1, v___f_647_);
lean_ctor_set(v___x_645_, 0, v___x_651_);
v___x_656_ = v___x_645_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v___f_647_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v___f_654_);
lean_ctor_set(v_reuseFailAlloc_667_, 3, v___f_653_);
lean_ctor_set(v_reuseFailAlloc_667_, 4, v___f_652_);
v___x_656_ = v_reuseFailAlloc_667_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_658_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 1, v___f_648_);
lean_ctor_set(v___x_638_, 0, v___x_656_);
v___x_658_ = v___x_638_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v___f_648_);
v___x_658_ = v_reuseFailAlloc_666_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___f_662_; lean_object* v___x_7100__overap_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_659_ = l_StateRefT_x27_instMonad___redArg(v___x_658_);
v___x_660_ = l_Lean_instInhabitedExpr;
v___x_661_ = l_instInhabitedOfMonad___redArg(v___x_659_, v___x_660_);
v___f_662_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_662_, 0, v___x_661_);
v___x_7100__overap_663_ = lean_panic_fn_borrowed(v___f_662_, v_msg_602_);
lean_dec_ref(v___f_662_);
v___x_664_ = lean_box(v___y_603_);
lean_inc(v___y_608_);
lean_inc_ref(v___y_607_);
lean_inc(v___y_606_);
lean_inc_ref(v___y_605_);
lean_inc(v___y_604_);
v___x_665_ = lean_apply_7(v___x_7100__overap_663_, v___x_664_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, lean_box(0));
return v___x_665_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___boxed(lean_object* v_msg_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
uint8_t v___y_7246__boxed_686_; lean_object* v_res_687_; 
v___y_7246__boxed_686_ = lean_unbox(v___y_679_);
v_res_687_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v_msg_678_, v___y_7246__boxed_686_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
return v_res_687_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_691_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_692_ = lean_unsigned_to_nat(20u);
v___x_693_ = lean_unsigned_to_nat(88u);
v___x_694_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__1));
v___x_695_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_696_ = l_mkPanicMessageWithDecl(v___x_695_, v___x_694_, v___x_693_, v___x_692_, v___x_691_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(uint8_t v_pu_697_, lean_object* v_e_698_, uint8_t v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
uint8_t v___x_706_; 
v___x_706_ = l_Lean_Expr_hasFVar(v_e_698_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; 
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v_e_698_);
return v___x_707_;
}
else
{
switch(lean_obj_tag(v_e_698_))
{
case 1:
{
lean_object* v_fvarId_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v_fvarId_708_ = lean_ctor_get(v_e_698_, 0);
v___x_709_ = lean_st_ref_get(v_a_700_);
v___x_710_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v___x_709_, v_fvarId_708_);
lean_dec(v___x_709_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v___x_711_; 
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v_e_698_);
return v___x_711_;
}
else
{
lean_object* v_val_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_757_; 
lean_dec_ref_known(v_e_698_, 1);
v_val_712_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_757_ == 0)
{
v___x_714_ = v___x_710_;
v_isShared_715_ = v_isSharedCheck_757_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_val_712_);
lean_dec(v___x_710_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_757_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
switch(lean_obj_tag(v_val_712_))
{
case 0:
{
lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_716_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_715_ == 0)
{
lean_ctor_set_tag(v___x_714_, 0);
lean_ctor_set(v___x_714_, 0, v___x_716_);
v___x_718_ = v___x_714_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
case 1:
{
lean_object* v_fvarId_720_; lean_object* v___x_721_; 
lean_del_object(v___x_714_);
v_fvarId_720_ = lean_ctor_get(v_val_712_, 0);
lean_inc(v_fvarId_720_);
lean_dec_ref_known(v_val_712_, 1);
v___x_721_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_697_, v_fvarId_720_, v_a_702_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_740_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_740_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_740_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_740_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
if (lean_obj_tag(v_a_722_) == 0)
{
lean_dec(v_fvarId_720_);
goto v___jp_726_;
}
else
{
lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_738_; 
v_isSharedCheck_738_ = !lean_is_exclusive(v_a_722_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; 
v_unused_739_ = lean_ctor_get(v_a_722_, 0);
lean_dec(v_unused_739_);
v___x_732_ = v_a_722_;
v_isShared_733_ = v_isSharedCheck_738_;
goto v_resetjp_731_;
}
else
{
lean_dec(v_a_722_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_738_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
if (v___x_706_ == 0)
{
lean_del_object(v___x_732_);
lean_dec(v_fvarId_720_);
goto v___jp_726_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_736_; 
lean_del_object(v___x_724_);
v___x_734_ = l_Lean_Expr_fvar___override(v_fvarId_720_);
if (v_isShared_733_ == 0)
{
lean_ctor_set_tag(v___x_732_, 0);
lean_ctor_set(v___x_732_, 0, v___x_734_);
v___x_736_ = v___x_732_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
v___jp_726_:
{
lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_727_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_727_);
v___x_729_ = v___x_724_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v_fvarId_720_);
v_a_741_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_721_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_721_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
default: 
{
lean_object* v_expr_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_del_object(v___x_714_);
v_expr_749_ = lean_ctor_get(v_val_712_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v_val_712_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v_val_712_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_expr_749_);
lean_dec(v_val_712_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set_tag(v___x_751_, 0);
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_expr_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_758_; lean_object* v_arg_759_; lean_object* v___x_760_; 
v_fn_758_ = lean_ctor_get(v_e_698_, 0);
v_arg_759_ = lean_ctor_get(v_e_698_, 1);
lean_inc_ref(v_fn_758_);
v___x_760_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_697_, v_fn_758_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_762_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_760_, 1);
lean_inc_ref(v_arg_759_);
v___x_762_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_697_, v_arg_759_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_781_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_781_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_781_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_781_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___y_768_; size_t v___x_773_; size_t v___x_774_; uint8_t v___x_775_; 
v___x_773_ = lean_ptr_addr(v_fn_758_);
v___x_774_ = lean_ptr_addr(v_a_761_);
v___x_775_ = lean_usize_dec_eq(v___x_773_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
lean_dec_ref_known(v_e_698_, 2);
v___x_776_ = l_Lean_Expr_app___override(v_a_761_, v_a_763_);
v___y_768_ = v___x_776_;
goto v___jp_767_;
}
else
{
size_t v___x_777_; size_t v___x_778_; uint8_t v___x_779_; 
v___x_777_ = lean_ptr_addr(v_arg_759_);
v___x_778_ = lean_ptr_addr(v_a_763_);
v___x_779_ = lean_usize_dec_eq(v___x_777_, v___x_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; 
lean_dec_ref_known(v_e_698_, 2);
v___x_780_ = l_Lean_Expr_app___override(v_a_761_, v_a_763_);
v___y_768_ = v___x_780_;
goto v___jp_767_;
}
else
{
lean_dec(v_a_763_);
lean_dec(v_a_761_);
v___y_768_ = v_e_698_;
goto v___jp_767_;
}
}
v___jp_767_:
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = l_Lean_Expr_headBeta(v___y_768_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_769_);
v___x_771_ = v___x_765_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
else
{
lean_dec(v_a_761_);
lean_dec_ref_known(v_e_698_, 2);
return v___x_762_;
}
}
else
{
lean_dec_ref_known(v_e_698_, 2);
return v___x_760_;
}
}
case 6:
{
lean_object* v_binderName_782_; lean_object* v_binderType_783_; lean_object* v_body_784_; uint8_t v_binderInfo_785_; lean_object* v___x_786_; 
v_binderName_782_ = lean_ctor_get(v_e_698_, 0);
v_binderType_783_ = lean_ctor_get(v_e_698_, 1);
v_body_784_ = lean_ctor_get(v_e_698_, 2);
v_binderInfo_785_ = lean_ctor_get_uint8(v_e_698_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_783_);
v___x_786_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_697_, v_binderType_783_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_788_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_786_, 1);
lean_inc_ref(v_body_784_);
v___x_788_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_697_, v_body_784_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_815_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_815_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_815_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_815_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
size_t v___x_793_; size_t v___x_794_; uint8_t v___x_795_; 
v___x_793_ = lean_ptr_addr(v_binderType_783_);
v___x_794_ = lean_ptr_addr(v_a_787_);
v___x_795_ = lean_usize_dec_eq(v___x_793_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_798_; 
lean_inc(v_binderName_782_);
lean_dec_ref_known(v_e_698_, 3);
v___x_796_ = l_Lean_Expr_lam___override(v_binderName_782_, v_a_787_, v_a_789_, v_binderInfo_785_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_796_);
v___x_798_ = v___x_791_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
else
{
size_t v___x_800_; size_t v___x_801_; uint8_t v___x_802_; 
v___x_800_ = lean_ptr_addr(v_body_784_);
v___x_801_ = lean_ptr_addr(v_a_789_);
v___x_802_ = lean_usize_dec_eq(v___x_800_, v___x_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_805_; 
lean_inc(v_binderName_782_);
lean_dec_ref_known(v_e_698_, 3);
v___x_803_ = l_Lean_Expr_lam___override(v_binderName_782_, v_a_787_, v_a_789_, v_binderInfo_785_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_803_);
v___x_805_ = v___x_791_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
else
{
uint8_t v___x_807_; 
v___x_807_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_785_, v_binderInfo_785_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_810_; 
lean_inc(v_binderName_782_);
lean_dec_ref_known(v_e_698_, 3);
v___x_808_ = l_Lean_Expr_lam___override(v_binderName_782_, v_a_787_, v_a_789_, v_binderInfo_785_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_808_);
v___x_810_ = v___x_791_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
else
{
lean_object* v___x_813_; 
lean_dec(v_a_789_);
lean_dec(v_a_787_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v_e_698_);
v___x_813_ = v___x_791_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_e_698_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
}
else
{
lean_dec(v_a_787_);
lean_dec_ref_known(v_e_698_, 3);
return v___x_788_;
}
}
else
{
lean_dec_ref_known(v_e_698_, 3);
return v___x_786_;
}
}
case 7:
{
lean_object* v_binderName_816_; lean_object* v_binderType_817_; lean_object* v_body_818_; uint8_t v_binderInfo_819_; lean_object* v___x_820_; 
v_binderName_816_ = lean_ctor_get(v_e_698_, 0);
v_binderType_817_ = lean_ctor_get(v_e_698_, 1);
v_body_818_ = lean_ctor_get(v_e_698_, 2);
v_binderInfo_819_ = lean_ctor_get_uint8(v_e_698_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_817_);
v___x_820_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_697_, v_binderType_817_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_822_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref_known(v___x_820_, 1);
lean_inc_ref(v_body_818_);
v___x_822_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_697_, v_body_818_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_849_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_849_ == 0)
{
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_849_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_849_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
size_t v___x_827_; size_t v___x_828_; uint8_t v___x_829_; 
v___x_827_ = lean_ptr_addr(v_binderType_817_);
v___x_828_ = lean_ptr_addr(v_a_821_);
v___x_829_ = lean_usize_dec_eq(v___x_827_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_832_; 
lean_inc(v_binderName_816_);
lean_dec_ref_known(v_e_698_, 3);
v___x_830_ = l_Lean_Expr_forallE___override(v_binderName_816_, v_a_821_, v_a_823_, v_binderInfo_819_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_830_);
v___x_832_ = v___x_825_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
else
{
size_t v___x_834_; size_t v___x_835_; uint8_t v___x_836_; 
v___x_834_ = lean_ptr_addr(v_body_818_);
v___x_835_ = lean_ptr_addr(v_a_823_);
v___x_836_ = lean_usize_dec_eq(v___x_834_, v___x_835_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_839_; 
lean_inc(v_binderName_816_);
lean_dec_ref_known(v_e_698_, 3);
v___x_837_ = l_Lean_Expr_forallE___override(v_binderName_816_, v_a_821_, v_a_823_, v_binderInfo_819_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_837_);
v___x_839_ = v___x_825_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
else
{
uint8_t v___x_841_; 
v___x_841_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_819_, v_binderInfo_819_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; lean_object* v___x_844_; 
lean_inc(v_binderName_816_);
lean_dec_ref_known(v_e_698_, 3);
v___x_842_ = l_Lean_Expr_forallE___override(v_binderName_816_, v_a_821_, v_a_823_, v_binderInfo_819_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_842_);
v___x_844_ = v___x_825_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
else
{
lean_object* v___x_847_; 
lean_dec(v_a_823_);
lean_dec(v_a_821_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v_e_698_);
v___x_847_ = v___x_825_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_e_698_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
}
else
{
lean_dec(v_a_821_);
lean_dec_ref_known(v_e_698_, 3);
return v___x_822_;
}
}
else
{
lean_dec_ref_known(v_e_698_, 3);
return v___x_820_;
}
}
case 8:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec_ref_known(v_e_698_, 4);
v___x_850_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3, &l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3);
v___x_851_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v___x_850_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
return v___x_851_;
}
case 10:
{
lean_object* v_data_852_; lean_object* v_expr_853_; lean_object* v___x_854_; 
v_data_852_ = lean_ctor_get(v_e_698_, 0);
v_expr_853_ = lean_ctor_get(v_e_698_, 1);
lean_inc_ref(v_expr_853_);
v___x_854_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_697_, v_expr_853_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_869_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_869_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_869_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_869_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
size_t v___x_859_; size_t v___x_860_; uint8_t v___x_861_; 
v___x_859_ = lean_ptr_addr(v_expr_853_);
v___x_860_ = lean_ptr_addr(v_a_855_);
v___x_861_ = lean_usize_dec_eq(v___x_859_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_864_; 
lean_inc(v_data_852_);
lean_dec_ref_known(v_e_698_, 2);
v___x_862_ = l_Lean_Expr_mdata___override(v_data_852_, v_a_855_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_862_);
v___x_864_ = v___x_857_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
else
{
lean_object* v___x_867_; 
lean_dec(v_a_855_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v_e_698_);
v___x_867_ = v___x_857_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_e_698_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_698_, 2);
return v___x_854_;
}
}
case 11:
{
lean_object* v_typeName_870_; lean_object* v_idx_871_; lean_object* v_struct_872_; lean_object* v___x_873_; 
v_typeName_870_ = lean_ctor_get(v_e_698_, 0);
v_idx_871_ = lean_ctor_get(v_e_698_, 1);
v_struct_872_ = lean_ctor_get(v_e_698_, 2);
lean_inc_ref(v_struct_872_);
v___x_873_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_697_, v_struct_872_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_888_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_888_ == 0)
{
v___x_876_ = v___x_873_;
v_isShared_877_ = v_isSharedCheck_888_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_888_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
size_t v___x_878_; size_t v___x_879_; uint8_t v___x_880_; 
v___x_878_ = lean_ptr_addr(v_struct_872_);
v___x_879_ = lean_ptr_addr(v_a_874_);
v___x_880_ = lean_usize_dec_eq(v___x_878_, v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; lean_object* v___x_883_; 
lean_inc(v_idx_871_);
lean_inc(v_typeName_870_);
lean_dec_ref_known(v_e_698_, 3);
v___x_881_ = l_Lean_Expr_proj___override(v_typeName_870_, v_idx_871_, v_a_874_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_881_);
v___x_883_ = v___x_876_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
else
{
lean_object* v___x_886_; 
lean_dec(v_a_874_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v_e_698_);
v___x_886_ = v___x_876_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_e_698_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_698_, 3);
return v___x_873_;
}
}
default: 
{
lean_object* v___x_889_; 
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v_e_698_);
return v___x_889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(uint8_t v_pu_890_, lean_object* v_e_891_, uint8_t v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
if (lean_obj_tag(v_e_891_) == 5)
{
lean_object* v_fn_899_; lean_object* v_arg_900_; lean_object* v___x_901_; 
v_fn_899_ = lean_ctor_get(v_e_891_, 0);
v_arg_900_ = lean_ctor_get(v_e_891_, 1);
lean_inc_ref(v_fn_899_);
v___x_901_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_890_, v_fn_899_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_903_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v___x_901_, 1);
lean_inc_ref(v_arg_900_);
v___x_903_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_890_, v_arg_900_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_925_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_925_ == 0)
{
v___x_906_ = v___x_903_;
v_isShared_907_ = v_isSharedCheck_925_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_903_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_925_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
size_t v___x_908_; size_t v___x_909_; uint8_t v___x_910_; 
v___x_908_ = lean_ptr_addr(v_fn_899_);
v___x_909_ = lean_ptr_addr(v_a_902_);
v___x_910_ = lean_usize_dec_eq(v___x_908_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_913_; 
lean_dec_ref_known(v_e_891_, 2);
v___x_911_ = l_Lean_Expr_app___override(v_a_902_, v_a_904_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_911_);
v___x_913_ = v___x_906_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
else
{
size_t v___x_915_; size_t v___x_916_; uint8_t v___x_917_; 
v___x_915_ = lean_ptr_addr(v_arg_900_);
v___x_916_ = lean_ptr_addr(v_a_904_);
v___x_917_ = lean_usize_dec_eq(v___x_915_, v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_920_; 
lean_dec_ref_known(v_e_891_, 2);
v___x_918_ = l_Lean_Expr_app___override(v_a_902_, v_a_904_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_918_);
v___x_920_ = v___x_906_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
else
{
lean_object* v___x_923_; 
lean_dec(v_a_904_);
lean_dec(v_a_902_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v_e_891_);
v___x_923_ = v___x_906_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_e_891_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
else
{
lean_dec(v_a_902_);
lean_dec_ref_known(v_e_891_, 2);
return v___x_903_;
}
}
else
{
lean_dec_ref_known(v_e_891_, 2);
return v___x_901_;
}
}
else
{
lean_object* v___x_926_; 
v___x_926_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_890_, v_e_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_);
return v___x_926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp___boxed(lean_object* v_pu_927_, lean_object* v_e_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
uint8_t v_pu_boxed_936_; uint8_t v_a_boxed_937_; lean_object* v_res_938_; 
v_pu_boxed_936_ = lean_unbox(v_pu_927_);
v_a_boxed_937_ = lean_unbox(v_a_929_);
v_res_938_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_boxed_936_, v_e_928_, v_a_boxed_937_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___boxed(lean_object* v_pu_939_, lean_object* v_e_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
uint8_t v_pu_boxed_948_; uint8_t v_a_boxed_949_; lean_object* v_res_950_; 
v_pu_boxed_948_ = lean_unbox(v_pu_939_);
v_a_boxed_949_ = lean_unbox(v_a_941_);
v_res_950_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_boxed_948_, v_e_940_, v_a_boxed_949_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(lean_object* v_00_u03b2_951_, lean_object* v_m_952_, lean_object* v_a_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v_m_952_, v_a_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___boxed(lean_object* v_00_u03b2_955_, lean_object* v_m_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(v_00_u03b2_955_, v_m_956_, v_a_957_);
lean_dec(v_a_957_);
lean_dec_ref(v_m_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(lean_object* v_00_u03b2_959_, lean_object* v_a_960_, lean_object* v_x_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_960_, v_x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_963_, lean_object* v_a_964_, lean_object* v_x_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(v_00_u03b2_963_, v_a_964_, v_x_965_);
lean_dec(v_x_965_);
lean_dec(v_a_964_);
return v_res_966_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___closed__0(void){
_start:
{
uint8_t v___x_967_; lean_object* v___x_968_; 
v___x_967_ = 1;
v___x_968_ = l_Lean_Compiler_LCNF_Purity_ctorIdx(v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(uint8_t v_pu_969_, lean_object* v_e_970_, uint8_t v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_978_ = l_Lean_Compiler_LCNF_Purity_ctorIdx(v_pu_969_);
v___x_979_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___closed__0, &l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___closed__0);
v___x_980_ = lean_nat_dec_eq(v___x_978_, v___x_979_);
lean_dec(v___x_978_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; 
v___x_981_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_969_, v_e_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
return v___x_981_;
}
else
{
lean_object* v___x_982_; 
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v_e_970_);
return v___x_982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___boxed(lean_object* v_pu_983_, lean_object* v_e_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
uint8_t v_pu_boxed_992_; uint8_t v_a_boxed_993_; lean_object* v_res_994_; 
v_pu_boxed_992_ = lean_unbox(v_pu_983_);
v_a_boxed_993_ = lean_unbox(v_a_985_);
v_res_994_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_boxed_992_, v_e_984_, v_a_boxed_993_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t v_pu_995_, lean_object* v_p_996_, uint8_t v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_fvarId_1004_; lean_object* v_binderName_1005_; lean_object* v_type_1006_; uint8_t v_borrow_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1055_; 
v_fvarId_1004_ = lean_ctor_get(v_p_996_, 0);
v_binderName_1005_ = lean_ctor_get(v_p_996_, 1);
v_type_1006_ = lean_ctor_get(v_p_996_, 2);
v_borrow_1007_ = lean_ctor_get_uint8(v_p_996_, sizeof(void*)*3);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_p_996_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1009_ = v_p_996_;
v_isShared_1010_ = v_isSharedCheck_1055_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_type_1006_);
lean_inc(v_binderName_1005_);
lean_inc(v_fvarId_1004_);
lean_dec(v_p_996_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1055_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v_a_1012_; lean_object* v___x_1013_; 
v___x_1011_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_1005_, v_a_997_, v_a_1000_);
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref(v___x_1011_);
v___x_1013_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_995_, v_type_1006_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1015_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1014_);
lean_dec_ref_known(v___x_1013_, 1);
v___x_1015_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_1004_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1038_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1018_ = v___x_1015_;
v_isShared_1019_ = v_isSharedCheck_1038_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1015_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1038_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v_lctx_1021_; lean_object* v_nextIdx_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1037_; 
v___x_1020_ = lean_st_ref_take(v_a_1000_);
v_lctx_1021_ = lean_ctor_get(v___x_1020_, 0);
v_nextIdx_1022_ = lean_ctor_get(v___x_1020_, 1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1024_ = v___x_1020_;
v_isShared_1025_ = v_isSharedCheck_1037_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_nextIdx_1022_);
lean_inc(v_lctx_1021_);
lean_dec(v___x_1020_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1037_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 2, v_a_1014_);
lean_ctor_set(v___x_1009_, 1, v_a_1012_);
lean_ctor_set(v___x_1009_, 0, v_a_1016_);
v___x_1027_ = v___x_1009_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1016_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_a_1012_);
lean_ctor_set(v_reuseFailAlloc_1036_, 2, v_a_1014_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*3, v_borrow_1007_);
v___x_1027_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
lean_inc_ref(v___x_1027_);
v___x_1028_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_995_, v_lctx_1021_, v___x_1027_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1028_);
v___x_1030_ = v___x_1024_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_nextIdx_1022_);
v___x_1030_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = lean_st_ref_put(v_a_1000_, v___x_1030_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1027_);
v___x_1033_ = v___x_1018_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1027_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec(v_a_1014_);
lean_dec(v_a_1012_);
lean_del_object(v___x_1009_);
v_a_1039_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1015_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1015_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec(v_a_1012_);
lean_del_object(v___x_1009_);
lean_dec(v_fvarId_1004_);
v_a_1047_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1013_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1013_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(lean_object* v_pu_1056_, lean_object* v_p_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
uint8_t v_pu_boxed_1065_; uint8_t v_a_boxed_1066_; lean_object* v_res_1067_; 
v_pu_boxed_1065_ = lean_unbox(v_pu_1056_);
v_a_boxed_1066_ = lean_unbox(v_a_1058_);
v_res_1067_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_boxed_1065_, v_p_1057_, v_a_boxed_1066_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg(uint8_t v_pu_1068_, lean_object* v_arg_1069_, uint8_t v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
switch(lean_obj_tag(v_arg_1069_))
{
case 0:
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v_arg_1069_);
return v___x_1077_;
}
case 1:
{
lean_object* v_fvarId_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v_fvarId_1078_ = lean_ctor_get(v_arg_1069_, 0);
v___x_1079_ = lean_st_ref_get(v_a_1071_);
v___x_1080_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v___x_1079_, v_fvarId_1078_);
lean_dec(v___x_1079_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_arg_1069_);
return v___x_1081_;
}
else
{
lean_object* v_val_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1112_; 
lean_dec_ref_known(v_arg_1069_, 1);
v_val_1082_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1084_ = v___x_1080_;
v_isShared_1085_ = v_isSharedCheck_1112_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_val_1082_);
lean_dec(v___x_1080_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1112_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
switch(lean_obj_tag(v_val_1082_))
{
case 0:
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1086_ = lean_box(0);
if (v_isShared_1085_ == 0)
{
lean_ctor_set_tag(v___x_1084_, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1086_);
v___x_1088_ = v___x_1084_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
case 1:
{
lean_object* v_fvarId_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1100_; 
v_fvarId_1090_ = lean_ctor_get(v_val_1082_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_val_1082_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1092_ = v_val_1082_;
v_isShared_1093_ = v_isSharedCheck_1100_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_fvarId_1090_);
lean_dec(v_val_1082_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1100_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_fvarId_1090_);
v___x_1095_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1097_; 
if (v_isShared_1085_ == 0)
{
lean_ctor_set_tag(v___x_1084_, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1095_);
v___x_1097_ = v___x_1084_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
default: 
{
lean_object* v_expr_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1111_; 
v_expr_1101_ = lean_ctor_get(v_val_1082_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_val_1082_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1103_ = v_val_1082_;
v_isShared_1104_ = v_isSharedCheck_1111_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_expr_1101_);
lean_dec(v_val_1082_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1111_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_expr_1101_);
v___x_1106_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1108_; 
if (v_isShared_1085_ == 0)
{
lean_ctor_set_tag(v___x_1084_, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1106_);
v___x_1108_ = v___x_1084_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
}
}
}
default: 
{
lean_object* v_expr_1113_; lean_object* v___x_1114_; 
v_expr_1113_ = lean_ctor_get(v_arg_1069_, 0);
lean_inc_ref(v_expr_1113_);
v___x_1114_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1068_, v_expr_1113_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1123_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1123_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1123_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1119_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1068_, v_arg_1069_, v_a_1115_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1119_);
v___x_1121_ = v___x_1117_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec_ref_known(v_arg_1069_, 1);
v_a_1124_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1114_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1114_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg___boxed(lean_object* v_pu_1132_, lean_object* v_arg_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
uint8_t v_pu_boxed_1141_; uint8_t v_a_boxed_1142_; lean_object* v_res_1143_; 
v_pu_boxed_1141_ = lean_unbox(v_pu_1132_);
v_a_boxed_1142_ = lean_unbox(v_a_1134_);
v_res_1143_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_boxed_1141_, v_arg_1133_, v_a_boxed_1142_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(uint8_t v_pu_1144_, size_t v_sz_1145_, size_t v_i_1146_, lean_object* v_bs_1147_, uint8_t v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
uint8_t v___x_1155_; 
v___x_1155_ = lean_usize_dec_lt(v_i_1146_, v_sz_1145_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v_bs_1147_);
return v___x_1156_;
}
else
{
lean_object* v_v_1157_; lean_object* v___x_1158_; 
v_v_1157_ = lean_array_uget_borrowed(v_bs_1147_, v_i_1146_);
lean_inc(v_v_1157_);
v___x_1158_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_1144_, v_v_1157_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1160_; lean_object* v_bs_x27_1161_; size_t v___x_1162_; size_t v___x_1163_; lean_object* v___x_1164_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
v___x_1160_ = lean_unsigned_to_nat(0u);
v_bs_x27_1161_ = lean_array_uset(v_bs_1147_, v_i_1146_, v___x_1160_);
v___x_1162_ = ((size_t)1ULL);
v___x_1163_ = lean_usize_add(v_i_1146_, v___x_1162_);
v___x_1164_ = lean_array_uset(v_bs_x27_1161_, v_i_1146_, v_a_1159_);
v_i_1146_ = v___x_1163_;
v_bs_1147_ = v___x_1164_;
goto _start;
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec_ref(v_bs_1147_);
v_a_1166_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1158_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1158_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0___boxed(lean_object* v_pu_1174_, lean_object* v_sz_1175_, lean_object* v_i_1176_, lean_object* v_bs_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
uint8_t v_pu_boxed_1185_; size_t v_sz_boxed_1186_; size_t v_i_boxed_1187_; uint8_t v___y_339__boxed_1188_; lean_object* v_res_1189_; 
v_pu_boxed_1185_ = lean_unbox(v_pu_1174_);
v_sz_boxed_1186_ = lean_unbox_usize(v_sz_1175_);
lean_dec(v_sz_1175_);
v_i_boxed_1187_ = lean_unbox_usize(v_i_1176_);
lean_dec(v_i_1176_);
v___y_339__boxed_1188_ = lean_unbox(v___y_1178_);
v_res_1189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_boxed_1185_, v_sz_boxed_1186_, v_i_boxed_1187_, v_bs_1177_, v___y_339__boxed_1188_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs(uint8_t v_pu_1190_, lean_object* v_args_1191_, uint8_t v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
size_t v_sz_1199_; size_t v___x_1200_; lean_object* v___x_1201_; 
v_sz_1199_ = lean_array_size(v_args_1191_);
v___x_1200_ = ((size_t)0ULL);
v___x_1201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_1190_, v_sz_1199_, v___x_1200_, v_args_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs___boxed(lean_object* v_pu_1202_, lean_object* v_args_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
uint8_t v_pu_boxed_1211_; uint8_t v_a_boxed_1212_; lean_object* v_res_1213_; 
v_pu_boxed_1211_ = lean_unbox(v_pu_1202_);
v_a_boxed_1212_ = lean_unbox(v_a_1204_);
v_res_1213_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_boxed_1211_, v_args_1203_, v_a_boxed_1212_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(uint8_t v_pu_1214_, lean_object* v_e_1215_, uint8_t v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v_fvarId_1224_; lean_object* v___y_1225_; lean_object* v_args_1241_; uint8_t v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; 
switch(lean_obj_tag(v_e_1215_))
{
case 2:
{
lean_object* v_struct_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; lean_object* v___x_1269_; 
v_struct_1266_ = lean_ctor_get(v_e_1215_, 2);
v___x_1267_ = lean_st_ref_get(v_a_1217_);
v___x_1268_ = 1;
lean_inc(v_struct_1266_);
v___x_1269_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1267_, v_struct_1266_, v___x_1268_);
lean_dec(v___x_1267_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_fvarId_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1278_; 
v_fvarId_1270_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1272_ = v___x_1269_;
v_isShared_1273_ = v_isSharedCheck_1278_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_fvarId_1270_);
lean_dec(v___x_1269_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1278_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1274_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1214_, v_e_1215_, v_fvarId_1270_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1274_);
v___x_1276_ = v___x_1272_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec_ref_known(v_e_1215_, 3);
v___x_1279_ = lean_box(1);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
return v___x_1280_;
}
}
case 3:
{
lean_object* v_args_1281_; lean_object* v___x_1282_; 
v_args_1281_ = lean_ctor_get(v_e_1215_, 2);
lean_inc_ref(v_args_1281_);
v___x_1282_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1214_, v_args_1281_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1291_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1291_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1291_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1287_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1214_, v_e_1215_, v_a_1283_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1287_);
v___x_1289_ = v___x_1285_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec_ref_known(v_e_1215_, 3);
v_a_1292_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1282_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1282_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
case 4:
{
lean_object* v_fvarId_1300_; lean_object* v_args_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; lean_object* v___x_1304_; 
v_fvarId_1300_ = lean_ctor_get(v_e_1215_, 0);
v_args_1301_ = lean_ctor_get(v_e_1215_, 1);
v___x_1302_ = lean_st_ref_get(v_a_1217_);
v___x_1303_ = 1;
lean_inc(v_fvarId_1300_);
v___x_1304_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1302_, v_fvarId_1300_, v___x_1303_);
lean_dec(v___x_1302_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_fvarId_1305_; lean_object* v___x_1306_; 
v_fvarId_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_fvarId_1305_);
lean_dec_ref_known(v___x_1304_, 1);
lean_inc_ref(v_args_1301_);
v___x_1306_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1214_, v_args_1301_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1315_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1315_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1315_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1311_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_1214_, v_e_1215_, v_fvarId_1305_, v_a_1307_);
lean_dec_ref_known(v_e_1215_, 2);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1311_);
v___x_1313_ = v___x_1309_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec(v_fvarId_1305_);
lean_dec_ref_known(v_e_1215_, 2);
v_a_1316_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1306_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1306_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_dec_ref_known(v_e_1215_, 2);
v___x_1324_ = lean_box(1);
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
return v___x_1325_;
}
}
case 5:
{
lean_object* v_args_1326_; lean_object* v___x_1327_; 
v_args_1326_ = lean_ctor_get(v_e_1215_, 1);
lean_inc_ref(v_args_1326_);
v___x_1327_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1214_, v_args_1326_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1336_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1336_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1336_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1332_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1214_, v_e_1215_, v_a_1328_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v___x_1332_);
v___x_1334_ = v___x_1330_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_dec_ref_known(v_e_1215_, 2);
v_a_1337_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1327_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1327_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
case 6:
{
lean_object* v_var_1345_; 
v_var_1345_ = lean_ctor_get(v_e_1215_, 1);
lean_inc(v_var_1345_);
v_fvarId_1224_ = v_var_1345_;
v___y_1225_ = v_a_1217_;
goto v___jp_1223_;
}
case 7:
{
lean_object* v_var_1346_; 
v_var_1346_ = lean_ctor_get(v_e_1215_, 1);
lean_inc(v_var_1346_);
v_fvarId_1224_ = v_var_1346_;
v___y_1225_ = v_a_1217_;
goto v___jp_1223_;
}
case 8:
{
lean_object* v_var_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; lean_object* v___x_1350_; 
v_var_1347_ = lean_ctor_get(v_e_1215_, 2);
v___x_1348_ = lean_st_ref_get(v_a_1217_);
v___x_1349_ = 1;
lean_inc(v_var_1347_);
v___x_1350_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1348_, v_var_1347_, v___x_1349_);
lean_dec(v___x_1348_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_fvarId_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1359_; 
v_fvarId_1351_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1353_ = v___x_1350_;
v_isShared_1354_ = v_isSharedCheck_1359_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_fvarId_1351_);
lean_dec(v___x_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1359_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1355_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1214_, v_e_1215_, v_fvarId_1351_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1355_);
v___x_1357_ = v___x_1353_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_dec_ref_known(v_e_1215_, 3);
v___x_1360_ = lean_box(1);
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
return v___x_1361_;
}
}
case 9:
{
lean_object* v_args_1362_; 
v_args_1362_ = lean_ctor_get(v_e_1215_, 1);
lean_inc_ref(v_args_1362_);
v_args_1241_ = v_args_1362_;
v___y_1242_ = v_a_1216_;
v___y_1243_ = v_a_1217_;
v___y_1244_ = v_a_1218_;
v___y_1245_ = v_a_1219_;
v___y_1246_ = v_a_1220_;
v___y_1247_ = v_a_1221_;
goto v___jp_1240_;
}
case 10:
{
lean_object* v_args_1363_; 
v_args_1363_ = lean_ctor_get(v_e_1215_, 1);
lean_inc_ref(v_args_1363_);
v_args_1241_ = v_args_1363_;
v___y_1242_ = v_a_1216_;
v___y_1243_ = v_a_1217_;
v___y_1244_ = v_a_1218_;
v___y_1245_ = v_a_1219_;
v___y_1246_ = v_a_1220_;
v___y_1247_ = v_a_1221_;
goto v___jp_1240_;
}
case 11:
{
lean_object* v_n_1364_; lean_object* v_var_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; lean_object* v___x_1368_; 
v_n_1364_ = lean_ctor_get(v_e_1215_, 0);
lean_inc(v_n_1364_);
v_var_1365_ = lean_ctor_get(v_e_1215_, 1);
v___x_1366_ = lean_st_ref_get(v_a_1217_);
v___x_1367_ = 1;
lean_inc(v_var_1365_);
v___x_1368_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1366_, v_var_1365_, v___x_1367_);
lean_dec(v___x_1366_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_fvarId_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1377_; 
v_fvarId_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1377_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_fvarId_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1377_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1373_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_1214_, v_e_1215_, v_n_1364_, v_fvarId_1369_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1373_);
v___x_1375_ = v___x_1371_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
lean_dec(v_n_1364_);
lean_dec_ref_known(v_e_1215_, 2);
v___x_1378_ = lean_box(1);
v___x_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
return v___x_1379_;
}
}
case 12:
{
lean_object* v_var_1380_; lean_object* v_i_1381_; uint8_t v_updateHeader_1382_; lean_object* v_args_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; lean_object* v___x_1386_; 
v_var_1380_ = lean_ctor_get(v_e_1215_, 0);
v_i_1381_ = lean_ctor_get(v_e_1215_, 1);
lean_inc_ref(v_i_1381_);
v_updateHeader_1382_ = lean_ctor_get_uint8(v_e_1215_, sizeof(void*)*3);
v_args_1383_ = lean_ctor_get(v_e_1215_, 2);
v___x_1384_ = lean_st_ref_get(v_a_1217_);
v___x_1385_ = 1;
lean_inc(v_var_1380_);
v___x_1386_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1384_, v_var_1380_, v___x_1385_);
lean_dec(v___x_1384_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_fvarId_1387_; lean_object* v___x_1388_; 
v_fvarId_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_fvarId_1387_);
lean_dec_ref_known(v___x_1386_, 1);
lean_inc_ref(v_args_1383_);
v___x_1388_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1214_, v_args_1383_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1397_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1397_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1397_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1393_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_1214_, v_e_1215_, v_fvarId_1387_, v_i_1381_, v_updateHeader_1382_, v_a_1389_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1393_);
v___x_1395_ = v___x_1391_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec(v_fvarId_1387_);
lean_dec_ref(v_i_1381_);
lean_dec_ref_known(v_e_1215_, 3);
v_a_1398_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1388_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1388_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_dec_ref(v_i_1381_);
lean_dec_ref_known(v_e_1215_, 3);
v___x_1406_ = lean_box(1);
v___x_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
return v___x_1407_;
}
}
case 13:
{
lean_object* v_ty_1408_; lean_object* v_fvarId_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; lean_object* v___x_1412_; 
v_ty_1408_ = lean_ctor_get(v_e_1215_, 0);
lean_inc_ref(v_ty_1408_);
v_fvarId_1409_ = lean_ctor_get(v_e_1215_, 1);
v___x_1410_ = lean_st_ref_get(v_a_1217_);
v___x_1411_ = 1;
lean_inc(v_fvarId_1409_);
v___x_1412_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1410_, v_fvarId_1409_, v___x_1411_);
lean_dec(v___x_1410_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_fvarId_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1421_; 
v_fvarId_1413_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1415_ = v___x_1412_;
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_fvarId_1413_);
lean_dec(v___x_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1417_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_1214_, v_e_1215_, v_ty_1408_, v_fvarId_1413_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1417_);
v___x_1419_ = v___x_1415_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_dec_ref(v_ty_1408_);
lean_dec_ref_known(v_e_1215_, 2);
v___x_1422_ = lean_box(1);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
return v___x_1423_;
}
}
case 14:
{
lean_object* v_fvarId_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; lean_object* v___x_1427_; 
v_fvarId_1424_ = lean_ctor_get(v_e_1215_, 0);
v___x_1425_ = lean_st_ref_get(v_a_1217_);
v___x_1426_ = 1;
lean_inc(v_fvarId_1424_);
v___x_1427_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1425_, v_fvarId_1424_, v___x_1426_);
lean_dec(v___x_1425_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_fvarId_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1436_; 
v_fvarId_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_fvarId_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_1214_, v_e_1215_, v_fvarId_1428_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
else
{
lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1444_; 
v_isSharedCheck_1444_ = !lean_is_exclusive(v_e_1215_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; 
v_unused_1445_ = lean_ctor_get(v_e_1215_, 0);
lean_dec(v_unused_1445_);
v___x_1438_ = v_e_1215_;
v_isShared_1439_ = v_isSharedCheck_1444_;
goto v_resetjp_1437_;
}
else
{
lean_dec(v_e_1215_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1444_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1440_ = lean_box(1);
if (v_isShared_1439_ == 0)
{
lean_ctor_set_tag(v___x_1438_, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1440_);
v___x_1442_ = v___x_1438_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
case 15:
{
lean_object* v_fvarId_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; lean_object* v___x_1449_; 
v_fvarId_1446_ = lean_ctor_get(v_e_1215_, 0);
v___x_1447_ = lean_st_ref_get(v_a_1217_);
v___x_1448_ = 1;
lean_inc(v_fvarId_1446_);
v___x_1449_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1447_, v_fvarId_1446_, v___x_1448_);
lean_dec(v___x_1447_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_fvarId_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1458_; 
v_fvarId_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_fvarId_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1454_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_1214_, v_e_1215_, v_fvarId_1450_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1454_);
v___x_1456_ = v___x_1452_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
else
{
lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1466_; 
v_isSharedCheck_1466_ = !lean_is_exclusive(v_e_1215_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v_e_1215_, 0);
lean_dec(v_unused_1467_);
v___x_1460_ = v_e_1215_;
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
else
{
lean_dec(v_e_1215_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1462_ = lean_box(1);
if (v_isShared_1461_ == 0)
{
lean_ctor_set_tag(v___x_1460_, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1462_);
v___x_1464_ = v___x_1460_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
default: 
{
lean_object* v___x_1468_; 
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v_e_1215_);
return v___x_1468_;
}
}
v___jp_1223_:
{
lean_object* v___x_1226_; uint8_t v___x_1227_; lean_object* v___x_1228_; 
v___x_1226_ = lean_st_ref_get(v___y_1225_);
v___x_1227_ = 1;
v___x_1228_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1226_, v_fvarId_1224_, v___x_1227_);
lean_dec(v___x_1226_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_fvarId_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1237_; 
v_fvarId_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1237_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_fvarId_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1237_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1233_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1214_, v_e_1215_, v_fvarId_1229_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1233_);
v___x_1235_ = v___x_1231_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_dec(v_e_1215_);
v___x_1238_ = lean_box(1);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
return v___x_1239_;
}
}
v___jp_1240_:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1214_, v_args_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1257_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1257_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1257_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1253_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1214_, v_e_1215_, v_a_1249_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1253_);
v___x_1255_ = v___x_1251_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec(v_e_1215_);
v_a_1258_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1248_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1248_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue___boxed(lean_object* v_pu_1469_, lean_object* v_e_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
uint8_t v_pu_boxed_1478_; uint8_t v_a_boxed_1479_; lean_object* v_res_1480_; 
v_pu_boxed_1478_ = lean_unbox(v_pu_1469_);
v_a_boxed_1479_ = lean_unbox(v_a_1471_);
v_res_1480_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_boxed_1478_, v_e_1470_, v_a_boxed_1479_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
lean_dec(v_a_1476_);
lean_dec_ref(v_a_1475_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
lean_dec(v_a_1472_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(uint8_t v_pu_1481_, lean_object* v_decl_1482_, uint8_t v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v_fvarId_1490_; lean_object* v_binderName_1491_; lean_object* v_type_1492_; lean_object* v_value_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1551_; 
v_fvarId_1490_ = lean_ctor_get(v_decl_1482_, 0);
v_binderName_1491_ = lean_ctor_get(v_decl_1482_, 1);
v_type_1492_ = lean_ctor_get(v_decl_1482_, 2);
v_value_1493_ = lean_ctor_get(v_decl_1482_, 3);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_decl_1482_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1495_ = v_decl_1482_;
v_isShared_1496_ = v_isSharedCheck_1551_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_value_1493_);
lean_inc(v_type_1492_);
lean_inc(v_binderName_1491_);
lean_inc(v_fvarId_1490_);
lean_dec(v_decl_1482_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1551_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v_a_1498_; lean_object* v___x_1499_; 
v___x_1497_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_1491_, v_a_1483_, v_a_1486_);
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref(v___x_1497_);
v___x_1499_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1481_, v_type_1492_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1501_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1499_, 1);
v___x_1501_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_1481_, v_value_1493_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1503_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1501_, 1);
v___x_1503_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_1490_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1526_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1526_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1526_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; lean_object* v_lctx_1509_; lean_object* v_nextIdx_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1525_; 
v___x_1508_ = lean_st_ref_take(v_a_1486_);
v_lctx_1509_ = lean_ctor_get(v___x_1508_, 0);
v_nextIdx_1510_ = lean_ctor_get(v___x_1508_, 1);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1512_ = v___x_1508_;
v_isShared_1513_ = v_isSharedCheck_1525_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_nextIdx_1510_);
lean_inc(v_lctx_1509_);
lean_dec(v___x_1508_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1525_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 3, v_a_1502_);
lean_ctor_set(v___x_1495_, 2, v_a_1500_);
lean_ctor_set(v___x_1495_, 1, v_a_1498_);
lean_ctor_set(v___x_1495_, 0, v_a_1504_);
v___x_1515_ = v___x_1495_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1504_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_a_1498_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_a_1500_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_a_1502_);
v___x_1515_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1516_; lean_object* v___x_1518_; 
lean_inc_ref(v___x_1515_);
v___x_1516_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_1481_, v_lctx_1509_, v___x_1515_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v___x_1516_);
v___x_1518_ = v___x_1512_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_nextIdx_1510_);
v___x_1518_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1519_ = lean_st_ref_put(v_a_1486_, v___x_1518_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1515_);
v___x_1521_ = v___x_1506_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1515_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec(v_a_1502_);
lean_dec(v_a_1500_);
lean_dec(v_a_1498_);
lean_del_object(v___x_1495_);
v_a_1527_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1503_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1503_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec(v_a_1500_);
lean_dec(v_a_1498_);
lean_del_object(v___x_1495_);
lean_dec(v_fvarId_1490_);
v_a_1535_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1501_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1501_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_dec(v_a_1498_);
lean_del_object(v___x_1495_);
lean_dec(v_value_1493_);
lean_dec(v_fvarId_1490_);
v_a_1543_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1499_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1499_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(lean_object* v_pu_1552_, lean_object* v_decl_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_){
_start:
{
uint8_t v_pu_boxed_1561_; uint8_t v_a_boxed_1562_; lean_object* v_res_1563_; 
v_pu_boxed_1561_ = lean_unbox(v_pu_1552_);
v_a_boxed_1562_ = lean_unbox(v_a_1554_);
v_res_1563_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_boxed_1561_, v_decl_1553_, v_a_boxed_1562_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec(v_a_1555_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(uint8_t v_pu_1564_, size_t v_sz_1565_, size_t v_i_1566_, lean_object* v_bs_1567_, uint8_t v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
uint8_t v___x_1575_; 
v___x_1575_ = lean_usize_dec_lt(v_i_1566_, v_sz_1565_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v_bs_1567_);
return v___x_1576_;
}
else
{
lean_object* v_v_1577_; lean_object* v___x_1578_; 
v_v_1577_ = lean_array_uget_borrowed(v_bs_1567_, v_i_1566_);
lean_inc(v_v_1577_);
v___x_1578_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_1564_, v_v_1577_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1580_; lean_object* v_bs_x27_1581_; size_t v___x_1582_; size_t v___x_1583_; lean_object* v___x_1584_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1578_, 1);
v___x_1580_ = lean_unsigned_to_nat(0u);
v_bs_x27_1581_ = lean_array_uset(v_bs_1567_, v_i_1566_, v___x_1580_);
v___x_1582_ = ((size_t)1ULL);
v___x_1583_ = lean_usize_add(v_i_1566_, v___x_1582_);
v___x_1584_ = lean_array_uset(v_bs_x27_1581_, v_i_1566_, v_a_1579_);
v_i_1566_ = v___x_1583_;
v_bs_1567_ = v___x_1584_;
goto _start;
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref(v_bs_1567_);
v_a_1586_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1578_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1578_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0___boxed(lean_object* v_pu_1594_, lean_object* v_sz_1595_, lean_object* v_i_1596_, lean_object* v_bs_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
uint8_t v_pu_boxed_1605_; size_t v_sz_boxed_1606_; size_t v_i_boxed_1607_; uint8_t v___y_26864__boxed_1608_; lean_object* v_res_1609_; 
v_pu_boxed_1605_ = lean_unbox(v_pu_1594_);
v_sz_boxed_1606_ = lean_unbox_usize(v_sz_1595_);
lean_dec(v_sz_1595_);
v_i_boxed_1607_ = lean_unbox_usize(v_i_1596_);
lean_dec(v_i_1596_);
v___y_26864__boxed_1608_ = lean_unbox(v___y_1598_);
v_res_1609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_boxed_1605_, v_sz_boxed_1606_, v_i_boxed_1607_, v_bs_1597_, v___y_26864__boxed_1608_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(uint8_t v_pu_1610_, size_t v_sz_1611_, size_t v_i_1612_, lean_object* v_bs_1613_, uint8_t v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
uint8_t v___x_1621_; 
v___x_1621_ = lean_usize_dec_lt(v_i_1612_, v_sz_1611_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v_bs_1613_);
return v___x_1622_;
}
else
{
lean_object* v_v_1623_; lean_object* v___x_1624_; lean_object* v_bs_x27_1625_; lean_object* v_a_1627_; 
v_v_1623_ = lean_array_uget(v_bs_1613_, v_i_1612_);
v___x_1624_ = lean_unsigned_to_nat(0u);
v_bs_x27_1625_ = lean_array_uset(v_bs_1613_, v_i_1612_, v___x_1624_);
switch(lean_obj_tag(v_v_1623_))
{
case 0:
{
lean_object* v_ctorName_1632_; lean_object* v_params_1633_; lean_object* v_code_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1655_; 
v_ctorName_1632_ = lean_ctor_get(v_v_1623_, 0);
v_params_1633_ = lean_ctor_get(v_v_1623_, 1);
v_code_1634_ = lean_ctor_get(v_v_1623_, 2);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_v_1623_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1636_ = v_v_1623_;
v_isShared_1637_ = v_isSharedCheck_1655_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_code_1634_);
lean_inc(v_params_1633_);
lean_inc(v_ctorName_1632_);
lean_dec(v_v_1623_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1655_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
size_t v_sz_1638_; size_t v___x_1639_; lean_object* v___x_1640_; 
v_sz_1638_ = lean_array_size(v_params_1633_);
v___x_1639_ = ((size_t)0ULL);
v___x_1640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_1610_, v_sz_1638_, v___x_1639_, v_params_1633_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1642_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref_known(v___x_1640_, 1);
v___x_1642_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1610_, v_code_1634_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_a_1643_);
lean_dec_ref_known(v___x_1642_, 1);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 2, v_a_1643_);
lean_ctor_set(v___x_1636_, 1, v_a_1641_);
v___x_1645_ = v___x_1636_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_ctorName_1632_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_a_1641_);
lean_ctor_set(v_reuseFailAlloc_1646_, 2, v_a_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
v_a_1627_ = v___x_1645_;
goto v___jp_1626_;
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_dec(v_a_1641_);
lean_del_object(v___x_1636_);
lean_dec(v_ctorName_1632_);
lean_dec_ref(v_bs_x27_1625_);
v_a_1647_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1642_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1642_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
else
{
lean_del_object(v___x_1636_);
lean_dec_ref(v_code_1634_);
lean_dec(v_ctorName_1632_);
lean_dec_ref(v_bs_x27_1625_);
return v___x_1640_;
}
}
}
case 1:
{
lean_object* v_info_1656_; lean_object* v_code_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1674_; 
v_info_1656_ = lean_ctor_get(v_v_1623_, 0);
v_code_1657_ = lean_ctor_get(v_v_1623_, 1);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_v_1623_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1659_ = v_v_1623_;
v_isShared_1660_ = v_isSharedCheck_1674_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_code_1657_);
lean_inc(v_info_1656_);
lean_dec(v_v_1623_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1674_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1610_, v_code_1657_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 1, v_a_1662_);
v___x_1664_ = v___x_1659_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_info_1656_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_a_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
v_a_1627_ = v___x_1664_;
goto v___jp_1626_;
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
lean_del_object(v___x_1659_);
lean_dec_ref(v_info_1656_);
lean_dec_ref(v_bs_x27_1625_);
v_a_1666_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1661_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1661_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
default: 
{
lean_object* v_code_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1692_; 
v_code_1675_ = lean_ctor_get(v_v_1623_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_v_1623_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1677_ = v_v_1623_;
v_isShared_1678_ = v_isSharedCheck_1692_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_code_1675_);
lean_dec(v_v_1623_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1692_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1610_, v_code_1675_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1682_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1679_, 1);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v_a_1680_);
v___x_1682_ = v___x_1677_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
v_a_1627_ = v___x_1682_;
goto v___jp_1626_;
}
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
lean_del_object(v___x_1677_);
lean_dec_ref(v_bs_x27_1625_);
v_a_1684_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v___x_1679_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1679_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
}
v___jp_1626_:
{
size_t v___x_1628_; size_t v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = ((size_t)1ULL);
v___x_1629_ = lean_usize_add(v_i_1612_, v___x_1628_);
v___x_1630_ = lean_array_uset(v_bs_x27_1625_, v_i_1612_, v_a_1627_);
v_i_1612_ = v___x_1629_;
v_bs_1613_ = v___x_1630_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t v_pu_1693_, lean_object* v_code_1694_, uint8_t v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
switch(lean_obj_tag(v_code_1694_))
{
case 0:
{
lean_object* v_decl_1702_; lean_object* v_k_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1729_; 
v_decl_1702_ = lean_ctor_get(v_code_1694_, 0);
v_k_1703_ = lean_ctor_get(v_code_1694_, 1);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_code_1694_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1705_ = v_code_1694_;
v_isShared_1706_ = v_isSharedCheck_1729_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_k_1703_);
lean_inc(v_decl_1702_);
lean_dec(v_code_1694_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1729_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_1693_, v_decl_1702_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1709_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1707_, 1);
v___x_1709_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1693_, v_k_1703_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1720_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1712_ = v___x_1709_;
v_isShared_1713_ = v_isSharedCheck_1720_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1709_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1720_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 1, v_a_1710_);
lean_ctor_set(v___x_1705_, 0, v_a_1708_);
v___x_1715_ = v___x_1705_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1708_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1717_; 
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v___x_1715_);
v___x_1717_ = v___x_1712_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
else
{
lean_dec(v_a_1708_);
lean_del_object(v___x_1705_);
return v___x_1709_;
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_del_object(v___x_1705_);
lean_dec_ref(v_k_1703_);
v_a_1721_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1707_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1707_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_1730_; lean_object* v_k_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1757_; 
v_decl_1730_ = lean_ctor_get(v_code_1694_, 0);
v_k_1731_ = lean_ctor_get(v_code_1694_, 1);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_code_1694_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1733_ = v_code_1694_;
v_isShared_1734_ = v_isSharedCheck_1757_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_k_1731_);
lean_inc(v_decl_1730_);
lean_dec(v_code_1694_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1757_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1693_, v_decl_1730_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1737_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1735_, 1);
v___x_1737_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1693_, v_k_1731_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1748_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1748_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1748_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 1, v_a_1738_);
lean_ctor_set(v___x_1733_, 0, v_a_1736_);
v___x_1743_ = v___x_1733_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1736_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1745_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1743_);
v___x_1745_ = v___x_1740_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
else
{
lean_dec(v_a_1736_);
lean_del_object(v___x_1733_);
return v___x_1737_;
}
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
lean_del_object(v___x_1733_);
lean_dec_ref(v_k_1731_);
v_a_1749_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1735_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1735_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
}
case 2:
{
lean_object* v_decl_1758_; lean_object* v_k_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1785_; 
v_decl_1758_ = lean_ctor_get(v_code_1694_, 0);
v_k_1759_ = lean_ctor_get(v_code_1694_, 1);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_code_1694_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1761_ = v_code_1694_;
v_isShared_1762_ = v_isSharedCheck_1785_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_k_1759_);
lean_inc(v_decl_1758_);
lean_dec(v_code_1694_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1785_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1693_, v_decl_1758_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1765_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
v___x_1765_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1693_, v_k_1759_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1776_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1776_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1776_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 1, v_a_1766_);
lean_ctor_set(v___x_1761_, 0, v_a_1764_);
v___x_1771_ = v___x_1761_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1764_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_a_1766_);
v___x_1771_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1773_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1771_);
v___x_1773_ = v___x_1768_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
else
{
lean_dec(v_a_1764_);
lean_del_object(v___x_1761_);
return v___x_1765_;
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_del_object(v___x_1761_);
lean_dec_ref(v_k_1759_);
v_a_1777_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1763_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1763_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_1786_; lean_object* v_args_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1816_; 
v_fvarId_1786_ = lean_ctor_get(v_code_1694_, 0);
v_args_1787_ = lean_ctor_get(v_code_1694_, 1);
v_isSharedCheck_1816_ = !lean_is_exclusive(v_code_1694_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1789_ = v_code_1694_;
v_isShared_1790_ = v_isSharedCheck_1816_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_args_1787_);
lean_inc(v_fvarId_1786_);
lean_dec(v_code_1694_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1816_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; uint8_t v___x_1792_; lean_object* v___x_1793_; 
v___x_1791_ = lean_st_ref_get(v_a_1696_);
v___x_1792_ = 1;
v___x_1793_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1791_, v_fvarId_1786_, v___x_1792_);
lean_dec(v___x_1791_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_fvarId_1794_; lean_object* v___x_1795_; 
v_fvarId_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_fvarId_1794_);
lean_dec_ref_known(v___x_1793_, 1);
v___x_1795_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1693_, v_args_1787_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1806_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1798_ = v___x_1795_;
v_isShared_1799_ = v_isSharedCheck_1806_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1795_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1806_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 1, v_a_1796_);
lean_ctor_set(v___x_1789_, 0, v_fvarId_1794_);
v___x_1801_ = v___x_1789_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_fvarId_1794_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
lean_object* v___x_1803_; 
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v___x_1801_);
v___x_1803_ = v___x_1798_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
lean_dec(v_fvarId_1794_);
lean_del_object(v___x_1789_);
v_a_1807_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1795_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1795_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
else
{
lean_object* v___x_1815_; 
lean_del_object(v___x_1789_);
lean_dec_ref(v_args_1787_);
v___x_1815_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1693_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
return v___x_1815_;
}
}
}
case 4:
{
lean_object* v_cases_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1869_; 
v_cases_1817_ = lean_ctor_get(v_code_1694_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_code_1694_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1819_ = v_code_1694_;
v_isShared_1820_ = v_isSharedCheck_1869_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_cases_1817_);
lean_dec(v_code_1694_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1869_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v_typeName_1821_; lean_object* v_resultType_1822_; lean_object* v_discr_1823_; lean_object* v_alts_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1868_; 
v_typeName_1821_ = lean_ctor_get(v_cases_1817_, 0);
v_resultType_1822_ = lean_ctor_get(v_cases_1817_, 1);
v_discr_1823_ = lean_ctor_get(v_cases_1817_, 2);
v_alts_1824_ = lean_ctor_get(v_cases_1817_, 3);
v_isSharedCheck_1868_ = !lean_is_exclusive(v_cases_1817_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1826_ = v_cases_1817_;
v_isShared_1827_ = v_isSharedCheck_1868_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_alts_1824_);
lean_inc(v_discr_1823_);
lean_inc(v_resultType_1822_);
lean_inc(v_typeName_1821_);
lean_dec(v_cases_1817_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1868_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; uint8_t v___x_1829_; lean_object* v___x_1830_; 
v___x_1828_ = lean_st_ref_get(v_a_1696_);
v___x_1829_ = 1;
v___x_1830_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1828_, v_discr_1823_, v___x_1829_);
lean_dec(v___x_1828_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_fvarId_1831_; lean_object* v___x_1832_; 
v_fvarId_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_fvarId_1831_);
lean_dec_ref_known(v___x_1830_, 1);
v___x_1832_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1693_, v_resultType_1822_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; size_t v_sz_1834_; size_t v___x_1835_; lean_object* v___x_1836_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1832_, 1);
v_sz_1834_ = lean_array_size(v_alts_1824_);
v___x_1835_ = ((size_t)0ULL);
v___x_1836_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_1693_, v_sz_1834_, v___x_1835_, v_alts_1824_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1850_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1850_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1850_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 3, v_a_1837_);
lean_ctor_set(v___x_1826_, 2, v_fvarId_1831_);
lean_ctor_set(v___x_1826_, 1, v_a_1833_);
v___x_1842_ = v___x_1826_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_typeName_1821_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_a_1833_);
lean_ctor_set(v_reuseFailAlloc_1849_, 2, v_fvarId_1831_);
lean_ctor_set(v_reuseFailAlloc_1849_, 3, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1844_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1842_);
v___x_1844_ = v___x_1819_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1846_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1844_);
v___x_1846_ = v___x_1839_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec(v_a_1833_);
lean_dec(v_fvarId_1831_);
lean_del_object(v___x_1826_);
lean_dec(v_typeName_1821_);
lean_del_object(v___x_1819_);
v_a_1851_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1836_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1836_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_fvarId_1831_);
lean_del_object(v___x_1826_);
lean_dec_ref(v_alts_1824_);
lean_dec(v_typeName_1821_);
lean_del_object(v___x_1819_);
v_a_1859_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1832_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1832_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
else
{
lean_object* v___x_1867_; 
lean_del_object(v___x_1826_);
lean_dec_ref(v_alts_1824_);
lean_dec_ref(v_resultType_1822_);
lean_dec(v_typeName_1821_);
lean_del_object(v___x_1819_);
v___x_1867_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1693_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
return v___x_1867_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1889_; 
v_fvarId_1870_ = lean_ctor_get(v_code_1694_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_code_1694_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1872_ = v_code_1694_;
v_isShared_1873_ = v_isSharedCheck_1889_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_fvarId_1870_);
lean_dec(v_code_1694_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1889_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; uint8_t v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = lean_st_ref_get(v_a_1696_);
v___x_1875_ = 1;
v___x_1876_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1874_, v_fvarId_1870_, v___x_1875_);
lean_dec(v___x_1874_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_fvarId_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1887_; 
v_fvarId_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1887_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_fvarId_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1887_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v_fvarId_1877_);
v___x_1882_ = v___x_1872_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_fvarId_1877_);
v___x_1882_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1884_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1882_);
v___x_1884_ = v___x_1879_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
else
{
lean_object* v___x_1888_; 
lean_del_object(v___x_1872_);
v___x_1888_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1693_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
return v___x_1888_;
}
}
}
case 6:
{
lean_object* v_type_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1914_; 
v_type_1890_ = lean_ctor_get(v_code_1694_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_code_1694_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1892_ = v_code_1694_;
v_isShared_1893_ = v_isSharedCheck_1914_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_type_1890_);
lean_dec(v_code_1694_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1914_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; 
v___x_1894_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1693_, v_type_1890_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1905_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1905_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1905_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v_a_1895_);
v___x_1900_ = v___x_1892_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
lean_object* v___x_1902_; 
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1900_);
v___x_1902_ = v___x_1897_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_del_object(v___x_1892_);
v_a_1906_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1894_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1894_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_1915_; lean_object* v_i_1916_; lean_object* v_y_1917_; lean_object* v_k_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1941_; 
v_fvarId_1915_ = lean_ctor_get(v_code_1694_, 0);
v_i_1916_ = lean_ctor_get(v_code_1694_, 1);
v_y_1917_ = lean_ctor_get(v_code_1694_, 2);
v_k_1918_ = lean_ctor_get(v_code_1694_, 3);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_code_1694_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1920_ = v_code_1694_;
v_isShared_1921_ = v_isSharedCheck_1941_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_k_1918_);
lean_inc(v_y_1917_);
lean_inc(v_i_1916_);
lean_inc(v_fvarId_1915_);
lean_dec(v_code_1694_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1941_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; uint8_t v___x_1923_; lean_object* v___x_1924_; 
v___x_1922_ = lean_st_ref_get(v_a_1696_);
v___x_1923_ = 1;
v___x_1924_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1922_, v_fvarId_1915_, v___x_1923_);
lean_dec(v___x_1922_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_fvarId_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v_fvarId_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_fvarId_1925_);
lean_dec_ref_known(v___x_1924_, 1);
v___x_1926_ = lean_st_ref_get(v_a_1696_);
v___x_1927_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1693_, v___x_1926_, v_y_1917_, v___x_1923_);
lean_dec(v___x_1926_);
v___x_1928_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1693_, v_k_1918_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1939_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1939_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1939_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 3, v_a_1929_);
lean_ctor_set(v___x_1920_, 2, v___x_1927_);
lean_ctor_set(v___x_1920_, 0, v_fvarId_1925_);
v___x_1934_ = v___x_1920_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_fvarId_1925_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_i_1916_);
lean_ctor_set(v_reuseFailAlloc_1938_, 2, v___x_1927_);
lean_ctor_set(v_reuseFailAlloc_1938_, 3, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1936_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_1934_);
v___x_1936_ = v___x_1931_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
else
{
lean_dec(v___x_1927_);
lean_dec(v_fvarId_1925_);
lean_del_object(v___x_1920_);
lean_dec(v_i_1916_);
return v___x_1928_;
}
}
else
{
lean_object* v___x_1940_; 
lean_del_object(v___x_1920_);
lean_dec_ref(v_k_1918_);
lean_dec(v_y_1917_);
lean_dec(v_i_1916_);
v___x_1940_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1693_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
return v___x_1940_;
}
}
}
case 8:
{
lean_object* v_fvarId_1942_; lean_object* v_i_1943_; lean_object* v_y_1944_; lean_object* v_k_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1970_; 
v_fvarId_1942_ = lean_ctor_get(v_code_1694_, 0);
v_i_1943_ = lean_ctor_get(v_code_1694_, 1);
v_y_1944_ = lean_ctor_get(v_code_1694_, 2);
v_k_1945_ = lean_ctor_get(v_code_1694_, 3);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_code_1694_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1947_ = v_code_1694_;
v_isShared_1948_ = v_isSharedCheck_1970_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_k_1945_);
lean_inc(v_y_1944_);
lean_inc(v_i_1943_);
lean_inc(v_fvarId_1942_);
lean_dec(v_code_1694_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1970_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; uint8_t v___x_1950_; lean_object* v___x_1951_; 
v___x_1949_ = lean_st_ref_get(v_a_1696_);
v___x_1950_ = 1;
v___x_1951_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1949_, v_fvarId_1942_, v___x_1950_);
lean_dec(v___x_1949_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_fvarId_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v_fvarId_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_fvarId_1952_);
lean_dec_ref_known(v___x_1951_, 1);
v___x_1953_ = lean_st_ref_get(v_a_1696_);
v___x_1954_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1953_, v_y_1944_, v___x_1950_);
lean_dec(v___x_1953_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_fvarId_1955_; lean_object* v___x_1956_; 
v_fvarId_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_fvarId_1955_);
lean_dec_ref_known(v___x_1954_, 1);
v___x_1956_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1693_, v_k_1945_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1967_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_1967_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1967_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 3, v_a_1957_);
lean_ctor_set(v___x_1947_, 2, v_fvarId_1955_);
lean_ctor_set(v___x_1947_, 0, v_fvarId_1952_);
v___x_1962_ = v___x_1947_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_fvarId_1952_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_i_1943_);
lean_ctor_set(v_reuseFailAlloc_1966_, 2, v_fvarId_1955_);
lean_ctor_set(v_reuseFailAlloc_1966_, 3, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
lean_object* v___x_1964_; 
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1962_);
v___x_1964_ = v___x_1959_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
else
{
lean_dec(v_fvarId_1955_);
lean_dec(v_fvarId_1952_);
lean_del_object(v___x_1947_);
lean_dec(v_i_1943_);
return v___x_1956_;
}
}
else
{
lean_object* v___x_1968_; 
lean_dec(v_fvarId_1952_);
lean_del_object(v___x_1947_);
lean_dec_ref(v_k_1945_);
lean_dec(v_i_1943_);
v___x_1968_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1693_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
return v___x_1968_;
}
}
else
{
lean_object* v___x_1969_; 
lean_del_object(v___x_1947_);
lean_dec_ref(v_k_1945_);
lean_dec(v_y_1944_);
lean_dec(v_i_1943_);
v___x_1969_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1693_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
return v___x_1969_;
}
}
}
case 9:
{
lean_object* v_fvarId_1971_; lean_object* v_i_1972_; lean_object* v_offset_1973_; lean_object* v_y_1974_; lean_object* v_ty_1975_; lean_object* v_k_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_2011_; 
v_fvarId_1971_ = lean_ctor_get(v_code_1694_, 0);
v_i_1972_ = lean_ctor_get(v_code_1694_, 1);
v_offset_1973_ = lean_ctor_get(v_code_1694_, 2);
v_y_1974_ = lean_ctor_get(v_code_1694_, 3);
v_ty_1975_ = lean_ctor_get(v_code_1694_, 4);
v_k_1976_ = lean_ctor_get(v_code_1694_, 5);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_code_1694_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_1978_ = v_code_1694_;
v_isShared_1979_ = v_isSharedCheck_2011_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_k_1976_);
lean_inc(v_ty_1975_);
lean_inc(v_y_1974_);
lean_inc(v_offset_1973_);
lean_inc(v_i_1972_);
lean_inc(v_fvarId_1971_);
lean_dec(v_code_1694_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_2011_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; uint8_t v___x_1981_; lean_object* v___x_1982_; 
v___x_1980_ = lean_st_ref_get(v_a_1696_);
v___x_1981_ = 1;
v___x_1982_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1980_, v_fvarId_1971_, v___x_1981_);
lean_dec(v___x_1980_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_fvarId_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v_fvarId_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_fvarId_1983_);
lean_dec_ref_known(v___x_1982_, 1);
v___x_1984_ = lean_st_ref_get(v_a_1696_);
v___x_1985_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1984_, v_y_1974_, v___x_1981_);
lean_dec(v___x_1984_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_fvarId_1986_; lean_object* v___x_1987_; 
v_fvarId_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_fvarId_1986_);
lean_dec_ref_known(v___x_1985_, 1);
v___x_1987_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1693_, v_ty_1975_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___x_1989_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1987_, 1);
v___x_1989_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1693_, v_k_1976_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2000_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_2000_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2000_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 5, v_a_1990_);
lean_ctor_set(v___x_1978_, 4, v_a_1988_);
lean_ctor_set(v___x_1978_, 3, v_fvarId_1986_);
lean_ctor_set(v___x_1978_, 0, v_fvarId_1983_);
v___x_1995_ = v___x_1978_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_fvarId_1983_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_i_1972_);
lean_ctor_set(v_reuseFailAlloc_1999_, 2, v_offset_1973_);
lean_ctor_set(v_reuseFailAlloc_1999_, 3, v_fvarId_1986_);
lean_ctor_set(v_reuseFailAlloc_1999_, 4, v_a_1988_);
lean_ctor_set(v_reuseFailAlloc_1999_, 5, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1997_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_1995_);
v___x_1997_ = v___x_1992_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_dec(v_a_1988_);
lean_dec(v_fvarId_1986_);
lean_dec(v_fvarId_1983_);
lean_del_object(v___x_1978_);
lean_dec(v_offset_1973_);
lean_dec(v_i_1972_);
return v___x_1989_;
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec(v_fvarId_1986_);
lean_dec(v_fvarId_1983_);
lean_del_object(v___x_1978_);
lean_dec_ref(v_k_1976_);
lean_dec(v_offset_1973_);
lean_dec(v_i_1972_);
v_a_2001_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1987_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1987_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
else
{
lean_object* v___x_2009_; 
lean_dec(v_fvarId_1983_);
lean_del_object(v___x_1978_);
lean_dec_ref(v_k_1976_);
lean_dec_ref(v_ty_1975_);
lean_dec(v_offset_1973_);
lean_dec(v_i_1972_);
v___x_2009_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1693_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
return v___x_2009_;
}
}
else
{
lean_object* v___x_2010_; 
lean_del_object(v___x_1978_);
lean_dec_ref(v_k_1976_);
lean_dec_ref(v_ty_1975_);
lean_dec(v_y_1974_);
lean_dec(v_offset_1973_);
lean_dec(v_i_1972_);
v___x_2010_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1693_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
return v___x_2010_;
}
}
}
case 10:
{
lean_object* v_fvarId_2012_; lean_object* v_cidx_2013_; lean_object* v_k_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2035_; 
v_fvarId_2012_ = lean_ctor_get(v_code_1694_, 0);
v_cidx_2013_ = lean_ctor_get(v_code_1694_, 1);
v_k_2014_ = lean_ctor_get(v_code_1694_, 2);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_code_1694_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2016_ = v_code_1694_;
v_isShared_2017_ = v_isSharedCheck_2035_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_k_2014_);
lean_inc(v_cidx_2013_);
lean_inc(v_fvarId_2012_);
lean_dec(v_code_1694_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2035_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; uint8_t v___x_2019_; lean_object* v___x_2020_; 
v___x_2018_ = lean_st_ref_get(v_a_1696_);
v___x_2019_ = 1;
v___x_2020_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2018_, v_fvarId_2012_, v___x_2019_);
lean_dec(v___x_2018_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_fvarId_2021_; lean_object* v___x_2022_; 
v_fvarId_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_fvarId_2021_);
lean_dec_ref_known(v___x_2020_, 1);
v___x_2022_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1693_, v_k_2014_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2033_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2033_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2033_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 2, v_a_2023_);
lean_ctor_set(v___x_2016_, 0, v_fvarId_2021_);
v___x_2028_ = v___x_2016_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_fvarId_2021_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_cidx_2013_);
lean_ctor_set(v_reuseFailAlloc_2032_, 2, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2030_; 
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2028_);
v___x_2030_ = v___x_2025_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
else
{
lean_dec(v_fvarId_2021_);
lean_del_object(v___x_2016_);
lean_dec(v_cidx_2013_);
return v___x_2022_;
}
}
else
{
lean_object* v___x_2034_; 
lean_del_object(v___x_2016_);
lean_dec_ref(v_k_2014_);
lean_dec(v_cidx_2013_);
v___x_2034_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1693_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
return v___x_2034_;
}
}
}
case 11:
{
lean_object* v_fvarId_2036_; lean_object* v_n_2037_; uint8_t v_check_2038_; uint8_t v_persistent_2039_; lean_object* v_k_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2061_; 
v_fvarId_2036_ = lean_ctor_get(v_code_1694_, 0);
v_n_2037_ = lean_ctor_get(v_code_1694_, 1);
v_check_2038_ = lean_ctor_get_uint8(v_code_1694_, sizeof(void*)*3);
v_persistent_2039_ = lean_ctor_get_uint8(v_code_1694_, sizeof(void*)*3 + 1);
v_k_2040_ = lean_ctor_get(v_code_1694_, 2);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_code_1694_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2042_ = v_code_1694_;
v_isShared_2043_ = v_isSharedCheck_2061_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_k_2040_);
lean_inc(v_n_2037_);
lean_inc(v_fvarId_2036_);
lean_dec(v_code_1694_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2061_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; uint8_t v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = lean_st_ref_get(v_a_1696_);
v___x_2045_ = 1;
v___x_2046_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2044_, v_fvarId_2036_, v___x_2045_);
lean_dec(v___x_2044_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_fvarId_2047_; lean_object* v___x_2048_; 
v_fvarId_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_fvarId_2047_);
lean_dec_ref_known(v___x_2046_, 1);
v___x_2048_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1693_, v_k_2040_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2059_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2051_ = v___x_2048_;
v_isShared_2052_ = v_isSharedCheck_2059_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2048_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2059_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 2, v_a_2049_);
lean_ctor_set(v___x_2042_, 0, v_fvarId_2047_);
v___x_2054_ = v___x_2042_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_fvarId_2047_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v_n_2037_);
lean_ctor_set(v_reuseFailAlloc_2058_, 2, v_a_2049_);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, sizeof(void*)*3, v_check_2038_);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, sizeof(void*)*3 + 1, v_persistent_2039_);
v___x_2054_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2056_; 
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2054_);
v___x_2056_ = v___x_2051_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
else
{
lean_dec(v_fvarId_2047_);
lean_del_object(v___x_2042_);
lean_dec(v_n_2037_);
return v___x_2048_;
}
}
else
{
lean_object* v___x_2060_; 
lean_del_object(v___x_2042_);
lean_dec_ref(v_k_2040_);
lean_dec(v_n_2037_);
v___x_2060_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1693_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
return v___x_2060_;
}
}
}
case 12:
{
lean_object* v_fvarId_2062_; lean_object* v_n_2063_; uint8_t v_check_2064_; uint8_t v_persistent_2065_; lean_object* v_objs_x3f_2066_; lean_object* v_k_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2088_; 
v_fvarId_2062_ = lean_ctor_get(v_code_1694_, 0);
v_n_2063_ = lean_ctor_get(v_code_1694_, 1);
v_check_2064_ = lean_ctor_get_uint8(v_code_1694_, sizeof(void*)*4);
v_persistent_2065_ = lean_ctor_get_uint8(v_code_1694_, sizeof(void*)*4 + 1);
v_objs_x3f_2066_ = lean_ctor_get(v_code_1694_, 2);
v_k_2067_ = lean_ctor_get(v_code_1694_, 3);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_code_1694_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2069_ = v_code_1694_;
v_isShared_2070_ = v_isSharedCheck_2088_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_k_2067_);
lean_inc(v_objs_x3f_2066_);
lean_inc(v_n_2063_);
lean_inc(v_fvarId_2062_);
lean_dec(v_code_1694_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2088_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; uint8_t v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = lean_st_ref_get(v_a_1696_);
v___x_2072_ = 1;
v___x_2073_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2071_, v_fvarId_2062_, v___x_2072_);
lean_dec(v___x_2071_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_fvarId_2074_; lean_object* v___x_2075_; 
v_fvarId_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_fvarId_2074_);
lean_dec_ref_known(v___x_2073_, 1);
v___x_2075_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1693_, v_k_2067_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2086_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2086_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2086_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 3, v_a_2076_);
lean_ctor_set(v___x_2069_, 0, v_fvarId_2074_);
v___x_2081_ = v___x_2069_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_fvarId_2074_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_n_2063_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_objs_x3f_2066_);
lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_a_2076_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*4, v_check_2064_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*4 + 1, v_persistent_2065_);
v___x_2081_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
lean_object* v___x_2083_; 
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2081_);
v___x_2083_ = v___x_2078_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
else
{
lean_dec(v_fvarId_2074_);
lean_del_object(v___x_2069_);
lean_dec(v_objs_x3f_2066_);
lean_dec(v_n_2063_);
return v___x_2075_;
}
}
else
{
lean_object* v___x_2087_; 
lean_del_object(v___x_2069_);
lean_dec_ref(v_k_2067_);
lean_dec(v_objs_x3f_2066_);
lean_dec(v_n_2063_);
v___x_2087_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1693_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
return v___x_2087_;
}
}
}
default: 
{
lean_object* v_fvarId_2089_; lean_object* v_k_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2111_; 
v_fvarId_2089_ = lean_ctor_get(v_code_1694_, 0);
v_k_2090_ = lean_ctor_get(v_code_1694_, 1);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_code_1694_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2092_ = v_code_1694_;
v_isShared_2093_ = v_isSharedCheck_2111_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_k_2090_);
lean_inc(v_fvarId_2089_);
lean_dec(v_code_1694_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2111_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; uint8_t v___x_2095_; lean_object* v___x_2096_; 
v___x_2094_ = lean_st_ref_get(v_a_1696_);
v___x_2095_ = 1;
v___x_2096_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2094_, v_fvarId_2089_, v___x_2095_);
lean_dec(v___x_2094_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_fvarId_2097_; lean_object* v___x_2098_; 
v_fvarId_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_fvarId_2097_);
lean_dec_ref_known(v___x_2096_, 1);
v___x_2098_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1693_, v_k_2090_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2109_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2109_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2109_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 1, v_a_2099_);
lean_ctor_set(v___x_2092_, 0, v_fvarId_2097_);
v___x_2104_ = v___x_2092_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_fvarId_2097_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2106_; 
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2104_);
v___x_2106_ = v___x_2101_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
else
{
lean_dec(v_fvarId_2097_);
lean_del_object(v___x_2092_);
return v___x_2098_;
}
}
else
{
lean_object* v___x_2110_; 
lean_del_object(v___x_2092_);
lean_dec_ref(v_k_2090_);
v___x_2110_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1693_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
return v___x_2110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(uint8_t v_pu_2112_, lean_object* v_decl_2113_, uint8_t v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v_fvarId_2121_; lean_object* v_binderName_2122_; lean_object* v_params_2123_; lean_object* v_type_2124_; lean_object* v_value_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2203_; 
v_fvarId_2121_ = lean_ctor_get(v_decl_2113_, 0);
v_binderName_2122_ = lean_ctor_get(v_decl_2113_, 1);
v_params_2123_ = lean_ctor_get(v_decl_2113_, 2);
v_type_2124_ = lean_ctor_get(v_decl_2113_, 3);
v_value_2125_ = lean_ctor_get(v_decl_2113_, 4);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_decl_2113_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2127_ = v_decl_2113_;
v_isShared_2128_ = v_isSharedCheck_2203_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_value_2125_);
lean_inc(v_type_2124_);
lean_inc(v_params_2123_);
lean_inc(v_binderName_2122_);
lean_inc(v_fvarId_2121_);
lean_dec(v_decl_2113_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2203_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; 
v___x_2129_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2112_, v_type_2124_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
v___x_2131_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_2122_, v_a_2114_, v_a_2117_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; size_t v_sz_2133_; size_t v___x_2134_; lean_object* v___x_2135_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2131_, 1);
v_sz_2133_ = lean_array_size(v_params_2123_);
v___x_2134_ = ((size_t)0ULL);
v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2112_, v_sz_2133_, v___x_2134_, v_params_2123_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2137_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v___x_2137_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2112_, v_value_2125_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2139_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v___x_2139_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_2121_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2162_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2162_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2162_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; lean_object* v_lctx_2145_; lean_object* v_nextIdx_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2161_; 
v___x_2144_ = lean_st_ref_take(v_a_2117_);
v_lctx_2145_ = lean_ctor_get(v___x_2144_, 0);
v_nextIdx_2146_ = lean_ctor_get(v___x_2144_, 1);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2148_ = v___x_2144_;
v_isShared_2149_ = v_isSharedCheck_2161_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_nextIdx_2146_);
lean_inc(v_lctx_2145_);
lean_dec(v___x_2144_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2161_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 4, v_a_2138_);
lean_ctor_set(v___x_2127_, 3, v_a_2130_);
lean_ctor_set(v___x_2127_, 2, v_a_2136_);
lean_ctor_set(v___x_2127_, 1, v_a_2132_);
lean_ctor_set(v___x_2127_, 0, v_a_2140_);
v___x_2151_ = v___x_2127_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2140_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_a_2132_);
lean_ctor_set(v_reuseFailAlloc_2160_, 2, v_a_2136_);
lean_ctor_set(v_reuseFailAlloc_2160_, 3, v_a_2130_);
lean_ctor_set(v_reuseFailAlloc_2160_, 4, v_a_2138_);
v___x_2151_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2152_; lean_object* v___x_2154_; 
lean_inc_ref(v___x_2151_);
v___x_2152_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2112_, v_lctx_2145_, v___x_2151_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v___x_2152_);
v___x_2154_ = v___x_2148_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_nextIdx_2146_);
v___x_2154_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2157_; 
v___x_2155_ = lean_st_ref_put(v_a_2117_, v___x_2154_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2151_);
v___x_2157_ = v___x_2142_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2151_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_dec(v_a_2138_);
lean_dec(v_a_2136_);
lean_dec(v_a_2132_);
lean_dec(v_a_2130_);
lean_del_object(v___x_2127_);
v_a_2163_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2139_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2139_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec(v_a_2136_);
lean_dec(v_a_2132_);
lean_dec(v_a_2130_);
lean_del_object(v___x_2127_);
lean_dec(v_fvarId_2121_);
v_a_2171_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2137_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2137_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec(v_a_2132_);
lean_dec(v_a_2130_);
lean_del_object(v___x_2127_);
lean_dec_ref(v_value_2125_);
lean_dec(v_fvarId_2121_);
v_a_2179_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2135_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2135_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec(v_a_2130_);
lean_del_object(v___x_2127_);
lean_dec_ref(v_value_2125_);
lean_dec_ref(v_params_2123_);
lean_dec(v_fvarId_2121_);
v_a_2187_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2131_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2131_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
else
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
lean_del_object(v___x_2127_);
lean_dec_ref(v_value_2125_);
lean_dec_ref(v_params_2123_);
lean_dec(v_binderName_2122_);
lean_dec(v_fvarId_2121_);
v_a_2195_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_2129_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2129_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(lean_object* v_pu_2204_, lean_object* v_decl_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_){
_start:
{
uint8_t v_pu_boxed_2213_; uint8_t v_a_boxed_2214_; lean_object* v_res_2215_; 
v_pu_boxed_2213_ = lean_unbox(v_pu_2204_);
v_a_boxed_2214_ = lean_unbox(v_a_2206_);
v_res_2215_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_boxed_2213_, v_decl_2205_, v_a_boxed_2214_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
lean_dec(v_a_2211_);
lean_dec_ref(v_a_2210_);
lean_dec(v_a_2209_);
lean_dec_ref(v_a_2208_);
lean_dec(v_a_2207_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2___boxed(lean_object* v_pu_2216_, lean_object* v_sz_2217_, lean_object* v_i_2218_, lean_object* v_bs_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
uint8_t v_pu_boxed_2227_; size_t v_sz_boxed_2228_; size_t v_i_boxed_2229_; uint8_t v___y_26952__boxed_2230_; lean_object* v_res_2231_; 
v_pu_boxed_2227_ = lean_unbox(v_pu_2216_);
v_sz_boxed_2228_ = lean_unbox_usize(v_sz_2217_);
lean_dec(v_sz_2217_);
v_i_boxed_2229_ = lean_unbox_usize(v_i_2218_);
lean_dec(v_i_2218_);
v___y_26952__boxed_2230_ = lean_unbox(v___y_2220_);
v_res_2231_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_boxed_2227_, v_sz_boxed_2228_, v_i_boxed_2229_, v_bs_2219_, v___y_26952__boxed_2230_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(lean_object* v_pu_2232_, lean_object* v_code_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
uint8_t v_pu_boxed_2241_; uint8_t v_a_boxed_2242_; lean_object* v_res_2243_; 
v_pu_boxed_2241_ = lean_unbox(v_pu_2232_);
v_a_boxed_2242_ = lean_unbox(v_a_2234_);
v_res_2243_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_boxed_2241_, v_code_2233_, v_a_boxed_2242_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_);
lean_dec(v_a_2239_);
lean_dec_ref(v_a_2238_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(uint8_t v_pu_2244_, lean_object* v_msg_2245_, uint8_t v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v_toApplicative_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2319_; 
v___x_2253_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
v___x_2254_ = l_StateRefT_x27_instMonad___redArg(v___x_2253_);
v_toApplicative_2255_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; 
v_unused_2320_ = lean_ctor_get(v___x_2254_, 1);
lean_dec(v_unused_2320_);
v___x_2257_ = v___x_2254_;
v_isShared_2258_ = v_isSharedCheck_2319_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_toApplicative_2255_);
lean_dec(v___x_2254_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2319_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v_toFunctor_2259_; lean_object* v_toSeq_2260_; lean_object* v_toSeqLeft_2261_; lean_object* v_toSeqRight_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2317_; 
v_toFunctor_2259_ = lean_ctor_get(v_toApplicative_2255_, 0);
v_toSeq_2260_ = lean_ctor_get(v_toApplicative_2255_, 2);
v_toSeqLeft_2261_ = lean_ctor_get(v_toApplicative_2255_, 3);
v_toSeqRight_2262_ = lean_ctor_get(v_toApplicative_2255_, 4);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_toApplicative_2255_);
if (v_isSharedCheck_2317_ == 0)
{
lean_object* v_unused_2318_; 
v_unused_2318_ = lean_ctor_get(v_toApplicative_2255_, 1);
lean_dec(v_unused_2318_);
v___x_2264_ = v_toApplicative_2255_;
v_isShared_2265_ = v_isSharedCheck_2317_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_toSeqRight_2262_);
lean_inc(v_toSeqLeft_2261_);
lean_inc(v_toSeq_2260_);
lean_inc(v_toFunctor_2259_);
lean_dec(v_toApplicative_2255_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2317_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___f_2266_; lean_object* v___f_2267_; lean_object* v___f_2268_; lean_object* v___f_2269_; lean_object* v___x_2270_; lean_object* v___f_2271_; lean_object* v___f_2272_; lean_object* v___f_2273_; lean_object* v___x_2275_; 
v___f_2266_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
v___f_2267_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_2259_);
v___f_2268_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2268_, 0, v_toFunctor_2259_);
v___f_2269_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2269_, 0, v_toFunctor_2259_);
v___x_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___f_2268_);
lean_ctor_set(v___x_2270_, 1, v___f_2269_);
v___f_2271_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2271_, 0, v_toSeqRight_2262_);
v___f_2272_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2272_, 0, v_toSeqLeft_2261_);
v___f_2273_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2273_, 0, v_toSeq_2260_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 4, v___f_2271_);
lean_ctor_set(v___x_2264_, 3, v___f_2272_);
lean_ctor_set(v___x_2264_, 2, v___f_2273_);
lean_ctor_set(v___x_2264_, 1, v___f_2266_);
lean_ctor_set(v___x_2264_, 0, v___x_2270_);
v___x_2275_ = v___x_2264_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2270_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v___f_2266_);
lean_ctor_set(v_reuseFailAlloc_2316_, 2, v___f_2273_);
lean_ctor_set(v_reuseFailAlloc_2316_, 3, v___f_2272_);
lean_ctor_set(v_reuseFailAlloc_2316_, 4, v___f_2271_);
v___x_2275_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
lean_object* v___x_2277_; 
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 1, v___f_2267_);
lean_ctor_set(v___x_2257_, 0, v___x_2275_);
v___x_2277_ = v___x_2257_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2275_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v___f_2267_);
v___x_2277_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
lean_object* v___x_2278_; lean_object* v_toApplicative_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2313_; 
v___x_2278_ = l_StateRefT_x27_instMonad___redArg(v___x_2277_);
v_toApplicative_2279_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2313_ == 0)
{
lean_object* v_unused_2314_; 
v_unused_2314_ = lean_ctor_get(v___x_2278_, 1);
lean_dec(v_unused_2314_);
v___x_2281_ = v___x_2278_;
v_isShared_2282_ = v_isSharedCheck_2313_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_toApplicative_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2313_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v_toFunctor_2283_; lean_object* v_toSeq_2284_; lean_object* v_toSeqLeft_2285_; lean_object* v_toSeqRight_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2311_; 
v_toFunctor_2283_ = lean_ctor_get(v_toApplicative_2279_, 0);
v_toSeq_2284_ = lean_ctor_get(v_toApplicative_2279_, 2);
v_toSeqLeft_2285_ = lean_ctor_get(v_toApplicative_2279_, 3);
v_toSeqRight_2286_ = lean_ctor_get(v_toApplicative_2279_, 4);
v_isSharedCheck_2311_ = !lean_is_exclusive(v_toApplicative_2279_);
if (v_isSharedCheck_2311_ == 0)
{
lean_object* v_unused_2312_; 
v_unused_2312_ = lean_ctor_get(v_toApplicative_2279_, 1);
lean_dec(v_unused_2312_);
v___x_2288_ = v_toApplicative_2279_;
v_isShared_2289_ = v_isSharedCheck_2311_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_toSeqRight_2286_);
lean_inc(v_toSeqLeft_2285_);
lean_inc(v_toSeq_2284_);
lean_inc(v_toFunctor_2283_);
lean_dec(v_toApplicative_2279_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2311_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___f_2290_; lean_object* v___f_2291_; lean_object* v___f_2292_; lean_object* v___f_2293_; lean_object* v___x_2294_; lean_object* v___f_2295_; lean_object* v___f_2296_; lean_object* v___f_2297_; lean_object* v___x_2299_; 
v___f_2290_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
v___f_2291_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(v_toFunctor_2283_);
v___f_2292_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2292_, 0, v_toFunctor_2283_);
v___f_2293_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2293_, 0, v_toFunctor_2283_);
v___x_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___f_2292_);
lean_ctor_set(v___x_2294_, 1, v___f_2293_);
v___f_2295_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2295_, 0, v_toSeqRight_2286_);
v___f_2296_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2296_, 0, v_toSeqLeft_2285_);
v___f_2297_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2297_, 0, v_toSeq_2284_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v___f_2295_);
lean_ctor_set(v___x_2288_, 3, v___f_2296_);
lean_ctor_set(v___x_2288_, 2, v___f_2297_);
lean_ctor_set(v___x_2288_, 1, v___f_2290_);
lean_ctor_set(v___x_2288_, 0, v___x_2294_);
v___x_2299_ = v___x_2288_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2294_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v___f_2290_);
lean_ctor_set(v_reuseFailAlloc_2310_, 2, v___f_2297_);
lean_ctor_set(v_reuseFailAlloc_2310_, 3, v___f_2296_);
lean_ctor_set(v_reuseFailAlloc_2310_, 4, v___f_2295_);
v___x_2299_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
lean_object* v___x_2301_; 
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 1, v___f_2291_);
lean_ctor_set(v___x_2281_, 0, v___x_2299_);
v___x_2301_ = v___x_2281_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2299_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v___f_2291_);
v___x_2301_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___f_2305_; lean_object* v___x_10948__overap_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2302_ = l_StateRefT_x27_instMonad___redArg(v___x_2301_);
v___x_2303_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v_pu_2244_);
v___x_2304_ = l_instInhabitedOfMonad___redArg(v___x_2302_, v___x_2303_);
v___f_2305_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2305_, 0, v___x_2304_);
v___x_10948__overap_2306_ = lean_panic_fn_borrowed(v___f_2305_, v_msg_2245_);
lean_dec_ref(v___f_2305_);
v___x_2307_ = lean_box(v___y_2246_);
lean_inc(v___y_2251_);
lean_inc_ref(v___y_2250_);
lean_inc(v___y_2249_);
lean_inc_ref(v___y_2248_);
lean_inc(v___y_2247_);
v___x_2308_ = lean_apply_7(v___x_10948__overap_2306_, v___x_2307_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, lean_box(0));
return v___x_2308_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___boxed(lean_object* v_pu_2321_, lean_object* v_msg_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
uint8_t v_pu_boxed_2330_; uint8_t v___y_10979__boxed_2331_; lean_object* v_res_2332_; 
v_pu_boxed_2330_ = lean_unbox(v_pu_2321_);
v___y_10979__boxed_2331_ = lean_unbox(v___y_2323_);
v_res_2332_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_boxed_2330_, v_msg_2322_, v___y_10979__boxed_2331_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
return v_res_2332_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1(void){
_start:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2334_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2335_ = lean_unsigned_to_nat(41u);
v___x_2336_ = lean_unsigned_to_nat(217u);
v___x_2337_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2338_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2339_ = l_mkPanicMessageWithDecl(v___x_2338_, v___x_2337_, v___x_2336_, v___x_2335_, v___x_2334_);
return v___x_2339_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2(void){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2340_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2341_ = lean_unsigned_to_nat(31u);
v___x_2342_ = lean_unsigned_to_nat(222u);
v___x_2343_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2344_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2345_ = l_mkPanicMessageWithDecl(v___x_2344_, v___x_2343_, v___x_2342_, v___x_2341_, v___x_2340_);
return v___x_2345_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2346_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2347_ = lean_unsigned_to_nat(41u);
v___x_2348_ = lean_unsigned_to_nat(221u);
v___x_2349_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2350_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2351_ = l_mkPanicMessageWithDecl(v___x_2350_, v___x_2349_, v___x_2348_, v___x_2347_, v___x_2346_);
return v___x_2351_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4(void){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2352_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2353_ = lean_unsigned_to_nat(31u);
v___x_2354_ = lean_unsigned_to_nat(226u);
v___x_2355_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2356_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2357_ = l_mkPanicMessageWithDecl(v___x_2356_, v___x_2355_, v___x_2354_, v___x_2353_, v___x_2352_);
return v___x_2357_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5(void){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2358_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2359_ = lean_unsigned_to_nat(41u);
v___x_2360_ = lean_unsigned_to_nat(225u);
v___x_2361_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2362_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2363_ = l_mkPanicMessageWithDecl(v___x_2362_, v___x_2361_, v___x_2360_, v___x_2359_, v___x_2358_);
return v___x_2363_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6(void){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2364_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2365_ = lean_unsigned_to_nat(41u);
v___x_2366_ = lean_unsigned_to_nat(230u);
v___x_2367_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2368_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2369_ = l_mkPanicMessageWithDecl(v___x_2368_, v___x_2367_, v___x_2366_, v___x_2365_, v___x_2364_);
return v___x_2369_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7(void){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2370_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2371_ = lean_unsigned_to_nat(41u);
v___x_2372_ = lean_unsigned_to_nat(233u);
v___x_2373_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2374_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2375_ = l_mkPanicMessageWithDecl(v___x_2374_, v___x_2373_, v___x_2372_, v___x_2371_, v___x_2370_);
return v___x_2375_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8(void){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2376_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2377_ = lean_unsigned_to_nat(41u);
v___x_2378_ = lean_unsigned_to_nat(236u);
v___x_2379_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2380_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2381_ = l_mkPanicMessageWithDecl(v___x_2380_, v___x_2379_, v___x_2378_, v___x_2377_, v___x_2376_);
return v___x_2381_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2382_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2383_ = lean_unsigned_to_nat(41u);
v___x_2384_ = lean_unsigned_to_nat(239u);
v___x_2385_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2386_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2387_ = l_mkPanicMessageWithDecl(v___x_2386_, v___x_2385_, v___x_2384_, v___x_2383_, v___x_2382_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t v_pu_2388_, lean_object* v_decl_2389_, uint8_t v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
switch(lean_obj_tag(v_decl_2389_))
{
case 0:
{
lean_object* v_decl_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2421_; 
v_decl_2397_ = lean_ctor_get(v_decl_2389_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_decl_2389_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2399_ = v_decl_2389_;
v_isShared_2400_ = v_isSharedCheck_2421_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_decl_2397_);
lean_dec(v_decl_2389_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2421_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_2388_, v_decl_2397_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2412_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2404_ = v___x_2401_;
v_isShared_2405_ = v_isSharedCheck_2412_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2401_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2412_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v_a_2402_);
v___x_2407_ = v___x_2399_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
lean_object* v___x_2409_; 
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 0, v___x_2407_);
v___x_2409_ = v___x_2404_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
else
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
lean_del_object(v___x_2399_);
v_a_2413_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2401_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2401_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2446_; 
v_decl_2422_ = lean_ctor_get(v_decl_2389_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v_decl_2389_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2424_ = v_decl_2389_;
v_isShared_2425_ = v_isSharedCheck_2446_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_decl_2422_);
lean_dec(v_decl_2389_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2446_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2388_, v_decl_2422_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2437_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2429_ = v___x_2426_;
v_isShared_2430_ = v_isSharedCheck_2437_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2426_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2437_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v_a_2427_);
v___x_2432_ = v___x_2424_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2434_; 
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 0, v___x_2432_);
v___x_2434_ = v___x_2429_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2432_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
else
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
lean_del_object(v___x_2424_);
v_a_2438_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2426_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2426_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2438_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
}
case 2:
{
lean_object* v_decl_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2471_; 
v_decl_2447_ = lean_ctor_get(v_decl_2389_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_decl_2389_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2449_ = v_decl_2389_;
v_isShared_2450_ = v_isSharedCheck_2471_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_decl_2447_);
lean_dec(v_decl_2389_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2471_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2388_, v_decl_2447_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2462_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2454_ = v___x_2451_;
v_isShared_2455_ = v_isSharedCheck_2462_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2451_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2462_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v_a_2452_);
v___x_2457_ = v___x_2449_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2459_; 
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v___x_2457_);
v___x_2459_ = v___x_2454_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_del_object(v___x_2449_);
v_a_2463_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2451_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2451_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_2472_; lean_object* v_i_2473_; lean_object* v_y_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2496_; 
v_fvarId_2472_ = lean_ctor_get(v_decl_2389_, 0);
v_i_2473_ = lean_ctor_get(v_decl_2389_, 1);
v_y_2474_ = lean_ctor_get(v_decl_2389_, 2);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_decl_2389_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2476_ = v_decl_2389_;
v_isShared_2477_ = v_isSharedCheck_2496_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_y_2474_);
lean_inc(v_i_2473_);
lean_inc(v_fvarId_2472_);
lean_dec(v_decl_2389_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2496_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2478_; uint8_t v___x_2479_; lean_object* v___x_2480_; 
v___x_2478_ = lean_st_ref_get(v_a_2391_);
v___x_2479_ = 1;
v___x_2480_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2478_, v_fvarId_2472_, v___x_2479_);
lean_dec(v___x_2478_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_fvarId_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2493_; 
v_fvarId_2481_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2483_ = v___x_2480_;
v_isShared_2484_ = v_isSharedCheck_2493_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_fvarId_2481_);
lean_dec(v___x_2480_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2493_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2488_; 
v___x_2485_ = lean_st_ref_get(v_a_2391_);
v___x_2486_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2388_, v___x_2485_, v_y_2474_, v___x_2479_);
lean_dec(v___x_2485_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 2, v___x_2486_);
lean_ctor_set(v___x_2476_, 0, v_fvarId_2481_);
v___x_2488_ = v___x_2476_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_fvarId_2481_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_i_2473_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v___x_2486_);
v___x_2488_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2490_; 
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 0, v___x_2488_);
v___x_2490_ = v___x_2483_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2488_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
else
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
lean_dec(v___x_2480_);
lean_del_object(v___x_2476_);
lean_dec(v_y_2474_);
lean_dec(v_i_2473_);
v___x_2494_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1);
v___x_2495_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2388_, v___x_2494_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
return v___x_2495_;
}
}
}
case 4:
{
lean_object* v_fvarId_2497_; lean_object* v_i_2498_; lean_object* v_y_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2524_; 
v_fvarId_2497_ = lean_ctor_get(v_decl_2389_, 0);
v_i_2498_ = lean_ctor_get(v_decl_2389_, 1);
v_y_2499_ = lean_ctor_get(v_decl_2389_, 2);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_decl_2389_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2501_ = v_decl_2389_;
v_isShared_2502_ = v_isSharedCheck_2524_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_y_2499_);
lean_inc(v_i_2498_);
lean_inc(v_fvarId_2497_);
lean_dec(v_decl_2389_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2524_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2503_; uint8_t v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = lean_st_ref_get(v_a_2391_);
v___x_2504_ = 1;
v___x_2505_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2503_, v_fvarId_2497_, v___x_2504_);
lean_dec(v___x_2503_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_fvarId_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v_fvarId_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_fvarId_2506_);
lean_dec_ref_known(v___x_2505_, 1);
v___x_2507_ = lean_st_ref_get(v_a_2391_);
v___x_2508_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2507_, v_y_2499_, v___x_2504_);
lean_dec(v___x_2507_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_fvarId_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2519_; 
v_fvarId_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2519_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_fvarId_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2519_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 2, v_fvarId_2509_);
lean_ctor_set(v___x_2501_, 0, v_fvarId_2506_);
v___x_2514_ = v___x_2501_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_fvarId_2506_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_i_2498_);
lean_ctor_set(v_reuseFailAlloc_2518_, 2, v_fvarId_2509_);
v___x_2514_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2516_; 
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v___x_2514_);
v___x_2516_ = v___x_2511_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
else
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
lean_dec(v___x_2508_);
lean_dec(v_fvarId_2506_);
lean_del_object(v___x_2501_);
lean_dec(v_i_2498_);
v___x_2520_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2);
v___x_2521_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2388_, v___x_2520_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
return v___x_2521_;
}
}
else
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_dec(v___x_2505_);
lean_del_object(v___x_2501_);
lean_dec(v_y_2499_);
lean_dec(v_i_2498_);
v___x_2522_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3);
v___x_2523_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2388_, v___x_2522_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
return v___x_2523_;
}
}
}
case 5:
{
lean_object* v_fvarId_2525_; lean_object* v_i_2526_; lean_object* v_offset_2527_; lean_object* v_y_2528_; lean_object* v_ty_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2556_; 
v_fvarId_2525_ = lean_ctor_get(v_decl_2389_, 0);
v_i_2526_ = lean_ctor_get(v_decl_2389_, 1);
v_offset_2527_ = lean_ctor_get(v_decl_2389_, 2);
v_y_2528_ = lean_ctor_get(v_decl_2389_, 3);
v_ty_2529_ = lean_ctor_get(v_decl_2389_, 4);
v_isSharedCheck_2556_ = !lean_is_exclusive(v_decl_2389_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2531_ = v_decl_2389_;
v_isShared_2532_ = v_isSharedCheck_2556_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_ty_2529_);
lean_inc(v_y_2528_);
lean_inc(v_offset_2527_);
lean_inc(v_i_2526_);
lean_inc(v_fvarId_2525_);
lean_dec(v_decl_2389_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2556_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2533_; uint8_t v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = lean_st_ref_get(v_a_2391_);
v___x_2534_ = 1;
v___x_2535_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2533_, v_fvarId_2525_, v___x_2534_);
lean_dec(v___x_2533_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_fvarId_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v_fvarId_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_fvarId_2536_);
lean_dec_ref_known(v___x_2535_, 1);
v___x_2537_ = lean_st_ref_get(v_a_2391_);
v___x_2538_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2537_, v_y_2528_, v___x_2534_);
lean_dec(v___x_2537_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_fvarId_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2551_; 
v_fvarId_2539_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2541_ = v___x_2538_;
v_isShared_2542_ = v_isSharedCheck_2551_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_fvarId_2539_);
lean_dec(v___x_2538_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2551_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2546_; 
v___x_2543_ = lean_st_ref_get(v_a_2391_);
v___x_2544_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2388_, v___x_2543_, v___x_2534_, v_ty_2529_);
lean_dec(v___x_2543_);
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 4, v___x_2544_);
lean_ctor_set(v___x_2531_, 3, v_fvarId_2539_);
lean_ctor_set(v___x_2531_, 0, v_fvarId_2536_);
v___x_2546_ = v___x_2531_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_fvarId_2536_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_i_2526_);
lean_ctor_set(v_reuseFailAlloc_2550_, 2, v_offset_2527_);
lean_ctor_set(v_reuseFailAlloc_2550_, 3, v_fvarId_2539_);
lean_ctor_set(v_reuseFailAlloc_2550_, 4, v___x_2544_);
v___x_2546_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
lean_object* v___x_2548_; 
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2546_);
v___x_2548_ = v___x_2541_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2546_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_dec(v___x_2538_);
lean_dec(v_fvarId_2536_);
lean_del_object(v___x_2531_);
lean_dec_ref(v_ty_2529_);
lean_dec(v_offset_2527_);
lean_dec(v_i_2526_);
v___x_2552_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4);
v___x_2553_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2388_, v___x_2552_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
return v___x_2553_;
}
}
else
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_dec(v___x_2535_);
lean_del_object(v___x_2531_);
lean_dec_ref(v_ty_2529_);
lean_dec(v_y_2528_);
lean_dec(v_offset_2527_);
lean_dec(v_i_2526_);
v___x_2554_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5);
v___x_2555_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2388_, v___x_2554_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
return v___x_2555_;
}
}
}
case 6:
{
lean_object* v_fvarId_2557_; lean_object* v_cidx_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2578_; 
v_fvarId_2557_ = lean_ctor_get(v_decl_2389_, 0);
v_cidx_2558_ = lean_ctor_get(v_decl_2389_, 1);
v_isSharedCheck_2578_ = !lean_is_exclusive(v_decl_2389_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2560_ = v_decl_2389_;
v_isShared_2561_ = v_isSharedCheck_2578_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_cidx_2558_);
lean_inc(v_fvarId_2557_);
lean_dec(v_decl_2389_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2578_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2562_; uint8_t v___x_2563_; lean_object* v___x_2564_; 
v___x_2562_ = lean_st_ref_get(v_a_2391_);
v___x_2563_ = 1;
v___x_2564_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2562_, v_fvarId_2557_, v___x_2563_);
lean_dec(v___x_2562_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_fvarId_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2575_; 
v_fvarId_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2575_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_fvarId_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2575_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v_fvarId_2565_);
v___x_2570_ = v___x_2560_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_fvarId_2565_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_cidx_2558_);
v___x_2570_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
lean_object* v___x_2572_; 
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2570_);
v___x_2572_ = v___x_2567_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_dec(v___x_2564_);
lean_del_object(v___x_2560_);
lean_dec(v_cidx_2558_);
v___x_2576_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6);
v___x_2577_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2388_, v___x_2576_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
return v___x_2577_;
}
}
}
case 7:
{
lean_object* v_fvarId_2579_; lean_object* v_n_2580_; uint8_t v_check_2581_; uint8_t v_persistent_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2602_; 
v_fvarId_2579_ = lean_ctor_get(v_decl_2389_, 0);
v_n_2580_ = lean_ctor_get(v_decl_2389_, 1);
v_check_2581_ = lean_ctor_get_uint8(v_decl_2389_, sizeof(void*)*2);
v_persistent_2582_ = lean_ctor_get_uint8(v_decl_2389_, sizeof(void*)*2 + 1);
v_isSharedCheck_2602_ = !lean_is_exclusive(v_decl_2389_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2584_ = v_decl_2389_;
v_isShared_2585_ = v_isSharedCheck_2602_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_n_2580_);
lean_inc(v_fvarId_2579_);
lean_dec(v_decl_2389_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2602_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; uint8_t v___x_2587_; lean_object* v___x_2588_; 
v___x_2586_ = lean_st_ref_get(v_a_2391_);
v___x_2587_ = 1;
v___x_2588_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2586_, v_fvarId_2579_, v___x_2587_);
lean_dec(v___x_2586_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_fvarId_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2599_; 
v_fvarId_2589_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2591_ = v___x_2588_;
v_isShared_2592_ = v_isSharedCheck_2599_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_fvarId_2589_);
lean_dec(v___x_2588_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2599_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v_fvarId_2589_);
v___x_2594_ = v___x_2584_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_fvarId_2589_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_n_2580_);
lean_ctor_set_uint8(v_reuseFailAlloc_2598_, sizeof(void*)*2, v_check_2581_);
lean_ctor_set_uint8(v_reuseFailAlloc_2598_, sizeof(void*)*2 + 1, v_persistent_2582_);
v___x_2594_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2596_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v___x_2594_);
v___x_2596_ = v___x_2591_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
else
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_dec(v___x_2588_);
lean_del_object(v___x_2584_);
lean_dec(v_n_2580_);
v___x_2600_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7);
v___x_2601_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2388_, v___x_2600_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
return v___x_2601_;
}
}
}
case 8:
{
lean_object* v_fvarId_2603_; lean_object* v_n_2604_; uint8_t v_check_2605_; uint8_t v_persistent_2606_; lean_object* v_objs_x3f_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2627_; 
v_fvarId_2603_ = lean_ctor_get(v_decl_2389_, 0);
v_n_2604_ = lean_ctor_get(v_decl_2389_, 1);
v_check_2605_ = lean_ctor_get_uint8(v_decl_2389_, sizeof(void*)*3);
v_persistent_2606_ = lean_ctor_get_uint8(v_decl_2389_, sizeof(void*)*3 + 1);
v_objs_x3f_2607_ = lean_ctor_get(v_decl_2389_, 2);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_decl_2389_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2609_ = v_decl_2389_;
v_isShared_2610_ = v_isSharedCheck_2627_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_objs_x3f_2607_);
lean_inc(v_n_2604_);
lean_inc(v_fvarId_2603_);
lean_dec(v_decl_2389_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2627_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2611_; uint8_t v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_st_ref_get(v_a_2391_);
v___x_2612_ = 1;
v___x_2613_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2611_, v_fvarId_2603_, v___x_2612_);
lean_dec(v___x_2611_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_fvarId_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2624_; 
v_fvarId_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2624_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_fvarId_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2624_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v_fvarId_2614_);
v___x_2619_ = v___x_2609_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(8, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_fvarId_2614_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_n_2604_);
lean_ctor_set(v_reuseFailAlloc_2623_, 2, v_objs_x3f_2607_);
lean_ctor_set_uint8(v_reuseFailAlloc_2623_, sizeof(void*)*3, v_check_2605_);
lean_ctor_set_uint8(v_reuseFailAlloc_2623_, sizeof(void*)*3 + 1, v_persistent_2606_);
v___x_2619_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
lean_object* v___x_2621_; 
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2619_);
v___x_2621_ = v___x_2616_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_dec(v___x_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_objs_x3f_2607_);
lean_dec(v_n_2604_);
v___x_2625_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8);
v___x_2626_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2388_, v___x_2625_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
return v___x_2626_;
}
}
}
default: 
{
lean_object* v_fvarId_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2648_; 
v_fvarId_2628_ = lean_ctor_get(v_decl_2389_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_decl_2389_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2630_ = v_decl_2389_;
v_isShared_2631_ = v_isSharedCheck_2648_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_fvarId_2628_);
lean_dec(v_decl_2389_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2648_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; uint8_t v___x_2633_; lean_object* v___x_2634_; 
v___x_2632_ = lean_st_ref_get(v_a_2391_);
v___x_2633_ = 1;
v___x_2634_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2632_, v_fvarId_2628_, v___x_2633_);
lean_dec(v___x_2632_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_fvarId_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2645_; 
v_fvarId_2635_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2637_ = v___x_2634_;
v_isShared_2638_ = v_isSharedCheck_2645_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_fvarId_2635_);
lean_dec(v___x_2634_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2645_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v_fvarId_2635_);
v___x_2640_ = v___x_2630_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_fvarId_2635_);
v___x_2640_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
lean_object* v___x_2642_; 
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v___x_2640_);
v___x_2642_ = v___x_2637_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2640_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
else
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
lean_dec(v___x_2634_);
lean_del_object(v___x_2630_);
v___x_2646_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9);
v___x_2647_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2388_, v___x_2646_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
return v___x_2647_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(lean_object* v_pu_2649_, lean_object* v_decl_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_){
_start:
{
uint8_t v_pu_boxed_2658_; uint8_t v_a_boxed_2659_; lean_object* v_res_2660_; 
v_pu_boxed_2658_ = lean_unbox(v_pu_2649_);
v_a_boxed_2659_ = lean_unbox(v_a_2651_);
v_res_2660_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v_pu_boxed_2658_, v_decl_2650_, v_a_boxed_2659_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t v_pu_2661_, lean_object* v_code_2662_, lean_object* v_s_2663_, uint8_t v_uniqueIdents_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = lean_st_mk_ref(v_s_2663_);
v___x_2671_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2661_, v_code_2662_, v_uniqueIdents_2664_, v___x_2670_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2680_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2680_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2680_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2676_; lean_object* v___x_2678_; 
v___x_2676_ = lean_st_ref_get(v___x_2670_);
lean_dec(v___x_2670_);
lean_dec(v___x_2676_);
if (v_isShared_2675_ == 0)
{
v___x_2678_ = v___x_2674_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2672_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
else
{
lean_dec(v___x_2670_);
return v___x_2671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize___boxed(lean_object* v_pu_2681_, lean_object* v_code_2682_, lean_object* v_s_2683_, lean_object* v_uniqueIdents_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
uint8_t v_pu_boxed_2690_; uint8_t v_uniqueIdents_boxed_2691_; lean_object* v_res_2692_; 
v_pu_boxed_2690_ = lean_unbox(v_pu_2681_);
v_uniqueIdents_boxed_2691_ = lean_unbox(v_uniqueIdents_2684_);
v_res_2692_ = l_Lean_Compiler_LCNF_Code_internalize(v_pu_boxed_2690_, v_code_2682_, v_s_2683_, v_uniqueIdents_boxed_2691_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(lean_object* v_f_2693_, lean_object* v_v_2694_, uint8_t v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
if (lean_obj_tag(v_v_2694_) == 0)
{
lean_object* v_code_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2727_; 
v_code_2702_ = lean_ctor_get(v_v_2694_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_v_2694_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2704_ = v_v_2694_;
v_isShared_2705_ = v_isSharedCheck_2727_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_code_2702_);
lean_dec(v_v_2694_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2727_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = lean_box(v___y_2695_);
lean_inc(v___y_2700_);
lean_inc_ref(v___y_2699_);
lean_inc(v___y_2698_);
lean_inc_ref(v___y_2697_);
lean_inc(v___y_2696_);
v___x_2707_ = lean_apply_8(v_f_2693_, v_code_2702_, v___x_2706_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, lean_box(0));
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2718_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2710_ = v___x_2707_;
v_isShared_2711_ = v_isSharedCheck_2718_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2718_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 0, v_a_2708_);
v___x_2713_ = v___x_2704_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
lean_object* v___x_2715_; 
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v___x_2713_);
v___x_2715_ = v___x_2710_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2713_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_del_object(v___x_2704_);
v_a_2719_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2707_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2707_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
else
{
lean_object* v___x_2728_; 
lean_dec_ref(v_f_2693_);
v___x_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2728_, 0, v_v_2694_);
return v___x_2728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg___boxed(lean_object* v_f_2729_, lean_object* v_v_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
uint8_t v___y_1412__boxed_2738_; lean_object* v_res_2739_; 
v___y_1412__boxed_2738_ = lean_unbox(v___y_2731_);
v_res_2739_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2729_, v_v_2730_, v___y_1412__boxed_2738_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(uint8_t v_pu_2740_, lean_object* v_f_2741_, lean_object* v_v_2742_, uint8_t v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2741_, v_v_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___boxed(lean_object* v_pu_2751_, lean_object* v_f_2752_, lean_object* v_v_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
uint8_t v_pu_boxed_2761_; uint8_t v___y_1488__boxed_2762_; lean_object* v_res_2763_; 
v_pu_boxed_2761_ = lean_unbox(v_pu_2751_);
v___y_1488__boxed_2762_ = lean_unbox(v___y_2754_);
v_res_2763_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(v_pu_boxed_2761_, v_f_2752_, v_v_2753_, v___y_1488__boxed_2762_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(uint8_t v_pu_2764_, lean_object* v_decl_2765_, uint8_t v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v_toSignature_2773_; lean_object* v_value_2774_; uint8_t v_recursive_2775_; lean_object* v_inlineAttr_x3f_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2836_; 
v_toSignature_2773_ = lean_ctor_get(v_decl_2765_, 0);
v_value_2774_ = lean_ctor_get(v_decl_2765_, 1);
v_recursive_2775_ = lean_ctor_get_uint8(v_decl_2765_, sizeof(void*)*3);
v_inlineAttr_x3f_2776_ = lean_ctor_get(v_decl_2765_, 2);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_decl_2765_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2778_ = v_decl_2765_;
v_isShared_2779_ = v_isSharedCheck_2836_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_inlineAttr_x3f_2776_);
lean_inc(v_value_2774_);
lean_inc(v_toSignature_2773_);
lean_dec(v_decl_2765_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2836_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v_name_2780_; lean_object* v_levelParams_2781_; lean_object* v_type_2782_; lean_object* v_params_2783_; uint8_t v_safe_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2835_; 
v_name_2780_ = lean_ctor_get(v_toSignature_2773_, 0);
v_levelParams_2781_ = lean_ctor_get(v_toSignature_2773_, 1);
v_type_2782_ = lean_ctor_get(v_toSignature_2773_, 2);
v_params_2783_ = lean_ctor_get(v_toSignature_2773_, 3);
v_safe_2784_ = lean_ctor_get_uint8(v_toSignature_2773_, sizeof(void*)*4);
v_isSharedCheck_2835_ = !lean_is_exclusive(v_toSignature_2773_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2786_ = v_toSignature_2773_;
v_isShared_2787_ = v_isSharedCheck_2835_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_params_2783_);
lean_inc(v_type_2782_);
lean_inc(v_levelParams_2781_);
lean_inc(v_name_2780_);
lean_dec(v_toSignature_2773_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2835_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2788_; 
v___x_2788_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2764_, v_type_2782_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; size_t v_sz_2790_; size_t v___x_2791_; lean_object* v___x_2792_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
v_sz_2790_ = lean_array_size(v_params_2783_);
v___x_2791_ = ((size_t)0ULL);
v___x_2792_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2764_, v_sz_2790_, v___x_2791_, v_params_2783_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2792_, 1);
v___x_2794_ = lean_box(v_pu_2764_);
v___x_2795_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed), 9, 1);
lean_closure_set(v___x_2795_, 0, v___x_2794_);
v___x_2796_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v___x_2795_, v_value_2774_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2810_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2799_ = v___x_2796_;
v_isShared_2800_ = v_isSharedCheck_2810_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v___x_2796_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2810_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2802_; 
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 3, v_a_2793_);
lean_ctor_set(v___x_2786_, 2, v_a_2789_);
v___x_2802_ = v___x_2786_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_name_2780_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v_levelParams_2781_);
lean_ctor_set(v_reuseFailAlloc_2809_, 2, v_a_2789_);
lean_ctor_set(v_reuseFailAlloc_2809_, 3, v_a_2793_);
lean_ctor_set_uint8(v_reuseFailAlloc_2809_, sizeof(void*)*4, v_safe_2784_);
v___x_2802_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2804_; 
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 1, v_a_2797_);
lean_ctor_set(v___x_2778_, 0, v___x_2802_);
v___x_2804_ = v___x_2778_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2802_);
lean_ctor_set(v_reuseFailAlloc_2808_, 1, v_a_2797_);
lean_ctor_set(v_reuseFailAlloc_2808_, 2, v_inlineAttr_x3f_2776_);
lean_ctor_set_uint8(v_reuseFailAlloc_2808_, sizeof(void*)*3, v_recursive_2775_);
v___x_2804_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
lean_object* v___x_2806_; 
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2804_);
v___x_2806_ = v___x_2799_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v___x_2804_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
lean_dec(v_a_2793_);
lean_dec(v_a_2789_);
lean_del_object(v___x_2786_);
lean_dec(v_levelParams_2781_);
lean_dec(v_name_2780_);
lean_del_object(v___x_2778_);
lean_dec(v_inlineAttr_x3f_2776_);
v_a_2811_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2796_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2796_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec(v_a_2789_);
lean_del_object(v___x_2786_);
lean_dec(v_levelParams_2781_);
lean_dec(v_name_2780_);
lean_del_object(v___x_2778_);
lean_dec(v_inlineAttr_x3f_2776_);
lean_dec_ref(v_value_2774_);
v_a_2819_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2792_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2792_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_del_object(v___x_2786_);
lean_dec_ref(v_params_2783_);
lean_dec(v_levelParams_2781_);
lean_dec(v_name_2780_);
lean_del_object(v___x_2778_);
lean_dec(v_inlineAttr_x3f_2776_);
lean_dec_ref(v_value_2774_);
v_a_2827_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2788_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2788_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go___boxed(lean_object* v_pu_2837_, lean_object* v_decl_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
uint8_t v_pu_boxed_2846_; uint8_t v_a_boxed_2847_; lean_object* v_res_2848_; 
v_pu_boxed_2846_ = lean_unbox(v_pu_2837_);
v_a_boxed_2847_ = lean_unbox(v_a_2839_);
v_res_2848_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_boxed_2846_, v_decl_2838_, v_a_boxed_2847_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
lean_dec(v_a_2842_);
lean_dec_ref(v_a_2841_);
lean_dec(v_a_2840_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t v_pu_2849_, lean_object* v_decl_2850_, lean_object* v_s_2851_, uint8_t v_uniqueIdents_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2858_ = lean_st_mk_ref(v_s_2851_);
v___x_2859_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_2849_, v_decl_2850_, v_uniqueIdents_2852_, v___x_2858_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2868_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2862_ = v___x_2859_;
v_isShared_2863_ = v_isSharedCheck_2868_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2859_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2868_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2864_; lean_object* v___x_2866_; 
v___x_2864_ = lean_st_ref_get(v___x_2858_);
lean_dec(v___x_2858_);
lean_dec(v___x_2864_);
if (v_isShared_2863_ == 0)
{
v___x_2866_ = v___x_2862_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2860_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
else
{
lean_dec(v___x_2858_);
return v___x_2859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize___boxed(lean_object* v_pu_2869_, lean_object* v_decl_2870_, lean_object* v_s_2871_, lean_object* v_uniqueIdents_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
uint8_t v_pu_boxed_2878_; uint8_t v_uniqueIdents_boxed_2879_; lean_object* v_res_2880_; 
v_pu_boxed_2878_ = lean_unbox(v_pu_2869_);
v_uniqueIdents_boxed_2879_ = lean_unbox(v_uniqueIdents_2872_);
v_res_2880_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_boxed_2878_, v_decl_2870_, v_s_2871_, v_uniqueIdents_boxed_2879_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
lean_dec(v_a_2876_);
lean_dec_ref(v_a_2875_);
lean_dec(v_a_2874_);
lean_dec_ref(v_a_2873_);
return v_res_2880_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2881_ = lean_box(0);
v___x_2882_ = lean_unsigned_to_nat(16u);
v___x_2883_ = lean_mk_array(v___x_2882_, v___x_2881_);
return v___x_2883_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2884_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0);
v___x_2885_ = lean_unsigned_to_nat(0u);
v___x_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
lean_ctor_set(v___x_2886_, 1, v___x_2884_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(uint8_t v_pu_2887_, size_t v_sz_2888_, size_t v_i_2889_, lean_object* v_bs_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
uint8_t v___x_2896_; 
v___x_2896_ = lean_usize_dec_lt(v_i_2889_, v_sz_2888_);
if (v___x_2896_ == 0)
{
lean_object* v___x_2897_; 
v___x_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2897_, 0, v_bs_2890_);
return v___x_2897_;
}
else
{
lean_object* v___x_2898_; lean_object* v_lctx_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2927_; 
v___x_2898_ = lean_st_ref_take(v___y_2892_);
v_lctx_2899_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2927_ == 0)
{
lean_object* v_unused_2928_; 
v_unused_2928_ = lean_ctor_get(v___x_2898_, 1);
lean_dec(v_unused_2928_);
v___x_2901_ = v___x_2898_;
v_isShared_2902_ = v_isSharedCheck_2927_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_lctx_2899_);
lean_dec(v___x_2898_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2927_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2903_; lean_object* v___x_2905_; 
v___x_2903_ = lean_unsigned_to_nat(1u);
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 1, v___x_2903_);
v___x_2905_ = v___x_2901_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_lctx_2899_);
lean_ctor_set(v_reuseFailAlloc_2926_, 1, v___x_2903_);
v___x_2905_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
lean_object* v___x_2906_; lean_object* v_v_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; uint8_t v___x_2910_; lean_object* v___x_2911_; 
v___x_2906_ = lean_st_ref_put(v___y_2892_, v___x_2905_);
v_v_2907_ = lean_array_uget_borrowed(v_bs_2890_, v_i_2889_);
v___x_2908_ = lean_unsigned_to_nat(0u);
v___x_2909_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_2910_ = 0;
lean_inc(v_v_2907_);
v___x_2911_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_2887_, v_v_2907_, v___x_2909_, v___x_2910_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v_bs_x27_2913_; size_t v___x_2914_; size_t v___x_2915_; lean_object* v___x_2916_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
lean_dec_ref_known(v___x_2911_, 1);
v_bs_x27_2913_ = lean_array_uset(v_bs_2890_, v_i_2889_, v___x_2908_);
v___x_2914_ = ((size_t)1ULL);
v___x_2915_ = lean_usize_add(v_i_2889_, v___x_2914_);
v___x_2916_ = lean_array_uset(v_bs_x27_2913_, v_i_2889_, v_a_2912_);
v_i_2889_ = v___x_2915_;
v_bs_2890_ = v___x_2916_;
goto _start;
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
lean_dec_ref(v_bs_2890_);
v_a_2918_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2911_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2911_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___boxed(lean_object* v_pu_2929_, lean_object* v_sz_2930_, lean_object* v_i_2931_, lean_object* v_bs_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
uint8_t v_pu_boxed_2938_; size_t v_sz_boxed_2939_; size_t v_i_boxed_2940_; lean_object* v_res_2941_; 
v_pu_boxed_2938_ = lean_unbox(v_pu_2929_);
v_sz_boxed_2939_ = lean_unbox_usize(v_sz_2930_);
lean_dec(v_sz_2930_);
v_i_boxed_2940_ = lean_unbox_usize(v_i_2931_);
lean_dec(v_i_2931_);
v_res_2941_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_boxed_2938_, v_sz_boxed_2939_, v_i_boxed_2940_, v_bs_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
return v_res_2941_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__0(void){
_start:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_2943_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
lean_ctor_set(v___x_2943_, 1, v___x_2942_);
lean_ctor_set(v___x_2943_, 2, v___x_2942_);
lean_ctor_set(v___x_2943_, 3, v___x_2942_);
lean_ctor_set(v___x_2943_, 4, v___x_2942_);
lean_ctor_set(v___x_2943_, 5, v___x_2942_);
return v___x_2943_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__1(void){
_start:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2944_ = lean_unsigned_to_nat(1u);
v___x_2945_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__0, &l_Lean_Compiler_LCNF_cleanup___closed__0_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__0);
v___x_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
lean_ctor_set(v___x_2946_, 1, v___x_2944_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup(uint8_t v_pu_2947_, lean_object* v_decl_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; size_t v_sz_2957_; size_t v___x_2958_; lean_object* v___x_2959_; 
v___x_2954_ = lean_st_ref_take(v_a_2950_);
lean_dec(v___x_2954_);
v___x_2955_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
v___x_2956_ = lean_st_ref_put(v_a_2950_, v___x_2955_);
v_sz_2957_ = lean_array_size(v_decl_2948_);
v___x_2958_ = ((size_t)0ULL);
v___x_2959_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_2947_, v_sz_2957_, v___x_2958_, v_decl_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup___boxed(lean_object* v_pu_2960_, lean_object* v_decl_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_){
_start:
{
uint8_t v_pu_boxed_2967_; lean_object* v_res_2968_; 
v_pu_boxed_2967_ = lean_unbox(v_pu_2960_);
v_res_2968_ = l_Lean_Compiler_LCNF_cleanup(v_pu_boxed_2967_, v_decl_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
lean_dec(v_a_2965_);
lean_dec_ref(v_a_2964_);
lean_dec(v_a_2963_);
lean_dec_ref(v_a_2962_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(lean_object* v_a_2969_, lean_object* v_ngen_2970_, lean_object* v_a_x3f_2971_){
_start:
{
lean_object* v___x_2973_; lean_object* v_env_2974_; lean_object* v_nextMacroScope_2975_; lean_object* v_auxDeclNGen_2976_; lean_object* v_traceState_2977_; lean_object* v_cache_2978_; lean_object* v_messages_2979_; lean_object* v_infoState_2980_; lean_object* v_snapshotTasks_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2991_; 
v___x_2973_ = lean_st_ref_take(v_a_2969_);
v_env_2974_ = lean_ctor_get(v___x_2973_, 0);
v_nextMacroScope_2975_ = lean_ctor_get(v___x_2973_, 1);
v_auxDeclNGen_2976_ = lean_ctor_get(v___x_2973_, 3);
v_traceState_2977_ = lean_ctor_get(v___x_2973_, 4);
v_cache_2978_ = lean_ctor_get(v___x_2973_, 5);
v_messages_2979_ = lean_ctor_get(v___x_2973_, 6);
v_infoState_2980_ = lean_ctor_get(v___x_2973_, 7);
v_snapshotTasks_2981_ = lean_ctor_get(v___x_2973_, 8);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_2991_ == 0)
{
lean_object* v_unused_2992_; 
v_unused_2992_ = lean_ctor_get(v___x_2973_, 2);
lean_dec(v_unused_2992_);
v___x_2983_ = v___x_2973_;
v_isShared_2984_ = v_isSharedCheck_2991_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_snapshotTasks_2981_);
lean_inc(v_infoState_2980_);
lean_inc(v_messages_2979_);
lean_inc(v_cache_2978_);
lean_inc(v_traceState_2977_);
lean_inc(v_auxDeclNGen_2976_);
lean_inc(v_nextMacroScope_2975_);
lean_inc(v_env_2974_);
lean_dec(v___x_2973_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2991_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 2, v_ngen_2970_);
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_env_2974_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v_nextMacroScope_2975_);
lean_ctor_set(v_reuseFailAlloc_2990_, 2, v_ngen_2970_);
lean_ctor_set(v_reuseFailAlloc_2990_, 3, v_auxDeclNGen_2976_);
lean_ctor_set(v_reuseFailAlloc_2990_, 4, v_traceState_2977_);
lean_ctor_set(v_reuseFailAlloc_2990_, 5, v_cache_2978_);
lean_ctor_set(v_reuseFailAlloc_2990_, 6, v_messages_2979_);
lean_ctor_set(v_reuseFailAlloc_2990_, 7, v_infoState_2980_);
lean_ctor_set(v_reuseFailAlloc_2990_, 8, v_snapshotTasks_2981_);
v___x_2986_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2987_ = lean_st_ref_put(v_a_2969_, v___x_2986_);
v___x_2988_ = lean_box(0);
v___x_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2988_);
return v___x_2989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0___boxed(lean_object* v_a_2993_, lean_object* v_ngen_2994_, lean_object* v_a_x3f_2995_, lean_object* v___y_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_2993_, v_ngen_2994_, v_a_x3f_2995_);
lean_dec(v_a_x3f_2995_);
lean_dec(v_a_2993_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(uint8_t v_pu_3004_, lean_object* v_decl_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v_env_3011_; lean_object* v_nextMacroScope_3012_; lean_object* v_auxDeclNGen_3013_; lean_object* v_traceState_3014_; lean_object* v_cache_3015_; lean_object* v_messages_3016_; lean_object* v_infoState_3017_; lean_object* v_snapshotTasks_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3064_; 
v___x_3009_ = lean_st_ref_get(v_a_3007_);
v___x_3010_ = lean_st_ref_take(v_a_3007_);
v_env_3011_ = lean_ctor_get(v___x_3010_, 0);
v_nextMacroScope_3012_ = lean_ctor_get(v___x_3010_, 1);
v_auxDeclNGen_3013_ = lean_ctor_get(v___x_3010_, 3);
v_traceState_3014_ = lean_ctor_get(v___x_3010_, 4);
v_cache_3015_ = lean_ctor_get(v___x_3010_, 5);
v_messages_3016_ = lean_ctor_get(v___x_3010_, 6);
v_infoState_3017_ = lean_ctor_get(v___x_3010_, 7);
v_snapshotTasks_3018_ = lean_ctor_get(v___x_3010_, 8);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3064_ == 0)
{
lean_object* v_unused_3065_; 
v_unused_3065_ = lean_ctor_get(v___x_3010_, 2);
lean_dec(v_unused_3065_);
v___x_3020_ = v___x_3010_;
v_isShared_3021_ = v_isSharedCheck_3064_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_snapshotTasks_3018_);
lean_inc(v_infoState_3017_);
lean_inc(v_messages_3016_);
lean_inc(v_cache_3015_);
lean_inc(v_traceState_3014_);
lean_inc(v_auxDeclNGen_3013_);
lean_inc(v_nextMacroScope_3012_);
lean_inc(v_env_3011_);
lean_dec(v___x_3010_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3064_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3022_; lean_object* v___x_3024_; 
v___x_3022_ = ((lean_object*)(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2));
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 2, v___x_3022_);
v___x_3024_ = v___x_3020_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_env_3011_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v_nextMacroScope_3012_);
lean_ctor_set(v_reuseFailAlloc_3063_, 2, v___x_3022_);
lean_ctor_set(v_reuseFailAlloc_3063_, 3, v_auxDeclNGen_3013_);
lean_ctor_set(v_reuseFailAlloc_3063_, 4, v_traceState_3014_);
lean_ctor_set(v_reuseFailAlloc_3063_, 5, v_cache_3015_);
lean_ctor_set(v_reuseFailAlloc_3063_, 6, v_messages_3016_);
lean_ctor_set(v_reuseFailAlloc_3063_, 7, v_infoState_3017_);
lean_ctor_set(v_reuseFailAlloc_3063_, 8, v_snapshotTasks_3018_);
v___x_3024_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3025_; lean_object* v_ngen_3026_; lean_object* v___x_3027_; uint8_t v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; uint8_t v___x_3033_; lean_object* v_r_3034_; 
v___x_3025_ = lean_st_ref_put(v_a_3007_, v___x_3024_);
v_ngen_3026_ = lean_ctor_get(v___x_3009_, 2);
lean_inc_ref(v_ngen_3026_);
lean_dec(v___x_3009_);
v___x_3027_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_3028_ = 0;
v___x_3029_ = lean_box(v_pu_3004_);
v___x_3030_ = lean_box(v___x_3028_);
v___x_3031_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_internalize___boxed), 9, 4);
lean_closure_set(v___x_3031_, 0, v___x_3029_);
lean_closure_set(v___x_3031_, 1, v_decl_3005_);
lean_closure_set(v___x_3031_, 2, v___x_3027_);
lean_closure_set(v___x_3031_, 3, v___x_3030_);
v___x_3032_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
v___x_3033_ = 0;
v_r_3034_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v___x_3031_, v___x_3032_, v___x_3033_, v_a_3006_, v_a_3007_);
if (lean_obj_tag(v_r_3034_) == 0)
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3051_; 
v_a_3035_ = lean_ctor_get(v_r_3034_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v_r_3034_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3037_ = v_r_3034_;
v_isShared_3038_ = v_isSharedCheck_3051_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v_r_3034_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3051_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
lean_inc(v_a_3035_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set_tag(v___x_3037_, 1);
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
v___x_3041_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3007_, v_ngen_3026_, v___x_3040_);
lean_dec_ref(v___x_3040_);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3048_ == 0)
{
lean_object* v_unused_3049_; 
v_unused_3049_ = lean_ctor_get(v___x_3041_, 0);
lean_dec(v_unused_3049_);
v___x_3043_ = v___x_3041_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_dec(v___x_3041_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v_a_3035_);
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3035_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
v_a_3052_ = lean_ctor_get(v_r_3034_, 0);
lean_inc(v_a_3052_);
lean_dec_ref_known(v_r_3034_, 1);
v___x_3053_ = lean_box(0);
v___x_3054_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3007_, v_ngen_3026_, v___x_3053_);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3061_ == 0)
{
lean_object* v_unused_3062_; 
v_unused_3062_ = lean_ctor_get(v___x_3054_, 0);
lean_dec(v_unused_3062_);
v___x_3056_ = v___x_3054_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_dec(v___x_3054_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
lean_ctor_set_tag(v___x_3056_, 1);
lean_ctor_set(v___x_3056_, 0, v_a_3052_);
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3052_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___boxed(lean_object* v_pu_3066_, lean_object* v_decl_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_){
_start:
{
uint8_t v_pu_boxed_3071_; lean_object* v_res_3072_; 
v_pu_boxed_3071_ = lean_unbox(v_pu_3066_);
v_res_3072_ = l_Lean_Compiler_LCNF_normalizeFVarIds(v_pu_boxed_3071_, v_decl_3067_, v_a_3068_, v_a_3069_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
return v_res_3072_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_Bind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Bind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Internalize(builtin);
}
#ifdef __cplusplus
}
#endif
