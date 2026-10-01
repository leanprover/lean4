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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Purity_ctorIdx(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
lean_object* l_instMonadEIO___redArg();
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftBaseIOEIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(lean_object*);
lean_object* l_instMonadStateOfOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadStateOfOfMonadLift___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadStateOfMonadStateOf___redArg(lean_object*);
lean_object* l_modify(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t, lean_object*, uint8_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_liftIOCore___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftBaseIOEIO___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__3_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__5_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__5_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__4_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__6_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__6_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__3_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__7_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__7_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__2_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__8_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__8_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__1_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__9_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__9_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__0_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__11;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0;
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
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___lam__0(uint8_t v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_st_ref_get(v___y_214_);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___lam__0___boxed(lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
uint8_t v___y_199__boxed_229_; lean_object* v_res_230_; 
v___y_199__boxed_229_ = lean_unbox(v___y_222_);
v_res_230_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___lam__0(v___y_199__boxed_229_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg(){
_start:
{
lean_object* v___f_233_; 
v___f_233_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___closed__0));
return v___f_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___boxed(lean_object* v___dummy_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg();
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue(uint8_t v_pu_236_){
_start:
{
lean_object* v___f_237_; 
v___f_237_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___closed__0));
return v___f_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___boxed(lean_object* v_pu_238_){
_start:
{
uint8_t v_pu_boxed_239_; lean_object* v_res_240_; 
v_pu_boxed_239_ = lean_unbox(v_pu_238_);
v_res_240_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue(v_pu_boxed_239_);
return v_res_240_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__11(void){
_start:
{
lean_object* v___f_262_; lean_object* v___x_263_; 
v___f_262_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__10));
v___x_263_ = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(v___f_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg(){
_start:
{
lean_object* v___f_265_; lean_object* v___x_266_; lean_object* v_get_267_; lean_object* v_set_268_; lean_object* v_modifyGet_269_; lean_object* v___f_270_; lean_object* v___f_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___f_265_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__0));
v___x_266_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__11, &l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__11_once, _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__11);
v_get_267_ = lean_ctor_get(v___x_266_, 0);
v_set_268_ = lean_ctor_get(v___x_266_, 1);
v_modifyGet_269_ = lean_ctor_get(v___x_266_, 2);
lean_inc(v_set_268_);
v___f_270_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_270_, 0, v_set_268_);
lean_closure_set(v___f_270_, 1, v___f_265_);
lean_inc(v_modifyGet_269_);
v___f_271_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_271_, 0, v_modifyGet_269_);
lean_closure_set(v___f_271_, 1, v___f_265_);
lean_inc(v_get_267_);
v___x_272_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___x_272_, 0, lean_box(0));
lean_closure_set(v___x_272_, 1, v_get_267_);
v___x_273_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___f_270_);
lean_ctor_set(v___x_273_, 2, v___f_271_);
v___x_274_ = l_instMonadStateOfMonadStateOf___redArg(v___x_273_);
v___x_275_ = lean_alloc_closure((void*)(l_modify), 4, 3);
lean_closure_set(v___x_275_, 0, lean_box(0));
lean_closure_set(v___x_275_, 1, lean_box(0));
lean_closure_set(v___x_275_, 2, v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___boxed(lean_object* v___dummy_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg();
return v_res_277_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0(void){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg();
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM(uint8_t v_pu_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0, &l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0_once, _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___boxed(lean_object* v_pu_281_){
_start:
{
uint8_t v_pu_boxed_282_; lean_object* v_res_283_; 
v_pu_boxed_282_ = lean_unbox(v_pu_281_);
v_res_283_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM(v_pu_boxed_282_);
return v_res_283_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(lean_object* v_a_284_, lean_object* v_x_285_){
_start:
{
if (lean_obj_tag(v_x_285_) == 0)
{
uint8_t v___x_286_; 
v___x_286_ = 0;
return v___x_286_;
}
else
{
lean_object* v_key_287_; lean_object* v_tail_288_; uint8_t v___x_289_; 
v_key_287_ = lean_ctor_get(v_x_285_, 0);
v_tail_288_ = lean_ctor_get(v_x_285_, 2);
v___x_289_ = l_Lean_instBEqFVarId_beq(v_key_287_, v_a_284_);
if (v___x_289_ == 0)
{
v_x_285_ = v_tail_288_;
goto _start;
}
else
{
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg___boxed(lean_object* v_a_291_, lean_object* v_x_292_){
_start:
{
uint8_t v_res_293_; lean_object* v_r_294_; 
v_res_293_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_a_291_, v_x_292_);
lean_dec(v_x_292_);
lean_dec(v_a_291_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(lean_object* v_a_295_, lean_object* v_b_296_, lean_object* v_x_297_){
_start:
{
if (lean_obj_tag(v_x_297_) == 0)
{
lean_dec(v_b_296_);
lean_dec(v_a_295_);
return v_x_297_;
}
else
{
lean_object* v_key_298_; lean_object* v_value_299_; lean_object* v_tail_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_312_; 
v_key_298_ = lean_ctor_get(v_x_297_, 0);
v_value_299_ = lean_ctor_get(v_x_297_, 1);
v_tail_300_ = lean_ctor_get(v_x_297_, 2);
v_isSharedCheck_312_ = !lean_is_exclusive(v_x_297_);
if (v_isSharedCheck_312_ == 0)
{
v___x_302_ = v_x_297_;
v_isShared_303_ = v_isSharedCheck_312_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_tail_300_);
lean_inc(v_value_299_);
lean_inc(v_key_298_);
lean_dec(v_x_297_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_312_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
uint8_t v___x_304_; 
v___x_304_ = l_Lean_instBEqFVarId_beq(v_key_298_, v_a_295_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_305_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(v_a_295_, v_b_296_, v_tail_300_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 2, v___x_305_);
v___x_307_ = v___x_302_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_key_298_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_value_299_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
else
{
lean_object* v___x_310_; 
lean_dec(v_value_299_);
lean_dec(v_key_298_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v_b_296_);
lean_ctor_set(v___x_302_, 0, v_a_295_);
v___x_310_ = v___x_302_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_295_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_b_296_);
lean_ctor_set(v_reuseFailAlloc_311_, 2, v_tail_300_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
if (lean_obj_tag(v_x_314_) == 0)
{
return v_x_313_;
}
else
{
lean_object* v_key_315_; lean_object* v_value_316_; lean_object* v_tail_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_340_; 
v_key_315_ = lean_ctor_get(v_x_314_, 0);
v_value_316_ = lean_ctor_get(v_x_314_, 1);
v_tail_317_ = lean_ctor_get(v_x_314_, 2);
v_isSharedCheck_340_ = !lean_is_exclusive(v_x_314_);
if (v_isSharedCheck_340_ == 0)
{
v___x_319_ = v_x_314_;
v_isShared_320_ = v_isSharedCheck_340_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_tail_317_);
lean_inc(v_value_316_);
lean_inc(v_key_315_);
lean_dec(v_x_314_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_340_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; uint64_t v___x_322_; uint64_t v___x_323_; uint64_t v___x_324_; uint64_t v_fold_325_; uint64_t v___x_326_; uint64_t v___x_327_; uint64_t v___x_328_; size_t v___x_329_; size_t v___x_330_; size_t v___x_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_321_ = lean_array_get_size(v_x_313_);
v___x_322_ = l_Lean_instHashableFVarId_hash(v_key_315_);
v___x_323_ = 32ULL;
v___x_324_ = lean_uint64_shift_right(v___x_322_, v___x_323_);
v_fold_325_ = lean_uint64_xor(v___x_322_, v___x_324_);
v___x_326_ = 16ULL;
v___x_327_ = lean_uint64_shift_right(v_fold_325_, v___x_326_);
v___x_328_ = lean_uint64_xor(v_fold_325_, v___x_327_);
v___x_329_ = lean_uint64_to_usize(v___x_328_);
v___x_330_ = lean_usize_of_nat(v___x_321_);
v___x_331_ = ((size_t)1ULL);
v___x_332_ = lean_usize_sub(v___x_330_, v___x_331_);
v___x_333_ = lean_usize_land(v___x_329_, v___x_332_);
v___x_334_ = lean_array_uget_borrowed(v_x_313_, v___x_333_);
lean_inc(v___x_334_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 2, v___x_334_);
v___x_336_ = v___x_319_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_key_315_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_value_316_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v___x_334_);
v___x_336_ = v_reuseFailAlloc_339_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; 
v___x_337_ = lean_array_uset(v_x_313_, v___x_333_, v___x_336_);
v_x_313_ = v___x_337_;
v_x_314_ = v_tail_317_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(lean_object* v_i_341_, lean_object* v_source_342_, lean_object* v_target_343_){
_start:
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = lean_array_get_size(v_source_342_);
v___x_345_ = lean_nat_dec_lt(v_i_341_, v___x_344_);
if (v___x_345_ == 0)
{
lean_dec_ref(v_source_342_);
lean_dec(v_i_341_);
return v_target_343_;
}
else
{
lean_object* v_es_346_; lean_object* v___x_347_; lean_object* v_source_348_; lean_object* v_target_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_es_346_ = lean_array_fget(v_source_342_, v_i_341_);
v___x_347_ = lean_box(0);
v_source_348_ = lean_array_fset(v_source_342_, v_i_341_, v___x_347_);
v_target_349_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(v_target_343_, v_es_346_);
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_nat_add(v_i_341_, v___x_350_);
lean_dec(v_i_341_);
v_i_341_ = v___x_351_;
v_source_342_ = v_source_348_;
v_target_343_ = v_target_349_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(lean_object* v_data_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v_nbuckets_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_354_ = lean_array_get_size(v_data_353_);
v___x_355_ = lean_unsigned_to_nat(2u);
v_nbuckets_356_ = lean_nat_mul(v___x_354_, v___x_355_);
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = lean_box(0);
v___x_359_ = lean_mk_array(v_nbuckets_356_, v___x_358_);
v___x_360_ = lean_array_propagate_mark(v_data_353_, v___x_359_);
v___x_361_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(v___x_357_, v_data_353_, v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(lean_object* v_m_362_, lean_object* v_a_363_, lean_object* v_b_364_){
_start:
{
lean_object* v_size_365_; lean_object* v_buckets_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_409_; 
v_size_365_ = lean_ctor_get(v_m_362_, 0);
v_buckets_366_ = lean_ctor_get(v_m_362_, 1);
v_isSharedCheck_409_ = !lean_is_exclusive(v_m_362_);
if (v_isSharedCheck_409_ == 0)
{
v___x_368_ = v_m_362_;
v_isShared_369_ = v_isSharedCheck_409_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_buckets_366_);
lean_inc(v_size_365_);
lean_dec(v_m_362_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_409_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; uint64_t v___x_371_; uint64_t v___x_372_; uint64_t v___x_373_; uint64_t v_fold_374_; uint64_t v___x_375_; uint64_t v___x_376_; uint64_t v___x_377_; size_t v___x_378_; size_t v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; lean_object* v_bkt_383_; uint8_t v___x_384_; 
v___x_370_ = lean_array_get_size(v_buckets_366_);
v___x_371_ = l_Lean_instHashableFVarId_hash(v_a_363_);
v___x_372_ = 32ULL;
v___x_373_ = lean_uint64_shift_right(v___x_371_, v___x_372_);
v_fold_374_ = lean_uint64_xor(v___x_371_, v___x_373_);
v___x_375_ = 16ULL;
v___x_376_ = lean_uint64_shift_right(v_fold_374_, v___x_375_);
v___x_377_ = lean_uint64_xor(v_fold_374_, v___x_376_);
v___x_378_ = lean_uint64_to_usize(v___x_377_);
v___x_379_ = lean_usize_of_nat(v___x_370_);
v___x_380_ = ((size_t)1ULL);
v___x_381_ = lean_usize_sub(v___x_379_, v___x_380_);
v___x_382_ = lean_usize_land(v___x_378_, v___x_381_);
v_bkt_383_ = lean_array_uget_borrowed(v_buckets_366_, v___x_382_);
v___x_384_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_a_363_, v_bkt_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v_size_x27_386_; lean_object* v___x_387_; lean_object* v_buckets_x27_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_385_ = lean_unsigned_to_nat(1u);
v_size_x27_386_ = lean_nat_add(v_size_365_, v___x_385_);
lean_dec(v_size_365_);
lean_inc(v_bkt_383_);
v___x_387_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_387_, 0, v_a_363_);
lean_ctor_set(v___x_387_, 1, v_b_364_);
lean_ctor_set(v___x_387_, 2, v_bkt_383_);
v_buckets_x27_388_ = lean_array_uset(v_buckets_366_, v___x_382_, v___x_387_);
v___x_389_ = lean_unsigned_to_nat(4u);
v___x_390_ = lean_nat_mul(v_size_x27_386_, v___x_389_);
v___x_391_ = lean_unsigned_to_nat(3u);
v___x_392_ = lean_nat_div(v___x_390_, v___x_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_array_get_size(v_buckets_x27_388_);
v___x_394_ = lean_nat_dec_le(v___x_392_, v___x_393_);
lean_dec(v___x_392_);
if (v___x_394_ == 0)
{
lean_object* v_val_395_; lean_object* v___x_397_; 
v_val_395_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(v_buckets_x27_388_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v_val_395_);
lean_ctor_set(v___x_368_, 0, v_size_x27_386_);
v___x_397_ = v___x_368_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_size_x27_386_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_val_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
else
{
lean_object* v___x_400_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v_buckets_x27_388_);
lean_ctor_set(v___x_368_, 0, v_size_x27_386_);
v___x_400_ = v___x_368_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_size_x27_386_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_buckets_x27_388_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
else
{
lean_object* v___x_402_; lean_object* v_buckets_x27_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_407_; 
lean_inc(v_bkt_383_);
v___x_402_ = lean_box(0);
v_buckets_x27_403_ = lean_array_uset(v_buckets_366_, v___x_382_, v___x_402_);
v___x_404_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(v_a_363_, v_b_364_, v_bkt_383_);
v___x_405_ = lean_array_uset(v_buckets_x27_403_, v___x_382_, v___x_404_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v___x_405_);
v___x_407_ = v___x_368_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_size_365_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(lean_object* v___y_410_){
_start:
{
lean_object* v___x_412_; lean_object* v_ngen_413_; lean_object* v_namePrefix_414_; lean_object* v_idx_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_445_; 
v___x_412_ = lean_st_ref_get(v___y_410_);
v_ngen_413_ = lean_ctor_get(v___x_412_, 2);
lean_inc_ref(v_ngen_413_);
lean_dec(v___x_412_);
v_namePrefix_414_ = lean_ctor_get(v_ngen_413_, 0);
v_idx_415_ = lean_ctor_get(v_ngen_413_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v_ngen_413_);
if (v_isSharedCheck_445_ == 0)
{
v___x_417_ = v_ngen_413_;
v_isShared_418_ = v_isSharedCheck_445_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_idx_415_);
lean_inc(v_namePrefix_414_);
lean_dec(v_ngen_413_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_445_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v_r_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
lean_inc(v_idx_415_);
lean_inc(v_namePrefix_414_);
v_r_419_ = l_Lean_Name_num___override(v_namePrefix_414_, v_idx_415_);
v___x_420_ = lean_unsigned_to_nat(1u);
v___x_421_ = lean_nat_add(v_idx_415_, v___x_420_);
lean_dec(v_idx_415_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v___x_421_);
v___x_423_ = v___x_417_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_namePrefix_414_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_421_);
v___x_423_ = v_reuseFailAlloc_444_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; lean_object* v_env_425_; lean_object* v_nextMacroScope_426_; lean_object* v_auxDeclNGen_427_; lean_object* v_traceState_428_; lean_object* v_cache_429_; lean_object* v_recordedDeps_430_; lean_object* v_messages_431_; lean_object* v_infoState_432_; lean_object* v_snapshotTasks_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_442_; 
v___x_424_ = lean_st_ref_take(v___y_410_);
v_env_425_ = lean_ctor_get(v___x_424_, 0);
v_nextMacroScope_426_ = lean_ctor_get(v___x_424_, 1);
v_auxDeclNGen_427_ = lean_ctor_get(v___x_424_, 3);
v_traceState_428_ = lean_ctor_get(v___x_424_, 4);
v_cache_429_ = lean_ctor_get(v___x_424_, 5);
v_recordedDeps_430_ = lean_ctor_get(v___x_424_, 6);
v_messages_431_ = lean_ctor_get(v___x_424_, 7);
v_infoState_432_ = lean_ctor_get(v___x_424_, 8);
v_snapshotTasks_433_ = lean_ctor_get(v___x_424_, 9);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; 
v_unused_443_ = lean_ctor_get(v___x_424_, 2);
lean_dec(v_unused_443_);
v___x_435_ = v___x_424_;
v_isShared_436_ = v_isSharedCheck_442_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_snapshotTasks_433_);
lean_inc(v_infoState_432_);
lean_inc(v_messages_431_);
lean_inc(v_recordedDeps_430_);
lean_inc(v_cache_429_);
lean_inc(v_traceState_428_);
lean_inc(v_auxDeclNGen_427_);
lean_inc(v_nextMacroScope_426_);
lean_inc(v_env_425_);
lean_dec(v___x_424_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_442_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 2, v___x_423_);
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_env_425_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_nextMacroScope_426_);
lean_ctor_set(v_reuseFailAlloc_441_, 2, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_441_, 3, v_auxDeclNGen_427_);
lean_ctor_set(v_reuseFailAlloc_441_, 4, v_traceState_428_);
lean_ctor_set(v_reuseFailAlloc_441_, 5, v_cache_429_);
lean_ctor_set(v_reuseFailAlloc_441_, 6, v_recordedDeps_430_);
lean_ctor_set(v_reuseFailAlloc_441_, 7, v_messages_431_);
lean_ctor_set(v_reuseFailAlloc_441_, 8, v_infoState_432_);
lean_ctor_set(v_reuseFailAlloc_441_, 9, v_snapshotTasks_433_);
v___x_438_ = v_reuseFailAlloc_441_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_st_ref_put(v___y_410_, v___x_438_);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v_r_419_);
return v___x_440_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg___boxed(lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_446_);
lean_dec(v___y_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(uint8_t v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v___x_456_; lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
v___x_456_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_454_);
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0___boxed(lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
uint8_t v___y_3132__boxed_472_; lean_object* v_res_473_; 
v___y_3132__boxed_472_ = lean_unbox(v___y_465_);
v_res_473_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(v___y_3132__boxed_472_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(lean_object* v_fvarId_474_, uint8_t v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_494_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_494_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_494_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_494_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_487_ = lean_st_ref_take(v_a_476_);
lean_inc(v_a_483_);
v___x_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_488_, 0, v_a_483_);
v___x_489_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v___x_487_, v_fvarId_474_, v___x_488_);
v___x_490_ = lean_st_ref_put(v_a_476_, v___x_489_);
if (v_isShared_486_ == 0)
{
v___x_492_ = v___x_485_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_483_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
else
{
lean_dec(v_fvarId_474_);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg___boxed(lean_object* v_fvarId_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
uint8_t v_a_boxed_503_; lean_object* v_res_504_; 
v_a_boxed_503_ = lean_unbox(v_a_496_);
v_res_504_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_495_, v_a_boxed_503_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
lean_dec(v_a_497_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(uint8_t v_pu_505_, lean_object* v_fvarId_506_, uint8_t v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___boxed(lean_object* v_pu_515_, lean_object* v_fvarId_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
uint8_t v_pu_boxed_524_; uint8_t v_a_boxed_525_; lean_object* v_res_526_; 
v_pu_boxed_524_ = lean_unbox(v_pu_515_);
v_a_boxed_525_ = lean_unbox(v_a_517_);
v_res_526_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(v_pu_boxed_524_, v_fvarId_516_, v_a_boxed_525_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(uint8_t v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_532_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___boxed(lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
uint8_t v___y_3207__boxed_542_; lean_object* v_res_543_; 
v___y_3207__boxed_542_ = lean_unbox(v___y_535_);
v_res_543_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(v___y_3207__boxed_542_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1(lean_object* v_00_u03b2_544_, lean_object* v_m_545_, lean_object* v_a_546_, lean_object* v_b_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v_m_545_, v_a_546_, v_b_547_);
return v___x_548_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(lean_object* v_00_u03b2_549_, lean_object* v_a_550_, lean_object* v_x_551_){
_start:
{
uint8_t v___x_552_; 
v___x_552_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_a_550_, v_x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___boxed(lean_object* v_00_u03b2_553_, lean_object* v_a_554_, lean_object* v_x_555_){
_start:
{
uint8_t v_res_556_; lean_object* v_r_557_; 
v_res_556_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(v_00_u03b2_553_, v_a_554_, v_x_555_);
lean_dec(v_x_555_);
lean_dec(v_a_554_);
v_r_557_ = lean_box(v_res_556_);
return v_r_557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3(lean_object* v_00_u03b2_558_, lean_object* v_data_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(v_data_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4(lean_object* v_00_u03b2_561_, lean_object* v_a_562_, lean_object* v_b_563_, lean_object* v_x_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(v_a_562_, v_b_563_, v_x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_566_, lean_object* v_i_567_, lean_object* v_source_568_, lean_object* v_target_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(v_i_567_, v_source_568_, v_target_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_571_, lean_object* v_x_572_, lean_object* v_x_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(v_x_572_, v_x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(lean_object* v_a_575_, lean_object* v_x_576_){
_start:
{
if (lean_obj_tag(v_x_576_) == 0)
{
lean_object* v___x_577_; 
v___x_577_ = lean_box(0);
return v___x_577_;
}
else
{
lean_object* v_key_578_; lean_object* v_value_579_; lean_object* v_tail_580_; uint8_t v___x_581_; 
v_key_578_ = lean_ctor_get(v_x_576_, 0);
v_value_579_ = lean_ctor_get(v_x_576_, 1);
v_tail_580_ = lean_ctor_get(v_x_576_, 2);
v___x_581_ = l_Lean_instBEqFVarId_beq(v_key_578_, v_a_575_);
if (v___x_581_ == 0)
{
v_x_576_ = v_tail_580_;
goto _start;
}
else
{
lean_object* v___x_583_; 
lean_inc(v_value_579_);
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v_value_579_);
return v___x_583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_584_, lean_object* v_x_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_584_, v_x_585_);
lean_dec(v_x_585_);
lean_dec(v_a_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(lean_object* v_m_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_buckets_589_; lean_object* v___x_590_; uint64_t v___x_591_; uint64_t v___x_592_; uint64_t v___x_593_; uint64_t v_fold_594_; uint64_t v___x_595_; uint64_t v___x_596_; uint64_t v___x_597_; size_t v___x_598_; size_t v___x_599_; size_t v___x_600_; size_t v___x_601_; size_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_buckets_589_ = lean_ctor_get(v_m_587_, 1);
v___x_590_ = lean_array_get_size(v_buckets_589_);
v___x_591_ = l_Lean_instHashableFVarId_hash(v_a_588_);
v___x_592_ = 32ULL;
v___x_593_ = lean_uint64_shift_right(v___x_591_, v___x_592_);
v_fold_594_ = lean_uint64_xor(v___x_591_, v___x_593_);
v___x_595_ = 16ULL;
v___x_596_ = lean_uint64_shift_right(v_fold_594_, v___x_595_);
v___x_597_ = lean_uint64_xor(v_fold_594_, v___x_596_);
v___x_598_ = lean_uint64_to_usize(v___x_597_);
v___x_599_ = lean_usize_of_nat(v___x_590_);
v___x_600_ = ((size_t)1ULL);
v___x_601_ = lean_usize_sub(v___x_599_, v___x_600_);
v___x_602_ = lean_usize_land(v___x_598_, v___x_601_);
v___x_603_ = lean_array_uget_borrowed(v_buckets_589_, v___x_602_);
v___x_604_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_588_, v___x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg___boxed(lean_object* v_m_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v_m_605_, v_a_606_);
lean_dec(v_a_606_);
lean_dec_ref(v_m_605_);
return v_res_607_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_instMonadEIO___redArg();
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(lean_object* v_msg_613_, uint8_t v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_toApplicative_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_687_; 
v___x_621_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
v___x_622_ = l_StateRefT_x27_instMonad___redArg(v___x_621_);
v_toApplicative_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v___x_622_, 1);
lean_dec(v_unused_688_);
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_687_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_toApplicative_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_687_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v_toFunctor_627_; lean_object* v_toSeq_628_; lean_object* v_toSeqLeft_629_; lean_object* v_toSeqRight_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_685_; 
v_toFunctor_627_ = lean_ctor_get(v_toApplicative_623_, 0);
v_toSeq_628_ = lean_ctor_get(v_toApplicative_623_, 2);
v_toSeqLeft_629_ = lean_ctor_get(v_toApplicative_623_, 3);
v_toSeqRight_630_ = lean_ctor_get(v_toApplicative_623_, 4);
v_isSharedCheck_685_ = !lean_is_exclusive(v_toApplicative_623_);
if (v_isSharedCheck_685_ == 0)
{
lean_object* v_unused_686_; 
v_unused_686_ = lean_ctor_get(v_toApplicative_623_, 1);
lean_dec(v_unused_686_);
v___x_632_ = v_toApplicative_623_;
v_isShared_633_ = v_isSharedCheck_685_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_toSeqRight_630_);
lean_inc(v_toSeqLeft_629_);
lean_inc(v_toSeq_628_);
lean_inc(v_toFunctor_627_);
lean_dec(v_toApplicative_623_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_685_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___f_634_; lean_object* v___f_635_; lean_object* v___f_636_; lean_object* v___f_637_; lean_object* v___x_638_; lean_object* v___f_639_; lean_object* v___f_640_; lean_object* v___f_641_; lean_object* v___x_643_; 
v___f_634_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
v___f_635_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_627_);
v___f_636_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_636_, 0, v_toFunctor_627_);
v___f_637_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_637_, 0, v_toFunctor_627_);
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v___f_636_);
lean_ctor_set(v___x_638_, 1, v___f_637_);
v___f_639_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_639_, 0, v_toSeqRight_630_);
v___f_640_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_640_, 0, v_toSeqLeft_629_);
v___f_641_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_641_, 0, v_toSeq_628_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 4, v___f_639_);
lean_ctor_set(v___x_632_, 3, v___f_640_);
lean_ctor_set(v___x_632_, 2, v___f_641_);
lean_ctor_set(v___x_632_, 1, v___f_634_);
lean_ctor_set(v___x_632_, 0, v___x_638_);
v___x_643_ = v___x_632_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v___f_634_);
lean_ctor_set(v_reuseFailAlloc_684_, 2, v___f_641_);
lean_ctor_set(v_reuseFailAlloc_684_, 3, v___f_640_);
lean_ctor_set(v_reuseFailAlloc_684_, 4, v___f_639_);
v___x_643_ = v_reuseFailAlloc_684_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_645_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___f_635_);
lean_ctor_set(v___x_625_, 0, v___x_643_);
v___x_645_ = v___x_625_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v___f_635_);
v___x_645_ = v_reuseFailAlloc_683_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_646_; lean_object* v_toApplicative_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_681_; 
v___x_646_ = l_StateRefT_x27_instMonad___redArg(v___x_645_);
v_toApplicative_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; 
v_unused_682_ = lean_ctor_get(v___x_646_, 1);
lean_dec(v_unused_682_);
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_681_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_toApplicative_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_681_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v_toFunctor_651_; lean_object* v_toSeq_652_; lean_object* v_toSeqLeft_653_; lean_object* v_toSeqRight_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_679_; 
v_toFunctor_651_ = lean_ctor_get(v_toApplicative_647_, 0);
v_toSeq_652_ = lean_ctor_get(v_toApplicative_647_, 2);
v_toSeqLeft_653_ = lean_ctor_get(v_toApplicative_647_, 3);
v_toSeqRight_654_ = lean_ctor_get(v_toApplicative_647_, 4);
v_isSharedCheck_679_ = !lean_is_exclusive(v_toApplicative_647_);
if (v_isSharedCheck_679_ == 0)
{
lean_object* v_unused_680_; 
v_unused_680_ = lean_ctor_get(v_toApplicative_647_, 1);
lean_dec(v_unused_680_);
v___x_656_ = v_toApplicative_647_;
v_isShared_657_ = v_isSharedCheck_679_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_toSeqRight_654_);
lean_inc(v_toSeqLeft_653_);
lean_inc(v_toSeq_652_);
lean_inc(v_toFunctor_651_);
lean_dec(v_toApplicative_647_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_679_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___f_658_; lean_object* v___f_659_; lean_object* v___f_660_; lean_object* v___f_661_; lean_object* v___x_662_; lean_object* v___f_663_; lean_object* v___f_664_; lean_object* v___f_665_; lean_object* v___x_667_; 
v___f_658_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
v___f_659_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(v_toFunctor_651_);
v___f_660_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_660_, 0, v_toFunctor_651_);
v___f_661_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_661_, 0, v_toFunctor_651_);
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v___f_660_);
lean_ctor_set(v___x_662_, 1, v___f_661_);
v___f_663_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_663_, 0, v_toSeqRight_654_);
v___f_664_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_664_, 0, v_toSeqLeft_653_);
v___f_665_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_665_, 0, v_toSeq_652_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 4, v___f_663_);
lean_ctor_set(v___x_656_, 3, v___f_664_);
lean_ctor_set(v___x_656_, 2, v___f_665_);
lean_ctor_set(v___x_656_, 1, v___f_658_);
lean_ctor_set(v___x_656_, 0, v___x_662_);
v___x_667_ = v___x_656_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v___f_658_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v___f_665_);
lean_ctor_set(v_reuseFailAlloc_678_, 3, v___f_664_);
lean_ctor_set(v_reuseFailAlloc_678_, 4, v___f_663_);
v___x_667_ = v_reuseFailAlloc_678_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_669_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v___f_659_);
lean_ctor_set(v___x_649_, 0, v___x_667_);
v___x_669_ = v___x_649_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v___f_659_);
v___x_669_ = v_reuseFailAlloc_677_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___f_673_; lean_object* v___x_7100__overap_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_670_ = l_StateRefT_x27_instMonad___redArg(v___x_669_);
v___x_671_ = l_Lean_instInhabitedExpr;
v___x_672_ = l_instInhabitedOfMonad___redArg(v___x_670_, v___x_671_);
v___f_673_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_673_, 0, v___x_672_);
v___x_7100__overap_674_ = lean_panic_fn_borrowed(v___f_673_, v_msg_613_);
lean_dec_ref(v___f_673_);
v___x_675_ = lean_box(v___y_614_);
lean_inc(v___y_619_);
lean_inc_ref(v___y_618_);
lean_inc(v___y_617_);
lean_inc_ref(v___y_616_);
lean_inc(v___y_615_);
v___x_676_ = lean_apply_7(v___x_7100__overap_674_, v___x_675_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, lean_box(0));
return v___x_676_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___boxed(lean_object* v_msg_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
uint8_t v___y_7249__boxed_697_; lean_object* v_res_698_; 
v___y_7249__boxed_697_ = lean_unbox(v___y_690_);
v_res_698_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v_msg_689_, v___y_7249__boxed_697_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
return v_res_698_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_702_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_703_ = lean_unsigned_to_nat(20u);
v___x_704_ = lean_unsigned_to_nat(88u);
v___x_705_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__1));
v___x_706_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_707_ = l_mkPanicMessageWithDecl(v___x_706_, v___x_705_, v___x_704_, v___x_703_, v___x_702_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(uint8_t v_pu_708_, lean_object* v_e_709_, uint8_t v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
uint8_t v___x_717_; 
v___x_717_ = l_Lean_Expr_hasFVar(v_e_709_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; 
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v_e_709_);
return v___x_718_;
}
else
{
switch(lean_obj_tag(v_e_709_))
{
case 1:
{
lean_object* v_fvarId_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_fvarId_719_ = lean_ctor_get(v_e_709_, 0);
v___x_720_ = lean_st_ref_get(v_a_711_);
v___x_721_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v___x_720_, v_fvarId_719_);
lean_dec(v___x_720_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v___x_722_; 
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v_e_709_);
return v___x_722_;
}
else
{
lean_object* v_val_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_768_; 
lean_dec_ref_known(v_e_709_, 1);
v_val_723_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_768_ == 0)
{
v___x_725_ = v___x_721_;
v_isShared_726_ = v_isSharedCheck_768_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_val_723_);
lean_dec(v___x_721_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_768_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
switch(lean_obj_tag(v_val_723_))
{
case 0:
{
lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_727_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_726_ == 0)
{
lean_ctor_set_tag(v___x_725_, 0);
lean_ctor_set(v___x_725_, 0, v___x_727_);
v___x_729_ = v___x_725_;
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
case 1:
{
lean_object* v_fvarId_731_; lean_object* v___x_732_; 
lean_del_object(v___x_725_);
v_fvarId_731_ = lean_ctor_get(v_val_723_, 0);
lean_inc(v_fvarId_731_);
lean_dec_ref_known(v_val_723_, 1);
v___x_732_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_708_, v_fvarId_731_, v_a_713_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_751_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_751_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_751_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_751_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
if (lean_obj_tag(v_a_733_) == 0)
{
lean_dec(v_fvarId_731_);
goto v___jp_737_;
}
else
{
lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_749_; 
v_isSharedCheck_749_ = !lean_is_exclusive(v_a_733_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; 
v_unused_750_ = lean_ctor_get(v_a_733_, 0);
lean_dec(v_unused_750_);
v___x_743_ = v_a_733_;
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
else
{
lean_dec(v_a_733_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
if (v___x_717_ == 0)
{
lean_del_object(v___x_743_);
lean_dec(v_fvarId_731_);
goto v___jp_737_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_747_; 
lean_del_object(v___x_735_);
v___x_745_ = l_Lean_Expr_fvar___override(v_fvarId_731_);
if (v_isShared_744_ == 0)
{
lean_ctor_set_tag(v___x_743_, 0);
lean_ctor_set(v___x_743_, 0, v___x_745_);
v___x_747_ = v___x_743_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
v___jp_737_:
{
lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_738_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_738_);
v___x_740_ = v___x_735_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec(v_fvarId_731_);
v_a_752_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_732_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_732_);
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
default: 
{
lean_object* v_expr_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_del_object(v___x_725_);
v_expr_760_ = lean_ctor_get(v_val_723_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v_val_723_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v_val_723_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_expr_760_);
lean_dec(v_val_723_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set_tag(v___x_762_, 0);
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_expr_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_769_; lean_object* v_arg_770_; lean_object* v___x_771_; 
v_fn_769_ = lean_ctor_get(v_e_709_, 0);
v_arg_770_ = lean_ctor_get(v_e_709_, 1);
lean_inc_ref(v_fn_769_);
v___x_771_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_708_, v_fn_769_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_773_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
lean_dec_ref_known(v___x_771_, 1);
lean_inc_ref(v_arg_770_);
v___x_773_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_708_, v_arg_770_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_792_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_792_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_792_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_792_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___y_779_; size_t v___x_784_; size_t v___x_785_; uint8_t v___x_786_; 
v___x_784_ = lean_ptr_addr(v_fn_769_);
v___x_785_ = lean_ptr_addr(v_a_772_);
v___x_786_ = lean_usize_dec_eq(v___x_784_, v___x_785_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; 
lean_dec_ref_known(v_e_709_, 2);
v___x_787_ = l_Lean_Expr_app___override(v_a_772_, v_a_774_);
v___y_779_ = v___x_787_;
goto v___jp_778_;
}
else
{
size_t v___x_788_; size_t v___x_789_; uint8_t v___x_790_; 
v___x_788_ = lean_ptr_addr(v_arg_770_);
v___x_789_ = lean_ptr_addr(v_a_774_);
v___x_790_ = lean_usize_dec_eq(v___x_788_, v___x_789_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
lean_dec_ref_known(v_e_709_, 2);
v___x_791_ = l_Lean_Expr_app___override(v_a_772_, v_a_774_);
v___y_779_ = v___x_791_;
goto v___jp_778_;
}
else
{
lean_dec(v_a_774_);
lean_dec(v_a_772_);
v___y_779_ = v_e_709_;
goto v___jp_778_;
}
}
v___jp_778_:
{
lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_780_ = l_Lean_Expr_headBeta(v___y_779_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_780_);
v___x_782_ = v___x_776_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_dec(v_a_772_);
lean_dec_ref_known(v_e_709_, 2);
return v___x_773_;
}
}
else
{
lean_dec_ref_known(v_e_709_, 2);
return v___x_771_;
}
}
case 6:
{
lean_object* v_binderName_793_; lean_object* v_binderType_794_; lean_object* v_body_795_; uint8_t v_binderInfo_796_; lean_object* v___x_797_; 
v_binderName_793_ = lean_ctor_get(v_e_709_, 0);
v_binderType_794_ = lean_ctor_get(v_e_709_, 1);
v_body_795_ = lean_ctor_get(v_e_709_, 2);
v_binderInfo_796_ = lean_ctor_get_uint8(v_e_709_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_794_);
v___x_797_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_708_, v_binderType_794_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_799_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_797_, 1);
lean_inc_ref(v_body_795_);
v___x_799_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_708_, v_body_795_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_826_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_826_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_826_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_826_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
size_t v___x_804_; size_t v___x_805_; uint8_t v___x_806_; 
v___x_804_ = lean_ptr_addr(v_binderType_794_);
v___x_805_ = lean_ptr_addr(v_a_798_);
v___x_806_ = lean_usize_dec_eq(v___x_804_, v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_809_; 
lean_inc(v_binderName_793_);
lean_dec_ref_known(v_e_709_, 3);
v___x_807_ = l_Lean_Expr_lam___override(v_binderName_793_, v_a_798_, v_a_800_, v_binderInfo_796_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_807_);
v___x_809_ = v___x_802_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
else
{
size_t v___x_811_; size_t v___x_812_; uint8_t v___x_813_; 
v___x_811_ = lean_ptr_addr(v_body_795_);
v___x_812_ = lean_ptr_addr(v_a_800_);
v___x_813_ = lean_usize_dec_eq(v___x_811_, v___x_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_816_; 
lean_inc(v_binderName_793_);
lean_dec_ref_known(v_e_709_, 3);
v___x_814_ = l_Lean_Expr_lam___override(v_binderName_793_, v_a_798_, v_a_800_, v_binderInfo_796_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_814_);
v___x_816_ = v___x_802_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
else
{
uint8_t v___x_818_; 
v___x_818_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_796_, v_binderInfo_796_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_821_; 
lean_inc(v_binderName_793_);
lean_dec_ref_known(v_e_709_, 3);
v___x_819_ = l_Lean_Expr_lam___override(v_binderName_793_, v_a_798_, v_a_800_, v_binderInfo_796_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_819_);
v___x_821_ = v___x_802_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
else
{
lean_object* v___x_824_; 
lean_dec(v_a_800_);
lean_dec(v_a_798_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v_e_709_);
v___x_824_ = v___x_802_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_e_709_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
}
else
{
lean_dec(v_a_798_);
lean_dec_ref_known(v_e_709_, 3);
return v___x_799_;
}
}
else
{
lean_dec_ref_known(v_e_709_, 3);
return v___x_797_;
}
}
case 7:
{
lean_object* v_binderName_827_; lean_object* v_binderType_828_; lean_object* v_body_829_; uint8_t v_binderInfo_830_; lean_object* v___x_831_; 
v_binderName_827_ = lean_ctor_get(v_e_709_, 0);
v_binderType_828_ = lean_ctor_get(v_e_709_, 1);
v_body_829_ = lean_ctor_get(v_e_709_, 2);
v_binderInfo_830_ = lean_ctor_get_uint8(v_e_709_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_828_);
v___x_831_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_708_, v_binderType_828_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v___x_833_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_831_, 1);
lean_inc_ref(v_body_829_);
v___x_833_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_708_, v_body_829_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_860_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_860_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_860_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_860_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
size_t v___x_838_; size_t v___x_839_; uint8_t v___x_840_; 
v___x_838_ = lean_ptr_addr(v_binderType_828_);
v___x_839_ = lean_ptr_addr(v_a_832_);
v___x_840_ = lean_usize_dec_eq(v___x_838_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_843_; 
lean_inc(v_binderName_827_);
lean_dec_ref_known(v_e_709_, 3);
v___x_841_ = l_Lean_Expr_forallE___override(v_binderName_827_, v_a_832_, v_a_834_, v_binderInfo_830_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_841_);
v___x_843_ = v___x_836_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
else
{
size_t v___x_845_; size_t v___x_846_; uint8_t v___x_847_; 
v___x_845_ = lean_ptr_addr(v_body_829_);
v___x_846_ = lean_ptr_addr(v_a_834_);
v___x_847_ = lean_usize_dec_eq(v___x_845_, v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; lean_object* v___x_850_; 
lean_inc(v_binderName_827_);
lean_dec_ref_known(v_e_709_, 3);
v___x_848_ = l_Lean_Expr_forallE___override(v_binderName_827_, v_a_832_, v_a_834_, v_binderInfo_830_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_848_);
v___x_850_ = v___x_836_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
else
{
uint8_t v___x_852_; 
v___x_852_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_830_, v_binderInfo_830_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___x_855_; 
lean_inc(v_binderName_827_);
lean_dec_ref_known(v_e_709_, 3);
v___x_853_ = l_Lean_Expr_forallE___override(v_binderName_827_, v_a_832_, v_a_834_, v_binderInfo_830_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_853_);
v___x_855_ = v___x_836_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
else
{
lean_object* v___x_858_; 
lean_dec(v_a_834_);
lean_dec(v_a_832_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v_e_709_);
v___x_858_ = v___x_836_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_e_709_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
}
else
{
lean_dec(v_a_832_);
lean_dec_ref_known(v_e_709_, 3);
return v___x_833_;
}
}
else
{
lean_dec_ref_known(v_e_709_, 3);
return v___x_831_;
}
}
case 8:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
lean_dec_ref_known(v_e_709_, 4);
v___x_861_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3, &l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3);
v___x_862_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v___x_861_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
return v___x_862_;
}
case 10:
{
lean_object* v_data_863_; lean_object* v_expr_864_; lean_object* v___x_865_; 
v_data_863_ = lean_ctor_get(v_e_709_, 0);
v_expr_864_ = lean_ctor_get(v_e_709_, 1);
lean_inc_ref(v_expr_864_);
v___x_865_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_708_, v_expr_864_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_880_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_880_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_880_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_880_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
size_t v___x_870_; size_t v___x_871_; uint8_t v___x_872_; 
v___x_870_ = lean_ptr_addr(v_expr_864_);
v___x_871_ = lean_ptr_addr(v_a_866_);
v___x_872_ = lean_usize_dec_eq(v___x_870_, v___x_871_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; lean_object* v___x_875_; 
lean_inc(v_data_863_);
lean_dec_ref_known(v_e_709_, 2);
v___x_873_ = l_Lean_Expr_mdata___override(v_data_863_, v_a_866_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_873_);
v___x_875_ = v___x_868_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
else
{
lean_object* v___x_878_; 
lean_dec(v_a_866_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v_e_709_);
v___x_878_ = v___x_868_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_e_709_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_709_, 2);
return v___x_865_;
}
}
case 11:
{
lean_object* v_typeName_881_; lean_object* v_idx_882_; lean_object* v_struct_883_; lean_object* v___x_884_; 
v_typeName_881_ = lean_ctor_get(v_e_709_, 0);
v_idx_882_ = lean_ctor_get(v_e_709_, 1);
v_struct_883_ = lean_ctor_get(v_e_709_, 2);
lean_inc_ref(v_struct_883_);
v___x_884_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_708_, v_struct_883_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_899_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_899_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_899_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_899_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
size_t v___x_889_; size_t v___x_890_; uint8_t v___x_891_; 
v___x_889_ = lean_ptr_addr(v_struct_883_);
v___x_890_ = lean_ptr_addr(v_a_885_);
v___x_891_ = lean_usize_dec_eq(v___x_889_, v___x_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; lean_object* v___x_894_; 
lean_inc(v_idx_882_);
lean_inc(v_typeName_881_);
lean_dec_ref_known(v_e_709_, 3);
v___x_892_ = l_Lean_Expr_proj___override(v_typeName_881_, v_idx_882_, v_a_885_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_892_);
v___x_894_ = v___x_887_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
else
{
lean_object* v___x_897_; 
lean_dec(v_a_885_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v_e_709_);
v___x_897_ = v___x_887_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_e_709_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_709_, 3);
return v___x_884_;
}
}
default: 
{
lean_object* v___x_900_; 
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v_e_709_);
return v___x_900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(uint8_t v_pu_901_, lean_object* v_e_902_, uint8_t v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
if (lean_obj_tag(v_e_902_) == 5)
{
lean_object* v_fn_910_; lean_object* v_arg_911_; lean_object* v___x_912_; 
v_fn_910_ = lean_ctor_get(v_e_902_, 0);
v_arg_911_ = lean_ctor_get(v_e_902_, 1);
lean_inc_ref(v_fn_910_);
v___x_912_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_901_, v_fn_910_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_914_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
lean_inc_ref(v_arg_911_);
v___x_914_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_901_, v_arg_911_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_936_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_936_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_936_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_936_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
size_t v___x_919_; size_t v___x_920_; uint8_t v___x_921_; 
v___x_919_ = lean_ptr_addr(v_fn_910_);
v___x_920_ = lean_ptr_addr(v_a_913_);
v___x_921_ = lean_usize_dec_eq(v___x_919_, v___x_920_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_924_; 
lean_dec_ref_known(v_e_902_, 2);
v___x_922_ = l_Lean_Expr_app___override(v_a_913_, v_a_915_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_922_);
v___x_924_ = v___x_917_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
else
{
size_t v___x_926_; size_t v___x_927_; uint8_t v___x_928_; 
v___x_926_ = lean_ptr_addr(v_arg_911_);
v___x_927_ = lean_ptr_addr(v_a_915_);
v___x_928_ = lean_usize_dec_eq(v___x_926_, v___x_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_931_; 
lean_dec_ref_known(v_e_902_, 2);
v___x_929_ = l_Lean_Expr_app___override(v_a_913_, v_a_915_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_929_);
v___x_931_ = v___x_917_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
else
{
lean_object* v___x_934_; 
lean_dec(v_a_915_);
lean_dec(v_a_913_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v_e_902_);
v___x_934_ = v___x_917_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_e_902_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
else
{
lean_dec(v_a_913_);
lean_dec_ref_known(v_e_902_, 2);
return v___x_914_;
}
}
else
{
lean_dec_ref_known(v_e_902_, 2);
return v___x_912_;
}
}
else
{
lean_object* v___x_937_; 
v___x_937_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_901_, v_e_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp___boxed(lean_object* v_pu_938_, lean_object* v_e_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
uint8_t v_pu_boxed_947_; uint8_t v_a_boxed_948_; lean_object* v_res_949_; 
v_pu_boxed_947_ = lean_unbox(v_pu_938_);
v_a_boxed_948_ = lean_unbox(v_a_940_);
v_res_949_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_boxed_947_, v_e_939_, v_a_boxed_948_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___boxed(lean_object* v_pu_950_, lean_object* v_e_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
uint8_t v_pu_boxed_959_; uint8_t v_a_boxed_960_; lean_object* v_res_961_; 
v_pu_boxed_959_ = lean_unbox(v_pu_950_);
v_a_boxed_960_ = lean_unbox(v_a_952_);
v_res_961_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_boxed_959_, v_e_951_, v_a_boxed_960_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(lean_object* v_00_u03b2_962_, lean_object* v_m_963_, lean_object* v_a_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v_m_963_, v_a_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___boxed(lean_object* v_00_u03b2_966_, lean_object* v_m_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(v_00_u03b2_966_, v_m_967_, v_a_968_);
lean_dec(v_a_968_);
lean_dec_ref(v_m_967_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(lean_object* v_00_u03b2_970_, lean_object* v_a_971_, lean_object* v_x_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_971_, v_x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_974_, lean_object* v_a_975_, lean_object* v_x_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(v_00_u03b2_974_, v_a_975_, v_x_976_);
lean_dec(v_x_976_);
lean_dec(v_a_975_);
return v_res_977_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___closed__0(void){
_start:
{
uint8_t v___x_978_; lean_object* v___x_979_; 
v___x_978_ = 1;
v___x_979_ = l_Lean_Compiler_LCNF_Purity_ctorIdx(v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(uint8_t v_pu_980_, lean_object* v_e_981_, uint8_t v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_989_ = l_Lean_Compiler_LCNF_Purity_ctorIdx(v_pu_980_);
v___x_990_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___closed__0, &l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___closed__0);
v___x_991_ = lean_nat_dec_eq(v___x_989_, v___x_990_);
lean_dec(v___x_989_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
v___x_992_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_980_, v_e_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
return v___x_992_;
}
else
{
lean_object* v___x_993_; 
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v_e_981_);
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___boxed(lean_object* v_pu_994_, lean_object* v_e_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
uint8_t v_pu_boxed_1003_; uint8_t v_a_boxed_1004_; lean_object* v_res_1005_; 
v_pu_boxed_1003_ = lean_unbox(v_pu_994_);
v_a_boxed_1004_ = lean_unbox(v_a_996_);
v_res_1005_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_boxed_1003_, v_e_995_, v_a_boxed_1004_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t v_pu_1006_, lean_object* v_p_1007_, uint8_t v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_fvarId_1015_; lean_object* v_binderName_1016_; lean_object* v_type_1017_; uint8_t v_borrow_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1066_; 
v_fvarId_1015_ = lean_ctor_get(v_p_1007_, 0);
v_binderName_1016_ = lean_ctor_get(v_p_1007_, 1);
v_type_1017_ = lean_ctor_get(v_p_1007_, 2);
v_borrow_1018_ = lean_ctor_get_uint8(v_p_1007_, sizeof(void*)*3);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_p_1007_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1020_ = v_p_1007_;
v_isShared_1021_ = v_isSharedCheck_1066_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_type_1017_);
lean_inc(v_binderName_1016_);
lean_inc(v_fvarId_1015_);
lean_dec(v_p_1007_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1066_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1022_; lean_object* v_a_1023_; lean_object* v___x_1024_; 
v___x_1022_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_1016_, v_a_1008_, v_a_1011_);
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref(v___x_1022_);
v___x_1024_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1006_, v_type_1017_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1026_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v___x_1026_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_1015_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1049_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1049_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1049_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 2, v_a_1025_);
lean_ctor_set(v___x_1020_, 1, v_a_1023_);
lean_ctor_set(v___x_1020_, 0, v_a_1027_);
v___x_1032_ = v___x_1020_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1027_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_a_1023_);
lean_ctor_set(v_reuseFailAlloc_1048_, 2, v_a_1025_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, sizeof(void*)*3, v_borrow_1018_);
v___x_1032_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1033_; lean_object* v_lctx_1034_; lean_object* v_nextIdx_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1047_; 
v___x_1033_ = lean_st_ref_take(v_a_1011_);
v_lctx_1034_ = lean_ctor_get(v___x_1033_, 0);
v_nextIdx_1035_ = lean_ctor_get(v___x_1033_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1037_ = v___x_1033_;
v_isShared_1038_ = v_isSharedCheck_1047_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_nextIdx_1035_);
lean_inc(v_lctx_1034_);
lean_dec(v___x_1033_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1047_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
lean_inc_ref(v___x_1032_);
v___x_1039_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_1006_, v_lctx_1034_, v___x_1032_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1039_);
v___x_1041_ = v___x_1037_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_nextIdx_1035_);
v___x_1041_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1042_ = lean_st_ref_put(v_a_1011_, v___x_1041_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1032_);
v___x_1044_ = v___x_1029_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1032_);
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
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec(v_a_1025_);
lean_dec(v_a_1023_);
lean_del_object(v___x_1020_);
v_a_1050_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1026_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1026_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec(v_a_1023_);
lean_del_object(v___x_1020_);
lean_dec(v_fvarId_1015_);
v_a_1058_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1024_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1024_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(lean_object* v_pu_1067_, lean_object* v_p_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
uint8_t v_pu_boxed_1076_; uint8_t v_a_boxed_1077_; lean_object* v_res_1078_; 
v_pu_boxed_1076_ = lean_unbox(v_pu_1067_);
v_a_boxed_1077_ = lean_unbox(v_a_1069_);
v_res_1078_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_boxed_1076_, v_p_1068_, v_a_boxed_1077_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg(uint8_t v_pu_1079_, lean_object* v_arg_1080_, uint8_t v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
switch(lean_obj_tag(v_arg_1080_))
{
case 0:
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_arg_1080_);
return v___x_1088_;
}
case 1:
{
lean_object* v_fvarId_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_fvarId_1089_ = lean_ctor_get(v_arg_1080_, 0);
v___x_1090_ = lean_st_ref_get(v_a_1082_);
v___x_1091_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v___x_1090_, v_fvarId_1089_);
lean_dec(v___x_1090_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v_arg_1080_);
return v___x_1092_;
}
else
{
lean_object* v_val_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1123_; 
lean_dec_ref_known(v_arg_1080_, 1);
v_val_1093_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1095_ = v___x_1091_;
v_isShared_1096_ = v_isSharedCheck_1123_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_val_1093_);
lean_dec(v___x_1091_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1123_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
switch(lean_obj_tag(v_val_1093_))
{
case 0:
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1097_ = lean_box(0);
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1097_);
v___x_1099_ = v___x_1095_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
case 1:
{
lean_object* v_fvarId_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1111_; 
v_fvarId_1101_ = lean_ctor_get(v_val_1093_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_val_1093_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1103_ = v_val_1093_;
v_isShared_1104_ = v_isSharedCheck_1111_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_fvarId_1101_);
lean_dec(v_val_1093_);
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
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_fvarId_1101_);
v___x_1106_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1108_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1106_);
v___x_1108_ = v___x_1095_;
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
default: 
{
lean_object* v_expr_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1122_; 
v_expr_1112_ = lean_ctor_get(v_val_1093_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_val_1093_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1114_ = v_val_1093_;
v_isShared_1115_ = v_isSharedCheck_1122_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_expr_1112_);
lean_dec(v_val_1093_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1122_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_expr_1112_);
v___x_1117_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1119_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1117_);
v___x_1119_ = v___x_1095_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
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
lean_object* v_expr_1124_; lean_object* v___x_1125_; 
v_expr_1124_ = lean_ctor_get(v_arg_1080_, 0);
lean_inc_ref(v_expr_1124_);
v___x_1125_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1079_, v_expr_1124_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1134_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1128_ = v___x_1125_;
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1125_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1130_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1079_, v_arg_1080_, v_a_1126_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v___x_1130_);
v___x_1132_ = v___x_1128_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec_ref_known(v_arg_1080_, 1);
v_a_1135_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1125_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1125_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg___boxed(lean_object* v_pu_1143_, lean_object* v_arg_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
uint8_t v_pu_boxed_1152_; uint8_t v_a_boxed_1153_; lean_object* v_res_1154_; 
v_pu_boxed_1152_ = lean_unbox(v_pu_1143_);
v_a_boxed_1153_ = lean_unbox(v_a_1145_);
v_res_1154_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_boxed_1152_, v_arg_1144_, v_a_boxed_1153_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_a_1146_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(uint8_t v_pu_1155_, size_t v_sz_1156_, size_t v_i_1157_, lean_object* v_bs_1158_, uint8_t v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
uint8_t v___x_1166_; 
v___x_1166_ = lean_usize_dec_lt(v_i_1157_, v_sz_1156_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v_bs_1158_);
return v___x_1167_;
}
else
{
lean_object* v_v_1168_; lean_object* v___x_1169_; lean_object* v_bs_x27_1170_; lean_object* v___x_1171_; 
v_v_1168_ = lean_array_uget(v_bs_1158_, v_i_1157_);
v___x_1169_ = lean_unsigned_to_nat(0u);
v_bs_x27_1170_ = lean_array_uset(v_bs_1158_, v_i_1157_, v___x_1169_);
v___x_1171_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_1155_, v_v_1168_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; size_t v___x_1173_; size_t v___x_1174_; lean_object* v___x_1175_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref_known(v___x_1171_, 1);
v___x_1173_ = ((size_t)1ULL);
v___x_1174_ = lean_usize_add(v_i_1157_, v___x_1173_);
v___x_1175_ = lean_array_uset(v_bs_x27_1170_, v_i_1157_, v_a_1172_);
v_i_1157_ = v___x_1174_;
v_bs_1158_ = v___x_1175_;
goto _start;
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec_ref(v_bs_x27_1170_);
v_a_1177_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1171_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1171_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0___boxed(lean_object* v_pu_1185_, lean_object* v_sz_1186_, lean_object* v_i_1187_, lean_object* v_bs_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
uint8_t v_pu_boxed_1196_; size_t v_sz_boxed_1197_; size_t v_i_boxed_1198_; uint8_t v___y_339__boxed_1199_; lean_object* v_res_1200_; 
v_pu_boxed_1196_ = lean_unbox(v_pu_1185_);
v_sz_boxed_1197_ = lean_unbox_usize(v_sz_1186_);
lean_dec(v_sz_1186_);
v_i_boxed_1198_ = lean_unbox_usize(v_i_1187_);
lean_dec(v_i_1187_);
v___y_339__boxed_1199_ = lean_unbox(v___y_1189_);
v_res_1200_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_boxed_1196_, v_sz_boxed_1197_, v_i_boxed_1198_, v_bs_1188_, v___y_339__boxed_1199_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs(uint8_t v_pu_1201_, lean_object* v_args_1202_, uint8_t v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
size_t v_sz_1210_; size_t v___x_1211_; lean_object* v___x_1212_; 
v_sz_1210_ = lean_array_size(v_args_1202_);
v___x_1211_ = ((size_t)0ULL);
v___x_1212_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_1201_, v_sz_1210_, v___x_1211_, v_args_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs___boxed(lean_object* v_pu_1213_, lean_object* v_args_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
uint8_t v_pu_boxed_1222_; uint8_t v_a_boxed_1223_; lean_object* v_res_1224_; 
v_pu_boxed_1222_ = lean_unbox(v_pu_1213_);
v_a_boxed_1223_ = lean_unbox(v_a_1215_);
v_res_1224_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_boxed_1222_, v_args_1214_, v_a_boxed_1223_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec(v_a_1216_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(uint8_t v_pu_1225_, lean_object* v_e_1226_, uint8_t v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v_fvarId_1235_; lean_object* v___y_1236_; lean_object* v_args_1252_; uint8_t v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; 
switch(lean_obj_tag(v_e_1226_))
{
case 2:
{
lean_object* v_struct_1277_; uint8_t v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v_struct_1277_ = lean_ctor_get(v_e_1226_, 2);
v___x_1278_ = 1;
v___x_1279_ = lean_st_ref_get(v_a_1228_);
lean_inc(v_struct_1277_);
v___x_1280_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1279_, v_struct_1277_, v___x_1278_);
lean_dec(v___x_1279_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_fvarId_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1289_; 
v_fvarId_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_fvarId_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1285_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1225_, v_e_1226_, v_fvarId_1281_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1285_);
v___x_1287_ = v___x_1283_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
else
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_dec_ref_known(v_e_1226_, 3);
v___x_1290_ = lean_box(1);
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
return v___x_1291_;
}
}
case 3:
{
lean_object* v_args_1292_; lean_object* v___x_1293_; 
v_args_1292_ = lean_ctor_get(v_e_1226_, 2);
lean_inc_ref(v_args_1292_);
v___x_1293_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1225_, v_args_1292_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1302_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1302_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1302_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1298_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1226_, v_a_1294_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1298_);
v___x_1300_ = v___x_1296_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec_ref_known(v_e_1226_, 3);
v_a_1303_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1293_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1293_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
case 4:
{
lean_object* v_fvarId_1311_; lean_object* v_args_1312_; uint8_t v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v_fvarId_1311_ = lean_ctor_get(v_e_1226_, 0);
v_args_1312_ = lean_ctor_get(v_e_1226_, 1);
v___x_1313_ = 1;
v___x_1314_ = lean_st_ref_get(v_a_1228_);
lean_inc(v_fvarId_1311_);
v___x_1315_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1314_, v_fvarId_1311_, v___x_1313_);
lean_dec(v___x_1314_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_fvarId_1316_; lean_object* v___x_1317_; 
v_fvarId_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_fvarId_1316_);
lean_dec_ref_known(v___x_1315_, 1);
lean_inc_ref(v_args_1312_);
v___x_1317_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1225_, v_args_1312_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1326_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1326_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1326_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1322_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___redArg(v_e_1226_, v_fvarId_1316_, v_a_1318_);
lean_dec_ref_known(v_e_1226_, 2);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1322_);
v___x_1324_ = v___x_1320_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec(v_fvarId_1316_);
lean_dec_ref_known(v_e_1226_, 2);
v_a_1327_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1317_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1317_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec_ref_known(v_e_1226_, 2);
v___x_1335_ = lean_box(1);
v___x_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
return v___x_1336_;
}
}
case 5:
{
lean_object* v_args_1337_; lean_object* v___x_1338_; 
v_args_1337_ = lean_ctor_get(v_e_1226_, 1);
lean_inc_ref(v_args_1337_);
v___x_1338_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1225_, v_args_1337_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1347_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1341_ = v___x_1338_;
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1338_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1343_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1226_, v_a_1339_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v___x_1343_);
v___x_1345_ = v___x_1341_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
lean_dec_ref_known(v_e_1226_, 2);
v_a_1348_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1338_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1338_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
case 6:
{
lean_object* v_var_1356_; 
v_var_1356_ = lean_ctor_get(v_e_1226_, 1);
lean_inc(v_var_1356_);
v_fvarId_1235_ = v_var_1356_;
v___y_1236_ = v_a_1228_;
goto v___jp_1234_;
}
case 7:
{
lean_object* v_var_1357_; 
v_var_1357_ = lean_ctor_get(v_e_1226_, 1);
lean_inc(v_var_1357_);
v_fvarId_1235_ = v_var_1357_;
v___y_1236_ = v_a_1228_;
goto v___jp_1234_;
}
case 8:
{
lean_object* v_var_1358_; uint8_t v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_var_1358_ = lean_ctor_get(v_e_1226_, 2);
v___x_1359_ = 1;
v___x_1360_ = lean_st_ref_get(v_a_1228_);
lean_inc(v_var_1358_);
v___x_1361_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1360_, v_var_1358_, v___x_1359_);
lean_dec(v___x_1360_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_fvarId_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1370_; 
v_fvarId_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1370_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_fvarId_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1370_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1366_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1225_, v_e_1226_, v_fvarId_1362_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1366_);
v___x_1368_ = v___x_1364_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_dec_ref_known(v_e_1226_, 3);
v___x_1371_ = lean_box(1);
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
return v___x_1372_;
}
}
case 9:
{
lean_object* v_args_1373_; 
v_args_1373_ = lean_ctor_get(v_e_1226_, 1);
lean_inc_ref(v_args_1373_);
v_args_1252_ = v_args_1373_;
v___y_1253_ = v_a_1227_;
v___y_1254_ = v_a_1228_;
v___y_1255_ = v_a_1229_;
v___y_1256_ = v_a_1230_;
v___y_1257_ = v_a_1231_;
v___y_1258_ = v_a_1232_;
goto v___jp_1251_;
}
case 10:
{
lean_object* v_args_1374_; 
v_args_1374_ = lean_ctor_get(v_e_1226_, 1);
lean_inc_ref(v_args_1374_);
v_args_1252_ = v_args_1374_;
v___y_1253_ = v_a_1227_;
v___y_1254_ = v_a_1228_;
v___y_1255_ = v_a_1229_;
v___y_1256_ = v_a_1230_;
v___y_1257_ = v_a_1231_;
v___y_1258_ = v_a_1232_;
goto v___jp_1251_;
}
case 11:
{
lean_object* v_n_1375_; lean_object* v_var_1376_; uint8_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v_n_1375_ = lean_ctor_get(v_e_1226_, 0);
lean_inc(v_n_1375_);
v_var_1376_ = lean_ctor_get(v_e_1226_, 1);
v___x_1377_ = 1;
v___x_1378_ = lean_st_ref_get(v_a_1228_);
lean_inc(v_var_1376_);
v___x_1379_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1378_, v_var_1376_, v___x_1377_);
lean_dec(v___x_1378_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_fvarId_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1388_; 
v_fvarId_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1388_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_fvarId_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1388_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1384_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp___redArg(v_e_1226_, v_n_1375_, v_fvarId_1380_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1384_);
v___x_1386_ = v___x_1382_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_dec(v_n_1375_);
lean_dec_ref_known(v_e_1226_, 2);
v___x_1389_ = lean_box(1);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
}
case 12:
{
lean_object* v_var_1391_; lean_object* v_i_1392_; uint8_t v_updateHeader_1393_; lean_object* v_args_1394_; uint8_t v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v_var_1391_ = lean_ctor_get(v_e_1226_, 0);
v_i_1392_ = lean_ctor_get(v_e_1226_, 1);
lean_inc_ref(v_i_1392_);
v_updateHeader_1393_ = lean_ctor_get_uint8(v_e_1226_, sizeof(void*)*3);
v_args_1394_ = lean_ctor_get(v_e_1226_, 2);
v___x_1395_ = 1;
v___x_1396_ = lean_st_ref_get(v_a_1228_);
lean_inc(v_var_1391_);
v___x_1397_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1396_, v_var_1391_, v___x_1395_);
lean_dec(v___x_1396_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_fvarId_1398_; lean_object* v___x_1399_; 
v_fvarId_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_fvarId_1398_);
lean_dec_ref_known(v___x_1397_, 1);
lean_inc_ref(v_args_1394_);
v___x_1399_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1225_, v_args_1394_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1408_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1408_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1408_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1404_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp___redArg(v_e_1226_, v_fvarId_1398_, v_i_1392_, v_updateHeader_1393_, v_a_1400_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v___x_1404_);
v___x_1406_ = v___x_1402_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_dec(v_fvarId_1398_);
lean_dec_ref(v_i_1392_);
lean_dec_ref_known(v_e_1226_, 3);
v_a_1409_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1399_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1399_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
lean_dec_ref(v_i_1392_);
lean_dec_ref_known(v_e_1226_, 3);
v___x_1417_ = lean_box(1);
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
return v___x_1418_;
}
}
case 13:
{
lean_object* v_ty_1419_; lean_object* v_fvarId_1420_; uint8_t v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v_ty_1419_ = lean_ctor_get(v_e_1226_, 0);
lean_inc_ref(v_ty_1419_);
v_fvarId_1420_ = lean_ctor_get(v_e_1226_, 1);
v___x_1421_ = 1;
v___x_1422_ = lean_st_ref_get(v_a_1228_);
lean_inc(v_fvarId_1420_);
v___x_1423_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1422_, v_fvarId_1420_, v___x_1421_);
lean_dec(v___x_1422_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_fvarId_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1432_; 
v_fvarId_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1432_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_fvarId_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1432_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1428_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp___redArg(v_e_1226_, v_ty_1419_, v_fvarId_1424_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1428_);
v___x_1430_ = v___x_1426_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_dec_ref(v_ty_1419_);
lean_dec_ref_known(v_e_1226_, 2);
v___x_1433_ = lean_box(1);
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
return v___x_1434_;
}
}
case 14:
{
lean_object* v_fvarId_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v_fvarId_1435_ = lean_ctor_get(v_e_1226_, 0);
v___x_1436_ = 1;
v___x_1437_ = lean_st_ref_get(v_a_1228_);
lean_inc(v_fvarId_1435_);
v___x_1438_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1437_, v_fvarId_1435_, v___x_1436_);
lean_dec(v___x_1437_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_fvarId_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1447_; 
v_fvarId_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1447_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_fvarId_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1447_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1443_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp___redArg(v_e_1226_, v_fvarId_1439_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1443_);
v___x_1445_ = v___x_1441_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
else
{
lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1455_; 
v_isSharedCheck_1455_ = !lean_is_exclusive(v_e_1226_);
if (v_isSharedCheck_1455_ == 0)
{
lean_object* v_unused_1456_; 
v_unused_1456_ = lean_ctor_get(v_e_1226_, 0);
lean_dec(v_unused_1456_);
v___x_1449_ = v_e_1226_;
v_isShared_1450_ = v_isSharedCheck_1455_;
goto v_resetjp_1448_;
}
else
{
lean_dec(v_e_1226_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1455_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1451_ = lean_box(1);
if (v_isShared_1450_ == 0)
{
lean_ctor_set_tag(v___x_1449_, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1451_);
v___x_1453_ = v___x_1449_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
case 15:
{
lean_object* v_fvarId_1457_; uint8_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v_fvarId_1457_ = lean_ctor_get(v_e_1226_, 0);
v___x_1458_ = 1;
v___x_1459_ = lean_st_ref_get(v_a_1228_);
lean_inc(v_fvarId_1457_);
v___x_1460_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1459_, v_fvarId_1457_, v___x_1458_);
lean_dec(v___x_1459_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_fvarId_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1469_; 
v_fvarId_1461_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1463_ = v___x_1460_;
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_fvarId_1461_);
lean_dec(v___x_1460_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1465_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp___redArg(v_e_1226_, v_fvarId_1461_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 0, v___x_1465_);
v___x_1467_ = v___x_1463_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
else
{
lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1477_; 
v_isSharedCheck_1477_ = !lean_is_exclusive(v_e_1226_);
if (v_isSharedCheck_1477_ == 0)
{
lean_object* v_unused_1478_; 
v_unused_1478_ = lean_ctor_get(v_e_1226_, 0);
lean_dec(v_unused_1478_);
v___x_1471_ = v_e_1226_;
v_isShared_1472_ = v_isSharedCheck_1477_;
goto v_resetjp_1470_;
}
else
{
lean_dec(v_e_1226_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1477_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1473_ = lean_box(1);
if (v_isShared_1472_ == 0)
{
lean_ctor_set_tag(v___x_1471_, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1473_);
v___x_1475_ = v___x_1471_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
default: 
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v_e_1226_);
return v___x_1479_;
}
}
v___jp_1234_:
{
uint8_t v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = 1;
v___x_1238_ = lean_st_ref_get(v___y_1236_);
v___x_1239_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1238_, v_fvarId_1235_, v___x_1237_);
lean_dec(v___x_1238_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_fvarId_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1248_; 
v_fvarId_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1248_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_fvarId_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1248_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; lean_object* v___x_1246_; 
v___x_1244_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1225_, v_e_1226_, v_fvarId_1240_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1244_);
v___x_1246_ = v___x_1242_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
else
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_dec(v_e_1226_);
v___x_1249_ = lean_box(1);
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
}
v___jp_1251_:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1225_, v_args_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1268_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1262_ = v___x_1259_;
v_isShared_1263_ = v_isSharedCheck_1268_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1259_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1268_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1264_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1226_, v_a_1260_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1264_);
v___x_1266_ = v___x_1262_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec(v_e_1226_);
v_a_1269_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1259_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1259_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue___boxed(lean_object* v_pu_1480_, lean_object* v_e_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_){
_start:
{
uint8_t v_pu_boxed_1489_; uint8_t v_a_boxed_1490_; lean_object* v_res_1491_; 
v_pu_boxed_1489_ = lean_unbox(v_pu_1480_);
v_a_boxed_1490_ = lean_unbox(v_a_1482_);
v_res_1491_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_boxed_1489_, v_e_1481_, v_a_boxed_1490_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
lean_dec(v_a_1487_);
lean_dec_ref(v_a_1486_);
lean_dec(v_a_1485_);
lean_dec_ref(v_a_1484_);
lean_dec(v_a_1483_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(uint8_t v_pu_1492_, lean_object* v_decl_1493_, uint8_t v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_){
_start:
{
lean_object* v_fvarId_1501_; lean_object* v_binderName_1502_; lean_object* v_type_1503_; lean_object* v_value_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1562_; 
v_fvarId_1501_ = lean_ctor_get(v_decl_1493_, 0);
v_binderName_1502_ = lean_ctor_get(v_decl_1493_, 1);
v_type_1503_ = lean_ctor_get(v_decl_1493_, 2);
v_value_1504_ = lean_ctor_get(v_decl_1493_, 3);
v_isSharedCheck_1562_ = !lean_is_exclusive(v_decl_1493_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1506_ = v_decl_1493_;
v_isShared_1507_ = v_isSharedCheck_1562_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_value_1504_);
lean_inc(v_type_1503_);
lean_inc(v_binderName_1502_);
lean_inc(v_fvarId_1501_);
lean_dec(v_decl_1493_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1562_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; lean_object* v_a_1509_; lean_object* v___x_1510_; 
v___x_1508_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_1502_, v_a_1494_, v_a_1497_);
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1509_);
lean_dec_ref(v___x_1508_);
v___x_1510_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1492_, v_type_1503_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1512_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref_known(v___x_1510_, 1);
v___x_1512_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_1492_, v_value_1504_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1514_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1512_, 1);
v___x_1514_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_1501_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1537_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1537_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1537_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 3, v_a_1513_);
lean_ctor_set(v___x_1506_, 2, v_a_1511_);
lean_ctor_set(v___x_1506_, 1, v_a_1509_);
lean_ctor_set(v___x_1506_, 0, v_a_1515_);
v___x_1520_ = v___x_1506_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1515_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_a_1509_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v_a_1511_);
lean_ctor_set(v_reuseFailAlloc_1536_, 3, v_a_1513_);
v___x_1520_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1521_; lean_object* v_lctx_1522_; lean_object* v_nextIdx_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1535_; 
v___x_1521_ = lean_st_ref_take(v_a_1497_);
v_lctx_1522_ = lean_ctor_get(v___x_1521_, 0);
v_nextIdx_1523_ = lean_ctor_get(v___x_1521_, 1);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1525_ = v___x_1521_;
v_isShared_1526_ = v_isSharedCheck_1535_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_nextIdx_1523_);
lean_inc(v_lctx_1522_);
lean_dec(v___x_1521_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1535_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1529_; 
lean_inc_ref(v___x_1520_);
v___x_1527_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_1492_, v_lctx_1522_, v___x_1520_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1527_);
v___x_1529_ = v___x_1525_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_nextIdx_1523_);
v___x_1529_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1530_; lean_object* v___x_1532_; 
v___x_1530_ = lean_st_ref_put(v_a_1497_, v___x_1529_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1520_);
v___x_1532_ = v___x_1517_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1520_);
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
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec(v_a_1513_);
lean_dec(v_a_1511_);
lean_dec(v_a_1509_);
lean_del_object(v___x_1506_);
v_a_1538_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1514_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1514_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v_a_1511_);
lean_dec(v_a_1509_);
lean_del_object(v___x_1506_);
lean_dec(v_fvarId_1501_);
v_a_1546_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1512_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1512_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_dec(v_a_1509_);
lean_del_object(v___x_1506_);
lean_dec(v_value_1504_);
lean_dec(v_fvarId_1501_);
v_a_1554_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1510_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1510_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(lean_object* v_pu_1563_, lean_object* v_decl_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_){
_start:
{
uint8_t v_pu_boxed_1572_; uint8_t v_a_boxed_1573_; lean_object* v_res_1574_; 
v_pu_boxed_1572_ = lean_unbox(v_pu_1563_);
v_a_boxed_1573_ = lean_unbox(v_a_1565_);
v_res_1574_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_boxed_1572_, v_decl_1564_, v_a_boxed_1573_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
lean_dec(v_a_1570_);
lean_dec_ref(v_a_1569_);
lean_dec(v_a_1568_);
lean_dec_ref(v_a_1567_);
lean_dec(v_a_1566_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(uint8_t v_pu_1575_, size_t v_sz_1576_, size_t v_i_1577_, lean_object* v_bs_1578_, uint8_t v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
uint8_t v___x_1586_; 
v___x_1586_ = lean_usize_dec_lt(v_i_1577_, v_sz_1576_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; 
v___x_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1587_, 0, v_bs_1578_);
return v___x_1587_;
}
else
{
lean_object* v_v_1588_; lean_object* v___x_1589_; lean_object* v_bs_x27_1590_; lean_object* v___x_1591_; 
v_v_1588_ = lean_array_uget(v_bs_1578_, v_i_1577_);
v___x_1589_ = lean_unsigned_to_nat(0u);
v_bs_x27_1590_ = lean_array_uset(v_bs_1578_, v_i_1577_, v___x_1589_);
v___x_1591_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_1575_, v_v_1588_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; size_t v___x_1593_; size_t v___x_1594_; lean_object* v___x_1595_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1591_, 1);
v___x_1593_ = ((size_t)1ULL);
v___x_1594_ = lean_usize_add(v_i_1577_, v___x_1593_);
v___x_1595_ = lean_array_uset(v_bs_x27_1590_, v_i_1577_, v_a_1592_);
v_i_1577_ = v___x_1594_;
v_bs_1578_ = v___x_1595_;
goto _start;
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec_ref(v_bs_x27_1590_);
v_a_1597_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1591_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1591_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0___boxed(lean_object* v_pu_1605_, lean_object* v_sz_1606_, lean_object* v_i_1607_, lean_object* v_bs_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
uint8_t v_pu_boxed_1616_; size_t v_sz_boxed_1617_; size_t v_i_boxed_1618_; uint8_t v___y_26878__boxed_1619_; lean_object* v_res_1620_; 
v_pu_boxed_1616_ = lean_unbox(v_pu_1605_);
v_sz_boxed_1617_ = lean_unbox_usize(v_sz_1606_);
lean_dec(v_sz_1606_);
v_i_boxed_1618_ = lean_unbox_usize(v_i_1607_);
lean_dec(v_i_1607_);
v___y_26878__boxed_1619_ = lean_unbox(v___y_1609_);
v_res_1620_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_boxed_1616_, v_sz_boxed_1617_, v_i_boxed_1618_, v_bs_1608_, v___y_26878__boxed_1619_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(uint8_t v_pu_1621_, size_t v_sz_1622_, size_t v_i_1623_, lean_object* v_bs_1624_, uint8_t v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
uint8_t v___x_1632_; 
v___x_1632_ = lean_usize_dec_lt(v_i_1623_, v_sz_1622_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; 
v___x_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1633_, 0, v_bs_1624_);
return v___x_1633_;
}
else
{
lean_object* v_v_1634_; lean_object* v___x_1635_; lean_object* v_bs_x27_1636_; lean_object* v_a_1638_; 
v_v_1634_ = lean_array_uget(v_bs_1624_, v_i_1623_);
v___x_1635_ = lean_unsigned_to_nat(0u);
v_bs_x27_1636_ = lean_array_uset(v_bs_1624_, v_i_1623_, v___x_1635_);
switch(lean_obj_tag(v_v_1634_))
{
case 0:
{
lean_object* v_ctorName_1643_; lean_object* v_params_1644_; lean_object* v_code_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1666_; 
v_ctorName_1643_ = lean_ctor_get(v_v_1634_, 0);
v_params_1644_ = lean_ctor_get(v_v_1634_, 1);
v_code_1645_ = lean_ctor_get(v_v_1634_, 2);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_v_1634_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1647_ = v_v_1634_;
v_isShared_1648_ = v_isSharedCheck_1666_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_code_1645_);
lean_inc(v_params_1644_);
lean_inc(v_ctorName_1643_);
lean_dec(v_v_1634_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1666_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
size_t v_sz_1649_; size_t v___x_1650_; lean_object* v___x_1651_; 
v_sz_1649_ = lean_array_size(v_params_1644_);
v___x_1650_ = ((size_t)0ULL);
v___x_1651_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_1621_, v_sz_1649_, v___x_1650_, v_params_1644_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1653_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref_known(v___x_1651_, 1);
v___x_1653_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1621_, v_code_1645_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1656_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v___x_1653_, 1);
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 2, v_a_1654_);
lean_ctor_set(v___x_1647_, 1, v_a_1652_);
v___x_1656_ = v___x_1647_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_ctorName_1643_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_a_1652_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v_a_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
v_a_1638_ = v___x_1656_;
goto v___jp_1637_;
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec(v_a_1652_);
lean_del_object(v___x_1647_);
lean_dec(v_ctorName_1643_);
lean_dec_ref(v_bs_x27_1636_);
v_a_1658_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1653_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1653_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
else
{
lean_del_object(v___x_1647_);
lean_dec_ref(v_code_1645_);
lean_dec(v_ctorName_1643_);
lean_dec_ref(v_bs_x27_1636_);
return v___x_1651_;
}
}
}
case 1:
{
lean_object* v_info_1667_; lean_object* v_code_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1685_; 
v_info_1667_ = lean_ctor_get(v_v_1634_, 0);
v_code_1668_ = lean_ctor_get(v_v_1634_, 1);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_v_1634_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1670_ = v_v_1634_;
v_isShared_1671_ = v_isSharedCheck_1685_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_code_1668_);
lean_inc(v_info_1667_);
lean_dec(v_v_1634_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1685_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1621_, v_code_1668_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1675_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_a_1673_);
lean_dec_ref_known(v___x_1672_, 1);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 1, v_a_1673_);
v___x_1675_ = v___x_1670_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_info_1667_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_a_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
v_a_1638_ = v___x_1675_;
goto v___jp_1637_;
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
lean_del_object(v___x_1670_);
lean_dec_ref(v_info_1667_);
lean_dec_ref(v_bs_x27_1636_);
v_a_1677_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1672_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1672_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
default: 
{
lean_object* v_code_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1703_; 
v_code_1686_ = lean_ctor_get(v_v_1634_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_v_1634_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1688_ = v_v_1634_;
v_isShared_1689_ = v_isSharedCheck_1703_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_code_1686_);
lean_dec(v_v_1634_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1703_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1621_, v_code_1686_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1693_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref_known(v___x_1690_, 1);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v_a_1691_);
v___x_1693_ = v___x_1688_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
v_a_1638_ = v___x_1693_;
goto v___jp_1637_;
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_del_object(v___x_1688_);
lean_dec_ref(v_bs_x27_1636_);
v_a_1695_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1690_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1690_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
}
v___jp_1637_:
{
size_t v___x_1639_; size_t v___x_1640_; lean_object* v___x_1641_; 
v___x_1639_ = ((size_t)1ULL);
v___x_1640_ = lean_usize_add(v_i_1623_, v___x_1639_);
v___x_1641_ = lean_array_uset(v_bs_x27_1636_, v_i_1623_, v_a_1638_);
v_i_1623_ = v___x_1640_;
v_bs_1624_ = v___x_1641_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t v_pu_1704_, lean_object* v_code_1705_, uint8_t v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
switch(lean_obj_tag(v_code_1705_))
{
case 0:
{
lean_object* v_decl_1713_; lean_object* v_k_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1740_; 
v_decl_1713_ = lean_ctor_get(v_code_1705_, 0);
v_k_1714_ = lean_ctor_get(v_code_1705_, 1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_code_1705_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1716_ = v_code_1705_;
v_isShared_1717_ = v_isSharedCheck_1740_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_k_1714_);
lean_inc(v_decl_1713_);
lean_dec(v_code_1705_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1740_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_1704_, v_decl_1713_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1720_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
v___x_1720_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1704_, v_k_1714_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1731_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1723_ = v___x_1720_;
v_isShared_1724_ = v_isSharedCheck_1731_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1720_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1731_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 1, v_a_1721_);
lean_ctor_set(v___x_1716_, 0, v_a_1719_);
v___x_1726_ = v___x_1716_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1719_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
lean_object* v___x_1728_; 
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v___x_1726_);
v___x_1728_ = v___x_1723_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
else
{
lean_dec(v_a_1719_);
lean_del_object(v___x_1716_);
return v___x_1720_;
}
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_del_object(v___x_1716_);
lean_dec_ref(v_k_1714_);
v_a_1732_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1718_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1718_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_1741_; lean_object* v_k_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1768_; 
v_decl_1741_ = lean_ctor_get(v_code_1705_, 0);
v_k_1742_ = lean_ctor_get(v_code_1705_, 1);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_code_1705_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1744_ = v_code_1705_;
v_isShared_1745_ = v_isSharedCheck_1768_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_k_1742_);
lean_inc(v_decl_1741_);
lean_dec(v_code_1705_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1768_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1704_, v_decl_1741_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1748_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref_known(v___x_1746_, 1);
v___x_1748_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1704_, v_k_1742_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1759_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1759_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1759_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 1, v_a_1749_);
lean_ctor_set(v___x_1744_, 0, v_a_1747_);
v___x_1754_ = v___x_1744_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1747_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1756_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1754_);
v___x_1756_ = v___x_1751_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
else
{
lean_dec(v_a_1747_);
lean_del_object(v___x_1744_);
return v___x_1748_;
}
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_del_object(v___x_1744_);
lean_dec_ref(v_k_1742_);
v_a_1760_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1746_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1746_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
}
case 2:
{
lean_object* v_decl_1769_; lean_object* v_k_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1796_; 
v_decl_1769_ = lean_ctor_get(v_code_1705_, 0);
v_k_1770_ = lean_ctor_get(v_code_1705_, 1);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_code_1705_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1772_ = v_code_1705_;
v_isShared_1773_ = v_isSharedCheck_1796_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_k_1770_);
lean_inc(v_decl_1769_);
lean_dec(v_code_1705_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1796_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1704_, v_decl_1769_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1776_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref_known(v___x_1774_, 1);
v___x_1776_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1704_, v_k_1770_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1787_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1787_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1787_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 1, v_a_1777_);
lean_ctor_set(v___x_1772_, 0, v_a_1775_);
v___x_1782_ = v___x_1772_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1775_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1784_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1782_);
v___x_1784_ = v___x_1779_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_dec(v_a_1775_);
lean_del_object(v___x_1772_);
return v___x_1776_;
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_del_object(v___x_1772_);
lean_dec_ref(v_k_1770_);
v_a_1788_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1774_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1774_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_1797_; lean_object* v_args_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1827_; 
v_fvarId_1797_ = lean_ctor_get(v_code_1705_, 0);
v_args_1798_ = lean_ctor_get(v_code_1705_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_code_1705_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1800_ = v_code_1705_;
v_isShared_1801_ = v_isSharedCheck_1827_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_args_1798_);
lean_inc(v_fvarId_1797_);
lean_dec(v_code_1705_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1827_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
uint8_t v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = 1;
v___x_1803_ = lean_st_ref_get(v_a_1707_);
v___x_1804_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1803_, v_fvarId_1797_, v___x_1802_);
lean_dec(v___x_1803_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_fvarId_1805_; lean_object* v___x_1806_; 
v_fvarId_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_fvarId_1805_);
lean_dec_ref_known(v___x_1804_, 1);
v___x_1806_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1704_, v_args_1798_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1817_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1817_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1817_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 1, v_a_1807_);
lean_ctor_set(v___x_1800_, 0, v_fvarId_1805_);
v___x_1812_ = v___x_1800_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_fvarId_1805_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1814_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1812_);
v___x_1814_ = v___x_1809_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec(v_fvarId_1805_);
lean_del_object(v___x_1800_);
v_a_1818_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1806_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1806_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
else
{
lean_object* v___x_1826_; 
lean_del_object(v___x_1800_);
lean_dec_ref(v_args_1798_);
v___x_1826_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1704_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
return v___x_1826_;
}
}
}
case 4:
{
lean_object* v_cases_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1880_; 
v_cases_1828_ = lean_ctor_get(v_code_1705_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_code_1705_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1830_ = v_code_1705_;
v_isShared_1831_ = v_isSharedCheck_1880_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_cases_1828_);
lean_dec(v_code_1705_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1880_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v_typeName_1832_; lean_object* v_resultType_1833_; lean_object* v_discr_1834_; lean_object* v_alts_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1879_; 
v_typeName_1832_ = lean_ctor_get(v_cases_1828_, 0);
v_resultType_1833_ = lean_ctor_get(v_cases_1828_, 1);
v_discr_1834_ = lean_ctor_get(v_cases_1828_, 2);
v_alts_1835_ = lean_ctor_get(v_cases_1828_, 3);
v_isSharedCheck_1879_ = !lean_is_exclusive(v_cases_1828_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1837_ = v_cases_1828_;
v_isShared_1838_ = v_isSharedCheck_1879_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_alts_1835_);
lean_inc(v_discr_1834_);
lean_inc(v_resultType_1833_);
lean_inc(v_typeName_1832_);
lean_dec(v_cases_1828_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1879_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
uint8_t v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = 1;
v___x_1840_ = lean_st_ref_get(v_a_1707_);
v___x_1841_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1840_, v_discr_1834_, v___x_1839_);
lean_dec(v___x_1840_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_fvarId_1842_; lean_object* v___x_1843_; 
v_fvarId_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_fvarId_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v___x_1843_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1704_, v_resultType_1833_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; size_t v_sz_1845_; size_t v___x_1846_; lean_object* v___x_1847_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v___x_1843_, 1);
v_sz_1845_ = lean_array_size(v_alts_1835_);
v___x_1846_ = ((size_t)0ULL);
v___x_1847_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_1704_, v_sz_1845_, v___x_1846_, v_alts_1835_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1861_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1861_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1861_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 3, v_a_1848_);
lean_ctor_set(v___x_1837_, 2, v_fvarId_1842_);
lean_ctor_set(v___x_1837_, 1, v_a_1844_);
v___x_1853_ = v___x_1837_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_typeName_1832_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_a_1844_);
lean_ctor_set(v_reuseFailAlloc_1860_, 2, v_fvarId_1842_);
lean_ctor_set(v_reuseFailAlloc_1860_, 3, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1855_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1853_);
v___x_1855_ = v___x_1830_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
lean_object* v___x_1857_; 
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1855_);
v___x_1857_ = v___x_1850_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec(v_a_1844_);
lean_dec(v_fvarId_1842_);
lean_del_object(v___x_1837_);
lean_dec(v_typeName_1832_);
lean_del_object(v___x_1830_);
v_a_1862_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1847_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1847_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec(v_fvarId_1842_);
lean_del_object(v___x_1837_);
lean_dec_ref(v_alts_1835_);
lean_dec(v_typeName_1832_);
lean_del_object(v___x_1830_);
v_a_1870_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1843_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1843_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
else
{
lean_object* v___x_1878_; 
lean_del_object(v___x_1837_);
lean_dec_ref(v_alts_1835_);
lean_dec_ref(v_resultType_1833_);
lean_dec(v_typeName_1832_);
lean_del_object(v___x_1830_);
v___x_1878_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1704_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
return v___x_1878_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1900_; 
v_fvarId_1881_ = lean_ctor_get(v_code_1705_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_code_1705_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1883_ = v_code_1705_;
v_isShared_1884_ = v_isSharedCheck_1900_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_fvarId_1881_);
lean_dec(v_code_1705_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1900_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
uint8_t v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1885_ = 1;
v___x_1886_ = lean_st_ref_get(v_a_1707_);
v___x_1887_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1886_, v_fvarId_1881_, v___x_1885_);
lean_dec(v___x_1886_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_fvarId_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1898_; 
v_fvarId_1888_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1890_ = v___x_1887_;
v_isShared_1891_ = v_isSharedCheck_1898_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_fvarId_1888_);
lean_dec(v___x_1887_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1898_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v_fvarId_1888_);
v___x_1893_ = v___x_1883_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_fvarId_1888_);
v___x_1893_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
lean_object* v___x_1895_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1893_);
v___x_1895_ = v___x_1890_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
else
{
lean_object* v___x_1899_; 
lean_del_object(v___x_1883_);
v___x_1899_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1704_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
return v___x_1899_;
}
}
}
case 6:
{
lean_object* v_type_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1925_; 
v_type_1901_ = lean_ctor_get(v_code_1705_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v_code_1705_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1903_ = v_code_1705_;
v_isShared_1904_ = v_isSharedCheck_1925_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_type_1901_);
lean_dec(v_code_1705_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1925_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; 
v___x_1905_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1704_, v_type_1901_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1916_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1908_ = v___x_1905_;
v_isShared_1909_ = v_isSharedCheck_1916_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1916_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v_a_1906_);
v___x_1911_ = v___x_1903_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1913_; 
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v___x_1911_);
v___x_1913_ = v___x_1908_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_del_object(v___x_1903_);
v_a_1917_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1905_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1905_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_1926_; lean_object* v_i_1927_; lean_object* v_y_1928_; lean_object* v_k_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1952_; 
v_fvarId_1926_ = lean_ctor_get(v_code_1705_, 0);
v_i_1927_ = lean_ctor_get(v_code_1705_, 1);
v_y_1928_ = lean_ctor_get(v_code_1705_, 2);
v_k_1929_ = lean_ctor_get(v_code_1705_, 3);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_code_1705_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1931_ = v_code_1705_;
v_isShared_1932_ = v_isSharedCheck_1952_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_k_1929_);
lean_inc(v_y_1928_);
lean_inc(v_i_1927_);
lean_inc(v_fvarId_1926_);
lean_dec(v_code_1705_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1952_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
uint8_t v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = 1;
v___x_1934_ = lean_st_ref_get(v_a_1707_);
v___x_1935_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1934_, v_fvarId_1926_, v___x_1933_);
lean_dec(v___x_1934_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_fvarId_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_fvarId_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_fvarId_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v___x_1937_ = lean_st_ref_get(v_a_1707_);
v___x_1938_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1704_, v___x_1937_, v_y_1928_, v___x_1933_);
lean_dec(v___x_1937_);
v___x_1939_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1704_, v_k_1929_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1950_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1942_ = v___x_1939_;
v_isShared_1943_ = v_isSharedCheck_1950_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1939_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1950_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 3, v_a_1940_);
lean_ctor_set(v___x_1931_, 2, v___x_1938_);
lean_ctor_set(v___x_1931_, 0, v_fvarId_1936_);
v___x_1945_ = v___x_1931_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_fvarId_1936_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_i_1927_);
lean_ctor_set(v_reuseFailAlloc_1949_, 2, v___x_1938_);
lean_ctor_set(v_reuseFailAlloc_1949_, 3, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
lean_object* v___x_1947_; 
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 0, v___x_1945_);
v___x_1947_ = v___x_1942_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_dec(v___x_1938_);
lean_dec(v_fvarId_1936_);
lean_del_object(v___x_1931_);
lean_dec(v_i_1927_);
return v___x_1939_;
}
}
else
{
lean_object* v___x_1951_; 
lean_del_object(v___x_1931_);
lean_dec_ref(v_k_1929_);
lean_dec(v_y_1928_);
lean_dec(v_i_1927_);
v___x_1951_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1704_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
return v___x_1951_;
}
}
}
case 8:
{
lean_object* v_fvarId_1953_; lean_object* v_i_1954_; lean_object* v_y_1955_; lean_object* v_k_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1981_; 
v_fvarId_1953_ = lean_ctor_get(v_code_1705_, 0);
v_i_1954_ = lean_ctor_get(v_code_1705_, 1);
v_y_1955_ = lean_ctor_get(v_code_1705_, 2);
v_k_1956_ = lean_ctor_get(v_code_1705_, 3);
v_isSharedCheck_1981_ = !lean_is_exclusive(v_code_1705_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1958_ = v_code_1705_;
v_isShared_1959_ = v_isSharedCheck_1981_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_k_1956_);
lean_inc(v_y_1955_);
lean_inc(v_i_1954_);
lean_inc(v_fvarId_1953_);
lean_dec(v_code_1705_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1981_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
uint8_t v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1960_ = 1;
v___x_1961_ = lean_st_ref_get(v_a_1707_);
v___x_1962_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1961_, v_fvarId_1953_, v___x_1960_);
lean_dec(v___x_1961_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_fvarId_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v_fvarId_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_fvarId_1963_);
lean_dec_ref_known(v___x_1962_, 1);
v___x_1964_ = lean_st_ref_get(v_a_1707_);
v___x_1965_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1964_, v_y_1955_, v___x_1960_);
lean_dec(v___x_1964_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_fvarId_1966_; lean_object* v___x_1967_; 
v_fvarId_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_fvarId_1966_);
lean_dec_ref_known(v___x_1965_, 1);
v___x_1967_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1704_, v_k_1956_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1978_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1970_ = v___x_1967_;
v_isShared_1971_ = v_isSharedCheck_1978_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1967_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1978_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 3, v_a_1968_);
lean_ctor_set(v___x_1958_, 2, v_fvarId_1966_);
lean_ctor_set(v___x_1958_, 0, v_fvarId_1963_);
v___x_1973_ = v___x_1958_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_fvarId_1963_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_i_1954_);
lean_ctor_set(v_reuseFailAlloc_1977_, 2, v_fvarId_1966_);
lean_ctor_set(v_reuseFailAlloc_1977_, 3, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
lean_object* v___x_1975_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1973_);
v___x_1975_ = v___x_1970_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1973_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
else
{
lean_dec(v_fvarId_1966_);
lean_dec(v_fvarId_1963_);
lean_del_object(v___x_1958_);
lean_dec(v_i_1954_);
return v___x_1967_;
}
}
else
{
lean_object* v___x_1979_; 
lean_dec(v_fvarId_1963_);
lean_del_object(v___x_1958_);
lean_dec_ref(v_k_1956_);
lean_dec(v_i_1954_);
v___x_1979_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1704_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
return v___x_1979_;
}
}
else
{
lean_object* v___x_1980_; 
lean_del_object(v___x_1958_);
lean_dec_ref(v_k_1956_);
lean_dec(v_y_1955_);
lean_dec(v_i_1954_);
v___x_1980_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1704_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
return v___x_1980_;
}
}
}
case 9:
{
lean_object* v_fvarId_1982_; lean_object* v_i_1983_; lean_object* v_offset_1984_; lean_object* v_y_1985_; lean_object* v_ty_1986_; lean_object* v_k_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2022_; 
v_fvarId_1982_ = lean_ctor_get(v_code_1705_, 0);
v_i_1983_ = lean_ctor_get(v_code_1705_, 1);
v_offset_1984_ = lean_ctor_get(v_code_1705_, 2);
v_y_1985_ = lean_ctor_get(v_code_1705_, 3);
v_ty_1986_ = lean_ctor_get(v_code_1705_, 4);
v_k_1987_ = lean_ctor_get(v_code_1705_, 5);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_code_1705_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_1989_ = v_code_1705_;
v_isShared_1990_ = v_isSharedCheck_2022_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_k_1987_);
lean_inc(v_ty_1986_);
lean_inc(v_y_1985_);
lean_inc(v_offset_1984_);
lean_inc(v_i_1983_);
lean_inc(v_fvarId_1982_);
lean_dec(v_code_1705_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2022_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
uint8_t v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1991_ = 1;
v___x_1992_ = lean_st_ref_get(v_a_1707_);
v___x_1993_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1992_, v_fvarId_1982_, v___x_1991_);
lean_dec(v___x_1992_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_fvarId_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v_fvarId_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_fvarId_1994_);
lean_dec_ref_known(v___x_1993_, 1);
v___x_1995_ = lean_st_ref_get(v_a_1707_);
v___x_1996_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1995_, v_y_1985_, v___x_1991_);
lean_dec(v___x_1995_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_fvarId_1997_; lean_object* v___x_1998_; 
v_fvarId_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_fvarId_1997_);
lean_dec_ref_known(v___x_1996_, 1);
v___x_1998_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1704_, v_ty_1986_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2000_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
v___x_2000_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1704_, v_k_1987_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2011_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2011_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2011_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 5, v_a_2001_);
lean_ctor_set(v___x_1989_, 4, v_a_1999_);
lean_ctor_set(v___x_1989_, 3, v_fvarId_1997_);
lean_ctor_set(v___x_1989_, 0, v_fvarId_1994_);
v___x_2006_ = v___x_1989_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_fvarId_1994_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_i_1983_);
lean_ctor_set(v_reuseFailAlloc_2010_, 2, v_offset_1984_);
lean_ctor_set(v_reuseFailAlloc_2010_, 3, v_fvarId_1997_);
lean_ctor_set(v_reuseFailAlloc_2010_, 4, v_a_1999_);
lean_ctor_set(v_reuseFailAlloc_2010_, 5, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2008_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2006_);
v___x_2008_ = v___x_2003_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
else
{
lean_dec(v_a_1999_);
lean_dec(v_fvarId_1997_);
lean_dec(v_fvarId_1994_);
lean_del_object(v___x_1989_);
lean_dec(v_offset_1984_);
lean_dec(v_i_1983_);
return v___x_2000_;
}
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec(v_fvarId_1997_);
lean_dec(v_fvarId_1994_);
lean_del_object(v___x_1989_);
lean_dec_ref(v_k_1987_);
lean_dec(v_offset_1984_);
lean_dec(v_i_1983_);
v_a_2012_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_1998_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_1998_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
else
{
lean_object* v___x_2020_; 
lean_dec(v_fvarId_1994_);
lean_del_object(v___x_1989_);
lean_dec_ref(v_k_1987_);
lean_dec_ref(v_ty_1986_);
lean_dec(v_offset_1984_);
lean_dec(v_i_1983_);
v___x_2020_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1704_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
return v___x_2020_;
}
}
else
{
lean_object* v___x_2021_; 
lean_del_object(v___x_1989_);
lean_dec_ref(v_k_1987_);
lean_dec_ref(v_ty_1986_);
lean_dec(v_y_1985_);
lean_dec(v_offset_1984_);
lean_dec(v_i_1983_);
v___x_2021_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1704_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
return v___x_2021_;
}
}
}
case 10:
{
lean_object* v_fvarId_2023_; lean_object* v_cidx_2024_; lean_object* v_k_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2046_; 
v_fvarId_2023_ = lean_ctor_get(v_code_1705_, 0);
v_cidx_2024_ = lean_ctor_get(v_code_1705_, 1);
v_k_2025_ = lean_ctor_get(v_code_1705_, 2);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_code_1705_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2027_ = v_code_1705_;
v_isShared_2028_ = v_isSharedCheck_2046_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_k_2025_);
lean_inc(v_cidx_2024_);
lean_inc(v_fvarId_2023_);
lean_dec(v_code_1705_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2046_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
uint8_t v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2029_ = 1;
v___x_2030_ = lean_st_ref_get(v_a_1707_);
v___x_2031_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2030_, v_fvarId_2023_, v___x_2029_);
lean_dec(v___x_2030_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_fvarId_2032_; lean_object* v___x_2033_; 
v_fvarId_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_fvarId_2032_);
lean_dec_ref_known(v___x_2031_, 1);
v___x_2033_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1704_, v_k_2025_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2044_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2036_ = v___x_2033_;
v_isShared_2037_ = v_isSharedCheck_2044_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2033_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2044_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 2, v_a_2034_);
lean_ctor_set(v___x_2027_, 0, v_fvarId_2032_);
v___x_2039_ = v___x_2027_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_fvarId_2032_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_cidx_2024_);
lean_ctor_set(v_reuseFailAlloc_2043_, 2, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2041_; 
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2039_);
v___x_2041_ = v___x_2036_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
else
{
lean_dec(v_fvarId_2032_);
lean_del_object(v___x_2027_);
lean_dec(v_cidx_2024_);
return v___x_2033_;
}
}
else
{
lean_object* v___x_2045_; 
lean_del_object(v___x_2027_);
lean_dec_ref(v_k_2025_);
lean_dec(v_cidx_2024_);
v___x_2045_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1704_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
return v___x_2045_;
}
}
}
case 11:
{
lean_object* v_fvarId_2047_; lean_object* v_n_2048_; uint8_t v_check_2049_; uint8_t v_persistent_2050_; lean_object* v_k_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2072_; 
v_fvarId_2047_ = lean_ctor_get(v_code_1705_, 0);
v_n_2048_ = lean_ctor_get(v_code_1705_, 1);
v_check_2049_ = lean_ctor_get_uint8(v_code_1705_, sizeof(void*)*3);
v_persistent_2050_ = lean_ctor_get_uint8(v_code_1705_, sizeof(void*)*3 + 1);
v_k_2051_ = lean_ctor_get(v_code_1705_, 2);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_code_1705_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2053_ = v_code_1705_;
v_isShared_2054_ = v_isSharedCheck_2072_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_k_2051_);
lean_inc(v_n_2048_);
lean_inc(v_fvarId_2047_);
lean_dec(v_code_1705_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2072_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
uint8_t v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2055_ = 1;
v___x_2056_ = lean_st_ref_get(v_a_1707_);
v___x_2057_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2056_, v_fvarId_2047_, v___x_2055_);
lean_dec(v___x_2056_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_fvarId_2058_; lean_object* v___x_2059_; 
v_fvarId_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_fvarId_2058_);
lean_dec_ref_known(v___x_2057_, 1);
v___x_2059_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1704_, v_k_2051_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2070_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2070_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2070_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 2, v_a_2060_);
lean_ctor_set(v___x_2053_, 0, v_fvarId_2058_);
v___x_2065_ = v___x_2053_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_fvarId_2058_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_n_2048_);
lean_ctor_set(v_reuseFailAlloc_2069_, 2, v_a_2060_);
lean_ctor_set_uint8(v_reuseFailAlloc_2069_, sizeof(void*)*3, v_check_2049_);
lean_ctor_set_uint8(v_reuseFailAlloc_2069_, sizeof(void*)*3 + 1, v_persistent_2050_);
v___x_2065_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2067_; 
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v___x_2065_);
v___x_2067_ = v___x_2062_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
else
{
lean_dec(v_fvarId_2058_);
lean_del_object(v___x_2053_);
lean_dec(v_n_2048_);
return v___x_2059_;
}
}
else
{
lean_object* v___x_2071_; 
lean_del_object(v___x_2053_);
lean_dec_ref(v_k_2051_);
lean_dec(v_n_2048_);
v___x_2071_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1704_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
return v___x_2071_;
}
}
}
case 12:
{
lean_object* v_fvarId_2073_; lean_object* v_n_2074_; uint8_t v_check_2075_; uint8_t v_persistent_2076_; lean_object* v_objs_x3f_2077_; lean_object* v_k_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2099_; 
v_fvarId_2073_ = lean_ctor_get(v_code_1705_, 0);
v_n_2074_ = lean_ctor_get(v_code_1705_, 1);
v_check_2075_ = lean_ctor_get_uint8(v_code_1705_, sizeof(void*)*4);
v_persistent_2076_ = lean_ctor_get_uint8(v_code_1705_, sizeof(void*)*4 + 1);
v_objs_x3f_2077_ = lean_ctor_get(v_code_1705_, 2);
v_k_2078_ = lean_ctor_get(v_code_1705_, 3);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_code_1705_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2080_ = v_code_1705_;
v_isShared_2081_ = v_isSharedCheck_2099_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_k_2078_);
lean_inc(v_objs_x3f_2077_);
lean_inc(v_n_2074_);
lean_inc(v_fvarId_2073_);
lean_dec(v_code_1705_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2099_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
uint8_t v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2082_ = 1;
v___x_2083_ = lean_st_ref_get(v_a_1707_);
v___x_2084_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2083_, v_fvarId_2073_, v___x_2082_);
lean_dec(v___x_2083_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_fvarId_2085_; lean_object* v___x_2086_; 
v_fvarId_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_fvarId_2085_);
lean_dec_ref_known(v___x_2084_, 1);
v___x_2086_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1704_, v_k_2078_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2097_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2089_ = v___x_2086_;
v_isShared_2090_ = v_isSharedCheck_2097_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2086_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2097_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 3, v_a_2087_);
lean_ctor_set(v___x_2080_, 0, v_fvarId_2085_);
v___x_2092_ = v___x_2080_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_fvarId_2085_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_n_2074_);
lean_ctor_set(v_reuseFailAlloc_2096_, 2, v_objs_x3f_2077_);
lean_ctor_set(v_reuseFailAlloc_2096_, 3, v_a_2087_);
lean_ctor_set_uint8(v_reuseFailAlloc_2096_, sizeof(void*)*4, v_check_2075_);
lean_ctor_set_uint8(v_reuseFailAlloc_2096_, sizeof(void*)*4 + 1, v_persistent_2076_);
v___x_2092_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2094_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2092_);
v___x_2094_ = v___x_2089_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
else
{
lean_dec(v_fvarId_2085_);
lean_del_object(v___x_2080_);
lean_dec(v_objs_x3f_2077_);
lean_dec(v_n_2074_);
return v___x_2086_;
}
}
else
{
lean_object* v___x_2098_; 
lean_del_object(v___x_2080_);
lean_dec_ref(v_k_2078_);
lean_dec(v_objs_x3f_2077_);
lean_dec(v_n_2074_);
v___x_2098_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1704_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
return v___x_2098_;
}
}
}
default: 
{
lean_object* v_fvarId_2100_; lean_object* v_k_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2122_; 
v_fvarId_2100_ = lean_ctor_get(v_code_1705_, 0);
v_k_2101_ = lean_ctor_get(v_code_1705_, 1);
v_isSharedCheck_2122_ = !lean_is_exclusive(v_code_1705_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2103_ = v_code_1705_;
v_isShared_2104_ = v_isSharedCheck_2122_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_k_2101_);
lean_inc(v_fvarId_2100_);
lean_dec(v_code_1705_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2122_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
uint8_t v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2105_ = 1;
v___x_2106_ = lean_st_ref_get(v_a_1707_);
v___x_2107_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2106_, v_fvarId_2100_, v___x_2105_);
lean_dec(v___x_2106_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_fvarId_2108_; lean_object* v___x_2109_; 
v_fvarId_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_fvarId_2108_);
lean_dec_ref_known(v___x_2107_, 1);
v___x_2109_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1704_, v_k_2101_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2120_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2112_ = v___x_2109_;
v_isShared_2113_ = v_isSharedCheck_2120_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2120_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 1, v_a_2110_);
lean_ctor_set(v___x_2103_, 0, v_fvarId_2108_);
v___x_2115_ = v___x_2103_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_fvarId_2108_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
lean_object* v___x_2117_; 
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v___x_2115_);
v___x_2117_ = v___x_2112_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
else
{
lean_dec(v_fvarId_2108_);
lean_del_object(v___x_2103_);
return v___x_2109_;
}
}
else
{
lean_object* v___x_2121_; 
lean_del_object(v___x_2103_);
lean_dec_ref(v_k_2101_);
v___x_2121_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1704_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
return v___x_2121_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(uint8_t v_pu_2123_, lean_object* v_decl_2124_, uint8_t v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v_fvarId_2132_; lean_object* v_binderName_2133_; lean_object* v_params_2134_; lean_object* v_type_2135_; lean_object* v_value_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2214_; 
v_fvarId_2132_ = lean_ctor_get(v_decl_2124_, 0);
v_binderName_2133_ = lean_ctor_get(v_decl_2124_, 1);
v_params_2134_ = lean_ctor_get(v_decl_2124_, 2);
v_type_2135_ = lean_ctor_get(v_decl_2124_, 3);
v_value_2136_ = lean_ctor_get(v_decl_2124_, 4);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_decl_2124_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2138_ = v_decl_2124_;
v_isShared_2139_ = v_isSharedCheck_2214_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_value_2136_);
lean_inc(v_type_2135_);
lean_inc(v_params_2134_);
lean_inc(v_binderName_2133_);
lean_inc(v_fvarId_2132_);
lean_dec(v_decl_2124_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2214_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; 
v___x_2140_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2123_, v_type_2135_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2142_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2140_, 1);
v___x_2142_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_2133_, v_a_2125_, v_a_2128_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; size_t v_sz_2144_; size_t v___x_2145_; lean_object* v___x_2146_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
v_sz_2144_ = lean_array_size(v_params_2134_);
v___x_2145_ = ((size_t)0ULL);
v___x_2146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2123_, v_sz_2144_, v___x_2145_, v_params_2134_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2148_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
v___x_2148_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2123_, v_value_2136_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2150_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref_known(v___x_2148_, 1);
v___x_2150_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_2132_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2173_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2153_ = v___x_2150_;
v_isShared_2154_ = v_isSharedCheck_2173_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2173_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 4, v_a_2149_);
lean_ctor_set(v___x_2138_, 3, v_a_2141_);
lean_ctor_set(v___x_2138_, 2, v_a_2147_);
lean_ctor_set(v___x_2138_, 1, v_a_2143_);
lean_ctor_set(v___x_2138_, 0, v_a_2151_);
v___x_2156_ = v___x_2138_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2151_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_a_2143_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_a_2147_);
lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_a_2141_);
lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_a_2149_);
v___x_2156_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2157_; lean_object* v_lctx_2158_; lean_object* v_nextIdx_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2171_; 
v___x_2157_ = lean_st_ref_take(v_a_2128_);
v_lctx_2158_ = lean_ctor_get(v___x_2157_, 0);
v_nextIdx_2159_ = lean_ctor_get(v___x_2157_, 1);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2161_ = v___x_2157_;
v_isShared_2162_ = v_isSharedCheck_2171_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_nextIdx_2159_);
lean_inc(v_lctx_2158_);
lean_dec(v___x_2157_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2171_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; lean_object* v___x_2165_; 
lean_inc_ref(v___x_2156_);
v___x_2163_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2123_, v_lctx_2158_, v___x_2156_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v___x_2163_);
v___x_2165_ = v___x_2161_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_nextIdx_2159_);
v___x_2165_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2166_ = lean_st_ref_put(v_a_2128_, v___x_2165_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 0, v___x_2156_);
v___x_2168_ = v___x_2153_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2156_);
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
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec(v_a_2149_);
lean_dec(v_a_2147_);
lean_dec(v_a_2143_);
lean_dec(v_a_2141_);
lean_del_object(v___x_2138_);
v_a_2174_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2150_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2150_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec(v_a_2147_);
lean_dec(v_a_2143_);
lean_dec(v_a_2141_);
lean_del_object(v___x_2138_);
lean_dec(v_fvarId_2132_);
v_a_2182_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2148_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2148_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec(v_a_2143_);
lean_dec(v_a_2141_);
lean_del_object(v___x_2138_);
lean_dec_ref(v_value_2136_);
lean_dec(v_fvarId_2132_);
v_a_2190_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2146_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2146_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec(v_a_2141_);
lean_del_object(v___x_2138_);
lean_dec_ref(v_value_2136_);
lean_dec_ref(v_params_2134_);
lean_dec(v_fvarId_2132_);
v_a_2198_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2142_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2142_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_del_object(v___x_2138_);
lean_dec_ref(v_value_2136_);
lean_dec_ref(v_params_2134_);
lean_dec(v_binderName_2133_);
lean_dec(v_fvarId_2132_);
v_a_2206_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2140_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2140_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(lean_object* v_pu_2215_, lean_object* v_decl_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
uint8_t v_pu_boxed_2224_; uint8_t v_a_boxed_2225_; lean_object* v_res_2226_; 
v_pu_boxed_2224_ = lean_unbox(v_pu_2215_);
v_a_boxed_2225_ = lean_unbox(v_a_2217_);
v_res_2226_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_boxed_2224_, v_decl_2216_, v_a_boxed_2225_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2___boxed(lean_object* v_pu_2227_, lean_object* v_sz_2228_, lean_object* v_i_2229_, lean_object* v_bs_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
uint8_t v_pu_boxed_2238_; size_t v_sz_boxed_2239_; size_t v_i_boxed_2240_; uint8_t v___y_26966__boxed_2241_; lean_object* v_res_2242_; 
v_pu_boxed_2238_ = lean_unbox(v_pu_2227_);
v_sz_boxed_2239_ = lean_unbox_usize(v_sz_2228_);
lean_dec(v_sz_2228_);
v_i_boxed_2240_ = lean_unbox_usize(v_i_2229_);
lean_dec(v_i_2229_);
v___y_26966__boxed_2241_ = lean_unbox(v___y_2231_);
v_res_2242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_boxed_2238_, v_sz_boxed_2239_, v_i_boxed_2240_, v_bs_2230_, v___y_26966__boxed_2241_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(lean_object* v_pu_2243_, lean_object* v_code_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
uint8_t v_pu_boxed_2252_; uint8_t v_a_boxed_2253_; lean_object* v_res_2254_; 
v_pu_boxed_2252_ = lean_unbox(v_pu_2243_);
v_a_boxed_2253_ = lean_unbox(v_a_2245_);
v_res_2254_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_boxed_2252_, v_code_2244_, v_a_boxed_2253_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
lean_dec(v_a_2248_);
lean_dec_ref(v_a_2247_);
lean_dec(v_a_2246_);
return v_res_2254_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(lean_object* v_msg_2256_, uint8_t v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v_toApplicative_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2330_; 
v___x_2264_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
v___x_2265_ = l_StateRefT_x27_instMonad___redArg(v___x_2264_);
v_toApplicative_2266_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2330_ == 0)
{
lean_object* v_unused_2331_; 
v_unused_2331_ = lean_ctor_get(v___x_2265_, 1);
lean_dec(v_unused_2331_);
v___x_2268_ = v___x_2265_;
v_isShared_2269_ = v_isSharedCheck_2330_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_toApplicative_2266_);
lean_dec(v___x_2265_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2330_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v_toFunctor_2270_; lean_object* v_toSeq_2271_; lean_object* v_toSeqLeft_2272_; lean_object* v_toSeqRight_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2328_; 
v_toFunctor_2270_ = lean_ctor_get(v_toApplicative_2266_, 0);
v_toSeq_2271_ = lean_ctor_get(v_toApplicative_2266_, 2);
v_toSeqLeft_2272_ = lean_ctor_get(v_toApplicative_2266_, 3);
v_toSeqRight_2273_ = lean_ctor_get(v_toApplicative_2266_, 4);
v_isSharedCheck_2328_ = !lean_is_exclusive(v_toApplicative_2266_);
if (v_isSharedCheck_2328_ == 0)
{
lean_object* v_unused_2329_; 
v_unused_2329_ = lean_ctor_get(v_toApplicative_2266_, 1);
lean_dec(v_unused_2329_);
v___x_2275_ = v_toApplicative_2266_;
v_isShared_2276_ = v_isSharedCheck_2328_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_toSeqRight_2273_);
lean_inc(v_toSeqLeft_2272_);
lean_inc(v_toSeq_2271_);
lean_inc(v_toFunctor_2270_);
lean_dec(v_toApplicative_2266_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2328_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___f_2277_; lean_object* v___f_2278_; lean_object* v___f_2279_; lean_object* v___f_2280_; lean_object* v___x_2281_; lean_object* v___f_2282_; lean_object* v___f_2283_; lean_object* v___f_2284_; lean_object* v___x_2286_; 
v___f_2277_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
v___f_2278_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_2270_);
v___f_2279_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2279_, 0, v_toFunctor_2270_);
v___f_2280_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2280_, 0, v_toFunctor_2270_);
v___x_2281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___f_2279_);
lean_ctor_set(v___x_2281_, 1, v___f_2280_);
v___f_2282_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2282_, 0, v_toSeqRight_2273_);
v___f_2283_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2283_, 0, v_toSeqLeft_2272_);
v___f_2284_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2284_, 0, v_toSeq_2271_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 4, v___f_2282_);
lean_ctor_set(v___x_2275_, 3, v___f_2283_);
lean_ctor_set(v___x_2275_, 2, v___f_2284_);
lean_ctor_set(v___x_2275_, 1, v___f_2277_);
lean_ctor_set(v___x_2275_, 0, v___x_2281_);
v___x_2286_ = v___x_2275_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2281_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v___f_2277_);
lean_ctor_set(v_reuseFailAlloc_2327_, 2, v___f_2284_);
lean_ctor_set(v_reuseFailAlloc_2327_, 3, v___f_2283_);
lean_ctor_set(v_reuseFailAlloc_2327_, 4, v___f_2282_);
v___x_2286_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
lean_object* v___x_2288_; 
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 1, v___f_2278_);
lean_ctor_set(v___x_2268_, 0, v___x_2286_);
v___x_2288_ = v___x_2268_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v___f_2278_);
v___x_2288_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2289_; lean_object* v_toApplicative_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2324_; 
v___x_2289_ = l_StateRefT_x27_instMonad___redArg(v___x_2288_);
v_toApplicative_2290_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2324_ == 0)
{
lean_object* v_unused_2325_; 
v_unused_2325_ = lean_ctor_get(v___x_2289_, 1);
lean_dec(v_unused_2325_);
v___x_2292_ = v___x_2289_;
v_isShared_2293_ = v_isSharedCheck_2324_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_toApplicative_2290_);
lean_dec(v___x_2289_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2324_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v_toFunctor_2294_; lean_object* v_toSeq_2295_; lean_object* v_toSeqLeft_2296_; lean_object* v_toSeqRight_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2322_; 
v_toFunctor_2294_ = lean_ctor_get(v_toApplicative_2290_, 0);
v_toSeq_2295_ = lean_ctor_get(v_toApplicative_2290_, 2);
v_toSeqLeft_2296_ = lean_ctor_get(v_toApplicative_2290_, 3);
v_toSeqRight_2297_ = lean_ctor_get(v_toApplicative_2290_, 4);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_toApplicative_2290_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v_toApplicative_2290_, 1);
lean_dec(v_unused_2323_);
v___x_2299_ = v_toApplicative_2290_;
v_isShared_2300_ = v_isSharedCheck_2322_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_toSeqRight_2297_);
lean_inc(v_toSeqLeft_2296_);
lean_inc(v_toSeq_2295_);
lean_inc(v_toFunctor_2294_);
lean_dec(v_toApplicative_2290_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2322_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___f_2301_; lean_object* v___f_2302_; lean_object* v___f_2303_; lean_object* v___f_2304_; lean_object* v___x_2305_; lean_object* v___f_2306_; lean_object* v___f_2307_; lean_object* v___f_2308_; lean_object* v___x_2310_; 
v___f_2301_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
v___f_2302_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(v_toFunctor_2294_);
v___f_2303_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2303_, 0, v_toFunctor_2294_);
v___f_2304_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2304_, 0, v_toFunctor_2294_);
v___x_2305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___f_2303_);
lean_ctor_set(v___x_2305_, 1, v___f_2304_);
v___f_2306_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2306_, 0, v_toSeqRight_2297_);
v___f_2307_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2307_, 0, v_toSeqLeft_2296_);
v___f_2308_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2308_, 0, v_toSeq_2295_);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 4, v___f_2306_);
lean_ctor_set(v___x_2299_, 3, v___f_2307_);
lean_ctor_set(v___x_2299_, 2, v___f_2308_);
lean_ctor_set(v___x_2299_, 1, v___f_2301_);
lean_ctor_set(v___x_2299_, 0, v___x_2305_);
v___x_2310_ = v___x_2299_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v___f_2301_);
lean_ctor_set(v_reuseFailAlloc_2321_, 2, v___f_2308_);
lean_ctor_set(v_reuseFailAlloc_2321_, 3, v___f_2307_);
lean_ctor_set(v_reuseFailAlloc_2321_, 4, v___f_2306_);
v___x_2310_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2312_; 
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 1, v___f_2302_);
lean_ctor_set(v___x_2292_, 0, v___x_2310_);
v___x_2312_ = v___x_2292_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2310_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v___f_2302_);
v___x_2312_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___f_2316_; lean_object* v___x_10948__overap_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2313_ = l_StateRefT_x27_instMonad___redArg(v___x_2312_);
v___x_2314_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___closed__0);
v___x_2315_ = l_instInhabitedOfMonad___redArg(v___x_2313_, v___x_2314_);
v___f_2316_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2316_, 0, v___x_2315_);
v___x_10948__overap_2317_ = lean_panic_fn_borrowed(v___f_2316_, v_msg_2256_);
lean_dec_ref(v___f_2316_);
v___x_2318_ = lean_box(v___y_2257_);
lean_inc(v___y_2262_);
lean_inc_ref(v___y_2261_);
lean_inc(v___y_2260_);
lean_inc_ref(v___y_2259_);
lean_inc(v___y_2258_);
v___x_2319_ = lean_apply_7(v___x_10948__overap_2317_, v___x_2318_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, lean_box(0));
return v___x_2319_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___boxed(lean_object* v_msg_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
uint8_t v___y_11009__boxed_2340_; lean_object* v_res_2341_; 
v___y_11009__boxed_2340_ = lean_unbox(v___y_2333_);
v_res_2341_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v_msg_2332_, v___y_11009__boxed_2340_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(uint8_t v_pu_2342_, lean_object* v_msg_2343_, uint8_t v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v___x_2351_; 
v___x_2351_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v_msg_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___boxed(lean_object* v_pu_2352_, lean_object* v_msg_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
uint8_t v_pu_boxed_2361_; uint8_t v___y_11145__boxed_2362_; lean_object* v_res_2363_; 
v_pu_boxed_2361_ = lean_unbox(v_pu_2352_);
v___y_11145__boxed_2362_ = lean_unbox(v___y_2354_);
v_res_2363_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_boxed_2361_, v_msg_2353_, v___y_11145__boxed_2362_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
return v_res_2363_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2365_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2366_ = lean_unsigned_to_nat(41u);
v___x_2367_ = lean_unsigned_to_nat(217u);
v___x_2368_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2369_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2370_ = l_mkPanicMessageWithDecl(v___x_2369_, v___x_2368_, v___x_2367_, v___x_2366_, v___x_2365_);
return v___x_2370_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2(void){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2371_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2372_ = lean_unsigned_to_nat(31u);
v___x_2373_ = lean_unsigned_to_nat(222u);
v___x_2374_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2375_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2376_ = l_mkPanicMessageWithDecl(v___x_2375_, v___x_2374_, v___x_2373_, v___x_2372_, v___x_2371_);
return v___x_2376_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2377_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2378_ = lean_unsigned_to_nat(41u);
v___x_2379_ = lean_unsigned_to_nat(221u);
v___x_2380_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2381_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2382_ = l_mkPanicMessageWithDecl(v___x_2381_, v___x_2380_, v___x_2379_, v___x_2378_, v___x_2377_);
return v___x_2382_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4(void){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2383_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2384_ = lean_unsigned_to_nat(31u);
v___x_2385_ = lean_unsigned_to_nat(226u);
v___x_2386_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2387_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2388_ = l_mkPanicMessageWithDecl(v___x_2387_, v___x_2386_, v___x_2385_, v___x_2384_, v___x_2383_);
return v___x_2388_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5(void){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2389_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2390_ = lean_unsigned_to_nat(41u);
v___x_2391_ = lean_unsigned_to_nat(225u);
v___x_2392_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2393_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2394_ = l_mkPanicMessageWithDecl(v___x_2393_, v___x_2392_, v___x_2391_, v___x_2390_, v___x_2389_);
return v___x_2394_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6(void){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2395_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2396_ = lean_unsigned_to_nat(41u);
v___x_2397_ = lean_unsigned_to_nat(230u);
v___x_2398_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2399_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2400_ = l_mkPanicMessageWithDecl(v___x_2399_, v___x_2398_, v___x_2397_, v___x_2396_, v___x_2395_);
return v___x_2400_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7(void){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2401_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2402_ = lean_unsigned_to_nat(41u);
v___x_2403_ = lean_unsigned_to_nat(233u);
v___x_2404_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2405_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2406_ = l_mkPanicMessageWithDecl(v___x_2405_, v___x_2404_, v___x_2403_, v___x_2402_, v___x_2401_);
return v___x_2406_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8(void){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2407_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2408_ = lean_unsigned_to_nat(41u);
v___x_2409_ = lean_unsigned_to_nat(236u);
v___x_2410_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2411_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2412_ = l_mkPanicMessageWithDecl(v___x_2411_, v___x_2410_, v___x_2409_, v___x_2408_, v___x_2407_);
return v___x_2412_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2413_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2414_ = lean_unsigned_to_nat(41u);
v___x_2415_ = lean_unsigned_to_nat(239u);
v___x_2416_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2417_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2418_ = l_mkPanicMessageWithDecl(v___x_2417_, v___x_2416_, v___x_2415_, v___x_2414_, v___x_2413_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t v_pu_2419_, lean_object* v_decl_2420_, uint8_t v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_){
_start:
{
switch(lean_obj_tag(v_decl_2420_))
{
case 0:
{
lean_object* v_decl_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2452_; 
v_decl_2428_ = lean_ctor_get(v_decl_2420_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v_decl_2420_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2430_ = v_decl_2420_;
v_isShared_2431_ = v_isSharedCheck_2452_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_decl_2428_);
lean_dec(v_decl_2420_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2452_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_2419_, v_decl_2428_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2443_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2435_ = v___x_2432_;
v_isShared_2436_ = v_isSharedCheck_2443_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2432_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2443_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 0, v_a_2433_);
v___x_2438_ = v___x_2430_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
lean_object* v___x_2440_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v___x_2438_);
v___x_2440_ = v___x_2435_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_del_object(v___x_2430_);
v_a_2444_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2432_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2432_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2477_; 
v_decl_2453_ = lean_ctor_get(v_decl_2420_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_decl_2420_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2455_ = v_decl_2420_;
v_isShared_2456_ = v_isSharedCheck_2477_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_decl_2453_);
lean_dec(v_decl_2420_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2477_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2457_; 
v___x_2457_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2419_, v_decl_2453_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2468_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2460_ = v___x_2457_;
v_isShared_2461_ = v_isSharedCheck_2468_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2457_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2468_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v_a_2458_);
v___x_2463_ = v___x_2455_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
lean_object* v___x_2465_; 
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v___x_2463_);
v___x_2465_ = v___x_2460_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_del_object(v___x_2455_);
v_a_2469_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2457_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2457_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
case 2:
{
lean_object* v_decl_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2502_; 
v_decl_2478_ = lean_ctor_get(v_decl_2420_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_decl_2420_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2480_ = v_decl_2420_;
v_isShared_2481_ = v_isSharedCheck_2502_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_decl_2478_);
lean_dec(v_decl_2420_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2502_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2419_, v_decl_2478_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2493_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2485_ = v___x_2482_;
v_isShared_2486_ = v_isSharedCheck_2493_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2493_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v_a_2483_);
v___x_2488_ = v___x_2480_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2490_; 
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2488_);
v___x_2490_ = v___x_2485_;
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
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_del_object(v___x_2480_);
v_a_2494_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2482_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2482_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_2503_; lean_object* v_i_2504_; lean_object* v_y_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2527_; 
v_fvarId_2503_ = lean_ctor_get(v_decl_2420_, 0);
v_i_2504_ = lean_ctor_get(v_decl_2420_, 1);
v_y_2505_ = lean_ctor_get(v_decl_2420_, 2);
v_isSharedCheck_2527_ = !lean_is_exclusive(v_decl_2420_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2507_ = v_decl_2420_;
v_isShared_2508_ = v_isSharedCheck_2527_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_y_2505_);
lean_inc(v_i_2504_);
lean_inc(v_fvarId_2503_);
lean_dec(v_decl_2420_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2527_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
uint8_t v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2509_ = 1;
v___x_2510_ = lean_st_ref_get(v_a_2422_);
v___x_2511_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2510_, v_fvarId_2503_, v___x_2509_);
lean_dec(v___x_2510_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_fvarId_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2524_; 
v_fvarId_2512_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2514_ = v___x_2511_;
v_isShared_2515_ = v_isSharedCheck_2524_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_fvarId_2512_);
lean_dec(v___x_2511_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2524_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2516_ = lean_st_ref_get(v_a_2422_);
v___x_2517_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2419_, v___x_2516_, v_y_2505_, v___x_2509_);
lean_dec(v___x_2516_);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 2, v___x_2517_);
lean_ctor_set(v___x_2507_, 0, v_fvarId_2512_);
v___x_2519_ = v___x_2507_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_fvarId_2512_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v_i_2504_);
lean_ctor_set(v_reuseFailAlloc_2523_, 2, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
lean_object* v___x_2521_; 
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v___x_2519_);
v___x_2521_ = v___x_2514_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
else
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
lean_dec(v___x_2511_);
lean_del_object(v___x_2507_);
lean_dec(v_y_2505_);
lean_dec(v_i_2504_);
v___x_2525_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1);
v___x_2526_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2525_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
return v___x_2526_;
}
}
}
case 4:
{
lean_object* v_fvarId_2528_; lean_object* v_i_2529_; lean_object* v_y_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2555_; 
v_fvarId_2528_ = lean_ctor_get(v_decl_2420_, 0);
v_i_2529_ = lean_ctor_get(v_decl_2420_, 1);
v_y_2530_ = lean_ctor_get(v_decl_2420_, 2);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_decl_2420_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2532_ = v_decl_2420_;
v_isShared_2533_ = v_isSharedCheck_2555_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_y_2530_);
lean_inc(v_i_2529_);
lean_inc(v_fvarId_2528_);
lean_dec(v_decl_2420_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2555_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
uint8_t v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = 1;
v___x_2535_ = lean_st_ref_get(v_a_2422_);
v___x_2536_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2535_, v_fvarId_2528_, v___x_2534_);
lean_dec(v___x_2535_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_fvarId_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v_fvarId_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_fvarId_2537_);
lean_dec_ref_known(v___x_2536_, 1);
v___x_2538_ = lean_st_ref_get(v_a_2422_);
v___x_2539_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2538_, v_y_2530_, v___x_2534_);
lean_dec(v___x_2538_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_fvarId_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2550_; 
v_fvarId_2540_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2542_ = v___x_2539_;
v_isShared_2543_ = v_isSharedCheck_2550_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_fvarId_2540_);
lean_dec(v___x_2539_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2550_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 2, v_fvarId_2540_);
lean_ctor_set(v___x_2532_, 0, v_fvarId_2537_);
v___x_2545_ = v___x_2532_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_fvarId_2537_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v_i_2529_);
lean_ctor_set(v_reuseFailAlloc_2549_, 2, v_fvarId_2540_);
v___x_2545_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2547_; 
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 0, v___x_2545_);
v___x_2547_ = v___x_2542_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2545_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
else
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
lean_dec(v___x_2539_);
lean_dec(v_fvarId_2537_);
lean_del_object(v___x_2532_);
lean_dec(v_i_2529_);
v___x_2551_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2);
v___x_2552_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2551_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
return v___x_2552_;
}
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
lean_dec(v___x_2536_);
lean_del_object(v___x_2532_);
lean_dec(v_y_2530_);
lean_dec(v_i_2529_);
v___x_2553_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3);
v___x_2554_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2553_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
return v___x_2554_;
}
}
}
case 5:
{
lean_object* v_fvarId_2556_; lean_object* v_i_2557_; lean_object* v_offset_2558_; lean_object* v_y_2559_; lean_object* v_ty_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2587_; 
v_fvarId_2556_ = lean_ctor_get(v_decl_2420_, 0);
v_i_2557_ = lean_ctor_get(v_decl_2420_, 1);
v_offset_2558_ = lean_ctor_get(v_decl_2420_, 2);
v_y_2559_ = lean_ctor_get(v_decl_2420_, 3);
v_ty_2560_ = lean_ctor_get(v_decl_2420_, 4);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_decl_2420_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2562_ = v_decl_2420_;
v_isShared_2563_ = v_isSharedCheck_2587_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_ty_2560_);
lean_inc(v_y_2559_);
lean_inc(v_offset_2558_);
lean_inc(v_i_2557_);
lean_inc(v_fvarId_2556_);
lean_dec(v_decl_2420_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2587_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
uint8_t v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2564_ = 1;
v___x_2565_ = lean_st_ref_get(v_a_2422_);
v___x_2566_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2565_, v_fvarId_2556_, v___x_2564_);
lean_dec(v___x_2565_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_fvarId_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v_fvarId_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_fvarId_2567_);
lean_dec_ref_known(v___x_2566_, 1);
v___x_2568_ = lean_st_ref_get(v_a_2422_);
v___x_2569_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2568_, v_y_2559_, v___x_2564_);
lean_dec(v___x_2568_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_fvarId_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2582_; 
v_fvarId_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2582_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_fvarId_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2582_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2574_ = lean_st_ref_get(v_a_2422_);
v___x_2575_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2419_, v___x_2574_, v___x_2564_, v_ty_2560_);
lean_dec(v___x_2574_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 4, v___x_2575_);
lean_ctor_set(v___x_2562_, 3, v_fvarId_2570_);
lean_ctor_set(v___x_2562_, 0, v_fvarId_2567_);
v___x_2577_ = v___x_2562_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_fvarId_2567_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_i_2557_);
lean_ctor_set(v_reuseFailAlloc_2581_, 2, v_offset_2558_);
lean_ctor_set(v_reuseFailAlloc_2581_, 3, v_fvarId_2570_);
lean_ctor_set(v_reuseFailAlloc_2581_, 4, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2579_; 
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___x_2577_);
v___x_2579_ = v___x_2572_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
else
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
lean_dec(v___x_2569_);
lean_dec(v_fvarId_2567_);
lean_del_object(v___x_2562_);
lean_dec_ref(v_ty_2560_);
lean_dec(v_offset_2558_);
lean_dec(v_i_2557_);
v___x_2583_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4);
v___x_2584_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2583_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
return v___x_2584_;
}
}
else
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
lean_dec(v___x_2566_);
lean_del_object(v___x_2562_);
lean_dec_ref(v_ty_2560_);
lean_dec(v_y_2559_);
lean_dec(v_offset_2558_);
lean_dec(v_i_2557_);
v___x_2585_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5);
v___x_2586_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2585_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
return v___x_2586_;
}
}
}
case 6:
{
lean_object* v_fvarId_2588_; lean_object* v_cidx_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2609_; 
v_fvarId_2588_ = lean_ctor_get(v_decl_2420_, 0);
v_cidx_2589_ = lean_ctor_get(v_decl_2420_, 1);
v_isSharedCheck_2609_ = !lean_is_exclusive(v_decl_2420_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2591_ = v_decl_2420_;
v_isShared_2592_ = v_isSharedCheck_2609_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_cidx_2589_);
lean_inc(v_fvarId_2588_);
lean_dec(v_decl_2420_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2609_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
uint8_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = 1;
v___x_2594_ = lean_st_ref_get(v_a_2422_);
v___x_2595_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2594_, v_fvarId_2588_, v___x_2593_);
lean_dec(v___x_2594_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_fvarId_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2606_; 
v_fvarId_2596_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2598_ = v___x_2595_;
v_isShared_2599_ = v_isSharedCheck_2606_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_fvarId_2596_);
lean_dec(v___x_2595_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2606_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v_fvarId_2596_);
v___x_2601_ = v___x_2591_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_fvarId_2596_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v_cidx_2589_);
v___x_2601_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2603_; 
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2601_);
v___x_2603_ = v___x_2598_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
else
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
lean_dec(v___x_2595_);
lean_del_object(v___x_2591_);
lean_dec(v_cidx_2589_);
v___x_2607_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6);
v___x_2608_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2607_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
return v___x_2608_;
}
}
}
case 7:
{
lean_object* v_fvarId_2610_; lean_object* v_n_2611_; uint8_t v_check_2612_; uint8_t v_persistent_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2633_; 
v_fvarId_2610_ = lean_ctor_get(v_decl_2420_, 0);
v_n_2611_ = lean_ctor_get(v_decl_2420_, 1);
v_check_2612_ = lean_ctor_get_uint8(v_decl_2420_, sizeof(void*)*2);
v_persistent_2613_ = lean_ctor_get_uint8(v_decl_2420_, sizeof(void*)*2 + 1);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_decl_2420_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2615_ = v_decl_2420_;
v_isShared_2616_ = v_isSharedCheck_2633_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_n_2611_);
lean_inc(v_fvarId_2610_);
lean_dec(v_decl_2420_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2633_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
uint8_t v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = 1;
v___x_2618_ = lean_st_ref_get(v_a_2422_);
v___x_2619_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2618_, v_fvarId_2610_, v___x_2617_);
lean_dec(v___x_2618_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_fvarId_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2630_; 
v_fvarId_2620_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2622_ = v___x_2619_;
v_isShared_2623_ = v_isSharedCheck_2630_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_fvarId_2620_);
lean_dec(v___x_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2630_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v_fvarId_2620_);
v___x_2625_ = v___x_2615_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_fvarId_2620_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v_n_2611_);
lean_ctor_set_uint8(v_reuseFailAlloc_2629_, sizeof(void*)*2, v_check_2612_);
lean_ctor_set_uint8(v_reuseFailAlloc_2629_, sizeof(void*)*2 + 1, v_persistent_2613_);
v___x_2625_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
lean_object* v___x_2627_; 
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___x_2625_);
v___x_2627_ = v___x_2622_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
else
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_dec(v___x_2619_);
lean_del_object(v___x_2615_);
lean_dec(v_n_2611_);
v___x_2631_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7);
v___x_2632_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2631_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
return v___x_2632_;
}
}
}
case 8:
{
lean_object* v_fvarId_2634_; lean_object* v_n_2635_; uint8_t v_check_2636_; uint8_t v_persistent_2637_; lean_object* v_objs_x3f_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2658_; 
v_fvarId_2634_ = lean_ctor_get(v_decl_2420_, 0);
v_n_2635_ = lean_ctor_get(v_decl_2420_, 1);
v_check_2636_ = lean_ctor_get_uint8(v_decl_2420_, sizeof(void*)*3);
v_persistent_2637_ = lean_ctor_get_uint8(v_decl_2420_, sizeof(void*)*3 + 1);
v_objs_x3f_2638_ = lean_ctor_get(v_decl_2420_, 2);
v_isSharedCheck_2658_ = !lean_is_exclusive(v_decl_2420_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2640_ = v_decl_2420_;
v_isShared_2641_ = v_isSharedCheck_2658_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_objs_x3f_2638_);
lean_inc(v_n_2635_);
lean_inc(v_fvarId_2634_);
lean_dec(v_decl_2420_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2658_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
uint8_t v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2642_ = 1;
v___x_2643_ = lean_st_ref_get(v_a_2422_);
v___x_2644_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2643_, v_fvarId_2634_, v___x_2642_);
lean_dec(v___x_2643_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_fvarId_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2655_; 
v_fvarId_2645_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2647_ = v___x_2644_;
v_isShared_2648_ = v_isSharedCheck_2655_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_fvarId_2645_);
lean_dec(v___x_2644_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2655_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 0, v_fvarId_2645_);
v___x_2650_ = v___x_2640_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(8, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_fvarId_2645_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v_n_2635_);
lean_ctor_set(v_reuseFailAlloc_2654_, 2, v_objs_x3f_2638_);
lean_ctor_set_uint8(v_reuseFailAlloc_2654_, sizeof(void*)*3, v_check_2636_);
lean_ctor_set_uint8(v_reuseFailAlloc_2654_, sizeof(void*)*3 + 1, v_persistent_2637_);
v___x_2650_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2652_; 
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v___x_2650_);
v___x_2652_ = v___x_2647_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2650_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_dec(v___x_2644_);
lean_del_object(v___x_2640_);
lean_dec(v_objs_x3f_2638_);
lean_dec(v_n_2635_);
v___x_2656_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8);
v___x_2657_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2656_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
return v___x_2657_;
}
}
}
default: 
{
lean_object* v_fvarId_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2679_; 
v_fvarId_2659_ = lean_ctor_get(v_decl_2420_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_decl_2420_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2661_ = v_decl_2420_;
v_isShared_2662_ = v_isSharedCheck_2679_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_fvarId_2659_);
lean_dec(v_decl_2420_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2679_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
uint8_t v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2663_ = 1;
v___x_2664_ = lean_st_ref_get(v_a_2422_);
v___x_2665_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2664_, v_fvarId_2659_, v___x_2663_);
lean_dec(v___x_2664_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_fvarId_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2676_; 
v_fvarId_2666_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2668_ = v___x_2665_;
v_isShared_2669_ = v_isSharedCheck_2676_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_fvarId_2666_);
lean_dec(v___x_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2676_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v_fvarId_2666_);
v___x_2671_ = v___x_2661_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_fvarId_2666_);
v___x_2671_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
lean_object* v___x_2673_; 
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2671_);
v___x_2673_ = v___x_2668_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
else
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
lean_dec(v___x_2665_);
lean_del_object(v___x_2661_);
v___x_2677_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9);
v___x_2678_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2677_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
return v___x_2678_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(lean_object* v_pu_2680_, lean_object* v_decl_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_){
_start:
{
uint8_t v_pu_boxed_2689_; uint8_t v_a_boxed_2690_; lean_object* v_res_2691_; 
v_pu_boxed_2689_ = lean_unbox(v_pu_2680_);
v_a_boxed_2690_ = lean_unbox(v_a_2682_);
v_res_2691_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v_pu_boxed_2689_, v_decl_2681_, v_a_boxed_2690_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t v_pu_2692_, lean_object* v_code_2693_, lean_object* v_s_2694_, uint8_t v_uniqueIdents_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = lean_st_mk_ref(v_s_2694_);
v___x_2702_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2692_, v_code_2693_, v_uniqueIdents_2695_, v___x_2701_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2711_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2705_ = v___x_2702_;
v_isShared_2706_ = v_isSharedCheck_2711_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2702_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2711_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2707_; lean_object* v___x_2709_; 
v___x_2707_ = lean_st_ref_get(v___x_2701_);
lean_dec(v___x_2701_);
lean_dec(v___x_2707_);
if (v_isShared_2706_ == 0)
{
v___x_2709_ = v___x_2705_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2703_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
else
{
lean_dec(v___x_2701_);
return v___x_2702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize___boxed(lean_object* v_pu_2712_, lean_object* v_code_2713_, lean_object* v_s_2714_, lean_object* v_uniqueIdents_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
uint8_t v_pu_boxed_2721_; uint8_t v_uniqueIdents_boxed_2722_; lean_object* v_res_2723_; 
v_pu_boxed_2721_ = lean_unbox(v_pu_2712_);
v_uniqueIdents_boxed_2722_ = lean_unbox(v_uniqueIdents_2715_);
v_res_2723_ = l_Lean_Compiler_LCNF_Code_internalize(v_pu_boxed_2721_, v_code_2713_, v_s_2714_, v_uniqueIdents_boxed_2722_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(lean_object* v_f_2724_, lean_object* v_v_2725_, uint8_t v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
if (lean_obj_tag(v_v_2725_) == 0)
{
lean_object* v_code_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2758_; 
v_code_2733_ = lean_ctor_get(v_v_2725_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v_v_2725_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2735_ = v_v_2725_;
v_isShared_2736_ = v_isSharedCheck_2758_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_code_2733_);
lean_dec(v_v_2725_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2758_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = lean_box(v___y_2726_);
lean_inc(v___y_2731_);
lean_inc_ref(v___y_2730_);
lean_inc(v___y_2729_);
lean_inc_ref(v___y_2728_);
lean_inc(v___y_2727_);
v___x_2738_ = lean_apply_8(v_f_2724_, v_code_2733_, v___x_2737_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, lean_box(0));
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2749_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2741_ = v___x_2738_;
v_isShared_2742_ = v_isSharedCheck_2749_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2738_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2749_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v_a_2739_);
v___x_2744_ = v___x_2735_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
lean_object* v___x_2746_; 
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v___x_2744_);
v___x_2746_ = v___x_2741_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2744_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
lean_del_object(v___x_2735_);
v_a_2750_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___x_2738_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2738_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
}
else
{
lean_object* v___x_2759_; 
lean_dec_ref(v_f_2724_);
v___x_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2759_, 0, v_v_2725_);
return v___x_2759_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg___boxed(lean_object* v_f_2760_, lean_object* v_v_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
uint8_t v___y_1412__boxed_2769_; lean_object* v_res_2770_; 
v___y_1412__boxed_2769_ = lean_unbox(v___y_2762_);
v_res_2770_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2760_, v_v_2761_, v___y_1412__boxed_2769_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(uint8_t v_pu_2771_, lean_object* v_f_2772_, lean_object* v_v_2773_, uint8_t v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2772_, v_v_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___boxed(lean_object* v_pu_2782_, lean_object* v_f_2783_, lean_object* v_v_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
uint8_t v_pu_boxed_2792_; uint8_t v___y_1488__boxed_2793_; lean_object* v_res_2794_; 
v_pu_boxed_2792_ = lean_unbox(v_pu_2782_);
v___y_1488__boxed_2793_ = lean_unbox(v___y_2785_);
v_res_2794_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(v_pu_boxed_2792_, v_f_2783_, v_v_2784_, v___y_1488__boxed_2793_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(uint8_t v_pu_2795_, lean_object* v_decl_2796_, uint8_t v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_){
_start:
{
lean_object* v_toSignature_2804_; lean_object* v_value_2805_; uint8_t v_recursive_2806_; lean_object* v_inlineAttr_x3f_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2867_; 
v_toSignature_2804_ = lean_ctor_get(v_decl_2796_, 0);
v_value_2805_ = lean_ctor_get(v_decl_2796_, 1);
v_recursive_2806_ = lean_ctor_get_uint8(v_decl_2796_, sizeof(void*)*3);
v_inlineAttr_x3f_2807_ = lean_ctor_get(v_decl_2796_, 2);
v_isSharedCheck_2867_ = !lean_is_exclusive(v_decl_2796_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2809_ = v_decl_2796_;
v_isShared_2810_ = v_isSharedCheck_2867_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_inlineAttr_x3f_2807_);
lean_inc(v_value_2805_);
lean_inc(v_toSignature_2804_);
lean_dec(v_decl_2796_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2867_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v_name_2811_; lean_object* v_levelParams_2812_; lean_object* v_type_2813_; lean_object* v_params_2814_; uint8_t v_safe_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2866_; 
v_name_2811_ = lean_ctor_get(v_toSignature_2804_, 0);
v_levelParams_2812_ = lean_ctor_get(v_toSignature_2804_, 1);
v_type_2813_ = lean_ctor_get(v_toSignature_2804_, 2);
v_params_2814_ = lean_ctor_get(v_toSignature_2804_, 3);
v_safe_2815_ = lean_ctor_get_uint8(v_toSignature_2804_, sizeof(void*)*4);
v_isSharedCheck_2866_ = !lean_is_exclusive(v_toSignature_2804_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2817_ = v_toSignature_2804_;
v_isShared_2818_ = v_isSharedCheck_2866_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_params_2814_);
lean_inc(v_type_2813_);
lean_inc(v_levelParams_2812_);
lean_inc(v_name_2811_);
lean_dec(v_toSignature_2804_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2866_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; 
v___x_2819_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2795_, v_type_2813_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; size_t v_sz_2821_; size_t v___x_2822_; lean_object* v___x_2823_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref_known(v___x_2819_, 1);
v_sz_2821_ = lean_array_size(v_params_2814_);
v___x_2822_ = ((size_t)0ULL);
v___x_2823_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2795_, v_sz_2821_, v___x_2822_, v_params_2814_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2823_, 1);
v___x_2825_ = lean_box(v_pu_2795_);
v___x_2826_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed), 9, 1);
lean_closure_set(v___x_2826_, 0, v___x_2825_);
v___x_2827_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v___x_2826_, v_value_2805_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2841_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2830_ = v___x_2827_;
v_isShared_2831_ = v_isSharedCheck_2841_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2827_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2841_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 3, v_a_2824_);
lean_ctor_set(v___x_2817_, 2, v_a_2820_);
v___x_2833_ = v___x_2817_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_name_2811_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_levelParams_2812_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_a_2820_);
lean_ctor_set(v_reuseFailAlloc_2840_, 3, v_a_2824_);
lean_ctor_set_uint8(v_reuseFailAlloc_2840_, sizeof(void*)*4, v_safe_2815_);
v___x_2833_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
lean_object* v___x_2835_; 
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 1, v_a_2828_);
lean_ctor_set(v___x_2809_, 0, v___x_2833_);
v___x_2835_ = v___x_2809_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_a_2828_);
lean_ctor_set(v_reuseFailAlloc_2839_, 2, v_inlineAttr_x3f_2807_);
lean_ctor_set_uint8(v_reuseFailAlloc_2839_, sizeof(void*)*3, v_recursive_2806_);
v___x_2835_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
lean_object* v___x_2837_; 
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 0, v___x_2835_);
v___x_2837_ = v___x_2830_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v___x_2835_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_dec(v_a_2824_);
lean_dec(v_a_2820_);
lean_del_object(v___x_2817_);
lean_dec(v_levelParams_2812_);
lean_dec(v_name_2811_);
lean_del_object(v___x_2809_);
lean_dec(v_inlineAttr_x3f_2807_);
v_a_2842_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2827_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2827_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_dec(v_a_2820_);
lean_del_object(v___x_2817_);
lean_dec(v_levelParams_2812_);
lean_dec(v_name_2811_);
lean_del_object(v___x_2809_);
lean_dec(v_inlineAttr_x3f_2807_);
lean_dec_ref(v_value_2805_);
v_a_2850_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2823_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2823_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_del_object(v___x_2817_);
lean_dec_ref(v_params_2814_);
lean_dec(v_levelParams_2812_);
lean_dec(v_name_2811_);
lean_del_object(v___x_2809_);
lean_dec(v_inlineAttr_x3f_2807_);
lean_dec_ref(v_value_2805_);
v_a_2858_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2819_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2819_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go___boxed(lean_object* v_pu_2868_, lean_object* v_decl_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_){
_start:
{
uint8_t v_pu_boxed_2877_; uint8_t v_a_boxed_2878_; lean_object* v_res_2879_; 
v_pu_boxed_2877_ = lean_unbox(v_pu_2868_);
v_a_boxed_2878_ = lean_unbox(v_a_2870_);
v_res_2879_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_boxed_2877_, v_decl_2869_, v_a_boxed_2878_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
lean_dec(v_a_2875_);
lean_dec_ref(v_a_2874_);
lean_dec(v_a_2873_);
lean_dec_ref(v_a_2872_);
lean_dec(v_a_2871_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t v_pu_2880_, lean_object* v_decl_2881_, lean_object* v_s_2882_, uint8_t v_uniqueIdents_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_st_mk_ref(v_s_2882_);
v___x_2890_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_2880_, v_decl_2881_, v_uniqueIdents_2883_, v___x_2889_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2899_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2893_ = v___x_2890_;
v_isShared_2894_ = v_isSharedCheck_2899_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2890_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2899_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2895_ = lean_st_ref_get(v___x_2889_);
lean_dec(v___x_2889_);
lean_dec(v___x_2895_);
if (v_isShared_2894_ == 0)
{
v___x_2897_ = v___x_2893_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2891_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
else
{
lean_dec(v___x_2889_);
return v___x_2890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize___boxed(lean_object* v_pu_2900_, lean_object* v_decl_2901_, lean_object* v_s_2902_, lean_object* v_uniqueIdents_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_){
_start:
{
uint8_t v_pu_boxed_2909_; uint8_t v_uniqueIdents_boxed_2910_; lean_object* v_res_2911_; 
v_pu_boxed_2909_ = lean_unbox(v_pu_2900_);
v_uniqueIdents_boxed_2910_ = lean_unbox(v_uniqueIdents_2903_);
v_res_2911_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_boxed_2909_, v_decl_2901_, v_s_2902_, v_uniqueIdents_boxed_2910_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec(v_a_2905_);
lean_dec_ref(v_a_2904_);
return v_res_2911_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2912_ = lean_box(0);
v___x_2913_ = lean_unsigned_to_nat(16u);
v___x_2914_ = lean_mk_array(v___x_2913_, v___x_2912_);
return v___x_2914_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2915_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0);
v___x_2916_ = lean_unsigned_to_nat(0u);
v___x_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2916_);
lean_ctor_set(v___x_2917_, 1, v___x_2915_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(uint8_t v_pu_2918_, size_t v_sz_2919_, size_t v_i_2920_, lean_object* v_bs_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
uint8_t v___x_2927_; 
v___x_2927_ = lean_usize_dec_lt(v_i_2920_, v_sz_2919_);
if (v___x_2927_ == 0)
{
lean_object* v___x_2928_; 
v___x_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2928_, 0, v_bs_2921_);
return v___x_2928_;
}
else
{
lean_object* v_v_2929_; lean_object* v___x_2930_; lean_object* v_bs_x27_2931_; lean_object* v___x_2932_; lean_object* v_lctx_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2958_; 
v_v_2929_ = lean_array_uget(v_bs_2921_, v_i_2920_);
v___x_2930_ = lean_unsigned_to_nat(0u);
v_bs_x27_2931_ = lean_array_uset(v_bs_2921_, v_i_2920_, v___x_2930_);
v___x_2932_ = lean_st_ref_take(v___y_2923_);
v_lctx_2933_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2958_ == 0)
{
lean_object* v_unused_2959_; 
v_unused_2959_ = lean_ctor_get(v___x_2932_, 1);
lean_dec(v_unused_2959_);
v___x_2935_ = v___x_2932_;
v_isShared_2936_ = v_isSharedCheck_2958_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_lctx_2933_);
lean_dec(v___x_2932_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2958_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2937_; lean_object* v___x_2939_; 
v___x_2937_ = lean_unsigned_to_nat(1u);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 1, v___x_2937_);
v___x_2939_ = v___x_2935_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_lctx_2933_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v___x_2937_);
v___x_2939_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; uint8_t v___x_2942_; lean_object* v___x_2943_; 
v___x_2940_ = lean_st_ref_put(v___y_2923_, v___x_2939_);
v___x_2941_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_2942_ = 0;
v___x_2943_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_2918_, v_v_2929_, v___x_2941_, v___x_2942_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; size_t v___x_2945_; size_t v___x_2946_; lean_object* v___x_2947_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref_known(v___x_2943_, 1);
v___x_2945_ = ((size_t)1ULL);
v___x_2946_ = lean_usize_add(v_i_2920_, v___x_2945_);
v___x_2947_ = lean_array_uset(v_bs_x27_2931_, v_i_2920_, v_a_2944_);
v_i_2920_ = v___x_2946_;
v_bs_2921_ = v___x_2947_;
goto _start;
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec_ref(v_bs_x27_2931_);
v_a_2949_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2943_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2943_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___boxed(lean_object* v_pu_2960_, lean_object* v_sz_2961_, lean_object* v_i_2962_, lean_object* v_bs_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
uint8_t v_pu_boxed_2969_; size_t v_sz_boxed_2970_; size_t v_i_boxed_2971_; lean_object* v_res_2972_; 
v_pu_boxed_2969_ = lean_unbox(v_pu_2960_);
v_sz_boxed_2970_ = lean_unbox_usize(v_sz_2961_);
lean_dec(v_sz_2961_);
v_i_boxed_2971_ = lean_unbox_usize(v_i_2962_);
lean_dec(v_i_2962_);
v_res_2972_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_boxed_2969_, v_sz_boxed_2970_, v_i_boxed_2971_, v_bs_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
return v_res_2972_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__0(void){
_start:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_2974_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
lean_ctor_set(v___x_2974_, 2, v___x_2973_);
lean_ctor_set(v___x_2974_, 3, v___x_2973_);
lean_ctor_set(v___x_2974_, 4, v___x_2973_);
lean_ctor_set(v___x_2974_, 5, v___x_2973_);
return v___x_2974_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__1(void){
_start:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2975_ = lean_unsigned_to_nat(1u);
v___x_2976_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__0, &l_Lean_Compiler_LCNF_cleanup___closed__0_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__0);
v___x_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
lean_ctor_set(v___x_2977_, 1, v___x_2975_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup(uint8_t v_pu_2978_, lean_object* v_decl_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; size_t v_sz_2988_; size_t v___x_2989_; lean_object* v___x_2990_; 
v___x_2985_ = lean_st_ref_take(v_a_2981_);
lean_dec(v___x_2985_);
v___x_2986_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
v___x_2987_ = lean_st_ref_put(v_a_2981_, v___x_2986_);
v_sz_2988_ = lean_array_size(v_decl_2979_);
v___x_2989_ = ((size_t)0ULL);
v___x_2990_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_2978_, v_sz_2988_, v___x_2989_, v_decl_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup___boxed(lean_object* v_pu_2991_, lean_object* v_decl_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_){
_start:
{
uint8_t v_pu_boxed_2998_; lean_object* v_res_2999_; 
v_pu_boxed_2998_ = lean_unbox(v_pu_2991_);
v_res_2999_ = l_Lean_Compiler_LCNF_cleanup(v_pu_boxed_2998_, v_decl_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_);
lean_dec(v_a_2996_);
lean_dec_ref(v_a_2995_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(lean_object* v_a_3000_, lean_object* v_ngen_3001_, lean_object* v_a_x3f_3002_){
_start:
{
lean_object* v___x_3004_; lean_object* v_env_3005_; lean_object* v_nextMacroScope_3006_; lean_object* v_auxDeclNGen_3007_; lean_object* v_traceState_3008_; lean_object* v_cache_3009_; lean_object* v_recordedDeps_3010_; lean_object* v_messages_3011_; lean_object* v_infoState_3012_; lean_object* v_snapshotTasks_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3023_; 
v___x_3004_ = lean_st_ref_take(v_a_3000_);
v_env_3005_ = lean_ctor_get(v___x_3004_, 0);
v_nextMacroScope_3006_ = lean_ctor_get(v___x_3004_, 1);
v_auxDeclNGen_3007_ = lean_ctor_get(v___x_3004_, 3);
v_traceState_3008_ = lean_ctor_get(v___x_3004_, 4);
v_cache_3009_ = lean_ctor_get(v___x_3004_, 5);
v_recordedDeps_3010_ = lean_ctor_get(v___x_3004_, 6);
v_messages_3011_ = lean_ctor_get(v___x_3004_, 7);
v_infoState_3012_ = lean_ctor_get(v___x_3004_, 8);
v_snapshotTasks_3013_ = lean_ctor_get(v___x_3004_, 9);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3023_ == 0)
{
lean_object* v_unused_3024_; 
v_unused_3024_ = lean_ctor_get(v___x_3004_, 2);
lean_dec(v_unused_3024_);
v___x_3015_ = v___x_3004_;
v_isShared_3016_ = v_isSharedCheck_3023_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_snapshotTasks_3013_);
lean_inc(v_infoState_3012_);
lean_inc(v_messages_3011_);
lean_inc(v_recordedDeps_3010_);
lean_inc(v_cache_3009_);
lean_inc(v_traceState_3008_);
lean_inc(v_auxDeclNGen_3007_);
lean_inc(v_nextMacroScope_3006_);
lean_inc(v_env_3005_);
lean_dec(v___x_3004_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3023_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3017_; lean_object* v___x_3019_; 
v___x_3017_ = lean_box(0);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 2, v_ngen_3001_);
v___x_3019_ = v___x_3015_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_env_3005_);
lean_ctor_set(v_reuseFailAlloc_3022_, 1, v_nextMacroScope_3006_);
lean_ctor_set(v_reuseFailAlloc_3022_, 2, v_ngen_3001_);
lean_ctor_set(v_reuseFailAlloc_3022_, 3, v_auxDeclNGen_3007_);
lean_ctor_set(v_reuseFailAlloc_3022_, 4, v_traceState_3008_);
lean_ctor_set(v_reuseFailAlloc_3022_, 5, v_cache_3009_);
lean_ctor_set(v_reuseFailAlloc_3022_, 6, v_recordedDeps_3010_);
lean_ctor_set(v_reuseFailAlloc_3022_, 7, v_messages_3011_);
lean_ctor_set(v_reuseFailAlloc_3022_, 8, v_infoState_3012_);
lean_ctor_set(v_reuseFailAlloc_3022_, 9, v_snapshotTasks_3013_);
v___x_3019_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3020_ = lean_st_ref_put(v_a_3000_, v___x_3019_);
v___x_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3017_);
return v___x_3021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0___boxed(lean_object* v_a_3025_, lean_object* v_ngen_3026_, lean_object* v_a_x3f_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3025_, v_ngen_3026_, v_a_x3f_3027_);
lean_dec(v_a_x3f_3027_);
lean_dec(v_a_3025_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(uint8_t v_pu_3036_, lean_object* v_decl_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v___x_3041_; lean_object* v_ngen_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v_env_3045_; lean_object* v_nextMacroScope_3046_; lean_object* v_auxDeclNGen_3047_; lean_object* v_traceState_3048_; lean_object* v_cache_3049_; lean_object* v_recordedDeps_3050_; lean_object* v_messages_3051_; lean_object* v_infoState_3052_; lean_object* v_snapshotTasks_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3097_; 
v___x_3041_ = lean_st_ref_get(v_a_3039_);
v_ngen_3042_ = lean_ctor_get(v___x_3041_, 2);
lean_inc_ref(v_ngen_3042_);
lean_dec(v___x_3041_);
v___x_3043_ = ((lean_object*)(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2));
v___x_3044_ = lean_st_ref_take(v_a_3039_);
v_env_3045_ = lean_ctor_get(v___x_3044_, 0);
v_nextMacroScope_3046_ = lean_ctor_get(v___x_3044_, 1);
v_auxDeclNGen_3047_ = lean_ctor_get(v___x_3044_, 3);
v_traceState_3048_ = lean_ctor_get(v___x_3044_, 4);
v_cache_3049_ = lean_ctor_get(v___x_3044_, 5);
v_recordedDeps_3050_ = lean_ctor_get(v___x_3044_, 6);
v_messages_3051_ = lean_ctor_get(v___x_3044_, 7);
v_infoState_3052_ = lean_ctor_get(v___x_3044_, 8);
v_snapshotTasks_3053_ = lean_ctor_get(v___x_3044_, 9);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3097_ == 0)
{
lean_object* v_unused_3098_; 
v_unused_3098_ = lean_ctor_get(v___x_3044_, 2);
lean_dec(v_unused_3098_);
v___x_3055_ = v___x_3044_;
v_isShared_3056_ = v_isSharedCheck_3097_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_snapshotTasks_3053_);
lean_inc(v_infoState_3052_);
lean_inc(v_messages_3051_);
lean_inc(v_recordedDeps_3050_);
lean_inc(v_cache_3049_);
lean_inc(v_traceState_3048_);
lean_inc(v_auxDeclNGen_3047_);
lean_inc(v_nextMacroScope_3046_);
lean_inc(v_env_3045_);
lean_dec(v___x_3044_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3097_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 2, v___x_3043_);
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_env_3045_);
lean_ctor_set(v_reuseFailAlloc_3096_, 1, v_nextMacroScope_3046_);
lean_ctor_set(v_reuseFailAlloc_3096_, 2, v___x_3043_);
lean_ctor_set(v_reuseFailAlloc_3096_, 3, v_auxDeclNGen_3047_);
lean_ctor_set(v_reuseFailAlloc_3096_, 4, v_traceState_3048_);
lean_ctor_set(v_reuseFailAlloc_3096_, 5, v_cache_3049_);
lean_ctor_set(v_reuseFailAlloc_3096_, 6, v_recordedDeps_3050_);
lean_ctor_set(v_reuseFailAlloc_3096_, 7, v_messages_3051_);
lean_ctor_set(v_reuseFailAlloc_3096_, 8, v_infoState_3052_);
lean_ctor_set(v_reuseFailAlloc_3096_, 9, v_snapshotTasks_3053_);
v___x_3058_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; uint8_t v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; uint8_t v___x_3066_; lean_object* v_r_3067_; 
v___x_3059_ = lean_st_ref_put(v_a_3039_, v___x_3058_);
v___x_3060_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_3061_ = 0;
v___x_3062_ = lean_box(v_pu_3036_);
v___x_3063_ = lean_box(v___x_3061_);
v___x_3064_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_internalize___boxed), 9, 4);
lean_closure_set(v___x_3064_, 0, v___x_3062_);
lean_closure_set(v___x_3064_, 1, v_decl_3037_);
lean_closure_set(v___x_3064_, 2, v___x_3060_);
lean_closure_set(v___x_3064_, 3, v___x_3063_);
v___x_3065_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
v___x_3066_ = 0;
v_r_3067_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v___x_3064_, v___x_3065_, v___x_3066_, v_a_3038_, v_a_3039_);
if (lean_obj_tag(v_r_3067_) == 0)
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3084_; 
v_a_3068_ = lean_ctor_get(v_r_3067_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v_r_3067_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3070_ = v_r_3067_;
v_isShared_3071_ = v_isSharedCheck_3084_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v_r_3067_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3084_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
lean_inc(v_a_3068_);
if (v_isShared_3071_ == 0)
{
lean_ctor_set_tag(v___x_3070_, 1);
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
lean_object* v___x_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
v___x_3074_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3039_, v_ngen_3042_, v___x_3073_);
lean_dec_ref(v___x_3073_);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3081_ == 0)
{
lean_object* v_unused_3082_; 
v_unused_3082_ = lean_ctor_get(v___x_3074_, 0);
lean_dec(v_unused_3082_);
v___x_3076_ = v___x_3074_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_dec(v___x_3074_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 0, v_a_3068_);
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3068_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
v_a_3085_ = lean_ctor_get(v_r_3067_, 0);
lean_inc(v_a_3085_);
lean_dec_ref_known(v_r_3067_, 1);
v___x_3086_ = lean_box(0);
v___x_3087_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3039_, v_ngen_3042_, v___x_3086_);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3094_ == 0)
{
lean_object* v_unused_3095_; 
v_unused_3095_ = lean_ctor_get(v___x_3087_, 0);
lean_dec(v_unused_3095_);
v___x_3089_ = v___x_3087_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_dec(v___x_3087_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
lean_ctor_set_tag(v___x_3089_, 1);
lean_ctor_set(v___x_3089_, 0, v_a_3085_);
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3085_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___boxed(lean_object* v_pu_3099_, lean_object* v_decl_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_){
_start:
{
uint8_t v_pu_boxed_3104_; lean_object* v_res_3105_; 
v_pu_boxed_3104_ = lean_unbox(v_pu_3099_);
v_res_3105_ = l_Lean_Compiler_LCNF_normalizeFVarIds(v_pu_boxed_3104_, v_decl_3100_, v_a_3101_, v_a_3102_);
lean_dec(v_a_3102_);
lean_dec_ref(v_a_3101_);
return v_res_3105_;
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
