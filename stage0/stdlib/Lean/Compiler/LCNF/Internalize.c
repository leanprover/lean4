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
lean_object* v___x_412_; lean_object* v_ngen_413_; lean_object* v_namePrefix_414_; lean_object* v_idx_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_444_; 
v___x_412_ = lean_st_ref_get(v___y_410_);
v_ngen_413_ = lean_ctor_get(v___x_412_, 2);
lean_inc_ref(v_ngen_413_);
lean_dec(v___x_412_);
v_namePrefix_414_ = lean_ctor_get(v_ngen_413_, 0);
v_idx_415_ = lean_ctor_get(v_ngen_413_, 1);
v_isSharedCheck_444_ = !lean_is_exclusive(v_ngen_413_);
if (v_isSharedCheck_444_ == 0)
{
v___x_417_ = v_ngen_413_;
v_isShared_418_ = v_isSharedCheck_444_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_idx_415_);
lean_inc(v_namePrefix_414_);
lean_dec(v_ngen_413_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_444_;
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
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_namePrefix_414_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v___x_421_);
v___x_423_ = v_reuseFailAlloc_443_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; lean_object* v_env_425_; lean_object* v_nextMacroScope_426_; lean_object* v_auxDeclNGen_427_; lean_object* v_traceState_428_; lean_object* v_cache_429_; lean_object* v_messages_430_; lean_object* v_infoState_431_; lean_object* v_snapshotTasks_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_441_; 
v___x_424_ = lean_st_ref_take(v___y_410_);
v_env_425_ = lean_ctor_get(v___x_424_, 0);
v_nextMacroScope_426_ = lean_ctor_get(v___x_424_, 1);
v_auxDeclNGen_427_ = lean_ctor_get(v___x_424_, 3);
v_traceState_428_ = lean_ctor_get(v___x_424_, 4);
v_cache_429_ = lean_ctor_get(v___x_424_, 5);
v_messages_430_ = lean_ctor_get(v___x_424_, 6);
v_infoState_431_ = lean_ctor_get(v___x_424_, 7);
v_snapshotTasks_432_ = lean_ctor_get(v___x_424_, 8);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_441_ == 0)
{
lean_object* v_unused_442_; 
v_unused_442_ = lean_ctor_get(v___x_424_, 2);
lean_dec(v_unused_442_);
v___x_434_ = v___x_424_;
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_snapshotTasks_432_);
lean_inc(v_infoState_431_);
lean_inc(v_messages_430_);
lean_inc(v_cache_429_);
lean_inc(v_traceState_428_);
lean_inc(v_auxDeclNGen_427_);
lean_inc(v_nextMacroScope_426_);
lean_inc(v_env_425_);
lean_dec(v___x_424_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 2, v___x_423_);
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_env_425_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_nextMacroScope_426_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v_auxDeclNGen_427_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v_traceState_428_);
lean_ctor_set(v_reuseFailAlloc_440_, 5, v_cache_429_);
lean_ctor_set(v_reuseFailAlloc_440_, 6, v_messages_430_);
lean_ctor_set(v_reuseFailAlloc_440_, 7, v_infoState_431_);
lean_ctor_set(v_reuseFailAlloc_440_, 8, v_snapshotTasks_432_);
v___x_437_ = v_reuseFailAlloc_440_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_st_ref_put(v___y_410_, v___x_437_);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v_r_419_);
return v___x_439_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg___boxed(lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_445_);
lean_dec(v___y_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(uint8_t v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___x_455_; lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
v___x_455_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_453_);
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0___boxed(lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
uint8_t v___y_3111__boxed_471_; lean_object* v_res_472_; 
v___y_3111__boxed_471_ = lean_unbox(v___y_464_);
v_res_472_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(v___y_3111__boxed_471_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(lean_object* v_fvarId_473_, uint8_t v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_493_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_493_ == 0)
{
v___x_484_ = v___x_481_;
v_isShared_485_ = v_isSharedCheck_493_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_493_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_486_ = lean_st_ref_take(v_a_475_);
lean_inc(v_a_482_);
v___x_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_487_, 0, v_a_482_);
v___x_488_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v___x_486_, v_fvarId_473_, v___x_487_);
v___x_489_ = lean_st_ref_put(v_a_475_, v___x_488_);
if (v_isShared_485_ == 0)
{
v___x_491_ = v___x_484_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_482_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
else
{
lean_dec(v_fvarId_473_);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg___boxed(lean_object* v_fvarId_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
uint8_t v_a_boxed_502_; lean_object* v_res_503_; 
v_a_boxed_502_ = lean_unbox(v_a_495_);
v_res_503_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_494_, v_a_boxed_502_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec(v_a_496_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(uint8_t v_pu_504_, lean_object* v_fvarId_505_, uint8_t v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___boxed(lean_object* v_pu_514_, lean_object* v_fvarId_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
uint8_t v_pu_boxed_523_; uint8_t v_a_boxed_524_; lean_object* v_res_525_; 
v_pu_boxed_523_ = lean_unbox(v_pu_514_);
v_a_boxed_524_ = lean_unbox(v_a_516_);
v_res_525_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(v_pu_boxed_523_, v_fvarId_515_, v_a_boxed_524_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(uint8_t v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_531_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___boxed(lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
uint8_t v___y_3186__boxed_541_; lean_object* v_res_542_; 
v___y_3186__boxed_541_ = lean_unbox(v___y_534_);
v_res_542_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(v___y_3186__boxed_541_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1(lean_object* v_00_u03b2_543_, lean_object* v_m_544_, lean_object* v_a_545_, lean_object* v_b_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v_m_544_, v_a_545_, v_b_546_);
return v___x_547_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(lean_object* v_00_u03b2_548_, lean_object* v_a_549_, lean_object* v_x_550_){
_start:
{
uint8_t v___x_551_; 
v___x_551_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_a_549_, v_x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___boxed(lean_object* v_00_u03b2_552_, lean_object* v_a_553_, lean_object* v_x_554_){
_start:
{
uint8_t v_res_555_; lean_object* v_r_556_; 
v_res_555_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(v_00_u03b2_552_, v_a_553_, v_x_554_);
lean_dec(v_x_554_);
lean_dec(v_a_553_);
v_r_556_ = lean_box(v_res_555_);
return v_r_556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3(lean_object* v_00_u03b2_557_, lean_object* v_data_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(v_data_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4(lean_object* v_00_u03b2_560_, lean_object* v_a_561_, lean_object* v_b_562_, lean_object* v_x_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(v_a_561_, v_b_562_, v_x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_565_, lean_object* v_i_566_, lean_object* v_source_567_, lean_object* v_target_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(v_i_566_, v_source_567_, v_target_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_570_, lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(v_x_571_, v_x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(lean_object* v_a_574_, lean_object* v_x_575_){
_start:
{
if (lean_obj_tag(v_x_575_) == 0)
{
lean_object* v___x_576_; 
v___x_576_ = lean_box(0);
return v___x_576_;
}
else
{
lean_object* v_key_577_; lean_object* v_value_578_; lean_object* v_tail_579_; uint8_t v___x_580_; 
v_key_577_ = lean_ctor_get(v_x_575_, 0);
v_value_578_ = lean_ctor_get(v_x_575_, 1);
v_tail_579_ = lean_ctor_get(v_x_575_, 2);
v___x_580_ = l_Lean_instBEqFVarId_beq(v_key_577_, v_a_574_);
if (v___x_580_ == 0)
{
v_x_575_ = v_tail_579_;
goto _start;
}
else
{
lean_object* v___x_582_; 
lean_inc(v_value_578_);
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v_value_578_);
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_583_, lean_object* v_x_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_583_, v_x_584_);
lean_dec(v_x_584_);
lean_dec(v_a_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(lean_object* v_m_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_buckets_588_; lean_object* v___x_589_; uint64_t v___x_590_; uint64_t v___x_591_; uint64_t v___x_592_; uint64_t v_fold_593_; uint64_t v___x_594_; uint64_t v___x_595_; uint64_t v___x_596_; size_t v___x_597_; size_t v___x_598_; size_t v___x_599_; size_t v___x_600_; size_t v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_buckets_588_ = lean_ctor_get(v_m_586_, 1);
v___x_589_ = lean_array_get_size(v_buckets_588_);
v___x_590_ = l_Lean_instHashableFVarId_hash(v_a_587_);
v___x_591_ = 32ULL;
v___x_592_ = lean_uint64_shift_right(v___x_590_, v___x_591_);
v_fold_593_ = lean_uint64_xor(v___x_590_, v___x_592_);
v___x_594_ = 16ULL;
v___x_595_ = lean_uint64_shift_right(v_fold_593_, v___x_594_);
v___x_596_ = lean_uint64_xor(v_fold_593_, v___x_595_);
v___x_597_ = lean_uint64_to_usize(v___x_596_);
v___x_598_ = lean_usize_of_nat(v___x_589_);
v___x_599_ = ((size_t)1ULL);
v___x_600_ = lean_usize_sub(v___x_598_, v___x_599_);
v___x_601_ = lean_usize_land(v___x_597_, v___x_600_);
v___x_602_ = lean_array_uget_borrowed(v_buckets_588_, v___x_601_);
v___x_603_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_587_, v___x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg___boxed(lean_object* v_m_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v_m_604_, v_a_605_);
lean_dec(v_a_605_);
lean_dec_ref(v_m_604_);
return v_res_606_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_instMonadEIO___redArg();
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(lean_object* v_msg_612_, uint8_t v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_toApplicative_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_686_; 
v___x_620_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
v___x_621_ = l_StateRefT_x27_instMonad___redArg(v___x_620_);
v_toApplicative_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; 
v_unused_687_ = lean_ctor_get(v___x_621_, 1);
lean_dec(v_unused_687_);
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_686_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_toApplicative_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_686_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v_toFunctor_626_; lean_object* v_toSeq_627_; lean_object* v_toSeqLeft_628_; lean_object* v_toSeqRight_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_684_; 
v_toFunctor_626_ = lean_ctor_get(v_toApplicative_622_, 0);
v_toSeq_627_ = lean_ctor_get(v_toApplicative_622_, 2);
v_toSeqLeft_628_ = lean_ctor_get(v_toApplicative_622_, 3);
v_toSeqRight_629_ = lean_ctor_get(v_toApplicative_622_, 4);
v_isSharedCheck_684_ = !lean_is_exclusive(v_toApplicative_622_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; 
v_unused_685_ = lean_ctor_get(v_toApplicative_622_, 1);
lean_dec(v_unused_685_);
v___x_631_ = v_toApplicative_622_;
v_isShared_632_ = v_isSharedCheck_684_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_toSeqRight_629_);
lean_inc(v_toSeqLeft_628_);
lean_inc(v_toSeq_627_);
lean_inc(v_toFunctor_626_);
lean_dec(v_toApplicative_622_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_684_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___f_633_; lean_object* v___f_634_; lean_object* v___f_635_; lean_object* v___f_636_; lean_object* v___x_637_; lean_object* v___f_638_; lean_object* v___f_639_; lean_object* v___f_640_; lean_object* v___x_642_; 
v___f_633_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
v___f_634_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_626_);
v___f_635_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_635_, 0, v_toFunctor_626_);
v___f_636_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_636_, 0, v_toFunctor_626_);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v___f_635_);
lean_ctor_set(v___x_637_, 1, v___f_636_);
v___f_638_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_638_, 0, v_toSeqRight_629_);
v___f_639_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_639_, 0, v_toSeqLeft_628_);
v___f_640_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_640_, 0, v_toSeq_627_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 4, v___f_638_);
lean_ctor_set(v___x_631_, 3, v___f_639_);
lean_ctor_set(v___x_631_, 2, v___f_640_);
lean_ctor_set(v___x_631_, 1, v___f_633_);
lean_ctor_set(v___x_631_, 0, v___x_637_);
v___x_642_ = v___x_631_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v___f_633_);
lean_ctor_set(v_reuseFailAlloc_683_, 2, v___f_640_);
lean_ctor_set(v_reuseFailAlloc_683_, 3, v___f_639_);
lean_ctor_set(v_reuseFailAlloc_683_, 4, v___f_638_);
v___x_642_ = v_reuseFailAlloc_683_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_644_; 
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 1, v___f_634_);
lean_ctor_set(v___x_624_, 0, v___x_642_);
v___x_644_ = v___x_624_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v___f_634_);
v___x_644_ = v_reuseFailAlloc_682_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; lean_object* v_toApplicative_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_680_; 
v___x_645_ = l_StateRefT_x27_instMonad___redArg(v___x_644_);
v_toApplicative_646_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_680_ == 0)
{
lean_object* v_unused_681_; 
v_unused_681_ = lean_ctor_get(v___x_645_, 1);
lean_dec(v_unused_681_);
v___x_648_ = v___x_645_;
v_isShared_649_ = v_isSharedCheck_680_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_toApplicative_646_);
lean_dec(v___x_645_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_680_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v_toFunctor_650_; lean_object* v_toSeq_651_; lean_object* v_toSeqLeft_652_; lean_object* v_toSeqRight_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_678_; 
v_toFunctor_650_ = lean_ctor_get(v_toApplicative_646_, 0);
v_toSeq_651_ = lean_ctor_get(v_toApplicative_646_, 2);
v_toSeqLeft_652_ = lean_ctor_get(v_toApplicative_646_, 3);
v_toSeqRight_653_ = lean_ctor_get(v_toApplicative_646_, 4);
v_isSharedCheck_678_ = !lean_is_exclusive(v_toApplicative_646_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; 
v_unused_679_ = lean_ctor_get(v_toApplicative_646_, 1);
lean_dec(v_unused_679_);
v___x_655_ = v_toApplicative_646_;
v_isShared_656_ = v_isSharedCheck_678_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_toSeqRight_653_);
lean_inc(v_toSeqLeft_652_);
lean_inc(v_toSeq_651_);
lean_inc(v_toFunctor_650_);
lean_dec(v_toApplicative_646_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_678_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___f_657_; lean_object* v___f_658_; lean_object* v___f_659_; lean_object* v___f_660_; lean_object* v___x_661_; lean_object* v___f_662_; lean_object* v___f_663_; lean_object* v___f_664_; lean_object* v___x_666_; 
v___f_657_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
v___f_658_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(v_toFunctor_650_);
v___f_659_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_659_, 0, v_toFunctor_650_);
v___f_660_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_660_, 0, v_toFunctor_650_);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v___f_659_);
lean_ctor_set(v___x_661_, 1, v___f_660_);
v___f_662_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_662_, 0, v_toSeqRight_653_);
v___f_663_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_663_, 0, v_toSeqLeft_652_);
v___f_664_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_664_, 0, v_toSeq_651_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 4, v___f_662_);
lean_ctor_set(v___x_655_, 3, v___f_663_);
lean_ctor_set(v___x_655_, 2, v___f_664_);
lean_ctor_set(v___x_655_, 1, v___f_657_);
lean_ctor_set(v___x_655_, 0, v___x_661_);
v___x_666_ = v___x_655_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v___f_657_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v___f_664_);
lean_ctor_set(v_reuseFailAlloc_677_, 3, v___f_663_);
lean_ctor_set(v_reuseFailAlloc_677_, 4, v___f_662_);
v___x_666_ = v_reuseFailAlloc_677_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_668_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v___f_658_);
lean_ctor_set(v___x_648_, 0, v___x_666_);
v___x_668_ = v___x_648_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v___f_658_);
v___x_668_ = v_reuseFailAlloc_676_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___f_672_; lean_object* v___x_7100__overap_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_669_ = l_StateRefT_x27_instMonad___redArg(v___x_668_);
v___x_670_ = l_Lean_instInhabitedExpr;
v___x_671_ = l_instInhabitedOfMonad___redArg(v___x_669_, v___x_670_);
v___f_672_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_672_, 0, v___x_671_);
v___x_7100__overap_673_ = lean_panic_fn_borrowed(v___f_672_, v_msg_612_);
lean_dec_ref(v___f_672_);
v___x_674_ = lean_box(v___y_613_);
lean_inc(v___y_618_);
lean_inc_ref(v___y_617_);
lean_inc(v___y_616_);
lean_inc_ref(v___y_615_);
lean_inc(v___y_614_);
v___x_675_ = lean_apply_7(v___x_7100__overap_673_, v___x_674_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, lean_box(0));
return v___x_675_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___boxed(lean_object* v_msg_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
uint8_t v___y_7249__boxed_696_; lean_object* v_res_697_; 
v___y_7249__boxed_696_ = lean_unbox(v___y_689_);
v_res_697_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v_msg_688_, v___y_7249__boxed_696_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
return v_res_697_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_701_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_702_ = lean_unsigned_to_nat(20u);
v___x_703_ = lean_unsigned_to_nat(88u);
v___x_704_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__1));
v___x_705_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_706_ = l_mkPanicMessageWithDecl(v___x_705_, v___x_704_, v___x_703_, v___x_702_, v___x_701_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(uint8_t v_pu_707_, lean_object* v_e_708_, uint8_t v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
uint8_t v___x_716_; 
v___x_716_ = l_Lean_Expr_hasFVar(v_e_708_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v_e_708_);
return v___x_717_;
}
else
{
switch(lean_obj_tag(v_e_708_))
{
case 1:
{
lean_object* v_fvarId_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_fvarId_718_ = lean_ctor_get(v_e_708_, 0);
v___x_719_ = lean_st_ref_get(v_a_710_);
v___x_720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v___x_719_, v_fvarId_718_);
lean_dec(v___x_719_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v___x_721_; 
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v_e_708_);
return v___x_721_;
}
else
{
lean_object* v_val_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_767_; 
lean_dec_ref_known(v_e_708_, 1);
v_val_722_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_767_ == 0)
{
v___x_724_ = v___x_720_;
v_isShared_725_ = v_isSharedCheck_767_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_val_722_);
lean_dec(v___x_720_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_767_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
switch(lean_obj_tag(v_val_722_))
{
case 0:
{
lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_726_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_725_ == 0)
{
lean_ctor_set_tag(v___x_724_, 0);
lean_ctor_set(v___x_724_, 0, v___x_726_);
v___x_728_ = v___x_724_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
case 1:
{
lean_object* v_fvarId_730_; lean_object* v___x_731_; 
lean_del_object(v___x_724_);
v_fvarId_730_ = lean_ctor_get(v_val_722_, 0);
lean_inc(v_fvarId_730_);
lean_dec_ref_known(v_val_722_, 1);
v___x_731_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_707_, v_fvarId_730_, v_a_712_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_750_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_750_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_750_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_750_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
if (lean_obj_tag(v_a_732_) == 0)
{
lean_dec(v_fvarId_730_);
goto v___jp_736_;
}
else
{
lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_748_; 
v_isSharedCheck_748_ = !lean_is_exclusive(v_a_732_);
if (v_isSharedCheck_748_ == 0)
{
lean_object* v_unused_749_; 
v_unused_749_ = lean_ctor_get(v_a_732_, 0);
lean_dec(v_unused_749_);
v___x_742_ = v_a_732_;
v_isShared_743_ = v_isSharedCheck_748_;
goto v_resetjp_741_;
}
else
{
lean_dec(v_a_732_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_748_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
if (v___x_716_ == 0)
{
lean_del_object(v___x_742_);
lean_dec(v_fvarId_730_);
goto v___jp_736_;
}
else
{
lean_object* v___x_744_; lean_object* v___x_746_; 
lean_del_object(v___x_734_);
v___x_744_ = l_Lean_Expr_fvar___override(v_fvarId_730_);
if (v_isShared_743_ == 0)
{
lean_ctor_set_tag(v___x_742_, 0);
lean_ctor_set(v___x_742_, 0, v___x_744_);
v___x_746_ = v___x_742_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
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
v___jp_736_:
{
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v___x_737_);
v___x_739_ = v___x_734_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec(v_fvarId_730_);
v_a_751_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_731_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_731_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
default: 
{
lean_object* v_expr_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_del_object(v___x_724_);
v_expr_759_ = lean_ctor_get(v_val_722_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v_val_722_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v_val_722_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_expr_759_);
lean_dec(v_val_722_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set_tag(v___x_761_, 0);
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_expr_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_768_; lean_object* v_arg_769_; lean_object* v___x_770_; 
v_fn_768_ = lean_ctor_get(v_e_708_, 0);
v_arg_769_ = lean_ctor_get(v_e_708_, 1);
lean_inc_ref(v_fn_768_);
v___x_770_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_707_, v_fn_768_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_772_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref_known(v___x_770_, 1);
lean_inc_ref(v_arg_769_);
v___x_772_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_707_, v_arg_769_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_791_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_791_ == 0)
{
v___x_775_ = v___x_772_;
v_isShared_776_ = v_isSharedCheck_791_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_791_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___y_778_; size_t v___x_783_; size_t v___x_784_; uint8_t v___x_785_; 
v___x_783_ = lean_ptr_addr(v_fn_768_);
v___x_784_ = lean_ptr_addr(v_a_771_);
v___x_785_ = lean_usize_dec_eq(v___x_783_, v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; 
lean_dec_ref_known(v_e_708_, 2);
v___x_786_ = l_Lean_Expr_app___override(v_a_771_, v_a_773_);
v___y_778_ = v___x_786_;
goto v___jp_777_;
}
else
{
size_t v___x_787_; size_t v___x_788_; uint8_t v___x_789_; 
v___x_787_ = lean_ptr_addr(v_arg_769_);
v___x_788_ = lean_ptr_addr(v_a_773_);
v___x_789_ = lean_usize_dec_eq(v___x_787_, v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; 
lean_dec_ref_known(v_e_708_, 2);
v___x_790_ = l_Lean_Expr_app___override(v_a_771_, v_a_773_);
v___y_778_ = v___x_790_;
goto v___jp_777_;
}
else
{
lean_dec(v_a_773_);
lean_dec(v_a_771_);
v___y_778_ = v_e_708_;
goto v___jp_777_;
}
}
v___jp_777_:
{
lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_779_ = l_Lean_Expr_headBeta(v___y_778_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_779_);
v___x_781_ = v___x_775_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_dec(v_a_771_);
lean_dec_ref_known(v_e_708_, 2);
return v___x_772_;
}
}
else
{
lean_dec_ref_known(v_e_708_, 2);
return v___x_770_;
}
}
case 6:
{
lean_object* v_binderName_792_; lean_object* v_binderType_793_; lean_object* v_body_794_; uint8_t v_binderInfo_795_; lean_object* v___x_796_; 
v_binderName_792_ = lean_ctor_get(v_e_708_, 0);
v_binderType_793_ = lean_ctor_get(v_e_708_, 1);
v_body_794_ = lean_ctor_get(v_e_708_, 2);
v_binderInfo_795_ = lean_ctor_get_uint8(v_e_708_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_793_);
v___x_796_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_707_, v_binderType_793_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_798_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___x_796_, 1);
lean_inc_ref(v_body_794_);
v___x_798_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_707_, v_body_794_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_825_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_825_ == 0)
{
v___x_801_ = v___x_798_;
v_isShared_802_ = v_isSharedCheck_825_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_798_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_825_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
size_t v___x_803_; size_t v___x_804_; uint8_t v___x_805_; 
v___x_803_ = lean_ptr_addr(v_binderType_793_);
v___x_804_ = lean_ptr_addr(v_a_797_);
v___x_805_ = lean_usize_dec_eq(v___x_803_, v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_808_; 
lean_inc(v_binderName_792_);
lean_dec_ref_known(v_e_708_, 3);
v___x_806_ = l_Lean_Expr_lam___override(v_binderName_792_, v_a_797_, v_a_799_, v_binderInfo_795_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_806_);
v___x_808_ = v___x_801_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
else
{
size_t v___x_810_; size_t v___x_811_; uint8_t v___x_812_; 
v___x_810_ = lean_ptr_addr(v_body_794_);
v___x_811_ = lean_ptr_addr(v_a_799_);
v___x_812_ = lean_usize_dec_eq(v___x_810_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_815_; 
lean_inc(v_binderName_792_);
lean_dec_ref_known(v_e_708_, 3);
v___x_813_ = l_Lean_Expr_lam___override(v_binderName_792_, v_a_797_, v_a_799_, v_binderInfo_795_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_813_);
v___x_815_ = v___x_801_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
else
{
uint8_t v___x_817_; 
v___x_817_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_795_, v_binderInfo_795_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; lean_object* v___x_820_; 
lean_inc(v_binderName_792_);
lean_dec_ref_known(v_e_708_, 3);
v___x_818_ = l_Lean_Expr_lam___override(v_binderName_792_, v_a_797_, v_a_799_, v_binderInfo_795_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_818_);
v___x_820_ = v___x_801_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
else
{
lean_object* v___x_823_; 
lean_dec(v_a_799_);
lean_dec(v_a_797_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v_e_708_);
v___x_823_ = v___x_801_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_e_708_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
}
else
{
lean_dec(v_a_797_);
lean_dec_ref_known(v_e_708_, 3);
return v___x_798_;
}
}
else
{
lean_dec_ref_known(v_e_708_, 3);
return v___x_796_;
}
}
case 7:
{
lean_object* v_binderName_826_; lean_object* v_binderType_827_; lean_object* v_body_828_; uint8_t v_binderInfo_829_; lean_object* v___x_830_; 
v_binderName_826_ = lean_ctor_get(v_e_708_, 0);
v_binderType_827_ = lean_ctor_get(v_e_708_, 1);
v_body_828_ = lean_ctor_get(v_e_708_, 2);
v_binderInfo_829_ = lean_ctor_get_uint8(v_e_708_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_827_);
v___x_830_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_707_, v_binderType_827_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_832_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
lean_dec_ref_known(v___x_830_, 1);
lean_inc_ref(v_body_828_);
v___x_832_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_707_, v_body_828_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_859_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_859_ == 0)
{
v___x_835_ = v___x_832_;
v_isShared_836_ = v_isSharedCheck_859_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_832_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_859_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
size_t v___x_837_; size_t v___x_838_; uint8_t v___x_839_; 
v___x_837_ = lean_ptr_addr(v_binderType_827_);
v___x_838_ = lean_ptr_addr(v_a_831_);
v___x_839_ = lean_usize_dec_eq(v___x_837_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_842_; 
lean_inc(v_binderName_826_);
lean_dec_ref_known(v_e_708_, 3);
v___x_840_ = l_Lean_Expr_forallE___override(v_binderName_826_, v_a_831_, v_a_833_, v_binderInfo_829_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v___x_840_);
v___x_842_ = v___x_835_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
else
{
size_t v___x_844_; size_t v___x_845_; uint8_t v___x_846_; 
v___x_844_ = lean_ptr_addr(v_body_828_);
v___x_845_ = lean_ptr_addr(v_a_833_);
v___x_846_ = lean_usize_dec_eq(v___x_844_, v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_849_; 
lean_inc(v_binderName_826_);
lean_dec_ref_known(v_e_708_, 3);
v___x_847_ = l_Lean_Expr_forallE___override(v_binderName_826_, v_a_831_, v_a_833_, v_binderInfo_829_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v___x_847_);
v___x_849_ = v___x_835_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
else
{
uint8_t v___x_851_; 
v___x_851_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_829_, v_binderInfo_829_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_854_; 
lean_inc(v_binderName_826_);
lean_dec_ref_known(v_e_708_, 3);
v___x_852_ = l_Lean_Expr_forallE___override(v_binderName_826_, v_a_831_, v_a_833_, v_binderInfo_829_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v___x_852_);
v___x_854_ = v___x_835_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
else
{
lean_object* v___x_857_; 
lean_dec(v_a_833_);
lean_dec(v_a_831_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v_e_708_);
v___x_857_ = v___x_835_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_e_708_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
}
else
{
lean_dec(v_a_831_);
lean_dec_ref_known(v_e_708_, 3);
return v___x_832_;
}
}
else
{
lean_dec_ref_known(v_e_708_, 3);
return v___x_830_;
}
}
case 8:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec_ref_known(v_e_708_, 4);
v___x_860_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3, &l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3);
v___x_861_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v___x_860_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
return v___x_861_;
}
case 10:
{
lean_object* v_data_862_; lean_object* v_expr_863_; lean_object* v___x_864_; 
v_data_862_ = lean_ctor_get(v_e_708_, 0);
v_expr_863_ = lean_ctor_get(v_e_708_, 1);
lean_inc_ref(v_expr_863_);
v___x_864_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_707_, v_expr_863_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_879_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_879_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_879_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_879_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
size_t v___x_869_; size_t v___x_870_; uint8_t v___x_871_; 
v___x_869_ = lean_ptr_addr(v_expr_863_);
v___x_870_ = lean_ptr_addr(v_a_865_);
v___x_871_ = lean_usize_dec_eq(v___x_869_, v___x_870_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_874_; 
lean_inc(v_data_862_);
lean_dec_ref_known(v_e_708_, 2);
v___x_872_ = l_Lean_Expr_mdata___override(v_data_862_, v_a_865_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_872_);
v___x_874_ = v___x_867_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
else
{
lean_object* v___x_877_; 
lean_dec(v_a_865_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v_e_708_);
v___x_877_ = v___x_867_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_e_708_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_708_, 2);
return v___x_864_;
}
}
case 11:
{
lean_object* v_typeName_880_; lean_object* v_idx_881_; lean_object* v_struct_882_; lean_object* v___x_883_; 
v_typeName_880_ = lean_ctor_get(v_e_708_, 0);
v_idx_881_ = lean_ctor_get(v_e_708_, 1);
v_struct_882_ = lean_ctor_get(v_e_708_, 2);
lean_inc_ref(v_struct_882_);
v___x_883_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_707_, v_struct_882_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_898_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_898_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_898_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_898_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
size_t v___x_888_; size_t v___x_889_; uint8_t v___x_890_; 
v___x_888_ = lean_ptr_addr(v_struct_882_);
v___x_889_ = lean_ptr_addr(v_a_884_);
v___x_890_ = lean_usize_dec_eq(v___x_888_, v___x_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; lean_object* v___x_893_; 
lean_inc(v_idx_881_);
lean_inc(v_typeName_880_);
lean_dec_ref_known(v_e_708_, 3);
v___x_891_ = l_Lean_Expr_proj___override(v_typeName_880_, v_idx_881_, v_a_884_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_891_);
v___x_893_ = v___x_886_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
else
{
lean_object* v___x_896_; 
lean_dec(v_a_884_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v_e_708_);
v___x_896_ = v___x_886_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_e_708_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_708_, 3);
return v___x_883_;
}
}
default: 
{
lean_object* v___x_899_; 
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v_e_708_);
return v___x_899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(uint8_t v_pu_900_, lean_object* v_e_901_, uint8_t v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
if (lean_obj_tag(v_e_901_) == 5)
{
lean_object* v_fn_909_; lean_object* v_arg_910_; lean_object* v___x_911_; 
v_fn_909_ = lean_ctor_get(v_e_901_, 0);
v_arg_910_ = lean_ctor_get(v_e_901_, 1);
lean_inc_ref(v_fn_909_);
v___x_911_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_900_, v_fn_909_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 1);
lean_inc_ref(v_arg_910_);
v___x_913_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_900_, v_arg_910_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_935_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_935_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_935_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_935_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
size_t v___x_918_; size_t v___x_919_; uint8_t v___x_920_; 
v___x_918_ = lean_ptr_addr(v_fn_909_);
v___x_919_ = lean_ptr_addr(v_a_912_);
v___x_920_ = lean_usize_dec_eq(v___x_918_, v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_923_; 
lean_dec_ref_known(v_e_901_, 2);
v___x_921_ = l_Lean_Expr_app___override(v_a_912_, v_a_914_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_921_);
v___x_923_ = v___x_916_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
else
{
size_t v___x_925_; size_t v___x_926_; uint8_t v___x_927_; 
v___x_925_ = lean_ptr_addr(v_arg_910_);
v___x_926_ = lean_ptr_addr(v_a_914_);
v___x_927_ = lean_usize_dec_eq(v___x_925_, v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; lean_object* v___x_930_; 
lean_dec_ref_known(v_e_901_, 2);
v___x_928_ = l_Lean_Expr_app___override(v_a_912_, v_a_914_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_928_);
v___x_930_ = v___x_916_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
else
{
lean_object* v___x_933_; 
lean_dec(v_a_914_);
lean_dec(v_a_912_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v_e_901_);
v___x_933_ = v___x_916_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_e_901_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
else
{
lean_dec(v_a_912_);
lean_dec_ref_known(v_e_901_, 2);
return v___x_913_;
}
}
else
{
lean_dec_ref_known(v_e_901_, 2);
return v___x_911_;
}
}
else
{
lean_object* v___x_936_; 
v___x_936_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_900_, v_e_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
return v___x_936_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp___boxed(lean_object* v_pu_937_, lean_object* v_e_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
uint8_t v_pu_boxed_946_; uint8_t v_a_boxed_947_; lean_object* v_res_948_; 
v_pu_boxed_946_ = lean_unbox(v_pu_937_);
v_a_boxed_947_ = lean_unbox(v_a_939_);
v_res_948_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_boxed_946_, v_e_938_, v_a_boxed_947_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___boxed(lean_object* v_pu_949_, lean_object* v_e_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
uint8_t v_pu_boxed_958_; uint8_t v_a_boxed_959_; lean_object* v_res_960_; 
v_pu_boxed_958_ = lean_unbox(v_pu_949_);
v_a_boxed_959_ = lean_unbox(v_a_951_);
v_res_960_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_boxed_958_, v_e_950_, v_a_boxed_959_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(lean_object* v_00_u03b2_961_, lean_object* v_m_962_, lean_object* v_a_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v_m_962_, v_a_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___boxed(lean_object* v_00_u03b2_965_, lean_object* v_m_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(v_00_u03b2_965_, v_m_966_, v_a_967_);
lean_dec(v_a_967_);
lean_dec_ref(v_m_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(lean_object* v_00_u03b2_969_, lean_object* v_a_970_, lean_object* v_x_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_970_, v_x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_973_, lean_object* v_a_974_, lean_object* v_x_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(v_00_u03b2_973_, v_a_974_, v_x_975_);
lean_dec(v_x_975_);
lean_dec(v_a_974_);
return v_res_976_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___closed__0(void){
_start:
{
uint8_t v___x_977_; lean_object* v___x_978_; 
v___x_977_ = 1;
v___x_978_ = l_Lean_Compiler_LCNF_Purity_ctorIdx(v___x_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(uint8_t v_pu_979_, lean_object* v_e_980_, uint8_t v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_988_ = l_Lean_Compiler_LCNF_Purity_ctorIdx(v_pu_979_);
v___x_989_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___closed__0, &l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___closed__0);
v___x_990_ = lean_nat_dec_eq(v___x_988_, v___x_989_);
lean_dec(v___x_988_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; 
v___x_991_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_979_, v_e_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
return v___x_991_;
}
else
{
lean_object* v___x_992_; 
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v_e_980_);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___boxed(lean_object* v_pu_993_, lean_object* v_e_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
uint8_t v_pu_boxed_1002_; uint8_t v_a_boxed_1003_; lean_object* v_res_1004_; 
v_pu_boxed_1002_ = lean_unbox(v_pu_993_);
v_a_boxed_1003_ = lean_unbox(v_a_995_);
v_res_1004_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_boxed_1002_, v_e_994_, v_a_boxed_1003_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t v_pu_1005_, lean_object* v_p_1006_, uint8_t v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v_fvarId_1014_; lean_object* v_binderName_1015_; lean_object* v_type_1016_; uint8_t v_borrow_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1065_; 
v_fvarId_1014_ = lean_ctor_get(v_p_1006_, 0);
v_binderName_1015_ = lean_ctor_get(v_p_1006_, 1);
v_type_1016_ = lean_ctor_get(v_p_1006_, 2);
v_borrow_1017_ = lean_ctor_get_uint8(v_p_1006_, sizeof(void*)*3);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_p_1006_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1019_ = v_p_1006_;
v_isShared_1020_ = v_isSharedCheck_1065_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_type_1016_);
lean_inc(v_binderName_1015_);
lean_inc(v_fvarId_1014_);
lean_dec(v_p_1006_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1065_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v_a_1022_; lean_object* v___x_1023_; 
v___x_1021_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_1015_, v_a_1007_, v_a_1010_);
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref(v___x_1021_);
v___x_1023_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1005_, v_type_1016_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v___x_1025_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_1014_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1048_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1048_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1048_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 2, v_a_1024_);
lean_ctor_set(v___x_1019_, 1, v_a_1022_);
lean_ctor_set(v___x_1019_, 0, v_a_1026_);
v___x_1031_ = v___x_1019_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1026_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_a_1022_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_a_1024_);
lean_ctor_set_uint8(v_reuseFailAlloc_1047_, sizeof(void*)*3, v_borrow_1017_);
v___x_1031_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; lean_object* v_lctx_1033_; lean_object* v_nextIdx_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1046_; 
v___x_1032_ = lean_st_ref_take(v_a_1010_);
v_lctx_1033_ = lean_ctor_get(v___x_1032_, 0);
v_nextIdx_1034_ = lean_ctor_get(v___x_1032_, 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1036_ = v___x_1032_;
v_isShared_1037_ = v_isSharedCheck_1046_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_nextIdx_1034_);
lean_inc(v_lctx_1033_);
lean_dec(v___x_1032_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1046_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1040_; 
lean_inc_ref(v___x_1031_);
v___x_1038_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_1005_, v_lctx_1033_, v___x_1031_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1038_);
v___x_1040_ = v___x_1036_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_nextIdx_1034_);
v___x_1040_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1041_ = lean_st_ref_put(v_a_1010_, v___x_1040_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1031_);
v___x_1043_ = v___x_1028_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1031_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec(v_a_1024_);
lean_dec(v_a_1022_);
lean_del_object(v___x_1019_);
v_a_1049_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1025_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1025_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec(v_a_1022_);
lean_del_object(v___x_1019_);
lean_dec(v_fvarId_1014_);
v_a_1057_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1023_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1023_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(lean_object* v_pu_1066_, lean_object* v_p_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
uint8_t v_pu_boxed_1075_; uint8_t v_a_boxed_1076_; lean_object* v_res_1077_; 
v_pu_boxed_1075_ = lean_unbox(v_pu_1066_);
v_a_boxed_1076_ = lean_unbox(v_a_1068_);
v_res_1077_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_boxed_1075_, v_p_1067_, v_a_boxed_1076_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg(uint8_t v_pu_1078_, lean_object* v_arg_1079_, uint8_t v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
switch(lean_obj_tag(v_arg_1079_))
{
case 0:
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v_arg_1079_);
return v___x_1087_;
}
case 1:
{
lean_object* v_fvarId_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_fvarId_1088_ = lean_ctor_get(v_arg_1079_, 0);
v___x_1089_ = lean_st_ref_get(v_a_1081_);
v___x_1090_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v___x_1089_, v_fvarId_1088_);
lean_dec(v___x_1089_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v_arg_1079_);
return v___x_1091_;
}
else
{
lean_object* v_val_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1122_; 
lean_dec_ref_known(v_arg_1079_, 1);
v_val_1092_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1094_ = v___x_1090_;
v_isShared_1095_ = v_isSharedCheck_1122_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_val_1092_);
lean_dec(v___x_1090_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1122_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
switch(lean_obj_tag(v_val_1092_))
{
case 0:
{
lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1096_ = lean_box(0);
if (v_isShared_1095_ == 0)
{
lean_ctor_set_tag(v___x_1094_, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1096_);
v___x_1098_ = v___x_1094_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
case 1:
{
lean_object* v_fvarId_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1110_; 
v_fvarId_1100_ = lean_ctor_get(v_val_1092_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_val_1092_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1102_ = v_val_1092_;
v_isShared_1103_ = v_isSharedCheck_1110_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_fvarId_1100_);
lean_dec(v_val_1092_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1110_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_fvarId_1100_);
v___x_1105_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1107_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set_tag(v___x_1094_, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1105_);
v___x_1107_ = v___x_1094_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
default: 
{
lean_object* v_expr_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1121_; 
v_expr_1111_ = lean_ctor_get(v_val_1092_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_val_1092_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1113_ = v_val_1092_;
v_isShared_1114_ = v_isSharedCheck_1121_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_expr_1111_);
lean_dec(v_val_1092_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1121_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_expr_1111_);
v___x_1116_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1118_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set_tag(v___x_1094_, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1116_);
v___x_1118_ = v___x_1094_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
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
lean_object* v_expr_1123_; lean_object* v___x_1124_; 
v_expr_1123_ = lean_ctor_get(v_arg_1079_, 0);
lean_inc_ref(v_expr_1123_);
v___x_1124_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1078_, v_expr_1123_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1133_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1133_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1133_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1129_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1078_, v_arg_1079_, v_a_1125_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1129_);
v___x_1131_ = v___x_1127_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec_ref_known(v_arg_1079_, 1);
v_a_1134_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1124_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1124_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg___boxed(lean_object* v_pu_1142_, lean_object* v_arg_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
uint8_t v_pu_boxed_1151_; uint8_t v_a_boxed_1152_; lean_object* v_res_1153_; 
v_pu_boxed_1151_ = lean_unbox(v_pu_1142_);
v_a_boxed_1152_ = lean_unbox(v_a_1144_);
v_res_1153_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_boxed_1151_, v_arg_1143_, v_a_boxed_1152_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(uint8_t v_pu_1154_, size_t v_sz_1155_, size_t v_i_1156_, lean_object* v_bs_1157_, uint8_t v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
uint8_t v___x_1165_; 
v___x_1165_ = lean_usize_dec_lt(v_i_1156_, v_sz_1155_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v_bs_1157_);
return v___x_1166_;
}
else
{
lean_object* v_v_1167_; lean_object* v___x_1168_; lean_object* v_bs_x27_1169_; lean_object* v___x_1170_; 
v_v_1167_ = lean_array_uget(v_bs_1157_, v_i_1156_);
v___x_1168_ = lean_unsigned_to_nat(0u);
v_bs_x27_1169_ = lean_array_uset(v_bs_1157_, v_i_1156_, v___x_1168_);
v___x_1170_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_1154_, v_v_1167_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; size_t v___x_1172_; size_t v___x_1173_; lean_object* v___x_1174_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1170_, 1);
v___x_1172_ = ((size_t)1ULL);
v___x_1173_ = lean_usize_add(v_i_1156_, v___x_1172_);
v___x_1174_ = lean_array_uset(v_bs_x27_1169_, v_i_1156_, v_a_1171_);
v_i_1156_ = v___x_1173_;
v_bs_1157_ = v___x_1174_;
goto _start;
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec_ref(v_bs_x27_1169_);
v_a_1176_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1170_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1170_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0___boxed(lean_object* v_pu_1184_, lean_object* v_sz_1185_, lean_object* v_i_1186_, lean_object* v_bs_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
uint8_t v_pu_boxed_1195_; size_t v_sz_boxed_1196_; size_t v_i_boxed_1197_; uint8_t v___y_339__boxed_1198_; lean_object* v_res_1199_; 
v_pu_boxed_1195_ = lean_unbox(v_pu_1184_);
v_sz_boxed_1196_ = lean_unbox_usize(v_sz_1185_);
lean_dec(v_sz_1185_);
v_i_boxed_1197_ = lean_unbox_usize(v_i_1186_);
lean_dec(v_i_1186_);
v___y_339__boxed_1198_ = lean_unbox(v___y_1188_);
v_res_1199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_boxed_1195_, v_sz_boxed_1196_, v_i_boxed_1197_, v_bs_1187_, v___y_339__boxed_1198_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs(uint8_t v_pu_1200_, lean_object* v_args_1201_, uint8_t v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
size_t v_sz_1209_; size_t v___x_1210_; lean_object* v___x_1211_; 
v_sz_1209_ = lean_array_size(v_args_1201_);
v___x_1210_ = ((size_t)0ULL);
v___x_1211_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_1200_, v_sz_1209_, v___x_1210_, v_args_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs___boxed(lean_object* v_pu_1212_, lean_object* v_args_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
uint8_t v_pu_boxed_1221_; uint8_t v_a_boxed_1222_; lean_object* v_res_1223_; 
v_pu_boxed_1221_ = lean_unbox(v_pu_1212_);
v_a_boxed_1222_ = lean_unbox(v_a_1214_);
v_res_1223_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_boxed_1221_, v_args_1213_, v_a_boxed_1222_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(uint8_t v_pu_1224_, lean_object* v_e_1225_, uint8_t v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v_fvarId_1234_; lean_object* v___y_1235_; lean_object* v_args_1251_; uint8_t v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; 
switch(lean_obj_tag(v_e_1225_))
{
case 2:
{
lean_object* v_struct_1276_; uint8_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v_struct_1276_ = lean_ctor_get(v_e_1225_, 2);
v___x_1277_ = 1;
v___x_1278_ = lean_st_ref_get(v_a_1227_);
lean_inc(v_struct_1276_);
v___x_1279_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1278_, v_struct_1276_, v___x_1277_);
lean_dec(v___x_1278_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_fvarId_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1288_; 
v_fvarId_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1288_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_fvarId_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1288_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1284_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1224_, v_e_1225_, v_fvarId_1280_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v___x_1284_);
v___x_1286_ = v___x_1282_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
else
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_dec_ref_known(v_e_1225_, 3);
v___x_1289_ = lean_box(1);
v___x_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
return v___x_1290_;
}
}
case 3:
{
lean_object* v_args_1291_; lean_object* v___x_1292_; 
v_args_1291_ = lean_ctor_get(v_e_1225_, 2);
lean_inc_ref(v_args_1291_);
v___x_1292_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1224_, v_args_1291_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1301_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1301_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1301_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1297_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1225_, v_a_1293_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1297_);
v___x_1299_ = v___x_1295_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec_ref_known(v_e_1225_, 3);
v_a_1302_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1292_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1292_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
case 4:
{
lean_object* v_fvarId_1310_; lean_object* v_args_1311_; uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v_fvarId_1310_ = lean_ctor_get(v_e_1225_, 0);
v_args_1311_ = lean_ctor_get(v_e_1225_, 1);
v___x_1312_ = 1;
v___x_1313_ = lean_st_ref_get(v_a_1227_);
lean_inc(v_fvarId_1310_);
v___x_1314_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1313_, v_fvarId_1310_, v___x_1312_);
lean_dec(v___x_1313_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_fvarId_1315_; lean_object* v___x_1316_; 
v_fvarId_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_fvarId_1315_);
lean_dec_ref_known(v___x_1314_, 1);
lean_inc_ref(v_args_1311_);
v___x_1316_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1224_, v_args_1311_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1325_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1325_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1325_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1321_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___redArg(v_e_1225_, v_fvarId_1315_, v_a_1317_);
lean_dec_ref_known(v_e_1225_, 2);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1321_);
v___x_1323_ = v___x_1319_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec(v_fvarId_1315_);
lean_dec_ref_known(v_e_1225_, 2);
v_a_1326_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1316_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1316_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
else
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
lean_dec_ref_known(v_e_1225_, 2);
v___x_1334_ = lean_box(1);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
return v___x_1335_;
}
}
case 5:
{
lean_object* v_args_1336_; lean_object* v___x_1337_; 
v_args_1336_ = lean_ctor_get(v_e_1225_, 1);
lean_inc_ref(v_args_1336_);
v___x_1337_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1224_, v_args_1336_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1346_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1346_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1346_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1342_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1225_, v_a_1338_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1342_);
v___x_1344_ = v___x_1340_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
lean_dec_ref_known(v_e_1225_, 2);
v_a_1347_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1337_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1337_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
case 6:
{
lean_object* v_var_1355_; 
v_var_1355_ = lean_ctor_get(v_e_1225_, 1);
lean_inc(v_var_1355_);
v_fvarId_1234_ = v_var_1355_;
v___y_1235_ = v_a_1227_;
goto v___jp_1233_;
}
case 7:
{
lean_object* v_var_1356_; 
v_var_1356_ = lean_ctor_get(v_e_1225_, 1);
lean_inc(v_var_1356_);
v_fvarId_1234_ = v_var_1356_;
v___y_1235_ = v_a_1227_;
goto v___jp_1233_;
}
case 8:
{
lean_object* v_var_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_var_1357_ = lean_ctor_get(v_e_1225_, 2);
v___x_1358_ = 1;
v___x_1359_ = lean_st_ref_get(v_a_1227_);
lean_inc(v_var_1357_);
v___x_1360_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1359_, v_var_1357_, v___x_1358_);
lean_dec(v___x_1359_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_fvarId_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1369_; 
v_fvarId_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_fvarId_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1365_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1224_, v_e_1225_, v_fvarId_1361_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1365_);
v___x_1367_ = v___x_1363_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
lean_dec_ref_known(v_e_1225_, 3);
v___x_1370_ = lean_box(1);
v___x_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
return v___x_1371_;
}
}
case 9:
{
lean_object* v_args_1372_; 
v_args_1372_ = lean_ctor_get(v_e_1225_, 1);
lean_inc_ref(v_args_1372_);
v_args_1251_ = v_args_1372_;
v___y_1252_ = v_a_1226_;
v___y_1253_ = v_a_1227_;
v___y_1254_ = v_a_1228_;
v___y_1255_ = v_a_1229_;
v___y_1256_ = v_a_1230_;
v___y_1257_ = v_a_1231_;
goto v___jp_1250_;
}
case 10:
{
lean_object* v_args_1373_; 
v_args_1373_ = lean_ctor_get(v_e_1225_, 1);
lean_inc_ref(v_args_1373_);
v_args_1251_ = v_args_1373_;
v___y_1252_ = v_a_1226_;
v___y_1253_ = v_a_1227_;
v___y_1254_ = v_a_1228_;
v___y_1255_ = v_a_1229_;
v___y_1256_ = v_a_1230_;
v___y_1257_ = v_a_1231_;
goto v___jp_1250_;
}
case 11:
{
lean_object* v_n_1374_; lean_object* v_var_1375_; uint8_t v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v_n_1374_ = lean_ctor_get(v_e_1225_, 0);
lean_inc(v_n_1374_);
v_var_1375_ = lean_ctor_get(v_e_1225_, 1);
v___x_1376_ = 1;
v___x_1377_ = lean_st_ref_get(v_a_1227_);
lean_inc(v_var_1375_);
v___x_1378_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1377_, v_var_1375_, v___x_1376_);
lean_dec(v___x_1377_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_fvarId_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1387_; 
v_fvarId_1379_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1381_ = v___x_1378_;
v_isShared_1382_ = v_isSharedCheck_1387_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_fvarId_1379_);
lean_dec(v___x_1378_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1387_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1383_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp___redArg(v_e_1225_, v_n_1374_, v_fvarId_1379_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v___x_1383_);
v___x_1385_ = v___x_1381_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec(v_n_1374_);
lean_dec_ref_known(v_e_1225_, 2);
v___x_1388_ = lean_box(1);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
}
case 12:
{
lean_object* v_var_1390_; lean_object* v_i_1391_; uint8_t v_updateHeader_1392_; lean_object* v_args_1393_; uint8_t v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v_var_1390_ = lean_ctor_get(v_e_1225_, 0);
v_i_1391_ = lean_ctor_get(v_e_1225_, 1);
lean_inc_ref(v_i_1391_);
v_updateHeader_1392_ = lean_ctor_get_uint8(v_e_1225_, sizeof(void*)*3);
v_args_1393_ = lean_ctor_get(v_e_1225_, 2);
v___x_1394_ = 1;
v___x_1395_ = lean_st_ref_get(v_a_1227_);
lean_inc(v_var_1390_);
v___x_1396_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1395_, v_var_1390_, v___x_1394_);
lean_dec(v___x_1395_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_fvarId_1397_; lean_object* v___x_1398_; 
v_fvarId_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_fvarId_1397_);
lean_dec_ref_known(v___x_1396_, 1);
lean_inc_ref(v_args_1393_);
v___x_1398_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1224_, v_args_1393_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1407_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1403_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp___redArg(v_e_1225_, v_fvarId_1397_, v_i_1391_, v_updateHeader_1392_, v_a_1399_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v___x_1403_);
v___x_1405_ = v___x_1401_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec(v_fvarId_1397_);
lean_dec_ref(v_i_1391_);
lean_dec_ref_known(v_e_1225_, 3);
v_a_1408_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1398_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1398_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
lean_dec_ref(v_i_1391_);
lean_dec_ref_known(v_e_1225_, 3);
v___x_1416_ = lean_box(1);
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
return v___x_1417_;
}
}
case 13:
{
lean_object* v_ty_1418_; lean_object* v_fvarId_1419_; uint8_t v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v_ty_1418_ = lean_ctor_get(v_e_1225_, 0);
lean_inc_ref(v_ty_1418_);
v_fvarId_1419_ = lean_ctor_get(v_e_1225_, 1);
v___x_1420_ = 1;
v___x_1421_ = lean_st_ref_get(v_a_1227_);
lean_inc(v_fvarId_1419_);
v___x_1422_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1421_, v_fvarId_1419_, v___x_1420_);
lean_dec(v___x_1421_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_fvarId_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1431_; 
v_fvarId_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1431_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_fvarId_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1431_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1427_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp___redArg(v_e_1225_, v_ty_1418_, v_fvarId_1423_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1427_);
v___x_1429_ = v___x_1425_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
else
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec_ref(v_ty_1418_);
lean_dec_ref_known(v_e_1225_, 2);
v___x_1432_ = lean_box(1);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
return v___x_1433_;
}
}
case 14:
{
lean_object* v_fvarId_1434_; uint8_t v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v_fvarId_1434_ = lean_ctor_get(v_e_1225_, 0);
v___x_1435_ = 1;
v___x_1436_ = lean_st_ref_get(v_a_1227_);
lean_inc(v_fvarId_1434_);
v___x_1437_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1436_, v_fvarId_1434_, v___x_1435_);
lean_dec(v___x_1436_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_fvarId_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1446_; 
v_fvarId_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1446_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_fvarId_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1446_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1442_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp___redArg(v_e_1225_, v_fvarId_1438_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1442_);
v___x_1444_ = v___x_1440_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
else
{
lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1454_; 
v_isSharedCheck_1454_ = !lean_is_exclusive(v_e_1225_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; 
v_unused_1455_ = lean_ctor_get(v_e_1225_, 0);
lean_dec(v_unused_1455_);
v___x_1448_ = v_e_1225_;
v_isShared_1449_ = v_isSharedCheck_1454_;
goto v_resetjp_1447_;
}
else
{
lean_dec(v_e_1225_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1454_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1450_ = lean_box(1);
if (v_isShared_1449_ == 0)
{
lean_ctor_set_tag(v___x_1448_, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1450_);
v___x_1452_ = v___x_1448_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
case 15:
{
lean_object* v_fvarId_1456_; uint8_t v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_fvarId_1456_ = lean_ctor_get(v_e_1225_, 0);
v___x_1457_ = 1;
v___x_1458_ = lean_st_ref_get(v_a_1227_);
lean_inc(v_fvarId_1456_);
v___x_1459_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1458_, v_fvarId_1456_, v___x_1457_);
lean_dec(v___x_1458_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_fvarId_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1468_; 
v_fvarId_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1468_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_fvarId_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1468_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1464_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp___redArg(v_e_1225_, v_fvarId_1460_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1464_);
v___x_1466_ = v___x_1462_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
else
{
lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1476_; 
v_isSharedCheck_1476_ = !lean_is_exclusive(v_e_1225_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; 
v_unused_1477_ = lean_ctor_get(v_e_1225_, 0);
lean_dec(v_unused_1477_);
v___x_1470_ = v_e_1225_;
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
else
{
lean_dec(v_e_1225_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1472_ = lean_box(1);
if (v_isShared_1471_ == 0)
{
lean_ctor_set_tag(v___x_1470_, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1472_);
v___x_1474_ = v___x_1470_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
default: 
{
lean_object* v___x_1478_; 
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v_e_1225_);
return v___x_1478_;
}
}
v___jp_1233_:
{
uint8_t v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1236_ = 1;
v___x_1237_ = lean_st_ref_get(v___y_1235_);
v___x_1238_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1237_, v_fvarId_1234_, v___x_1236_);
lean_dec(v___x_1237_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_fvarId_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1247_; 
v_fvarId_1239_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1247_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_fvarId_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1247_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___x_1243_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1224_, v_e_1225_, v_fvarId_1239_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v___x_1243_);
v___x_1245_ = v___x_1241_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
else
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
lean_dec(v_e_1225_);
v___x_1248_ = lean_box(1);
v___x_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
return v___x_1249_;
}
}
v___jp_1250_:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1224_, v_args_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1267_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1261_ = v___x_1258_;
v_isShared_1262_ = v_isSharedCheck_1267_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1258_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1267_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1263_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1225_, v_a_1259_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v___x_1263_);
v___x_1265_ = v___x_1261_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec(v_e_1225_);
v_a_1268_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1258_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1258_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue___boxed(lean_object* v_pu_1479_, lean_object* v_e_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_){
_start:
{
uint8_t v_pu_boxed_1488_; uint8_t v_a_boxed_1489_; lean_object* v_res_1490_; 
v_pu_boxed_1488_ = lean_unbox(v_pu_1479_);
v_a_boxed_1489_ = lean_unbox(v_a_1481_);
v_res_1490_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_boxed_1488_, v_e_1480_, v_a_boxed_1489_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec(v_a_1482_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(uint8_t v_pu_1491_, lean_object* v_decl_1492_, uint8_t v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
lean_object* v_fvarId_1500_; lean_object* v_binderName_1501_; lean_object* v_type_1502_; lean_object* v_value_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1561_; 
v_fvarId_1500_ = lean_ctor_get(v_decl_1492_, 0);
v_binderName_1501_ = lean_ctor_get(v_decl_1492_, 1);
v_type_1502_ = lean_ctor_get(v_decl_1492_, 2);
v_value_1503_ = lean_ctor_get(v_decl_1492_, 3);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_decl_1492_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1505_ = v_decl_1492_;
v_isShared_1506_ = v_isSharedCheck_1561_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_value_1503_);
lean_inc(v_type_1502_);
lean_inc(v_binderName_1501_);
lean_inc(v_fvarId_1500_);
lean_dec(v_decl_1492_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1561_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1507_; lean_object* v_a_1508_; lean_object* v___x_1509_; 
v___x_1507_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_1501_, v_a_1493_, v_a_1496_);
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
lean_dec_ref(v___x_1507_);
v___x_1509_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1491_, v_type_1502_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1511_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v___x_1509_, 1);
v___x_1511_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_1491_, v_value_1503_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1513_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1511_, 1);
v___x_1513_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_1500_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1536_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1536_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1536_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 3, v_a_1512_);
lean_ctor_set(v___x_1505_, 2, v_a_1510_);
lean_ctor_set(v___x_1505_, 1, v_a_1508_);
lean_ctor_set(v___x_1505_, 0, v_a_1514_);
v___x_1519_ = v___x_1505_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1514_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_a_1508_);
lean_ctor_set(v_reuseFailAlloc_1535_, 2, v_a_1510_);
lean_ctor_set(v_reuseFailAlloc_1535_, 3, v_a_1512_);
v___x_1519_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1520_; lean_object* v_lctx_1521_; lean_object* v_nextIdx_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1534_; 
v___x_1520_ = lean_st_ref_take(v_a_1496_);
v_lctx_1521_ = lean_ctor_get(v___x_1520_, 0);
v_nextIdx_1522_ = lean_ctor_get(v___x_1520_, 1);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1524_ = v___x_1520_;
v_isShared_1525_ = v_isSharedCheck_1534_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_nextIdx_1522_);
lean_inc(v_lctx_1521_);
lean_dec(v___x_1520_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1534_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1526_; lean_object* v___x_1528_; 
lean_inc_ref(v___x_1519_);
v___x_1526_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_1491_, v_lctx_1521_, v___x_1519_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1526_);
v___x_1528_ = v___x_1524_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_nextIdx_1522_);
v___x_1528_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1529_ = lean_st_ref_put(v_a_1496_, v___x_1528_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1519_);
v___x_1531_ = v___x_1516_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1519_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_dec(v_a_1512_);
lean_dec(v_a_1510_);
lean_dec(v_a_1508_);
lean_del_object(v___x_1505_);
v_a_1537_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1513_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1513_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec(v_a_1510_);
lean_dec(v_a_1508_);
lean_del_object(v___x_1505_);
lean_dec(v_fvarId_1500_);
v_a_1545_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1511_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1511_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec(v_a_1508_);
lean_del_object(v___x_1505_);
lean_dec(v_value_1503_);
lean_dec(v_fvarId_1500_);
v_a_1553_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1509_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1509_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(lean_object* v_pu_1562_, lean_object* v_decl_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
uint8_t v_pu_boxed_1571_; uint8_t v_a_boxed_1572_; lean_object* v_res_1573_; 
v_pu_boxed_1571_ = lean_unbox(v_pu_1562_);
v_a_boxed_1572_ = lean_unbox(v_a_1564_);
v_res_1573_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_boxed_1571_, v_decl_1563_, v_a_boxed_1572_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
lean_dec(v_a_1565_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(uint8_t v_pu_1574_, size_t v_sz_1575_, size_t v_i_1576_, lean_object* v_bs_1577_, uint8_t v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
uint8_t v___x_1585_; 
v___x_1585_ = lean_usize_dec_lt(v_i_1576_, v_sz_1575_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v_bs_1577_);
return v___x_1586_;
}
else
{
lean_object* v_v_1587_; lean_object* v___x_1588_; lean_object* v_bs_x27_1589_; lean_object* v___x_1590_; 
v_v_1587_ = lean_array_uget(v_bs_1577_, v_i_1576_);
v___x_1588_ = lean_unsigned_to_nat(0u);
v_bs_x27_1589_ = lean_array_uset(v_bs_1577_, v_i_1576_, v___x_1588_);
v___x_1590_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_1574_, v_v_1587_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; size_t v___x_1592_; size_t v___x_1593_; lean_object* v___x_1594_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v___x_1592_ = ((size_t)1ULL);
v___x_1593_ = lean_usize_add(v_i_1576_, v___x_1592_);
v___x_1594_ = lean_array_uset(v_bs_x27_1589_, v_i_1576_, v_a_1591_);
v_i_1576_ = v___x_1593_;
v_bs_1577_ = v___x_1594_;
goto _start;
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec_ref(v_bs_x27_1589_);
v_a_1596_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1590_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1590_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0___boxed(lean_object* v_pu_1604_, lean_object* v_sz_1605_, lean_object* v_i_1606_, lean_object* v_bs_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
uint8_t v_pu_boxed_1615_; size_t v_sz_boxed_1616_; size_t v_i_boxed_1617_; uint8_t v___y_26878__boxed_1618_; lean_object* v_res_1619_; 
v_pu_boxed_1615_ = lean_unbox(v_pu_1604_);
v_sz_boxed_1616_ = lean_unbox_usize(v_sz_1605_);
lean_dec(v_sz_1605_);
v_i_boxed_1617_ = lean_unbox_usize(v_i_1606_);
lean_dec(v_i_1606_);
v___y_26878__boxed_1618_ = lean_unbox(v___y_1608_);
v_res_1619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_boxed_1615_, v_sz_boxed_1616_, v_i_boxed_1617_, v_bs_1607_, v___y_26878__boxed_1618_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(uint8_t v_pu_1620_, size_t v_sz_1621_, size_t v_i_1622_, lean_object* v_bs_1623_, uint8_t v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
uint8_t v___x_1631_; 
v___x_1631_ = lean_usize_dec_lt(v_i_1622_, v_sz_1621_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1632_, 0, v_bs_1623_);
return v___x_1632_;
}
else
{
lean_object* v_v_1633_; lean_object* v___x_1634_; lean_object* v_bs_x27_1635_; lean_object* v_a_1637_; 
v_v_1633_ = lean_array_uget(v_bs_1623_, v_i_1622_);
v___x_1634_ = lean_unsigned_to_nat(0u);
v_bs_x27_1635_ = lean_array_uset(v_bs_1623_, v_i_1622_, v___x_1634_);
switch(lean_obj_tag(v_v_1633_))
{
case 0:
{
lean_object* v_ctorName_1642_; lean_object* v_params_1643_; lean_object* v_code_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1665_; 
v_ctorName_1642_ = lean_ctor_get(v_v_1633_, 0);
v_params_1643_ = lean_ctor_get(v_v_1633_, 1);
v_code_1644_ = lean_ctor_get(v_v_1633_, 2);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_v_1633_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1646_ = v_v_1633_;
v_isShared_1647_ = v_isSharedCheck_1665_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_code_1644_);
lean_inc(v_params_1643_);
lean_inc(v_ctorName_1642_);
lean_dec(v_v_1633_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1665_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
size_t v_sz_1648_; size_t v___x_1649_; lean_object* v___x_1650_; 
v_sz_1648_ = lean_array_size(v_params_1643_);
v___x_1649_ = ((size_t)0ULL);
v___x_1650_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_1620_, v_sz_1648_, v___x_1649_, v_params_1643_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1652_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1652_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1620_, v_code_1644_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1655_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref_known(v___x_1652_, 1);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 2, v_a_1653_);
lean_ctor_set(v___x_1646_, 1, v_a_1651_);
v___x_1655_ = v___x_1646_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_ctorName_1642_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_a_1651_);
lean_ctor_set(v_reuseFailAlloc_1656_, 2, v_a_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
v_a_1637_ = v___x_1655_;
goto v___jp_1636_;
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec(v_a_1651_);
lean_del_object(v___x_1646_);
lean_dec(v_ctorName_1642_);
lean_dec_ref(v_bs_x27_1635_);
v_a_1657_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1652_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1652_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_del_object(v___x_1646_);
lean_dec_ref(v_code_1644_);
lean_dec(v_ctorName_1642_);
lean_dec_ref(v_bs_x27_1635_);
return v___x_1650_;
}
}
}
case 1:
{
lean_object* v_info_1666_; lean_object* v_code_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1684_; 
v_info_1666_ = lean_ctor_get(v_v_1633_, 0);
v_code_1667_ = lean_ctor_get(v_v_1633_, 1);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_v_1633_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1669_ = v_v_1633_;
v_isShared_1670_ = v_isSharedCheck_1684_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_code_1667_);
lean_inc(v_info_1666_);
lean_dec(v_v_1633_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1684_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1620_, v_code_1667_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1674_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
lean_dec_ref_known(v___x_1671_, 1);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 1, v_a_1672_);
v___x_1674_ = v___x_1669_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_info_1666_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_a_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
v_a_1637_ = v___x_1674_;
goto v___jp_1636_;
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_del_object(v___x_1669_);
lean_dec_ref(v_info_1666_);
lean_dec_ref(v_bs_x27_1635_);
v_a_1676_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1671_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1671_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
default: 
{
lean_object* v_code_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1702_; 
v_code_1685_ = lean_ctor_get(v_v_1633_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_v_1633_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1687_ = v_v_1633_;
v_isShared_1688_ = v_isSharedCheck_1702_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_code_1685_);
lean_dec(v_v_1633_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1702_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1620_, v_code_1685_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1692_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref_known(v___x_1689_, 1);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v_a_1690_);
v___x_1692_ = v___x_1687_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
v_a_1637_ = v___x_1692_;
goto v___jp_1636_;
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_del_object(v___x_1687_);
lean_dec_ref(v_bs_x27_1635_);
v_a_1694_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1689_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1689_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
}
}
v___jp_1636_:
{
size_t v___x_1638_; size_t v___x_1639_; lean_object* v___x_1640_; 
v___x_1638_ = ((size_t)1ULL);
v___x_1639_ = lean_usize_add(v_i_1622_, v___x_1638_);
v___x_1640_ = lean_array_uset(v_bs_x27_1635_, v_i_1622_, v_a_1637_);
v_i_1622_ = v___x_1639_;
v_bs_1623_ = v___x_1640_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t v_pu_1703_, lean_object* v_code_1704_, uint8_t v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
switch(lean_obj_tag(v_code_1704_))
{
case 0:
{
lean_object* v_decl_1712_; lean_object* v_k_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1739_; 
v_decl_1712_ = lean_ctor_get(v_code_1704_, 0);
v_k_1713_ = lean_ctor_get(v_code_1704_, 1);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_code_1704_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1715_ = v_code_1704_;
v_isShared_1716_ = v_isSharedCheck_1739_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_k_1713_);
lean_inc(v_decl_1712_);
lean_dec(v_code_1704_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1739_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_1703_, v_decl_1712_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1719_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
v___x_1719_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1703_, v_k_1713_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1730_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1722_ = v___x_1719_;
v_isShared_1723_ = v_isSharedCheck_1730_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1719_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1730_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v_a_1720_);
lean_ctor_set(v___x_1715_, 0, v_a_1718_);
v___x_1725_ = v___x_1715_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1718_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v___x_1727_; 
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v___x_1725_);
v___x_1727_ = v___x_1722_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
else
{
lean_dec(v_a_1718_);
lean_del_object(v___x_1715_);
return v___x_1719_;
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_del_object(v___x_1715_);
lean_dec_ref(v_k_1713_);
v_a_1731_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1717_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1717_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_1740_; lean_object* v_k_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1767_; 
v_decl_1740_ = lean_ctor_get(v_code_1704_, 0);
v_k_1741_ = lean_ctor_get(v_code_1704_, 1);
v_isSharedCheck_1767_ = !lean_is_exclusive(v_code_1704_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1743_ = v_code_1704_;
v_isShared_1744_ = v_isSharedCheck_1767_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_k_1741_);
lean_inc(v_decl_1740_);
lean_dec(v_code_1704_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1767_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1703_, v_decl_1740_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1747_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref_known(v___x_1745_, 1);
v___x_1747_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1703_, v_k_1741_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1758_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1750_ = v___x_1747_;
v_isShared_1751_ = v_isSharedCheck_1758_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1758_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 1, v_a_1748_);
lean_ctor_set(v___x_1743_, 0, v_a_1746_);
v___x_1753_ = v___x_1743_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1746_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1755_; 
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1753_);
v___x_1755_ = v___x_1750_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
else
{
lean_dec(v_a_1746_);
lean_del_object(v___x_1743_);
return v___x_1747_;
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_del_object(v___x_1743_);
lean_dec_ref(v_k_1741_);
v_a_1759_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1745_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1745_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
case 2:
{
lean_object* v_decl_1768_; lean_object* v_k_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1795_; 
v_decl_1768_ = lean_ctor_get(v_code_1704_, 0);
v_k_1769_ = lean_ctor_get(v_code_1704_, 1);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_code_1704_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1771_ = v_code_1704_;
v_isShared_1772_ = v_isSharedCheck_1795_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_k_1769_);
lean_inc(v_decl_1768_);
lean_dec(v_code_1704_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1795_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1703_, v_decl_1768_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1775_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref_known(v___x_1773_, 1);
v___x_1775_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1703_, v_k_1769_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1786_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1786_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1786_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 1, v_a_1776_);
lean_ctor_set(v___x_1771_, 0, v_a_1774_);
v___x_1781_ = v___x_1771_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1774_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1783_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1781_);
v___x_1783_ = v___x_1778_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
else
{
lean_dec(v_a_1774_);
lean_del_object(v___x_1771_);
return v___x_1775_;
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_del_object(v___x_1771_);
lean_dec_ref(v_k_1769_);
v_a_1787_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1773_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1773_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_1796_; lean_object* v_args_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1826_; 
v_fvarId_1796_ = lean_ctor_get(v_code_1704_, 0);
v_args_1797_ = lean_ctor_get(v_code_1704_, 1);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_code_1704_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1799_ = v_code_1704_;
v_isShared_1800_ = v_isSharedCheck_1826_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_args_1797_);
lean_inc(v_fvarId_1796_);
lean_dec(v_code_1704_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1826_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
uint8_t v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = 1;
v___x_1802_ = lean_st_ref_get(v_a_1706_);
v___x_1803_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1802_, v_fvarId_1796_, v___x_1801_);
lean_dec(v___x_1802_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_fvarId_1804_; lean_object* v___x_1805_; 
v_fvarId_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_fvarId_1804_);
lean_dec_ref_known(v___x_1803_, 1);
v___x_1805_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1703_, v_args_1797_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1816_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1808_ = v___x_1805_;
v_isShared_1809_ = v_isSharedCheck_1816_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1816_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 1, v_a_1806_);
lean_ctor_set(v___x_1799_, 0, v_fvarId_1804_);
v___x_1811_ = v___x_1799_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_fvarId_1804_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1813_; 
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1811_);
v___x_1813_ = v___x_1808_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec(v_fvarId_1804_);
lean_del_object(v___x_1799_);
v_a_1817_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1805_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1805_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
else
{
lean_object* v___x_1825_; 
lean_del_object(v___x_1799_);
lean_dec_ref(v_args_1797_);
v___x_1825_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1703_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
return v___x_1825_;
}
}
}
case 4:
{
lean_object* v_cases_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1879_; 
v_cases_1827_ = lean_ctor_get(v_code_1704_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v_code_1704_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1829_ = v_code_1704_;
v_isShared_1830_ = v_isSharedCheck_1879_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_cases_1827_);
lean_dec(v_code_1704_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1879_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v_typeName_1831_; lean_object* v_resultType_1832_; lean_object* v_discr_1833_; lean_object* v_alts_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1878_; 
v_typeName_1831_ = lean_ctor_get(v_cases_1827_, 0);
v_resultType_1832_ = lean_ctor_get(v_cases_1827_, 1);
v_discr_1833_ = lean_ctor_get(v_cases_1827_, 2);
v_alts_1834_ = lean_ctor_get(v_cases_1827_, 3);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_cases_1827_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1836_ = v_cases_1827_;
v_isShared_1837_ = v_isSharedCheck_1878_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_alts_1834_);
lean_inc(v_discr_1833_);
lean_inc(v_resultType_1832_);
lean_inc(v_typeName_1831_);
lean_dec(v_cases_1827_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1878_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
uint8_t v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = 1;
v___x_1839_ = lean_st_ref_get(v_a_1706_);
v___x_1840_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1839_, v_discr_1833_, v___x_1838_);
lean_dec(v___x_1839_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_fvarId_1841_; lean_object* v___x_1842_; 
v_fvarId_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_fvarId_1841_);
lean_dec_ref_known(v___x_1840_, 1);
v___x_1842_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1703_, v_resultType_1832_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; size_t v_sz_1844_; size_t v___x_1845_; lean_object* v___x_1846_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_a_1843_);
lean_dec_ref_known(v___x_1842_, 1);
v_sz_1844_ = lean_array_size(v_alts_1834_);
v___x_1845_ = ((size_t)0ULL);
v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_1703_, v_sz_1844_, v___x_1845_, v_alts_1834_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1860_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1860_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1860_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 3, v_a_1847_);
lean_ctor_set(v___x_1836_, 2, v_fvarId_1841_);
lean_ctor_set(v___x_1836_, 1, v_a_1843_);
v___x_1852_ = v___x_1836_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_typeName_1831_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_a_1843_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_fvarId_1841_);
lean_ctor_set(v_reuseFailAlloc_1859_, 3, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1854_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1852_);
v___x_1854_ = v___x_1829_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1856_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1854_);
v___x_1856_ = v___x_1849_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
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
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_a_1843_);
lean_dec(v_fvarId_1841_);
lean_del_object(v___x_1836_);
lean_dec(v_typeName_1831_);
lean_del_object(v___x_1829_);
v_a_1861_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1846_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1846_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_fvarId_1841_);
lean_del_object(v___x_1836_);
lean_dec_ref(v_alts_1834_);
lean_dec(v_typeName_1831_);
lean_del_object(v___x_1829_);
v_a_1869_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1842_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1842_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_object* v___x_1877_; 
lean_del_object(v___x_1836_);
lean_dec_ref(v_alts_1834_);
lean_dec_ref(v_resultType_1832_);
lean_dec(v_typeName_1831_);
lean_del_object(v___x_1829_);
v___x_1877_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1703_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
return v___x_1877_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1899_; 
v_fvarId_1880_ = lean_ctor_get(v_code_1704_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_code_1704_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1882_ = v_code_1704_;
v_isShared_1883_ = v_isSharedCheck_1899_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_fvarId_1880_);
lean_dec(v_code_1704_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1899_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
uint8_t v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = 1;
v___x_1885_ = lean_st_ref_get(v_a_1706_);
v___x_1886_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1885_, v_fvarId_1880_, v___x_1884_);
lean_dec(v___x_1885_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_fvarId_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1897_; 
v_fvarId_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1897_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_fvarId_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1897_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v_fvarId_1887_);
v___x_1892_ = v___x_1882_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_fvarId_1887_);
v___x_1892_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1894_; 
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v___x_1892_);
v___x_1894_ = v___x_1889_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
else
{
lean_object* v___x_1898_; 
lean_del_object(v___x_1882_);
v___x_1898_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1703_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
return v___x_1898_;
}
}
}
case 6:
{
lean_object* v_type_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1924_; 
v_type_1900_ = lean_ctor_get(v_code_1704_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_code_1704_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1902_ = v_code_1704_;
v_isShared_1903_ = v_isSharedCheck_1924_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_type_1900_);
lean_dec(v_code_1704_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1924_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; 
v___x_1904_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1703_, v_type_1900_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1915_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1915_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1915_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v_a_1905_);
v___x_1910_ = v___x_1902_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1912_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1910_);
v___x_1912_ = v___x_1907_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_del_object(v___x_1902_);
v_a_1916_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1904_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1904_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_1925_; lean_object* v_i_1926_; lean_object* v_y_1927_; lean_object* v_k_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1951_; 
v_fvarId_1925_ = lean_ctor_get(v_code_1704_, 0);
v_i_1926_ = lean_ctor_get(v_code_1704_, 1);
v_y_1927_ = lean_ctor_get(v_code_1704_, 2);
v_k_1928_ = lean_ctor_get(v_code_1704_, 3);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_code_1704_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1930_ = v_code_1704_;
v_isShared_1931_ = v_isSharedCheck_1951_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_k_1928_);
lean_inc(v_y_1927_);
lean_inc(v_i_1926_);
lean_inc(v_fvarId_1925_);
lean_dec(v_code_1704_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1951_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
uint8_t v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1932_ = 1;
v___x_1933_ = lean_st_ref_get(v_a_1706_);
v___x_1934_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1933_, v_fvarId_1925_, v___x_1932_);
lean_dec(v___x_1933_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_fvarId_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v_fvarId_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_fvarId_1935_);
lean_dec_ref_known(v___x_1934_, 1);
v___x_1936_ = lean_st_ref_get(v_a_1706_);
v___x_1937_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1703_, v___x_1936_, v_y_1927_, v___x_1932_);
lean_dec(v___x_1936_);
v___x_1938_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1703_, v_k_1928_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1949_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1949_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1949_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 3, v_a_1939_);
lean_ctor_set(v___x_1930_, 2, v___x_1937_);
lean_ctor_set(v___x_1930_, 0, v_fvarId_1935_);
v___x_1944_ = v___x_1930_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_fvarId_1935_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_i_1926_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v___x_1937_);
lean_ctor_set(v_reuseFailAlloc_1948_, 3, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1946_; 
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v___x_1944_);
v___x_1946_ = v___x_1941_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_dec(v___x_1937_);
lean_dec(v_fvarId_1935_);
lean_del_object(v___x_1930_);
lean_dec(v_i_1926_);
return v___x_1938_;
}
}
else
{
lean_object* v___x_1950_; 
lean_del_object(v___x_1930_);
lean_dec_ref(v_k_1928_);
lean_dec(v_y_1927_);
lean_dec(v_i_1926_);
v___x_1950_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1703_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
return v___x_1950_;
}
}
}
case 8:
{
lean_object* v_fvarId_1952_; lean_object* v_i_1953_; lean_object* v_y_1954_; lean_object* v_k_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1980_; 
v_fvarId_1952_ = lean_ctor_get(v_code_1704_, 0);
v_i_1953_ = lean_ctor_get(v_code_1704_, 1);
v_y_1954_ = lean_ctor_get(v_code_1704_, 2);
v_k_1955_ = lean_ctor_get(v_code_1704_, 3);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_code_1704_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1957_ = v_code_1704_;
v_isShared_1958_ = v_isSharedCheck_1980_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_k_1955_);
lean_inc(v_y_1954_);
lean_inc(v_i_1953_);
lean_inc(v_fvarId_1952_);
lean_dec(v_code_1704_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1980_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
uint8_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1959_ = 1;
v___x_1960_ = lean_st_ref_get(v_a_1706_);
v___x_1961_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1960_, v_fvarId_1952_, v___x_1959_);
lean_dec(v___x_1960_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_fvarId_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v_fvarId_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_fvarId_1962_);
lean_dec_ref_known(v___x_1961_, 1);
v___x_1963_ = lean_st_ref_get(v_a_1706_);
v___x_1964_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1963_, v_y_1954_, v___x_1959_);
lean_dec(v___x_1963_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_fvarId_1965_; lean_object* v___x_1966_; 
v_fvarId_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_fvarId_1965_);
lean_dec_ref_known(v___x_1964_, 1);
v___x_1966_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1703_, v_k_1955_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1977_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1969_ = v___x_1966_;
v_isShared_1970_ = v_isSharedCheck_1977_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1966_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1977_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 3, v_a_1967_);
lean_ctor_set(v___x_1957_, 2, v_fvarId_1965_);
lean_ctor_set(v___x_1957_, 0, v_fvarId_1962_);
v___x_1972_ = v___x_1957_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_fvarId_1962_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_i_1953_);
lean_ctor_set(v_reuseFailAlloc_1976_, 2, v_fvarId_1965_);
lean_ctor_set(v_reuseFailAlloc_1976_, 3, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1974_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_1972_);
v___x_1974_ = v___x_1969_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
else
{
lean_dec(v_fvarId_1965_);
lean_dec(v_fvarId_1962_);
lean_del_object(v___x_1957_);
lean_dec(v_i_1953_);
return v___x_1966_;
}
}
else
{
lean_object* v___x_1978_; 
lean_dec(v_fvarId_1962_);
lean_del_object(v___x_1957_);
lean_dec_ref(v_k_1955_);
lean_dec(v_i_1953_);
v___x_1978_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1703_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
return v___x_1978_;
}
}
else
{
lean_object* v___x_1979_; 
lean_del_object(v___x_1957_);
lean_dec_ref(v_k_1955_);
lean_dec(v_y_1954_);
lean_dec(v_i_1953_);
v___x_1979_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1703_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
return v___x_1979_;
}
}
}
case 9:
{
lean_object* v_fvarId_1981_; lean_object* v_i_1982_; lean_object* v_offset_1983_; lean_object* v_y_1984_; lean_object* v_ty_1985_; lean_object* v_k_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2021_; 
v_fvarId_1981_ = lean_ctor_get(v_code_1704_, 0);
v_i_1982_ = lean_ctor_get(v_code_1704_, 1);
v_offset_1983_ = lean_ctor_get(v_code_1704_, 2);
v_y_1984_ = lean_ctor_get(v_code_1704_, 3);
v_ty_1985_ = lean_ctor_get(v_code_1704_, 4);
v_k_1986_ = lean_ctor_get(v_code_1704_, 5);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_code_1704_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_1988_ = v_code_1704_;
v_isShared_1989_ = v_isSharedCheck_2021_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_k_1986_);
lean_inc(v_ty_1985_);
lean_inc(v_y_1984_);
lean_inc(v_offset_1983_);
lean_inc(v_i_1982_);
lean_inc(v_fvarId_1981_);
lean_dec(v_code_1704_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2021_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
uint8_t v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = 1;
v___x_1991_ = lean_st_ref_get(v_a_1706_);
v___x_1992_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1991_, v_fvarId_1981_, v___x_1990_);
lean_dec(v___x_1991_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_fvarId_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v_fvarId_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_fvarId_1993_);
lean_dec_ref_known(v___x_1992_, 1);
v___x_1994_ = lean_st_ref_get(v_a_1706_);
v___x_1995_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1994_, v_y_1984_, v___x_1990_);
lean_dec(v___x_1994_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_fvarId_1996_; lean_object* v___x_1997_; 
v_fvarId_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_fvarId_1996_);
lean_dec_ref_known(v___x_1995_, 1);
v___x_1997_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1703_, v_ty_1985_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_1999_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1997_, 1);
v___x_1999_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1703_, v_k_1986_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2010_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2002_ = v___x_1999_;
v_isShared_2003_ = v_isSharedCheck_2010_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2010_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 5, v_a_2000_);
lean_ctor_set(v___x_1988_, 4, v_a_1998_);
lean_ctor_set(v___x_1988_, 3, v_fvarId_1996_);
lean_ctor_set(v___x_1988_, 0, v_fvarId_1993_);
v___x_2005_ = v___x_1988_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_fvarId_1993_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_i_1982_);
lean_ctor_set(v_reuseFailAlloc_2009_, 2, v_offset_1983_);
lean_ctor_set(v_reuseFailAlloc_2009_, 3, v_fvarId_1996_);
lean_ctor_set(v_reuseFailAlloc_2009_, 4, v_a_1998_);
lean_ctor_set(v_reuseFailAlloc_2009_, 5, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2007_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v___x_2005_);
v___x_2007_ = v___x_2002_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
else
{
lean_dec(v_a_1998_);
lean_dec(v_fvarId_1996_);
lean_dec(v_fvarId_1993_);
lean_del_object(v___x_1988_);
lean_dec(v_offset_1983_);
lean_dec(v_i_1982_);
return v___x_1999_;
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec(v_fvarId_1996_);
lean_dec(v_fvarId_1993_);
lean_del_object(v___x_1988_);
lean_dec_ref(v_k_1986_);
lean_dec(v_offset_1983_);
lean_dec(v_i_1982_);
v_a_2011_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_1997_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_1997_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
else
{
lean_object* v___x_2019_; 
lean_dec(v_fvarId_1993_);
lean_del_object(v___x_1988_);
lean_dec_ref(v_k_1986_);
lean_dec_ref(v_ty_1985_);
lean_dec(v_offset_1983_);
lean_dec(v_i_1982_);
v___x_2019_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1703_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
return v___x_2019_;
}
}
else
{
lean_object* v___x_2020_; 
lean_del_object(v___x_1988_);
lean_dec_ref(v_k_1986_);
lean_dec_ref(v_ty_1985_);
lean_dec(v_y_1984_);
lean_dec(v_offset_1983_);
lean_dec(v_i_1982_);
v___x_2020_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1703_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
return v___x_2020_;
}
}
}
case 10:
{
lean_object* v_fvarId_2022_; lean_object* v_cidx_2023_; lean_object* v_k_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2045_; 
v_fvarId_2022_ = lean_ctor_get(v_code_1704_, 0);
v_cidx_2023_ = lean_ctor_get(v_code_1704_, 1);
v_k_2024_ = lean_ctor_get(v_code_1704_, 2);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_code_1704_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2026_ = v_code_1704_;
v_isShared_2027_ = v_isSharedCheck_2045_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_k_2024_);
lean_inc(v_cidx_2023_);
lean_inc(v_fvarId_2022_);
lean_dec(v_code_1704_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2045_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
uint8_t v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2028_ = 1;
v___x_2029_ = lean_st_ref_get(v_a_1706_);
v___x_2030_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2029_, v_fvarId_2022_, v___x_2028_);
lean_dec(v___x_2029_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_fvarId_2031_; lean_object* v___x_2032_; 
v_fvarId_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_fvarId_2031_);
lean_dec_ref_known(v___x_2030_, 1);
v___x_2032_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1703_, v_k_2024_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2043_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2035_ = v___x_2032_;
v_isShared_2036_ = v_isSharedCheck_2043_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2032_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2043_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 2, v_a_2033_);
lean_ctor_set(v___x_2026_, 0, v_fvarId_2031_);
v___x_2038_ = v___x_2026_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_fvarId_2031_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_cidx_2023_);
lean_ctor_set(v_reuseFailAlloc_2042_, 2, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2040_; 
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2038_);
v___x_2040_ = v___x_2035_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
else
{
lean_dec(v_fvarId_2031_);
lean_del_object(v___x_2026_);
lean_dec(v_cidx_2023_);
return v___x_2032_;
}
}
else
{
lean_object* v___x_2044_; 
lean_del_object(v___x_2026_);
lean_dec_ref(v_k_2024_);
lean_dec(v_cidx_2023_);
v___x_2044_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1703_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
return v___x_2044_;
}
}
}
case 11:
{
lean_object* v_fvarId_2046_; lean_object* v_n_2047_; uint8_t v_check_2048_; uint8_t v_persistent_2049_; lean_object* v_k_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2071_; 
v_fvarId_2046_ = lean_ctor_get(v_code_1704_, 0);
v_n_2047_ = lean_ctor_get(v_code_1704_, 1);
v_check_2048_ = lean_ctor_get_uint8(v_code_1704_, sizeof(void*)*3);
v_persistent_2049_ = lean_ctor_get_uint8(v_code_1704_, sizeof(void*)*3 + 1);
v_k_2050_ = lean_ctor_get(v_code_1704_, 2);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_code_1704_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2052_ = v_code_1704_;
v_isShared_2053_ = v_isSharedCheck_2071_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_k_2050_);
lean_inc(v_n_2047_);
lean_inc(v_fvarId_2046_);
lean_dec(v_code_1704_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2071_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
uint8_t v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = 1;
v___x_2055_ = lean_st_ref_get(v_a_1706_);
v___x_2056_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2055_, v_fvarId_2046_, v___x_2054_);
lean_dec(v___x_2055_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_fvarId_2057_; lean_object* v___x_2058_; 
v_fvarId_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_fvarId_2057_);
lean_dec_ref_known(v___x_2056_, 1);
v___x_2058_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1703_, v_k_2050_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2069_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2069_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2069_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 2, v_a_2059_);
lean_ctor_set(v___x_2052_, 0, v_fvarId_2057_);
v___x_2064_ = v___x_2052_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_fvarId_2057_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_n_2047_);
lean_ctor_set(v_reuseFailAlloc_2068_, 2, v_a_2059_);
lean_ctor_set_uint8(v_reuseFailAlloc_2068_, sizeof(void*)*3, v_check_2048_);
lean_ctor_set_uint8(v_reuseFailAlloc_2068_, sizeof(void*)*3 + 1, v_persistent_2049_);
v___x_2064_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
lean_object* v___x_2066_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2064_);
v___x_2066_ = v___x_2061_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_dec(v_fvarId_2057_);
lean_del_object(v___x_2052_);
lean_dec(v_n_2047_);
return v___x_2058_;
}
}
else
{
lean_object* v___x_2070_; 
lean_del_object(v___x_2052_);
lean_dec_ref(v_k_2050_);
lean_dec(v_n_2047_);
v___x_2070_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1703_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
return v___x_2070_;
}
}
}
case 12:
{
lean_object* v_fvarId_2072_; lean_object* v_n_2073_; uint8_t v_check_2074_; uint8_t v_persistent_2075_; lean_object* v_objs_x3f_2076_; lean_object* v_k_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2098_; 
v_fvarId_2072_ = lean_ctor_get(v_code_1704_, 0);
v_n_2073_ = lean_ctor_get(v_code_1704_, 1);
v_check_2074_ = lean_ctor_get_uint8(v_code_1704_, sizeof(void*)*4);
v_persistent_2075_ = lean_ctor_get_uint8(v_code_1704_, sizeof(void*)*4 + 1);
v_objs_x3f_2076_ = lean_ctor_get(v_code_1704_, 2);
v_k_2077_ = lean_ctor_get(v_code_1704_, 3);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_code_1704_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2079_ = v_code_1704_;
v_isShared_2080_ = v_isSharedCheck_2098_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_k_2077_);
lean_inc(v_objs_x3f_2076_);
lean_inc(v_n_2073_);
lean_inc(v_fvarId_2072_);
lean_dec(v_code_1704_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2098_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
uint8_t v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = 1;
v___x_2082_ = lean_st_ref_get(v_a_1706_);
v___x_2083_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2082_, v_fvarId_2072_, v___x_2081_);
lean_dec(v___x_2082_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_fvarId_2084_; lean_object* v___x_2085_; 
v_fvarId_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_fvarId_2084_);
lean_dec_ref_known(v___x_2083_, 1);
v___x_2085_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1703_, v_k_2077_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2096_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2088_ = v___x_2085_;
v_isShared_2089_ = v_isSharedCheck_2096_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2096_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 3, v_a_2086_);
lean_ctor_set(v___x_2079_, 0, v_fvarId_2084_);
v___x_2091_ = v___x_2079_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_fvarId_2084_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_n_2073_);
lean_ctor_set(v_reuseFailAlloc_2095_, 2, v_objs_x3f_2076_);
lean_ctor_set(v_reuseFailAlloc_2095_, 3, v_a_2086_);
lean_ctor_set_uint8(v_reuseFailAlloc_2095_, sizeof(void*)*4, v_check_2074_);
lean_ctor_set_uint8(v_reuseFailAlloc_2095_, sizeof(void*)*4 + 1, v_persistent_2075_);
v___x_2091_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2093_; 
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2091_);
v___x_2093_ = v___x_2088_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
else
{
lean_dec(v_fvarId_2084_);
lean_del_object(v___x_2079_);
lean_dec(v_objs_x3f_2076_);
lean_dec(v_n_2073_);
return v___x_2085_;
}
}
else
{
lean_object* v___x_2097_; 
lean_del_object(v___x_2079_);
lean_dec_ref(v_k_2077_);
lean_dec(v_objs_x3f_2076_);
lean_dec(v_n_2073_);
v___x_2097_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1703_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
return v___x_2097_;
}
}
}
default: 
{
lean_object* v_fvarId_2099_; lean_object* v_k_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2121_; 
v_fvarId_2099_ = lean_ctor_get(v_code_1704_, 0);
v_k_2100_ = lean_ctor_get(v_code_1704_, 1);
v_isSharedCheck_2121_ = !lean_is_exclusive(v_code_1704_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2102_ = v_code_1704_;
v_isShared_2103_ = v_isSharedCheck_2121_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_k_2100_);
lean_inc(v_fvarId_2099_);
lean_dec(v_code_1704_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2121_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
uint8_t v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2104_ = 1;
v___x_2105_ = lean_st_ref_get(v_a_1706_);
v___x_2106_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2105_, v_fvarId_2099_, v___x_2104_);
lean_dec(v___x_2105_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_fvarId_2107_; lean_object* v___x_2108_; 
v_fvarId_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_fvarId_2107_);
lean_dec_ref_known(v___x_2106_, 1);
v___x_2108_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1703_, v_k_2100_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2119_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2111_ = v___x_2108_;
v_isShared_2112_ = v_isSharedCheck_2119_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2108_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2119_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 1, v_a_2109_);
lean_ctor_set(v___x_2102_, 0, v_fvarId_2107_);
v___x_2114_ = v___x_2102_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_fvarId_2107_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2116_; 
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2114_);
v___x_2116_ = v___x_2111_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
else
{
lean_dec(v_fvarId_2107_);
lean_del_object(v___x_2102_);
return v___x_2108_;
}
}
else
{
lean_object* v___x_2120_; 
lean_del_object(v___x_2102_);
lean_dec_ref(v_k_2100_);
v___x_2120_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1703_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
return v___x_2120_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(uint8_t v_pu_2122_, lean_object* v_decl_2123_, uint8_t v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
lean_object* v_fvarId_2131_; lean_object* v_binderName_2132_; lean_object* v_params_2133_; lean_object* v_type_2134_; lean_object* v_value_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2213_; 
v_fvarId_2131_ = lean_ctor_get(v_decl_2123_, 0);
v_binderName_2132_ = lean_ctor_get(v_decl_2123_, 1);
v_params_2133_ = lean_ctor_get(v_decl_2123_, 2);
v_type_2134_ = lean_ctor_get(v_decl_2123_, 3);
v_value_2135_ = lean_ctor_get(v_decl_2123_, 4);
v_isSharedCheck_2213_ = !lean_is_exclusive(v_decl_2123_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2137_ = v_decl_2123_;
v_isShared_2138_ = v_isSharedCheck_2213_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_value_2135_);
lean_inc(v_type_2134_);
lean_inc(v_params_2133_);
lean_inc(v_binderName_2132_);
lean_inc(v_fvarId_2131_);
lean_dec(v_decl_2123_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2213_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; 
v___x_2139_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2122_, v_type_2134_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2141_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_2132_, v_a_2124_, v_a_2127_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; size_t v_sz_2143_; size_t v___x_2144_; lean_object* v___x_2145_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
v_sz_2143_ = lean_array_size(v_params_2133_);
v___x_2144_ = ((size_t)0ULL);
v___x_2145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2122_, v_sz_2143_, v___x_2144_, v_params_2133_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2147_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2145_, 1);
v___x_2147_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2122_, v_value_2135_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2149_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2147_, 1);
v___x_2149_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_2131_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2172_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2152_ = v___x_2149_;
v_isShared_2153_ = v_isSharedCheck_2172_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2172_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 4, v_a_2148_);
lean_ctor_set(v___x_2137_, 3, v_a_2140_);
lean_ctor_set(v___x_2137_, 2, v_a_2146_);
lean_ctor_set(v___x_2137_, 1, v_a_2142_);
lean_ctor_set(v___x_2137_, 0, v_a_2150_);
v___x_2155_ = v___x_2137_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2150_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_a_2142_);
lean_ctor_set(v_reuseFailAlloc_2171_, 2, v_a_2146_);
lean_ctor_set(v_reuseFailAlloc_2171_, 3, v_a_2140_);
lean_ctor_set(v_reuseFailAlloc_2171_, 4, v_a_2148_);
v___x_2155_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2156_; lean_object* v_lctx_2157_; lean_object* v_nextIdx_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2170_; 
v___x_2156_ = lean_st_ref_take(v_a_2127_);
v_lctx_2157_ = lean_ctor_get(v___x_2156_, 0);
v_nextIdx_2158_ = lean_ctor_get(v___x_2156_, 1);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2160_ = v___x_2156_;
v_isShared_2161_ = v_isSharedCheck_2170_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_nextIdx_2158_);
lean_inc(v_lctx_2157_);
lean_dec(v___x_2156_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2170_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v___x_2164_; 
lean_inc_ref(v___x_2155_);
v___x_2162_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2122_, v_lctx_2157_, v___x_2155_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2162_);
v___x_2164_ = v___x_2160_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2162_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v_nextIdx_2158_);
v___x_2164_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
v___x_2165_ = lean_st_ref_put(v_a_2127_, v___x_2164_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2155_);
v___x_2167_ = v___x_2152_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2155_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_a_2148_);
lean_dec(v_a_2146_);
lean_dec(v_a_2142_);
lean_dec(v_a_2140_);
lean_del_object(v___x_2137_);
v_a_2173_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2149_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2149_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec(v_a_2146_);
lean_dec(v_a_2142_);
lean_dec(v_a_2140_);
lean_del_object(v___x_2137_);
lean_dec(v_fvarId_2131_);
v_a_2181_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2147_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2147_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v_a_2142_);
lean_dec(v_a_2140_);
lean_del_object(v___x_2137_);
lean_dec_ref(v_value_2135_);
lean_dec(v_fvarId_2131_);
v_a_2189_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2145_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2145_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec(v_a_2140_);
lean_del_object(v___x_2137_);
lean_dec_ref(v_value_2135_);
lean_dec_ref(v_params_2133_);
lean_dec(v_fvarId_2131_);
v_a_2197_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2141_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2141_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_del_object(v___x_2137_);
lean_dec_ref(v_value_2135_);
lean_dec_ref(v_params_2133_);
lean_dec(v_binderName_2132_);
lean_dec(v_fvarId_2131_);
v_a_2205_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2139_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2139_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(lean_object* v_pu_2214_, lean_object* v_decl_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
uint8_t v_pu_boxed_2223_; uint8_t v_a_boxed_2224_; lean_object* v_res_2225_; 
v_pu_boxed_2223_ = lean_unbox(v_pu_2214_);
v_a_boxed_2224_ = lean_unbox(v_a_2216_);
v_res_2225_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_boxed_2223_, v_decl_2215_, v_a_boxed_2224_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2___boxed(lean_object* v_pu_2226_, lean_object* v_sz_2227_, lean_object* v_i_2228_, lean_object* v_bs_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
uint8_t v_pu_boxed_2237_; size_t v_sz_boxed_2238_; size_t v_i_boxed_2239_; uint8_t v___y_26966__boxed_2240_; lean_object* v_res_2241_; 
v_pu_boxed_2237_ = lean_unbox(v_pu_2226_);
v_sz_boxed_2238_ = lean_unbox_usize(v_sz_2227_);
lean_dec(v_sz_2227_);
v_i_boxed_2239_ = lean_unbox_usize(v_i_2228_);
lean_dec(v_i_2228_);
v___y_26966__boxed_2240_ = lean_unbox(v___y_2230_);
v_res_2241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_boxed_2237_, v_sz_boxed_2238_, v_i_boxed_2239_, v_bs_2229_, v___y_26966__boxed_2240_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(lean_object* v_pu_2242_, lean_object* v_code_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
uint8_t v_pu_boxed_2251_; uint8_t v_a_boxed_2252_; lean_object* v_res_2253_; 
v_pu_boxed_2251_ = lean_unbox(v_pu_2242_);
v_a_boxed_2252_ = lean_unbox(v_a_2244_);
v_res_2253_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_boxed_2251_, v_code_2243_, v_a_boxed_2252_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
lean_dec(v_a_2249_);
lean_dec_ref(v_a_2248_);
lean_dec(v_a_2247_);
lean_dec_ref(v_a_2246_);
lean_dec(v_a_2245_);
return v_res_2253_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(lean_object* v_msg_2255_, uint8_t v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v_toApplicative_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2329_; 
v___x_2263_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
v___x_2264_ = l_StateRefT_x27_instMonad___redArg(v___x_2263_);
v_toApplicative_2265_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2329_ == 0)
{
lean_object* v_unused_2330_; 
v_unused_2330_ = lean_ctor_get(v___x_2264_, 1);
lean_dec(v_unused_2330_);
v___x_2267_ = v___x_2264_;
v_isShared_2268_ = v_isSharedCheck_2329_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_toApplicative_2265_);
lean_dec(v___x_2264_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2329_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v_toFunctor_2269_; lean_object* v_toSeq_2270_; lean_object* v_toSeqLeft_2271_; lean_object* v_toSeqRight_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2327_; 
v_toFunctor_2269_ = lean_ctor_get(v_toApplicative_2265_, 0);
v_toSeq_2270_ = lean_ctor_get(v_toApplicative_2265_, 2);
v_toSeqLeft_2271_ = lean_ctor_get(v_toApplicative_2265_, 3);
v_toSeqRight_2272_ = lean_ctor_get(v_toApplicative_2265_, 4);
v_isSharedCheck_2327_ = !lean_is_exclusive(v_toApplicative_2265_);
if (v_isSharedCheck_2327_ == 0)
{
lean_object* v_unused_2328_; 
v_unused_2328_ = lean_ctor_get(v_toApplicative_2265_, 1);
lean_dec(v_unused_2328_);
v___x_2274_ = v_toApplicative_2265_;
v_isShared_2275_ = v_isSharedCheck_2327_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_toSeqRight_2272_);
lean_inc(v_toSeqLeft_2271_);
lean_inc(v_toSeq_2270_);
lean_inc(v_toFunctor_2269_);
lean_dec(v_toApplicative_2265_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2327_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___f_2276_; lean_object* v___f_2277_; lean_object* v___f_2278_; lean_object* v___f_2279_; lean_object* v___x_2280_; lean_object* v___f_2281_; lean_object* v___f_2282_; lean_object* v___f_2283_; lean_object* v___x_2285_; 
v___f_2276_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
v___f_2277_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_2269_);
v___f_2278_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2278_, 0, v_toFunctor_2269_);
v___f_2279_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2279_, 0, v_toFunctor_2269_);
v___x_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___f_2278_);
lean_ctor_set(v___x_2280_, 1, v___f_2279_);
v___f_2281_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2281_, 0, v_toSeqRight_2272_);
v___f_2282_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2282_, 0, v_toSeqLeft_2271_);
v___f_2283_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2283_, 0, v_toSeq_2270_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 4, v___f_2281_);
lean_ctor_set(v___x_2274_, 3, v___f_2282_);
lean_ctor_set(v___x_2274_, 2, v___f_2283_);
lean_ctor_set(v___x_2274_, 1, v___f_2276_);
lean_ctor_set(v___x_2274_, 0, v___x_2280_);
v___x_2285_ = v___x_2274_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2280_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v___f_2276_);
lean_ctor_set(v_reuseFailAlloc_2326_, 2, v___f_2283_);
lean_ctor_set(v_reuseFailAlloc_2326_, 3, v___f_2282_);
lean_ctor_set(v_reuseFailAlloc_2326_, 4, v___f_2281_);
v___x_2285_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
lean_object* v___x_2287_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 1, v___f_2277_);
lean_ctor_set(v___x_2267_, 0, v___x_2285_);
v___x_2287_ = v___x_2267_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v___x_2285_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v___f_2277_);
v___x_2287_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
lean_object* v___x_2288_; lean_object* v_toApplicative_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2323_; 
v___x_2288_ = l_StateRefT_x27_instMonad___redArg(v___x_2287_);
v_toApplicative_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2323_ == 0)
{
lean_object* v_unused_2324_; 
v_unused_2324_ = lean_ctor_get(v___x_2288_, 1);
lean_dec(v_unused_2324_);
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2323_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_toApplicative_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2323_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v_toFunctor_2293_; lean_object* v_toSeq_2294_; lean_object* v_toSeqLeft_2295_; lean_object* v_toSeqRight_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2321_; 
v_toFunctor_2293_ = lean_ctor_get(v_toApplicative_2289_, 0);
v_toSeq_2294_ = lean_ctor_get(v_toApplicative_2289_, 2);
v_toSeqLeft_2295_ = lean_ctor_get(v_toApplicative_2289_, 3);
v_toSeqRight_2296_ = lean_ctor_get(v_toApplicative_2289_, 4);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_toApplicative_2289_);
if (v_isSharedCheck_2321_ == 0)
{
lean_object* v_unused_2322_; 
v_unused_2322_ = lean_ctor_get(v_toApplicative_2289_, 1);
lean_dec(v_unused_2322_);
v___x_2298_ = v_toApplicative_2289_;
v_isShared_2299_ = v_isSharedCheck_2321_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_toSeqRight_2296_);
lean_inc(v_toSeqLeft_2295_);
lean_inc(v_toSeq_2294_);
lean_inc(v_toFunctor_2293_);
lean_dec(v_toApplicative_2289_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2321_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___f_2300_; lean_object* v___f_2301_; lean_object* v___f_2302_; lean_object* v___f_2303_; lean_object* v___x_2304_; lean_object* v___f_2305_; lean_object* v___f_2306_; lean_object* v___f_2307_; lean_object* v___x_2309_; 
v___f_2300_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
v___f_2301_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(v_toFunctor_2293_);
v___f_2302_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2302_, 0, v_toFunctor_2293_);
v___f_2303_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2303_, 0, v_toFunctor_2293_);
v___x_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___f_2302_);
lean_ctor_set(v___x_2304_, 1, v___f_2303_);
v___f_2305_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2305_, 0, v_toSeqRight_2296_);
v___f_2306_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2306_, 0, v_toSeqLeft_2295_);
v___f_2307_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2307_, 0, v_toSeq_2294_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 4, v___f_2305_);
lean_ctor_set(v___x_2298_, 3, v___f_2306_);
lean_ctor_set(v___x_2298_, 2, v___f_2307_);
lean_ctor_set(v___x_2298_, 1, v___f_2300_);
lean_ctor_set(v___x_2298_, 0, v___x_2304_);
v___x_2309_ = v___x_2298_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v___f_2300_);
lean_ctor_set(v_reuseFailAlloc_2320_, 2, v___f_2307_);
lean_ctor_set(v_reuseFailAlloc_2320_, 3, v___f_2306_);
lean_ctor_set(v_reuseFailAlloc_2320_, 4, v___f_2305_);
v___x_2309_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
lean_object* v___x_2311_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 1, v___f_2301_);
lean_ctor_set(v___x_2291_, 0, v___x_2309_);
v___x_2311_ = v___x_2291_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2309_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v___f_2301_);
v___x_2311_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___f_2315_; lean_object* v___x_10948__overap_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2312_ = l_StateRefT_x27_instMonad___redArg(v___x_2311_);
v___x_2313_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___closed__0);
v___x_2314_ = l_instInhabitedOfMonad___redArg(v___x_2312_, v___x_2313_);
v___f_2315_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2315_, 0, v___x_2314_);
v___x_10948__overap_2316_ = lean_panic_fn_borrowed(v___f_2315_, v_msg_2255_);
lean_dec_ref(v___f_2315_);
v___x_2317_ = lean_box(v___y_2256_);
lean_inc(v___y_2261_);
lean_inc_ref(v___y_2260_);
lean_inc(v___y_2259_);
lean_inc_ref(v___y_2258_);
lean_inc(v___y_2257_);
v___x_2318_ = lean_apply_7(v___x_10948__overap_2316_, v___x_2317_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, lean_box(0));
return v___x_2318_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___boxed(lean_object* v_msg_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
uint8_t v___y_11009__boxed_2339_; lean_object* v_res_2340_; 
v___y_11009__boxed_2339_ = lean_unbox(v___y_2332_);
v_res_2340_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v_msg_2331_, v___y_11009__boxed_2339_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(uint8_t v_pu_2341_, lean_object* v_msg_2342_, uint8_t v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v_msg_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___boxed(lean_object* v_pu_2351_, lean_object* v_msg_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
uint8_t v_pu_boxed_2360_; uint8_t v___y_11145__boxed_2361_; lean_object* v_res_2362_; 
v_pu_boxed_2360_ = lean_unbox(v_pu_2351_);
v___y_11145__boxed_2361_ = lean_unbox(v___y_2353_);
v_res_2362_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_boxed_2360_, v_msg_2352_, v___y_11145__boxed_2361_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
return v_res_2362_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1(void){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2364_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2365_ = lean_unsigned_to_nat(41u);
v___x_2366_ = lean_unsigned_to_nat(217u);
v___x_2367_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2368_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2369_ = l_mkPanicMessageWithDecl(v___x_2368_, v___x_2367_, v___x_2366_, v___x_2365_, v___x_2364_);
return v___x_2369_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2(void){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2370_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2371_ = lean_unsigned_to_nat(31u);
v___x_2372_ = lean_unsigned_to_nat(222u);
v___x_2373_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2374_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2375_ = l_mkPanicMessageWithDecl(v___x_2374_, v___x_2373_, v___x_2372_, v___x_2371_, v___x_2370_);
return v___x_2375_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3(void){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2376_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2377_ = lean_unsigned_to_nat(41u);
v___x_2378_ = lean_unsigned_to_nat(221u);
v___x_2379_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2380_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2381_ = l_mkPanicMessageWithDecl(v___x_2380_, v___x_2379_, v___x_2378_, v___x_2377_, v___x_2376_);
return v___x_2381_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2382_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2383_ = lean_unsigned_to_nat(31u);
v___x_2384_ = lean_unsigned_to_nat(226u);
v___x_2385_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2386_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2387_ = l_mkPanicMessageWithDecl(v___x_2386_, v___x_2385_, v___x_2384_, v___x_2383_, v___x_2382_);
return v___x_2387_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5(void){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2388_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2389_ = lean_unsigned_to_nat(41u);
v___x_2390_ = lean_unsigned_to_nat(225u);
v___x_2391_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2392_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2393_ = l_mkPanicMessageWithDecl(v___x_2392_, v___x_2391_, v___x_2390_, v___x_2389_, v___x_2388_);
return v___x_2393_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2394_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2395_ = lean_unsigned_to_nat(41u);
v___x_2396_ = lean_unsigned_to_nat(230u);
v___x_2397_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2398_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2399_ = l_mkPanicMessageWithDecl(v___x_2398_, v___x_2397_, v___x_2396_, v___x_2395_, v___x_2394_);
return v___x_2399_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7(void){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2400_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2401_ = lean_unsigned_to_nat(41u);
v___x_2402_ = lean_unsigned_to_nat(233u);
v___x_2403_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2404_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2405_ = l_mkPanicMessageWithDecl(v___x_2404_, v___x_2403_, v___x_2402_, v___x_2401_, v___x_2400_);
return v___x_2405_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8(void){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2406_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2407_ = lean_unsigned_to_nat(41u);
v___x_2408_ = lean_unsigned_to_nat(236u);
v___x_2409_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2410_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2411_ = l_mkPanicMessageWithDecl(v___x_2410_, v___x_2409_, v___x_2408_, v___x_2407_, v___x_2406_);
return v___x_2411_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9(void){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2412_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2413_ = lean_unsigned_to_nat(41u);
v___x_2414_ = lean_unsigned_to_nat(239u);
v___x_2415_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2416_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2417_ = l_mkPanicMessageWithDecl(v___x_2416_, v___x_2415_, v___x_2414_, v___x_2413_, v___x_2412_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t v_pu_2418_, lean_object* v_decl_2419_, uint8_t v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_){
_start:
{
switch(lean_obj_tag(v_decl_2419_))
{
case 0:
{
lean_object* v_decl_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2451_; 
v_decl_2427_ = lean_ctor_get(v_decl_2419_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v_decl_2419_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2429_ = v_decl_2419_;
v_isShared_2430_ = v_isSharedCheck_2451_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_decl_2427_);
lean_dec(v_decl_2419_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2451_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2431_; 
v___x_2431_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_2418_, v_decl_2427_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2442_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_2442_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2442_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 0, v_a_2432_);
v___x_2437_ = v___x_2429_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
lean_object* v___x_2439_; 
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 0, v___x_2437_);
v___x_2439_ = v___x_2434_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2437_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_del_object(v___x_2429_);
v_a_2443_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2431_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2431_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2476_; 
v_decl_2452_ = lean_ctor_get(v_decl_2419_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v_decl_2419_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2454_ = v_decl_2419_;
v_isShared_2455_ = v_isSharedCheck_2476_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_decl_2452_);
lean_dec(v_decl_2419_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2476_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2456_; 
v___x_2456_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2418_, v_decl_2452_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2467_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2459_ = v___x_2456_;
v_isShared_2460_ = v_isSharedCheck_2467_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2467_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v_a_2457_);
v___x_2462_ = v___x_2454_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
lean_object* v___x_2464_; 
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2462_);
v___x_2464_ = v___x_2459_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_del_object(v___x_2454_);
v_a_2468_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2456_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2456_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
}
case 2:
{
lean_object* v_decl_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2501_; 
v_decl_2477_ = lean_ctor_get(v_decl_2419_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v_decl_2419_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2479_ = v_decl_2419_;
v_isShared_2480_ = v_isSharedCheck_2501_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_decl_2477_);
lean_dec(v_decl_2419_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2501_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2418_, v_decl_2477_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2492_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2484_ = v___x_2481_;
v_isShared_2485_ = v_isSharedCheck_2492_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2481_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2492_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 0, v_a_2482_);
v___x_2487_ = v___x_2479_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
lean_object* v___x_2489_; 
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 0, v___x_2487_);
v___x_2489_ = v___x_2484_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2487_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_del_object(v___x_2479_);
v_a_2493_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2481_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2481_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_2502_; lean_object* v_i_2503_; lean_object* v_y_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2526_; 
v_fvarId_2502_ = lean_ctor_get(v_decl_2419_, 0);
v_i_2503_ = lean_ctor_get(v_decl_2419_, 1);
v_y_2504_ = lean_ctor_get(v_decl_2419_, 2);
v_isSharedCheck_2526_ = !lean_is_exclusive(v_decl_2419_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2506_ = v_decl_2419_;
v_isShared_2507_ = v_isSharedCheck_2526_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_y_2504_);
lean_inc(v_i_2503_);
lean_inc(v_fvarId_2502_);
lean_dec(v_decl_2419_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2526_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
uint8_t v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2508_ = 1;
v___x_2509_ = lean_st_ref_get(v_a_2421_);
v___x_2510_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2509_, v_fvarId_2502_, v___x_2508_);
lean_dec(v___x_2509_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_fvarId_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2523_; 
v_fvarId_2511_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2513_ = v___x_2510_;
v_isShared_2514_ = v_isSharedCheck_2523_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_fvarId_2511_);
lean_dec(v___x_2510_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2523_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2515_ = lean_st_ref_get(v_a_2421_);
v___x_2516_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2418_, v___x_2515_, v_y_2504_, v___x_2508_);
lean_dec(v___x_2515_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 2, v___x_2516_);
lean_ctor_set(v___x_2506_, 0, v_fvarId_2511_);
v___x_2518_ = v___x_2506_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_fvarId_2511_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_i_2503_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2520_; 
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 0, v___x_2518_);
v___x_2520_ = v___x_2513_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
else
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
lean_dec(v___x_2510_);
lean_del_object(v___x_2506_);
lean_dec(v_y_2504_);
lean_dec(v_i_2503_);
v___x_2524_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1);
v___x_2525_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2524_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
return v___x_2525_;
}
}
}
case 4:
{
lean_object* v_fvarId_2527_; lean_object* v_i_2528_; lean_object* v_y_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2554_; 
v_fvarId_2527_ = lean_ctor_get(v_decl_2419_, 0);
v_i_2528_ = lean_ctor_get(v_decl_2419_, 1);
v_y_2529_ = lean_ctor_get(v_decl_2419_, 2);
v_isSharedCheck_2554_ = !lean_is_exclusive(v_decl_2419_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2531_ = v_decl_2419_;
v_isShared_2532_ = v_isSharedCheck_2554_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_y_2529_);
lean_inc(v_i_2528_);
lean_inc(v_fvarId_2527_);
lean_dec(v_decl_2419_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2554_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
uint8_t v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = 1;
v___x_2534_ = lean_st_ref_get(v_a_2421_);
v___x_2535_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2534_, v_fvarId_2527_, v___x_2533_);
lean_dec(v___x_2534_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_fvarId_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v_fvarId_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_fvarId_2536_);
lean_dec_ref_known(v___x_2535_, 1);
v___x_2537_ = lean_st_ref_get(v_a_2421_);
v___x_2538_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2537_, v_y_2529_, v___x_2533_);
lean_dec(v___x_2537_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_fvarId_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2549_; 
v_fvarId_2539_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2541_ = v___x_2538_;
v_isShared_2542_ = v_isSharedCheck_2549_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_fvarId_2539_);
lean_dec(v___x_2538_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2549_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 2, v_fvarId_2539_);
lean_ctor_set(v___x_2531_, 0, v_fvarId_2536_);
v___x_2544_ = v___x_2531_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_fvarId_2536_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_i_2528_);
lean_ctor_set(v_reuseFailAlloc_2548_, 2, v_fvarId_2539_);
v___x_2544_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2546_; 
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2544_);
v___x_2546_ = v___x_2541_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2544_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
else
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
lean_dec(v___x_2538_);
lean_dec(v_fvarId_2536_);
lean_del_object(v___x_2531_);
lean_dec(v_i_2528_);
v___x_2550_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2);
v___x_2551_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2550_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
return v___x_2551_;
}
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_dec(v___x_2535_);
lean_del_object(v___x_2531_);
lean_dec(v_y_2529_);
lean_dec(v_i_2528_);
v___x_2552_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3);
v___x_2553_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2552_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
return v___x_2553_;
}
}
}
case 5:
{
lean_object* v_fvarId_2555_; lean_object* v_i_2556_; lean_object* v_offset_2557_; lean_object* v_y_2558_; lean_object* v_ty_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2586_; 
v_fvarId_2555_ = lean_ctor_get(v_decl_2419_, 0);
v_i_2556_ = lean_ctor_get(v_decl_2419_, 1);
v_offset_2557_ = lean_ctor_get(v_decl_2419_, 2);
v_y_2558_ = lean_ctor_get(v_decl_2419_, 3);
v_ty_2559_ = lean_ctor_get(v_decl_2419_, 4);
v_isSharedCheck_2586_ = !lean_is_exclusive(v_decl_2419_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2561_ = v_decl_2419_;
v_isShared_2562_ = v_isSharedCheck_2586_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_ty_2559_);
lean_inc(v_y_2558_);
lean_inc(v_offset_2557_);
lean_inc(v_i_2556_);
lean_inc(v_fvarId_2555_);
lean_dec(v_decl_2419_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2586_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
uint8_t v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2563_ = 1;
v___x_2564_ = lean_st_ref_get(v_a_2421_);
v___x_2565_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2564_, v_fvarId_2555_, v___x_2563_);
lean_dec(v___x_2564_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_fvarId_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v_fvarId_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_fvarId_2566_);
lean_dec_ref_known(v___x_2565_, 1);
v___x_2567_ = lean_st_ref_get(v_a_2421_);
v___x_2568_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2567_, v_y_2558_, v___x_2563_);
lean_dec(v___x_2567_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_fvarId_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2581_; 
v_fvarId_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2581_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_fvarId_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2581_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2576_; 
v___x_2573_ = lean_st_ref_get(v_a_2421_);
v___x_2574_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2418_, v___x_2573_, v___x_2563_, v_ty_2559_);
lean_dec(v___x_2573_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 4, v___x_2574_);
lean_ctor_set(v___x_2561_, 3, v_fvarId_2569_);
lean_ctor_set(v___x_2561_, 0, v_fvarId_2566_);
v___x_2576_ = v___x_2561_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_fvarId_2566_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_i_2556_);
lean_ctor_set(v_reuseFailAlloc_2580_, 2, v_offset_2557_);
lean_ctor_set(v_reuseFailAlloc_2580_, 3, v_fvarId_2569_);
lean_ctor_set(v_reuseFailAlloc_2580_, 4, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
lean_object* v___x_2578_; 
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 0, v___x_2576_);
v___x_2578_ = v___x_2571_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
else
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
lean_dec(v___x_2568_);
lean_dec(v_fvarId_2566_);
lean_del_object(v___x_2561_);
lean_dec_ref(v_ty_2559_);
lean_dec(v_offset_2557_);
lean_dec(v_i_2556_);
v___x_2582_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4);
v___x_2583_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2582_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
return v___x_2583_;
}
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
lean_dec(v___x_2565_);
lean_del_object(v___x_2561_);
lean_dec_ref(v_ty_2559_);
lean_dec(v_y_2558_);
lean_dec(v_offset_2557_);
lean_dec(v_i_2556_);
v___x_2584_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5);
v___x_2585_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2584_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
return v___x_2585_;
}
}
}
case 6:
{
lean_object* v_fvarId_2587_; lean_object* v_cidx_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2608_; 
v_fvarId_2587_ = lean_ctor_get(v_decl_2419_, 0);
v_cidx_2588_ = lean_ctor_get(v_decl_2419_, 1);
v_isSharedCheck_2608_ = !lean_is_exclusive(v_decl_2419_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2590_ = v_decl_2419_;
v_isShared_2591_ = v_isSharedCheck_2608_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_cidx_2588_);
lean_inc(v_fvarId_2587_);
lean_dec(v_decl_2419_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2608_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
uint8_t v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2592_ = 1;
v___x_2593_ = lean_st_ref_get(v_a_2421_);
v___x_2594_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2593_, v_fvarId_2587_, v___x_2592_);
lean_dec(v___x_2593_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_fvarId_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2605_; 
v_fvarId_2595_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2597_ = v___x_2594_;
v_isShared_2598_ = v_isSharedCheck_2605_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_fvarId_2595_);
lean_dec(v___x_2594_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2605_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v_fvarId_2595_);
v___x_2600_ = v___x_2590_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_fvarId_2595_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_cidx_2588_);
v___x_2600_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2602_; 
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v___x_2600_);
v___x_2602_ = v___x_2597_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
else
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
lean_dec(v___x_2594_);
lean_del_object(v___x_2590_);
lean_dec(v_cidx_2588_);
v___x_2606_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6);
v___x_2607_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2606_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
return v___x_2607_;
}
}
}
case 7:
{
lean_object* v_fvarId_2609_; lean_object* v_n_2610_; uint8_t v_check_2611_; uint8_t v_persistent_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2632_; 
v_fvarId_2609_ = lean_ctor_get(v_decl_2419_, 0);
v_n_2610_ = lean_ctor_get(v_decl_2419_, 1);
v_check_2611_ = lean_ctor_get_uint8(v_decl_2419_, sizeof(void*)*2);
v_persistent_2612_ = lean_ctor_get_uint8(v_decl_2419_, sizeof(void*)*2 + 1);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_decl_2419_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2614_ = v_decl_2419_;
v_isShared_2615_ = v_isSharedCheck_2632_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_n_2610_);
lean_inc(v_fvarId_2609_);
lean_dec(v_decl_2419_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2632_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
uint8_t v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2616_ = 1;
v___x_2617_ = lean_st_ref_get(v_a_2421_);
v___x_2618_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2617_, v_fvarId_2609_, v___x_2616_);
lean_dec(v___x_2617_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_fvarId_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2629_; 
v_fvarId_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2629_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_fvarId_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2629_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v_fvarId_2619_);
v___x_2624_ = v___x_2614_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_fvarId_2619_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v_n_2610_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, sizeof(void*)*2, v_check_2611_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, sizeof(void*)*2 + 1, v_persistent_2612_);
v___x_2624_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
lean_object* v___x_2626_; 
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2624_);
v___x_2626_ = v___x_2621_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
else
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
lean_dec(v___x_2618_);
lean_del_object(v___x_2614_);
lean_dec(v_n_2610_);
v___x_2630_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7);
v___x_2631_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2630_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
return v___x_2631_;
}
}
}
case 8:
{
lean_object* v_fvarId_2633_; lean_object* v_n_2634_; uint8_t v_check_2635_; uint8_t v_persistent_2636_; lean_object* v_objs_x3f_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2657_; 
v_fvarId_2633_ = lean_ctor_get(v_decl_2419_, 0);
v_n_2634_ = lean_ctor_get(v_decl_2419_, 1);
v_check_2635_ = lean_ctor_get_uint8(v_decl_2419_, sizeof(void*)*3);
v_persistent_2636_ = lean_ctor_get_uint8(v_decl_2419_, sizeof(void*)*3 + 1);
v_objs_x3f_2637_ = lean_ctor_get(v_decl_2419_, 2);
v_isSharedCheck_2657_ = !lean_is_exclusive(v_decl_2419_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2639_ = v_decl_2419_;
v_isShared_2640_ = v_isSharedCheck_2657_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_objs_x3f_2637_);
lean_inc(v_n_2634_);
lean_inc(v_fvarId_2633_);
lean_dec(v_decl_2419_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2657_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
uint8_t v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = 1;
v___x_2642_ = lean_st_ref_get(v_a_2421_);
v___x_2643_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2642_, v_fvarId_2633_, v___x_2641_);
lean_dec(v___x_2642_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_fvarId_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2654_; 
v_fvarId_2644_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2646_ = v___x_2643_;
v_isShared_2647_ = v_isSharedCheck_2654_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_fvarId_2644_);
lean_dec(v___x_2643_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2654_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v_fvarId_2644_);
v___x_2649_ = v___x_2639_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(8, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_fvarId_2644_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_n_2634_);
lean_ctor_set(v_reuseFailAlloc_2653_, 2, v_objs_x3f_2637_);
lean_ctor_set_uint8(v_reuseFailAlloc_2653_, sizeof(void*)*3, v_check_2635_);
lean_ctor_set_uint8(v_reuseFailAlloc_2653_, sizeof(void*)*3 + 1, v_persistent_2636_);
v___x_2649_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v___x_2651_; 
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v___x_2649_);
v___x_2651_ = v___x_2646_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
else
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
lean_dec(v___x_2643_);
lean_del_object(v___x_2639_);
lean_dec(v_objs_x3f_2637_);
lean_dec(v_n_2634_);
v___x_2655_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8);
v___x_2656_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2655_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
return v___x_2656_;
}
}
}
default: 
{
lean_object* v_fvarId_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2678_; 
v_fvarId_2658_ = lean_ctor_get(v_decl_2419_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_decl_2419_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2660_ = v_decl_2419_;
v_isShared_2661_ = v_isSharedCheck_2678_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_fvarId_2658_);
lean_dec(v_decl_2419_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2678_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
uint8_t v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2662_ = 1;
v___x_2663_ = lean_st_ref_get(v_a_2421_);
v___x_2664_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2663_, v_fvarId_2658_, v___x_2662_);
lean_dec(v___x_2663_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_fvarId_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2675_; 
v_fvarId_2665_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2667_ = v___x_2664_;
v_isShared_2668_ = v_isSharedCheck_2675_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_fvarId_2665_);
lean_dec(v___x_2664_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2675_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v_fvarId_2665_);
v___x_2670_ = v___x_2660_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_fvarId_2665_);
v___x_2670_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2672_; 
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v___x_2670_);
v___x_2672_ = v___x_2667_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
else
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
lean_dec(v___x_2664_);
lean_del_object(v___x_2660_);
v___x_2676_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9);
v___x_2677_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2676_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
return v___x_2677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(lean_object* v_pu_2679_, lean_object* v_decl_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_){
_start:
{
uint8_t v_pu_boxed_2688_; uint8_t v_a_boxed_2689_; lean_object* v_res_2690_; 
v_pu_boxed_2688_ = lean_unbox(v_pu_2679_);
v_a_boxed_2689_ = lean_unbox(v_a_2681_);
v_res_2690_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v_pu_boxed_2688_, v_decl_2680_, v_a_boxed_2689_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
lean_dec(v_a_2682_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t v_pu_2691_, lean_object* v_code_2692_, lean_object* v_s_2693_, uint8_t v_uniqueIdents_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = lean_st_mk_ref(v_s_2693_);
v___x_2701_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2691_, v_code_2692_, v_uniqueIdents_2694_, v___x_2700_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2710_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2704_ = v___x_2701_;
v_isShared_2705_ = v_isSharedCheck_2710_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2701_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2710_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2706_; lean_object* v___x_2708_; 
v___x_2706_ = lean_st_ref_get(v___x_2700_);
lean_dec(v___x_2700_);
lean_dec(v___x_2706_);
if (v_isShared_2705_ == 0)
{
v___x_2708_ = v___x_2704_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2702_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
else
{
lean_dec(v___x_2700_);
return v___x_2701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize___boxed(lean_object* v_pu_2711_, lean_object* v_code_2712_, lean_object* v_s_2713_, lean_object* v_uniqueIdents_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
uint8_t v_pu_boxed_2720_; uint8_t v_uniqueIdents_boxed_2721_; lean_object* v_res_2722_; 
v_pu_boxed_2720_ = lean_unbox(v_pu_2711_);
v_uniqueIdents_boxed_2721_ = lean_unbox(v_uniqueIdents_2714_);
v_res_2722_ = l_Lean_Compiler_LCNF_Code_internalize(v_pu_boxed_2720_, v_code_2712_, v_s_2713_, v_uniqueIdents_boxed_2721_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_);
lean_dec(v_a_2718_);
lean_dec_ref(v_a_2717_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(lean_object* v_f_2723_, lean_object* v_v_2724_, uint8_t v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
if (lean_obj_tag(v_v_2724_) == 0)
{
lean_object* v_code_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2757_; 
v_code_2732_ = lean_ctor_get(v_v_2724_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v_v_2724_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2734_ = v_v_2724_;
v_isShared_2735_ = v_isSharedCheck_2757_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_code_2732_);
lean_dec(v_v_2724_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2757_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = lean_box(v___y_2725_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
lean_inc(v___y_2728_);
lean_inc_ref(v___y_2727_);
lean_inc(v___y_2726_);
v___x_2737_ = lean_apply_8(v_f_2723_, v_code_2732_, v___x_2736_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, lean_box(0));
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2748_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2740_ = v___x_2737_;
v_isShared_2741_ = v_isSharedCheck_2748_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2737_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2748_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 0, v_a_2738_);
v___x_2743_ = v___x_2734_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
lean_object* v___x_2745_; 
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 0, v___x_2743_);
v___x_2745_ = v___x_2740_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2743_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
lean_del_object(v___x_2734_);
v_a_2749_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2737_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2737_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
}
else
{
lean_object* v___x_2758_; 
lean_dec_ref(v_f_2723_);
v___x_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2758_, 0, v_v_2724_);
return v___x_2758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg___boxed(lean_object* v_f_2759_, lean_object* v_v_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
uint8_t v___y_1412__boxed_2768_; lean_object* v_res_2769_; 
v___y_1412__boxed_2768_ = lean_unbox(v___y_2761_);
v_res_2769_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2759_, v_v_2760_, v___y_1412__boxed_2768_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(uint8_t v_pu_2770_, lean_object* v_f_2771_, lean_object* v_v_2772_, uint8_t v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2771_, v_v_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___boxed(lean_object* v_pu_2781_, lean_object* v_f_2782_, lean_object* v_v_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
uint8_t v_pu_boxed_2791_; uint8_t v___y_1488__boxed_2792_; lean_object* v_res_2793_; 
v_pu_boxed_2791_ = lean_unbox(v_pu_2781_);
v___y_1488__boxed_2792_ = lean_unbox(v___y_2784_);
v_res_2793_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(v_pu_boxed_2791_, v_f_2782_, v_v_2783_, v___y_1488__boxed_2792_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v___y_2785_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(uint8_t v_pu_2794_, lean_object* v_decl_2795_, uint8_t v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_toSignature_2803_; lean_object* v_value_2804_; uint8_t v_recursive_2805_; lean_object* v_inlineAttr_x3f_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2866_; 
v_toSignature_2803_ = lean_ctor_get(v_decl_2795_, 0);
v_value_2804_ = lean_ctor_get(v_decl_2795_, 1);
v_recursive_2805_ = lean_ctor_get_uint8(v_decl_2795_, sizeof(void*)*3);
v_inlineAttr_x3f_2806_ = lean_ctor_get(v_decl_2795_, 2);
v_isSharedCheck_2866_ = !lean_is_exclusive(v_decl_2795_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2808_ = v_decl_2795_;
v_isShared_2809_ = v_isSharedCheck_2866_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_inlineAttr_x3f_2806_);
lean_inc(v_value_2804_);
lean_inc(v_toSignature_2803_);
lean_dec(v_decl_2795_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2866_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v_name_2810_; lean_object* v_levelParams_2811_; lean_object* v_type_2812_; lean_object* v_params_2813_; uint8_t v_safe_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2865_; 
v_name_2810_ = lean_ctor_get(v_toSignature_2803_, 0);
v_levelParams_2811_ = lean_ctor_get(v_toSignature_2803_, 1);
v_type_2812_ = lean_ctor_get(v_toSignature_2803_, 2);
v_params_2813_ = lean_ctor_get(v_toSignature_2803_, 3);
v_safe_2814_ = lean_ctor_get_uint8(v_toSignature_2803_, sizeof(void*)*4);
v_isSharedCheck_2865_ = !lean_is_exclusive(v_toSignature_2803_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2816_ = v_toSignature_2803_;
v_isShared_2817_ = v_isSharedCheck_2865_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_params_2813_);
lean_inc(v_type_2812_);
lean_inc(v_levelParams_2811_);
lean_inc(v_name_2810_);
lean_dec(v_toSignature_2803_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2865_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2818_; 
v___x_2818_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2794_, v_type_2812_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; size_t v_sz_2820_; size_t v___x_2821_; lean_object* v___x_2822_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2818_, 1);
v_sz_2820_ = lean_array_size(v_params_2813_);
v___x_2821_ = ((size_t)0ULL);
v___x_2822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2794_, v_sz_2820_, v___x_2821_, v_params_2813_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref_known(v___x_2822_, 1);
v___x_2824_ = lean_box(v_pu_2794_);
v___x_2825_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed), 9, 1);
lean_closure_set(v___x_2825_, 0, v___x_2824_);
v___x_2826_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v___x_2825_, v_value_2804_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2840_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2829_ = v___x_2826_;
v_isShared_2830_ = v_isSharedCheck_2840_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2826_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2840_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 3, v_a_2823_);
lean_ctor_set(v___x_2816_, 2, v_a_2819_);
v___x_2832_ = v___x_2816_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_name_2810_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_levelParams_2811_);
lean_ctor_set(v_reuseFailAlloc_2839_, 2, v_a_2819_);
lean_ctor_set(v_reuseFailAlloc_2839_, 3, v_a_2823_);
lean_ctor_set_uint8(v_reuseFailAlloc_2839_, sizeof(void*)*4, v_safe_2814_);
v___x_2832_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
lean_object* v___x_2834_; 
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 1, v_a_2827_);
lean_ctor_set(v___x_2808_, 0, v___x_2832_);
v___x_2834_ = v___x_2808_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v___x_2832_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_a_2827_);
lean_ctor_set(v_reuseFailAlloc_2838_, 2, v_inlineAttr_x3f_2806_);
lean_ctor_set_uint8(v_reuseFailAlloc_2838_, sizeof(void*)*3, v_recursive_2805_);
v___x_2834_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
lean_object* v___x_2836_; 
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v___x_2834_);
v___x_2836_ = v___x_2829_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2834_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
lean_dec(v_a_2823_);
lean_dec(v_a_2819_);
lean_del_object(v___x_2816_);
lean_dec(v_levelParams_2811_);
lean_dec(v_name_2810_);
lean_del_object(v___x_2808_);
lean_dec(v_inlineAttr_x3f_2806_);
v_a_2841_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2826_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2826_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_dec(v_a_2819_);
lean_del_object(v___x_2816_);
lean_dec(v_levelParams_2811_);
lean_dec(v_name_2810_);
lean_del_object(v___x_2808_);
lean_dec(v_inlineAttr_x3f_2806_);
lean_dec_ref(v_value_2804_);
v_a_2849_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2822_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2822_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_del_object(v___x_2816_);
lean_dec_ref(v_params_2813_);
lean_dec(v_levelParams_2811_);
lean_dec(v_name_2810_);
lean_del_object(v___x_2808_);
lean_dec(v_inlineAttr_x3f_2806_);
lean_dec_ref(v_value_2804_);
v_a_2857_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2818_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2818_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go___boxed(lean_object* v_pu_2867_, lean_object* v_decl_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_){
_start:
{
uint8_t v_pu_boxed_2876_; uint8_t v_a_boxed_2877_; lean_object* v_res_2878_; 
v_pu_boxed_2876_ = lean_unbox(v_pu_2867_);
v_a_boxed_2877_ = lean_unbox(v_a_2869_);
v_res_2878_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_boxed_2876_, v_decl_2868_, v_a_boxed_2877_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
lean_dec(v_a_2874_);
lean_dec_ref(v_a_2873_);
lean_dec(v_a_2872_);
lean_dec_ref(v_a_2871_);
lean_dec(v_a_2870_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t v_pu_2879_, lean_object* v_decl_2880_, lean_object* v_s_2881_, uint8_t v_uniqueIdents_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2888_ = lean_st_mk_ref(v_s_2881_);
v___x_2889_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_2879_, v_decl_2880_, v_uniqueIdents_2882_, v___x_2888_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2898_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2892_ = v___x_2889_;
v_isShared_2893_ = v_isSharedCheck_2898_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2889_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2898_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2894_ = lean_st_ref_get(v___x_2888_);
lean_dec(v___x_2888_);
lean_dec(v___x_2894_);
if (v_isShared_2893_ == 0)
{
v___x_2896_ = v___x_2892_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2890_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
else
{
lean_dec(v___x_2888_);
return v___x_2889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize___boxed(lean_object* v_pu_2899_, lean_object* v_decl_2900_, lean_object* v_s_2901_, lean_object* v_uniqueIdents_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
uint8_t v_pu_boxed_2908_; uint8_t v_uniqueIdents_boxed_2909_; lean_object* v_res_2910_; 
v_pu_boxed_2908_ = lean_unbox(v_pu_2899_);
v_uniqueIdents_boxed_2909_ = lean_unbox(v_uniqueIdents_2902_);
v_res_2910_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_boxed_2908_, v_decl_2900_, v_s_2901_, v_uniqueIdents_boxed_2909_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
return v_res_2910_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2911_ = lean_box(0);
v___x_2912_ = lean_unsigned_to_nat(16u);
v___x_2913_ = lean_mk_array(v___x_2912_, v___x_2911_);
return v___x_2913_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2914_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0);
v___x_2915_ = lean_unsigned_to_nat(0u);
v___x_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2915_);
lean_ctor_set(v___x_2916_, 1, v___x_2914_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(uint8_t v_pu_2917_, size_t v_sz_2918_, size_t v_i_2919_, lean_object* v_bs_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
uint8_t v___x_2926_; 
v___x_2926_ = lean_usize_dec_lt(v_i_2919_, v_sz_2918_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; 
v___x_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2927_, 0, v_bs_2920_);
return v___x_2927_;
}
else
{
lean_object* v_v_2928_; lean_object* v___x_2929_; lean_object* v_bs_x27_2930_; lean_object* v___x_2931_; lean_object* v_lctx_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2957_; 
v_v_2928_ = lean_array_uget(v_bs_2920_, v_i_2919_);
v___x_2929_ = lean_unsigned_to_nat(0u);
v_bs_x27_2930_ = lean_array_uset(v_bs_2920_, v_i_2919_, v___x_2929_);
v___x_2931_ = lean_st_ref_take(v___y_2922_);
v_lctx_2932_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2957_ == 0)
{
lean_object* v_unused_2958_; 
v_unused_2958_ = lean_ctor_get(v___x_2931_, 1);
lean_dec(v_unused_2958_);
v___x_2934_ = v___x_2931_;
v_isShared_2935_ = v_isSharedCheck_2957_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_lctx_2932_);
lean_dec(v___x_2931_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2957_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2936_; lean_object* v___x_2938_; 
v___x_2936_ = lean_unsigned_to_nat(1u);
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 1, v___x_2936_);
v___x_2938_ = v___x_2934_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_lctx_2932_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v___x_2936_);
v___x_2938_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; lean_object* v___x_2942_; 
v___x_2939_ = lean_st_ref_put(v___y_2922_, v___x_2938_);
v___x_2940_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_2941_ = 0;
v___x_2942_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_2917_, v_v_2928_, v___x_2940_, v___x_2941_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; size_t v___x_2944_; size_t v___x_2945_; lean_object* v___x_2946_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
lean_dec_ref_known(v___x_2942_, 1);
v___x_2944_ = ((size_t)1ULL);
v___x_2945_ = lean_usize_add(v_i_2919_, v___x_2944_);
v___x_2946_ = lean_array_uset(v_bs_x27_2930_, v_i_2919_, v_a_2943_);
v_i_2919_ = v___x_2945_;
v_bs_2920_ = v___x_2946_;
goto _start;
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
lean_dec_ref(v_bs_x27_2930_);
v_a_2948_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2942_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2942_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___boxed(lean_object* v_pu_2959_, lean_object* v_sz_2960_, lean_object* v_i_2961_, lean_object* v_bs_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
uint8_t v_pu_boxed_2968_; size_t v_sz_boxed_2969_; size_t v_i_boxed_2970_; lean_object* v_res_2971_; 
v_pu_boxed_2968_ = lean_unbox(v_pu_2959_);
v_sz_boxed_2969_ = lean_unbox_usize(v_sz_2960_);
lean_dec(v_sz_2960_);
v_i_boxed_2970_ = lean_unbox_usize(v_i_2961_);
lean_dec(v_i_2961_);
v_res_2971_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_boxed_2968_, v_sz_boxed_2969_, v_i_boxed_2970_, v_bs_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
return v_res_2971_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__0(void){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_2973_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
lean_ctor_set(v___x_2973_, 2, v___x_2972_);
lean_ctor_set(v___x_2973_, 3, v___x_2972_);
lean_ctor_set(v___x_2973_, 4, v___x_2972_);
lean_ctor_set(v___x_2973_, 5, v___x_2972_);
return v___x_2973_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__1(void){
_start:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2974_ = lean_unsigned_to_nat(1u);
v___x_2975_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__0, &l_Lean_Compiler_LCNF_cleanup___closed__0_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__0);
v___x_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
lean_ctor_set(v___x_2976_, 1, v___x_2974_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup(uint8_t v_pu_2977_, lean_object* v_decl_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; size_t v_sz_2987_; size_t v___x_2988_; lean_object* v___x_2989_; 
v___x_2984_ = lean_st_ref_take(v_a_2980_);
lean_dec(v___x_2984_);
v___x_2985_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
v___x_2986_ = lean_st_ref_put(v_a_2980_, v___x_2985_);
v_sz_2987_ = lean_array_size(v_decl_2978_);
v___x_2988_ = ((size_t)0ULL);
v___x_2989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_2977_, v_sz_2987_, v___x_2988_, v_decl_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup___boxed(lean_object* v_pu_2990_, lean_object* v_decl_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
uint8_t v_pu_boxed_2997_; lean_object* v_res_2998_; 
v_pu_boxed_2997_ = lean_unbox(v_pu_2990_);
v_res_2998_ = l_Lean_Compiler_LCNF_cleanup(v_pu_boxed_2997_, v_decl_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(lean_object* v_a_2999_, lean_object* v_ngen_3000_, lean_object* v_a_x3f_3001_){
_start:
{
lean_object* v___x_3003_; lean_object* v_env_3004_; lean_object* v_nextMacroScope_3005_; lean_object* v_auxDeclNGen_3006_; lean_object* v_traceState_3007_; lean_object* v_cache_3008_; lean_object* v_messages_3009_; lean_object* v_infoState_3010_; lean_object* v_snapshotTasks_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3021_; 
v___x_3003_ = lean_st_ref_take(v_a_2999_);
v_env_3004_ = lean_ctor_get(v___x_3003_, 0);
v_nextMacroScope_3005_ = lean_ctor_get(v___x_3003_, 1);
v_auxDeclNGen_3006_ = lean_ctor_get(v___x_3003_, 3);
v_traceState_3007_ = lean_ctor_get(v___x_3003_, 4);
v_cache_3008_ = lean_ctor_get(v___x_3003_, 5);
v_messages_3009_ = lean_ctor_get(v___x_3003_, 6);
v_infoState_3010_ = lean_ctor_get(v___x_3003_, 7);
v_snapshotTasks_3011_ = lean_ctor_get(v___x_3003_, 8);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3021_ == 0)
{
lean_object* v_unused_3022_; 
v_unused_3022_ = lean_ctor_get(v___x_3003_, 2);
lean_dec(v_unused_3022_);
v___x_3013_ = v___x_3003_;
v_isShared_3014_ = v_isSharedCheck_3021_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_snapshotTasks_3011_);
lean_inc(v_infoState_3010_);
lean_inc(v_messages_3009_);
lean_inc(v_cache_3008_);
lean_inc(v_traceState_3007_);
lean_inc(v_auxDeclNGen_3006_);
lean_inc(v_nextMacroScope_3005_);
lean_inc(v_env_3004_);
lean_dec(v___x_3003_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3021_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3015_; lean_object* v___x_3017_; 
v___x_3015_ = lean_box(0);
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 2, v_ngen_3000_);
v___x_3017_ = v___x_3013_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_env_3004_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v_nextMacroScope_3005_);
lean_ctor_set(v_reuseFailAlloc_3020_, 2, v_ngen_3000_);
lean_ctor_set(v_reuseFailAlloc_3020_, 3, v_auxDeclNGen_3006_);
lean_ctor_set(v_reuseFailAlloc_3020_, 4, v_traceState_3007_);
lean_ctor_set(v_reuseFailAlloc_3020_, 5, v_cache_3008_);
lean_ctor_set(v_reuseFailAlloc_3020_, 6, v_messages_3009_);
lean_ctor_set(v_reuseFailAlloc_3020_, 7, v_infoState_3010_);
lean_ctor_set(v_reuseFailAlloc_3020_, 8, v_snapshotTasks_3011_);
v___x_3017_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = lean_st_ref_put(v_a_2999_, v___x_3017_);
v___x_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3015_);
return v___x_3019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0___boxed(lean_object* v_a_3023_, lean_object* v_ngen_3024_, lean_object* v_a_x3f_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3023_, v_ngen_3024_, v_a_x3f_3025_);
lean_dec(v_a_x3f_3025_);
lean_dec(v_a_3023_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(uint8_t v_pu_3034_, lean_object* v_decl_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v___x_3039_; lean_object* v_ngen_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v_env_3043_; lean_object* v_nextMacroScope_3044_; lean_object* v_auxDeclNGen_3045_; lean_object* v_traceState_3046_; lean_object* v_cache_3047_; lean_object* v_messages_3048_; lean_object* v_infoState_3049_; lean_object* v_snapshotTasks_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3094_; 
v___x_3039_ = lean_st_ref_get(v_a_3037_);
v_ngen_3040_ = lean_ctor_get(v___x_3039_, 2);
lean_inc_ref(v_ngen_3040_);
lean_dec(v___x_3039_);
v___x_3041_ = ((lean_object*)(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2));
v___x_3042_ = lean_st_ref_take(v_a_3037_);
v_env_3043_ = lean_ctor_get(v___x_3042_, 0);
v_nextMacroScope_3044_ = lean_ctor_get(v___x_3042_, 1);
v_auxDeclNGen_3045_ = lean_ctor_get(v___x_3042_, 3);
v_traceState_3046_ = lean_ctor_get(v___x_3042_, 4);
v_cache_3047_ = lean_ctor_get(v___x_3042_, 5);
v_messages_3048_ = lean_ctor_get(v___x_3042_, 6);
v_infoState_3049_ = lean_ctor_get(v___x_3042_, 7);
v_snapshotTasks_3050_ = lean_ctor_get(v___x_3042_, 8);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3094_ == 0)
{
lean_object* v_unused_3095_; 
v_unused_3095_ = lean_ctor_get(v___x_3042_, 2);
lean_dec(v_unused_3095_);
v___x_3052_ = v___x_3042_;
v_isShared_3053_ = v_isSharedCheck_3094_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_snapshotTasks_3050_);
lean_inc(v_infoState_3049_);
lean_inc(v_messages_3048_);
lean_inc(v_cache_3047_);
lean_inc(v_traceState_3046_);
lean_inc(v_auxDeclNGen_3045_);
lean_inc(v_nextMacroScope_3044_);
lean_inc(v_env_3043_);
lean_dec(v___x_3042_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3094_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 2, v___x_3041_);
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_env_3043_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v_nextMacroScope_3044_);
lean_ctor_set(v_reuseFailAlloc_3093_, 2, v___x_3041_);
lean_ctor_set(v_reuseFailAlloc_3093_, 3, v_auxDeclNGen_3045_);
lean_ctor_set(v_reuseFailAlloc_3093_, 4, v_traceState_3046_);
lean_ctor_set(v_reuseFailAlloc_3093_, 5, v_cache_3047_);
lean_ctor_set(v_reuseFailAlloc_3093_, 6, v_messages_3048_);
lean_ctor_set(v_reuseFailAlloc_3093_, 7, v_infoState_3049_);
lean_ctor_set(v_reuseFailAlloc_3093_, 8, v_snapshotTasks_3050_);
v___x_3055_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; uint8_t v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; uint8_t v___x_3063_; lean_object* v_r_3064_; 
v___x_3056_ = lean_st_ref_put(v_a_3037_, v___x_3055_);
v___x_3057_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_3058_ = 0;
v___x_3059_ = lean_box(v_pu_3034_);
v___x_3060_ = lean_box(v___x_3058_);
v___x_3061_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_internalize___boxed), 9, 4);
lean_closure_set(v___x_3061_, 0, v___x_3059_);
lean_closure_set(v___x_3061_, 1, v_decl_3035_);
lean_closure_set(v___x_3061_, 2, v___x_3057_);
lean_closure_set(v___x_3061_, 3, v___x_3060_);
v___x_3062_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
v___x_3063_ = 0;
v_r_3064_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v___x_3061_, v___x_3062_, v___x_3063_, v_a_3036_, v_a_3037_);
if (lean_obj_tag(v_r_3064_) == 0)
{
lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3081_; 
v_a_3065_ = lean_ctor_get(v_r_3064_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v_r_3064_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3067_ = v_r_3064_;
v_isShared_3068_ = v_isSharedCheck_3081_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v_r_3064_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3081_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
lean_inc(v_a_3065_);
if (v_isShared_3068_ == 0)
{
lean_ctor_set_tag(v___x_3067_, 1);
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3065_);
v___x_3070_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
v___x_3071_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3037_, v_ngen_3040_, v___x_3070_);
lean_dec_ref(v___x_3070_);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3078_ == 0)
{
lean_object* v_unused_3079_; 
v_unused_3079_ = lean_ctor_get(v___x_3071_, 0);
lean_dec(v_unused_3079_);
v___x_3073_ = v___x_3071_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_dec(v___x_3071_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 0, v_a_3065_);
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3065_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
v_a_3082_ = lean_ctor_get(v_r_3064_, 0);
lean_inc(v_a_3082_);
lean_dec_ref_known(v_r_3064_, 1);
v___x_3083_ = lean_box(0);
v___x_3084_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3037_, v_ngen_3040_, v___x_3083_);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3091_ == 0)
{
lean_object* v_unused_3092_; 
v_unused_3092_ = lean_ctor_get(v___x_3084_, 0);
lean_dec(v_unused_3092_);
v___x_3086_ = v___x_3084_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_dec(v___x_3084_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
lean_ctor_set_tag(v___x_3086_, 1);
lean_ctor_set(v___x_3086_, 0, v_a_3082_);
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3082_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___boxed(lean_object* v_pu_3096_, lean_object* v_decl_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
uint8_t v_pu_boxed_3101_; lean_object* v_res_3102_; 
v_pu_boxed_3101_ = lean_unbox(v_pu_3096_);
v_res_3102_ = l_Lean_Compiler_LCNF_normalizeFVarIds(v_pu_boxed_3101_, v_decl_3097_, v_a_3098_, v_a_3099_);
lean_dec(v_a_3099_);
lean_dec_ref(v_a_3098_);
return v_res_3102_;
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
