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
lean_object* lean_obj_tag_nat(lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___redArg(lean_object* v_x_1_, lean_object* v_state_2_, uint8_t v_ctx_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_){
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v_state_2_ = stack[1].m_obj;
uint8_t v_ctx_3_ = stack[2].m_num;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_res_30_;
v_res_30_ = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___redArg(v_x_1_, v_state_2_, v_ctx_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_);
stack->m_obj
 = v_res_30_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___redArg___boxed(lean_object* v_x_31_, lean_object* v_state_32_, lean_object* v_ctx_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_){
_start:
{
uint8_t v_ctx_boxed_39_; lean_object* v_res_40_; 
v_ctx_boxed_39_ = lean_unbox(v_ctx_33_);
v_res_40_ = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___redArg(v_x_31_, v_state_32_, v_ctx_boxed_39_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
return v_res_40_;
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run(uint8_t v_pu_41_, lean_object* v_00_u03b1_42_, lean_object* v_x_43_, lean_object* v_state_44_, uint8_t v_ctx_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_st_mk_ref(v_state_44_);
v___x_52_ = lean_box(v_ctx_45_);
lean_inc(v_a_49_);
lean_inc_ref(v_a_48_);
lean_inc(v_a_47_);
lean_inc_ref(v_a_46_);
lean_inc(v___x_51_);
v___x_53_ = lean_apply_7(v_x_43_, v___x_52_, v___x_51_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, lean_box(0));
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_63_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_63_ == 0)
{
v___x_56_ = v___x_53_;
v_isShared_57_ = v_isSharedCheck_63_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_53_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_63_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_61_; 
v___x_58_ = lean_st_ref_get(v___x_51_);
lean_dec(v___x_51_);
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v_a_54_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 0, v___x_59_);
v___x_61_ = v___x_56_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_59_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
else
{
lean_object* v_a_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_71_; 
lean_dec(v___x_51_);
v_a_64_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_71_ == 0)
{
v___x_66_ = v___x_53_;
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v___x_53_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_69_; 
if (v_isShared_67_ == 0)
{
v___x_69_ = v___x_66_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_a_64_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_41_ = stack[0].m_num;
lean_object* v_x_43_ = stack[2].m_obj;
lean_object* v_state_44_ = stack[3].m_obj;
uint8_t v_ctx_45_ = stack[4].m_num;
lean_object* v_a_46_ = stack[5].m_obj;
lean_object* v_a_47_ = stack[6].m_obj;
lean_object* v_a_48_ = stack[7].m_obj;
lean_object* v_a_49_ = stack[8].m_obj;
lean_object* v_res_72_;
v_res_72_ = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run(v_pu_41_, lean_box(0), v_x_43_, v_state_44_, v_ctx_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
stack->m_obj
 = v_res_72_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___boxed(lean_object* v_pu_73_, lean_object* v_00_u03b1_74_, lean_object* v_x_75_, lean_object* v_state_76_, lean_object* v_ctx_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
uint8_t v_pu_boxed_83_; uint8_t v_ctx_boxed_84_; lean_object* v_res_85_; 
v_pu_boxed_83_ = lean_unbox(v_pu_73_);
v_ctx_boxed_84_ = lean_unbox(v_ctx_77_);
v_res_85_ = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run(v_pu_boxed_83_, v_00_u03b1_74_, v_x_75_, v_state_76_, v_ctx_boxed_84_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
return v_res_85_;
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___redArg(lean_object* v_x_86_, lean_object* v_state_87_, uint8_t v_ctx_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_st_mk_ref(v_state_87_);
v___x_95_ = lean_box(v_ctx_88_);
lean_inc(v_a_92_);
lean_inc_ref(v_a_91_);
lean_inc(v_a_90_);
lean_inc_ref(v_a_89_);
lean_inc(v___x_94_);
v___x_96_ = lean_apply_7(v_x_86_, v___x_95_, v___x_94_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, lean_box(0));
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_105_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_105_ == 0)
{
v___x_99_ = v___x_96_;
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_96_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_101_ = lean_st_ref_get(v___x_94_);
lean_dec(v___x_94_);
lean_dec(v___x_101_);
if (v_isShared_100_ == 0)
{
v___x_103_ = v___x_99_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_a_97_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
else
{
lean_dec(v___x_94_);
return v___x_96_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_86_ = stack[0].m_obj;
lean_object* v_state_87_ = stack[1].m_obj;
uint8_t v_ctx_88_ = stack[2].m_num;
lean_object* v_a_89_ = stack[3].m_obj;
lean_object* v_a_90_ = stack[4].m_obj;
lean_object* v_a_91_ = stack[5].m_obj;
lean_object* v_a_92_ = stack[6].m_obj;
lean_object* v_res_106_;
v_res_106_ = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___redArg(v_x_86_, v_state_87_, v_ctx_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
stack->m_obj
 = v_res_106_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___redArg___boxed(lean_object* v_x_107_, lean_object* v_state_108_, lean_object* v_ctx_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
uint8_t v_ctx_boxed_115_; lean_object* v_res_116_; 
v_ctx_boxed_115_ = lean_unbox(v_ctx_109_);
v_res_116_ = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___redArg(v_x_107_, v_state_108_, v_ctx_boxed_115_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
return v_res_116_;
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27(uint8_t v_pu_117_, lean_object* v_00_u03b1_118_, lean_object* v_x_119_, lean_object* v_state_120_, uint8_t v_ctx_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = lean_st_mk_ref(v_state_120_);
v___x_128_ = lean_box(v_ctx_121_);
lean_inc(v_a_125_);
lean_inc_ref(v_a_124_);
lean_inc(v_a_123_);
lean_inc_ref(v_a_122_);
lean_inc(v___x_127_);
v___x_129_ = lean_apply_7(v_x_119_, v___x_128_, v___x_127_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, lean_box(0));
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_138_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_138_ == 0)
{
v___x_132_ = v___x_129_;
v_isShared_133_ = v_isSharedCheck_138_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_138_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_134_ = lean_st_ref_get(v___x_127_);
lean_dec(v___x_127_);
lean_dec(v___x_134_);
if (v_isShared_133_ == 0)
{
v___x_136_ = v___x_132_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_130_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
else
{
lean_dec(v___x_127_);
return v___x_129_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_117_ = stack[0].m_num;
lean_object* v_x_119_ = stack[2].m_obj;
lean_object* v_state_120_ = stack[3].m_obj;
uint8_t v_ctx_121_ = stack[4].m_num;
lean_object* v_a_122_ = stack[5].m_obj;
lean_object* v_a_123_ = stack[6].m_obj;
lean_object* v_a_124_ = stack[7].m_obj;
lean_object* v_a_125_ = stack[8].m_obj;
lean_object* v_res_139_;
v_res_139_ = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27(v_pu_117_, lean_box(0), v_x_119_, v_state_120_, v_ctx_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___boxed(lean_object* v_pu_140_, lean_object* v_00_u03b1_141_, lean_object* v_x_142_, lean_object* v_state_143_, lean_object* v_ctx_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
uint8_t v_pu_boxed_150_; uint8_t v_ctx_boxed_151_; lean_object* v_res_152_; 
v_pu_boxed_150_ = lean_unbox(v_pu_140_);
v_ctx_boxed_151_ = lean_unbox(v_ctx_144_);
v_res_152_ = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27(v_pu_boxed_150_, v_00_u03b1_141_, v_x_142_, v_state_143_, v_ctx_boxed_151_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
return v_res_152_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(lean_object* v_binderName_153_, uint8_t v_a_154_, lean_object* v_a_155_){
_start:
{
if (lean_obj_tag(v_binderName_153_) == 2)
{
lean_object* v_pre_157_; lean_object* v___x_158_; lean_object* v_lctx_159_; lean_object* v_nextIdx_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_172_; 
v_pre_157_ = lean_ctor_get(v_binderName_153_, 0);
lean_inc(v_pre_157_);
lean_dec_ref_known(v_binderName_153_, 2);
v___x_158_ = lean_st_ref_take(v_a_155_);
v_lctx_159_ = lean_ctor_get(v___x_158_, 0);
v_nextIdx_160_ = lean_ctor_get(v___x_158_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_172_ == 0)
{
v___x_162_ = v___x_158_;
v_isShared_163_ = v_isSharedCheck_172_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_nextIdx_160_);
lean_inc(v_lctx_159_);
lean_dec(v___x_158_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_172_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_164_ = lean_unsigned_to_nat(1u);
v___x_165_ = lean_nat_add(v_nextIdx_160_, v___x_164_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 1, v___x_165_);
v___x_167_ = v___x_162_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_lctx_159_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_165_);
v___x_167_ = v_reuseFailAlloc_171_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_st_ref_put(v_a_155_, v___x_167_);
v___x_169_ = l_Lean_Name_num___override(v_pre_157_, v_nextIdx_160_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
}
}
else
{
if (v_a_154_ == 0)
{
lean_object* v___x_173_; 
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v_binderName_153_);
return v___x_173_;
}
else
{
lean_object* v___x_174_; lean_object* v_lctx_175_; lean_object* v_nextIdx_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_188_; 
v___x_174_ = lean_st_ref_take(v_a_155_);
v_lctx_175_ = lean_ctor_get(v___x_174_, 0);
v_nextIdx_176_ = lean_ctor_get(v___x_174_, 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_188_ == 0)
{
v___x_178_ = v___x_174_;
v_isShared_179_ = v_isSharedCheck_188_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_nextIdx_176_);
lean_inc(v_lctx_175_);
lean_dec(v___x_174_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_188_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_add(v_nextIdx_176_, v___x_180_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v___x_181_);
v___x_183_ = v___x_178_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_lctx_175_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_181_);
v___x_183_ = v_reuseFailAlloc_187_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = lean_st_ref_put(v_a_155_, v___x_183_);
v___x_185_ = l_Lean_Name_num___override(v_binderName_153_, v_nextIdx_176_);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderName_153_ = stack[0].m_obj;
uint8_t v_a_154_ = stack[1].m_num;
lean_object* v_a_155_ = stack[2].m_obj;
lean_object* v_res_189_;
v_res_189_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_153_, v_a_154_, v_a_155_);
stack->m_obj
 = v_res_189_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg___boxed(lean_object* v_binderName_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
uint8_t v_a_boxed_194_; lean_object* v_res_195_; 
v_a_boxed_194_ = lean_unbox(v_a_191_);
v_res_195_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_190_, v_a_boxed_194_, v_a_192_);
lean_dec(v_a_192_);
return v_res_195_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName(uint8_t v_pu_196_, lean_object* v_binderName_197_, uint8_t v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_197_, v_a_198_, v_a_201_);
return v___x_205_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_196_ = stack[0].m_num;
lean_object* v_binderName_197_ = stack[1].m_obj;
uint8_t v_a_198_ = stack[2].m_num;
lean_object* v_a_199_ = stack[3].m_obj;
lean_object* v_a_200_ = stack[4].m_obj;
lean_object* v_a_201_ = stack[5].m_obj;
lean_object* v_a_202_ = stack[6].m_obj;
lean_object* v_a_203_ = stack[7].m_obj;
lean_object* v_res_206_;
v_res_206_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName(v_pu_196_, v_binderName_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
stack->m_obj
 = v_res_206_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___boxed(lean_object* v_pu_207_, lean_object* v_binderName_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
uint8_t v_pu_boxed_216_; uint8_t v_a_boxed_217_; lean_object* v_res_218_; 
v_pu_boxed_216_ = lean_unbox(v_pu_207_);
v_a_boxed_217_ = lean_unbox(v_a_209_);
v_res_218_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName(v_pu_boxed_216_, v_binderName_208_, v_a_boxed_217_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
return v_res_218_;
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___lam__0(uint8_t v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_st_ref_get(v___y_220_);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_219_ = stack[0].m_num;
lean_object* v___y_220_ = stack[1].m_obj;
lean_object* v___y_221_ = stack[2].m_obj;
lean_object* v___y_222_ = stack[3].m_obj;
lean_object* v___y_223_ = stack[4].m_obj;
lean_object* v___y_224_ = stack[5].m_obj;
lean_object* v_res_228_;
v_res_228_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___lam__0(v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
stack->m_obj
 = v_res_228_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___lam__0___boxed(lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
uint8_t v___y_199__boxed_236_; lean_object* v_res_237_; 
v___y_199__boxed_236_ = lean_unbox(v___y_229_);
v_res_237_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___lam__0(v___y_199__boxed_236_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
return v_res_237_;
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg(){
_start:
{
lean_object* v___f_240_; 
v___f_240_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___closed__0));
return v___f_240_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_241_;
v_res_241_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg();
stack->m_obj
 = v_res_241_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___boxed(lean_object* v___dummy_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg();
return v_res_243_;
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue(uint8_t v_pu_244_){
_start:
{
lean_object* v___f_245_; 
v___f_245_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___redArg___closed__0));
return v___f_245_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_244_ = stack[0].m_num;
lean_object* v_res_246_;
v_res_246_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue(v_pu_244_);
stack->m_obj
 = v_res_246_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___boxed(lean_object* v_pu_247_){
_start:
{
uint8_t v_pu_boxed_248_; lean_object* v_res_249_; 
v_pu_boxed_248_ = lean_unbox(v_pu_247_);
v_res_249_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue(v_pu_boxed_248_);
return v_res_249_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__11(void){
_start:
{
lean_object* v___f_271_; lean_object* v___x_272_; 
v___f_271_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__10));
v___x_272_ = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(v___f_271_);
return v___x_272_;
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg(){
_start:
{
lean_object* v___f_274_; lean_object* v___x_275_; lean_object* v_get_276_; lean_object* v_set_277_; lean_object* v_modifyGet_278_; lean_object* v___f_279_; lean_object* v___f_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___f_274_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__0));
v___x_275_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__11, &l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__11_once, _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___closed__11);
v_get_276_ = lean_ctor_get(v___x_275_, 0);
v_set_277_ = lean_ctor_get(v___x_275_, 1);
v_modifyGet_278_ = lean_ctor_get(v___x_275_, 2);
lean_inc(v_set_277_);
v___f_279_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_279_, 0, v_set_277_);
lean_closure_set(v___f_279_, 1, v___f_274_);
lean_inc(v_modifyGet_278_);
v___f_280_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_280_, 0, v_modifyGet_278_);
lean_closure_set(v___f_280_, 1, v___f_274_);
lean_inc(v_get_276_);
v___x_281_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___x_281_, 0, lean_box(0));
lean_closure_set(v___x_281_, 1, v_get_276_);
v___x_282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___f_279_);
lean_ctor_set(v___x_282_, 2, v___f_280_);
v___x_283_ = l_instMonadStateOfMonadStateOf___redArg(v___x_282_);
v___x_284_ = lean_alloc_closure((void*)(l_modify), 4, 3);
lean_closure_set(v___x_284_, 0, lean_box(0));
lean_closure_set(v___x_284_, 1, lean_box(0));
lean_closure_set(v___x_284_, 2, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_285_;
v_res_285_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg();
stack->m_obj
 = v_res_285_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg___boxed(lean_object* v___dummy_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg();
return v_res_287_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0(void){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___redArg();
return v___x_288_;
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM(uint8_t v_pu_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0, &l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0_once, _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0);
return v___x_290_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_289_ = stack[0].m_num;
lean_object* v_res_291_;
v_res_291_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM(v_pu_289_);
stack->m_obj
 = v_res_291_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___boxed(lean_object* v_pu_292_){
_start:
{
uint8_t v_pu_boxed_293_; lean_object* v_res_294_; 
v_pu_boxed_293_ = lean_unbox(v_pu_292_);
v_res_294_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM(v_pu_boxed_293_);
return v_res_294_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(lean_object* v_a_295_, lean_object* v_x_296_){
_start:
{
if (lean_obj_tag(v_x_296_) == 0)
{
uint8_t v___x_297_; 
v___x_297_ = 0;
return v___x_297_;
}
else
{
lean_object* v_key_298_; lean_object* v_tail_299_; uint8_t v___x_300_; 
v_key_298_ = lean_ctor_get(v_x_296_, 0);
v_tail_299_ = lean_ctor_get(v_x_296_, 2);
v___x_300_ = l_Lean_instBEqFVarId_beq(v_key_298_, v_a_295_);
if (v___x_300_ == 0)
{
v_x_296_ = v_tail_299_;
goto _start;
}
else
{
return v___x_300_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_295_ = stack[0].m_obj;
lean_object* v_x_296_ = stack[1].m_obj;
uint8_t v_res_302_;
v_res_302_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_a_295_, v_x_296_);
stack->m_num = v_res_302_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg___boxed(lean_object* v_a_303_, lean_object* v_x_304_){
_start:
{
uint8_t v_res_305_; lean_object* v_r_306_; 
v_res_305_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_a_303_, v_x_304_);
lean_dec(v_x_304_);
lean_dec(v_a_303_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(lean_object* v_a_307_, lean_object* v_b_308_, lean_object* v_x_309_){
_start:
{
if (lean_obj_tag(v_x_309_) == 0)
{
lean_dec(v_b_308_);
lean_dec(v_a_307_);
return v_x_309_;
}
else
{
lean_object* v_key_310_; lean_object* v_value_311_; lean_object* v_tail_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_324_; 
v_key_310_ = lean_ctor_get(v_x_309_, 0);
v_value_311_ = lean_ctor_get(v_x_309_, 1);
v_tail_312_ = lean_ctor_get(v_x_309_, 2);
v_isSharedCheck_324_ = !lean_is_exclusive(v_x_309_);
if (v_isSharedCheck_324_ == 0)
{
v___x_314_ = v_x_309_;
v_isShared_315_ = v_isSharedCheck_324_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_tail_312_);
lean_inc(v_value_311_);
lean_inc(v_key_310_);
lean_dec(v_x_309_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_324_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
uint8_t v___x_316_; 
v___x_316_ = l_Lean_instBEqFVarId_beq(v_key_310_, v_a_307_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(v_a_307_, v_b_308_, v_tail_312_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 2, v___x_317_);
v___x_319_ = v___x_314_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_key_310_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_value_311_);
lean_ctor_set(v_reuseFailAlloc_320_, 2, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
else
{
lean_object* v___x_322_; 
lean_dec(v_value_311_);
lean_dec(v_key_310_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v_b_308_);
lean_ctor_set(v___x_314_, 0, v_a_307_);
v___x_322_ = v___x_314_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_307_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_b_308_);
lean_ctor_set(v_reuseFailAlloc_323_, 2, v_tail_312_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
if (lean_obj_tag(v_x_326_) == 0)
{
return v_x_325_;
}
else
{
lean_object* v_key_327_; lean_object* v_value_328_; lean_object* v_tail_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_352_; 
v_key_327_ = lean_ctor_get(v_x_326_, 0);
v_value_328_ = lean_ctor_get(v_x_326_, 1);
v_tail_329_ = lean_ctor_get(v_x_326_, 2);
v_isSharedCheck_352_ = !lean_is_exclusive(v_x_326_);
if (v_isSharedCheck_352_ == 0)
{
v___x_331_ = v_x_326_;
v_isShared_332_ = v_isSharedCheck_352_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_tail_329_);
lean_inc(v_value_328_);
lean_inc(v_key_327_);
lean_dec(v_x_326_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_352_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; uint64_t v_fold_337_; uint64_t v___x_338_; uint64_t v___x_339_; uint64_t v___x_340_; size_t v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_333_ = lean_array_get_size(v_x_325_);
v___x_334_ = l_Lean_instHashableFVarId_hash(v_key_327_);
v___x_335_ = 32ULL;
v___x_336_ = lean_uint64_shift_right(v___x_334_, v___x_335_);
v_fold_337_ = lean_uint64_xor(v___x_334_, v___x_336_);
v___x_338_ = 16ULL;
v___x_339_ = lean_uint64_shift_right(v_fold_337_, v___x_338_);
v___x_340_ = lean_uint64_xor(v_fold_337_, v___x_339_);
v___x_341_ = lean_uint64_to_usize(v___x_340_);
v___x_342_ = lean_usize_of_nat(v___x_333_);
v___x_343_ = ((size_t)1ULL);
v___x_344_ = lean_usize_sub(v___x_342_, v___x_343_);
v___x_345_ = lean_usize_land(v___x_341_, v___x_344_);
v___x_346_ = lean_array_uget_borrowed(v_x_325_, v___x_345_);
lean_inc(v___x_346_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 2, v___x_346_);
v___x_348_ = v___x_331_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_key_327_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_value_328_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v___x_346_);
v___x_348_ = v_reuseFailAlloc_351_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v___x_349_; 
v___x_349_ = lean_array_uset(v_x_325_, v___x_345_, v___x_348_);
v_x_325_ = v___x_349_;
v_x_326_ = v_tail_329_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(lean_object* v_i_353_, lean_object* v_source_354_, lean_object* v_target_355_){
_start:
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = lean_array_get_size(v_source_354_);
v___x_357_ = lean_nat_dec_lt(v_i_353_, v___x_356_);
if (v___x_357_ == 0)
{
lean_dec_ref(v_source_354_);
lean_dec(v_i_353_);
return v_target_355_;
}
else
{
lean_object* v_es_358_; lean_object* v___x_359_; lean_object* v_source_360_; lean_object* v_target_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v_es_358_ = lean_array_fget(v_source_354_, v_i_353_);
v___x_359_ = lean_box(0);
v_source_360_ = lean_array_fset(v_source_354_, v_i_353_, v___x_359_);
v_target_361_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(v_target_355_, v_es_358_);
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_363_ = lean_nat_add(v_i_353_, v___x_362_);
lean_dec(v_i_353_);
v_i_353_ = v___x_363_;
v_source_354_ = v_source_360_;
v_target_355_ = v_target_361_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(lean_object* v_data_365_){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_nbuckets_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_366_ = lean_array_get_size(v_data_365_);
v___x_367_ = lean_unsigned_to_nat(2u);
v_nbuckets_368_ = lean_nat_mul(v___x_366_, v___x_367_);
v___x_369_ = lean_unsigned_to_nat(0u);
v___x_370_ = lean_box(0);
v___x_371_ = lean_mk_array(v_nbuckets_368_, v___x_370_);
v___x_372_ = lean_array_propagate_mark(v_data_365_, v___x_371_);
v___x_373_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(v___x_369_, v_data_365_, v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(lean_object* v_m_374_, lean_object* v_a_375_, lean_object* v_b_376_){
_start:
{
lean_object* v_size_377_; lean_object* v_buckets_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_421_; 
v_size_377_ = lean_ctor_get(v_m_374_, 0);
v_buckets_378_ = lean_ctor_get(v_m_374_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v_m_374_);
if (v_isSharedCheck_421_ == 0)
{
v___x_380_ = v_m_374_;
v_isShared_381_ = v_isSharedCheck_421_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_buckets_378_);
lean_inc(v_size_377_);
lean_dec(v_m_374_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_421_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; uint64_t v___x_383_; uint64_t v___x_384_; uint64_t v___x_385_; uint64_t v_fold_386_; uint64_t v___x_387_; uint64_t v___x_388_; uint64_t v___x_389_; size_t v___x_390_; size_t v___x_391_; size_t v___x_392_; size_t v___x_393_; size_t v___x_394_; lean_object* v_bkt_395_; uint8_t v___x_396_; 
v___x_382_ = lean_array_get_size(v_buckets_378_);
v___x_383_ = l_Lean_instHashableFVarId_hash(v_a_375_);
v___x_384_ = 32ULL;
v___x_385_ = lean_uint64_shift_right(v___x_383_, v___x_384_);
v_fold_386_ = lean_uint64_xor(v___x_383_, v___x_385_);
v___x_387_ = 16ULL;
v___x_388_ = lean_uint64_shift_right(v_fold_386_, v___x_387_);
v___x_389_ = lean_uint64_xor(v_fold_386_, v___x_388_);
v___x_390_ = lean_uint64_to_usize(v___x_389_);
v___x_391_ = lean_usize_of_nat(v___x_382_);
v___x_392_ = ((size_t)1ULL);
v___x_393_ = lean_usize_sub(v___x_391_, v___x_392_);
v___x_394_ = lean_usize_land(v___x_390_, v___x_393_);
v_bkt_395_ = lean_array_uget_borrowed(v_buckets_378_, v___x_394_);
v___x_396_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_a_375_, v_bkt_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v_size_x27_398_; lean_object* v___x_399_; lean_object* v_buckets_x27_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_397_ = lean_unsigned_to_nat(1u);
v_size_x27_398_ = lean_nat_add(v_size_377_, v___x_397_);
lean_dec(v_size_377_);
lean_inc(v_bkt_395_);
v___x_399_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_399_, 0, v_a_375_);
lean_ctor_set(v___x_399_, 1, v_b_376_);
lean_ctor_set(v___x_399_, 2, v_bkt_395_);
v_buckets_x27_400_ = lean_array_uset(v_buckets_378_, v___x_394_, v___x_399_);
v___x_401_ = lean_unsigned_to_nat(4u);
v___x_402_ = lean_nat_mul(v_size_x27_398_, v___x_401_);
v___x_403_ = lean_unsigned_to_nat(3u);
v___x_404_ = lean_nat_div(v___x_402_, v___x_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_array_get_size(v_buckets_x27_400_);
v___x_406_ = lean_nat_dec_le(v___x_404_, v___x_405_);
lean_dec(v___x_404_);
if (v___x_406_ == 0)
{
lean_object* v_val_407_; lean_object* v___x_409_; 
v_val_407_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(v_buckets_x27_400_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 1, v_val_407_);
lean_ctor_set(v___x_380_, 0, v_size_x27_398_);
v___x_409_ = v___x_380_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_size_x27_398_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_val_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
else
{
lean_object* v___x_412_; 
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 1, v_buckets_x27_400_);
lean_ctor_set(v___x_380_, 0, v_size_x27_398_);
v___x_412_ = v___x_380_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_size_x27_398_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_buckets_x27_400_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
else
{
lean_object* v___x_414_; lean_object* v_buckets_x27_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
lean_inc(v_bkt_395_);
v___x_414_ = lean_box(0);
v_buckets_x27_415_ = lean_array_uset(v_buckets_378_, v___x_394_, v___x_414_);
v___x_416_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(v_a_375_, v_b_376_, v_bkt_395_);
v___x_417_ = lean_array_uset(v_buckets_x27_415_, v___x_394_, v___x_416_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 1, v___x_417_);
v___x_419_ = v___x_380_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_size_377_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(lean_object* v___y_422_){
_start:
{
lean_object* v___x_424_; lean_object* v_ngen_425_; lean_object* v_namePrefix_426_; lean_object* v_idx_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_457_; 
v___x_424_ = lean_st_ref_get(v___y_422_);
v_ngen_425_ = lean_ctor_get(v___x_424_, 2);
lean_inc_ref(v_ngen_425_);
lean_dec(v___x_424_);
v_namePrefix_426_ = lean_ctor_get(v_ngen_425_, 0);
v_idx_427_ = lean_ctor_get(v_ngen_425_, 1);
v_isSharedCheck_457_ = !lean_is_exclusive(v_ngen_425_);
if (v_isSharedCheck_457_ == 0)
{
v___x_429_ = v_ngen_425_;
v_isShared_430_ = v_isSharedCheck_457_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_idx_427_);
lean_inc(v_namePrefix_426_);
lean_dec(v_ngen_425_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_457_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v_r_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_435_; 
lean_inc(v_idx_427_);
lean_inc(v_namePrefix_426_);
v_r_431_ = l_Lean_Name_num___override(v_namePrefix_426_, v_idx_427_);
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_433_ = lean_nat_add(v_idx_427_, v___x_432_);
lean_dec(v_idx_427_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v___x_433_);
v___x_435_ = v___x_429_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_namePrefix_426_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v___x_433_);
v___x_435_ = v_reuseFailAlloc_456_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; lean_object* v_env_437_; lean_object* v_nextMacroScope_438_; lean_object* v_auxDeclNGen_439_; lean_object* v_traceState_440_; lean_object* v_cache_441_; lean_object* v_recordedDeps_442_; lean_object* v_messages_443_; lean_object* v_infoState_444_; lean_object* v_snapshotTasks_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_454_; 
v___x_436_ = lean_st_ref_take(v___y_422_);
v_env_437_ = lean_ctor_get(v___x_436_, 0);
v_nextMacroScope_438_ = lean_ctor_get(v___x_436_, 1);
v_auxDeclNGen_439_ = lean_ctor_get(v___x_436_, 3);
v_traceState_440_ = lean_ctor_get(v___x_436_, 4);
v_cache_441_ = lean_ctor_get(v___x_436_, 5);
v_recordedDeps_442_ = lean_ctor_get(v___x_436_, 6);
v_messages_443_ = lean_ctor_get(v___x_436_, 7);
v_infoState_444_ = lean_ctor_get(v___x_436_, 8);
v_snapshotTasks_445_ = lean_ctor_get(v___x_436_, 9);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_454_ == 0)
{
lean_object* v_unused_455_; 
v_unused_455_ = lean_ctor_get(v___x_436_, 2);
lean_dec(v_unused_455_);
v___x_447_ = v___x_436_;
v_isShared_448_ = v_isSharedCheck_454_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_snapshotTasks_445_);
lean_inc(v_infoState_444_);
lean_inc(v_messages_443_);
lean_inc(v_recordedDeps_442_);
lean_inc(v_cache_441_);
lean_inc(v_traceState_440_);
lean_inc(v_auxDeclNGen_439_);
lean_inc(v_nextMacroScope_438_);
lean_inc(v_env_437_);
lean_dec(v___x_436_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_454_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 2, v___x_435_);
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_env_437_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_nextMacroScope_438_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_453_, 3, v_auxDeclNGen_439_);
lean_ctor_set(v_reuseFailAlloc_453_, 4, v_traceState_440_);
lean_ctor_set(v_reuseFailAlloc_453_, 5, v_cache_441_);
lean_ctor_set(v_reuseFailAlloc_453_, 6, v_recordedDeps_442_);
lean_ctor_set(v_reuseFailAlloc_453_, 7, v_messages_443_);
lean_ctor_set(v_reuseFailAlloc_453_, 8, v_infoState_444_);
lean_ctor_set(v_reuseFailAlloc_453_, 9, v_snapshotTasks_445_);
v___x_450_ = v_reuseFailAlloc_453_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_st_ref_put(v___y_422_, v___x_450_);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v_r_431_);
return v___x_452_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_422_ = stack[0].m_obj;
lean_object* v_res_458_;
v_res_458_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_422_);
stack->m_obj
 = v_res_458_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg___boxed(lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_459_);
lean_dec(v___y_459_);
return v_res_461_;
}
}
lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(uint8_t v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v___x_469_; lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
v___x_469_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_467_);
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_462_ = stack[0].m_num;
lean_object* v___y_463_ = stack[1].m_obj;
lean_object* v___y_464_ = stack[2].m_obj;
lean_object* v___y_465_ = stack[3].m_obj;
lean_object* v___y_466_ = stack[4].m_obj;
lean_object* v___y_467_ = stack[5].m_obj;
lean_object* v_res_478_;
v_res_478_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
stack->m_obj
 = v_res_478_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0___boxed(lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
uint8_t v___y_3260__boxed_486_; lean_object* v_res_487_; 
v___y_3260__boxed_486_ = lean_unbox(v___y_479_);
v_res_487_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(v___y_3260__boxed_486_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
return v_res_487_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(lean_object* v_fvarId_488_, uint8_t v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_508_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_508_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_508_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_508_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_501_ = lean_st_ref_take(v_a_490_);
lean_inc(v_a_497_);
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v_a_497_);
v___x_503_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v___x_501_, v_fvarId_488_, v___x_502_);
v___x_504_ = lean_st_ref_put(v_a_490_, v___x_503_);
if (v_isShared_500_ == 0)
{
v___x_506_ = v___x_499_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_497_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
else
{
lean_dec(v_fvarId_488_);
return v___x_496_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_488_ = stack[0].m_obj;
uint8_t v_a_489_ = stack[1].m_num;
lean_object* v_a_490_ = stack[2].m_obj;
lean_object* v_a_491_ = stack[3].m_obj;
lean_object* v_a_492_ = stack[4].m_obj;
lean_object* v_a_493_ = stack[5].m_obj;
lean_object* v_a_494_ = stack[6].m_obj;
lean_object* v_res_509_;
v_res_509_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
stack->m_obj
 = v_res_509_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg___boxed(lean_object* v_fvarId_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
uint8_t v_a_boxed_518_; lean_object* v_res_519_; 
v_a_boxed_518_ = lean_unbox(v_a_511_);
v_res_519_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_510_, v_a_boxed_518_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
return v_res_519_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(uint8_t v_pu_520_, lean_object* v_fvarId_521_, uint8_t v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_);
return v___x_529_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_520_ = stack[0].m_num;
lean_object* v_fvarId_521_ = stack[1].m_obj;
uint8_t v_a_522_ = stack[2].m_num;
lean_object* v_a_523_ = stack[3].m_obj;
lean_object* v_a_524_ = stack[4].m_obj;
lean_object* v_a_525_ = stack[5].m_obj;
lean_object* v_a_526_ = stack[6].m_obj;
lean_object* v_a_527_ = stack[7].m_obj;
lean_object* v_res_530_;
v_res_530_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(v_pu_520_, v_fvarId_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_);
stack->m_obj
 = v_res_530_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___boxed(lean_object* v_pu_531_, lean_object* v_fvarId_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
uint8_t v_pu_boxed_540_; uint8_t v_a_boxed_541_; lean_object* v_res_542_; 
v_pu_boxed_540_ = lean_unbox(v_pu_531_);
v_a_boxed_541_ = lean_unbox(v_a_533_);
v_res_542_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(v_pu_boxed_540_, v_fvarId_532_, v_a_boxed_541_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
return v_res_542_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(uint8_t v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_548_);
return v___x_550_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_543_ = stack[0].m_num;
lean_object* v___y_544_ = stack[1].m_obj;
lean_object* v___y_545_ = stack[2].m_obj;
lean_object* v___y_546_ = stack[3].m_obj;
lean_object* v___y_547_ = stack[4].m_obj;
lean_object* v___y_548_ = stack[5].m_obj;
lean_object* v_res_551_;
v_res_551_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
stack->m_obj
 = v_res_551_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___boxed(lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
uint8_t v___y_3376__boxed_559_; lean_object* v_res_560_; 
v___y_3376__boxed_559_ = lean_unbox(v___y_552_);
v_res_560_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(v___y_3376__boxed_559_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1(lean_object* v_00_u03b2_561_, lean_object* v_m_562_, lean_object* v_a_563_, lean_object* v_b_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v_m_562_, v_a_563_, v_b_564_);
return v___x_565_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(lean_object* v_00_u03b2_566_, lean_object* v_a_567_, lean_object* v_x_568_){
_start:
{
uint8_t v___x_569_; 
v___x_569_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_a_567_, v_x_568_);
return v___x_569_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_567_ = stack[1].m_obj;
lean_object* v_x_568_ = stack[2].m_obj;
uint8_t v_res_570_;
v_res_570_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(lean_box(0), v_a_567_, v_x_568_);
stack->m_num = v_res_570_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___boxed(lean_object* v_00_u03b2_571_, lean_object* v_a_572_, lean_object* v_x_573_){
_start:
{
uint8_t v_res_574_; lean_object* v_r_575_; 
v_res_574_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(v_00_u03b2_571_, v_a_572_, v_x_573_);
lean_dec(v_x_573_);
lean_dec(v_a_572_);
v_r_575_ = lean_box(v_res_574_);
return v_r_575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3(lean_object* v_00_u03b2_576_, lean_object* v_data_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(v_data_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4(lean_object* v_00_u03b2_579_, lean_object* v_a_580_, lean_object* v_b_581_, lean_object* v_x_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(v_a_580_, v_b_581_, v_x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_584_, lean_object* v_i_585_, lean_object* v_source_586_, lean_object* v_target_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(v_i_585_, v_source_586_, v_target_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_589_, lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(v_x_590_, v_x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(lean_object* v_a_593_, lean_object* v_x_594_){
_start:
{
if (lean_obj_tag(v_x_594_) == 0)
{
lean_object* v___x_595_; 
v___x_595_ = lean_box(0);
return v___x_595_;
}
else
{
lean_object* v_key_596_; lean_object* v_value_597_; lean_object* v_tail_598_; uint8_t v___x_599_; 
v_key_596_ = lean_ctor_get(v_x_594_, 0);
v_value_597_ = lean_ctor_get(v_x_594_, 1);
v_tail_598_ = lean_ctor_get(v_x_594_, 2);
v___x_599_ = l_Lean_instBEqFVarId_beq(v_key_596_, v_a_593_);
if (v___x_599_ == 0)
{
v_x_594_ = v_tail_598_;
goto _start;
}
else
{
lean_object* v___x_601_; 
lean_inc(v_value_597_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_value_597_);
return v___x_601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_602_, lean_object* v_x_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_602_, v_x_603_);
lean_dec(v_x_603_);
lean_dec(v_a_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(lean_object* v_m_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_buckets_607_; lean_object* v___x_608_; uint64_t v___x_609_; uint64_t v___x_610_; uint64_t v___x_611_; uint64_t v_fold_612_; uint64_t v___x_613_; uint64_t v___x_614_; uint64_t v___x_615_; size_t v___x_616_; size_t v___x_617_; size_t v___x_618_; size_t v___x_619_; size_t v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_buckets_607_ = lean_ctor_get(v_m_605_, 1);
v___x_608_ = lean_array_get_size(v_buckets_607_);
v___x_609_ = l_Lean_instHashableFVarId_hash(v_a_606_);
v___x_610_ = 32ULL;
v___x_611_ = lean_uint64_shift_right(v___x_609_, v___x_610_);
v_fold_612_ = lean_uint64_xor(v___x_609_, v___x_611_);
v___x_613_ = 16ULL;
v___x_614_ = lean_uint64_shift_right(v_fold_612_, v___x_613_);
v___x_615_ = lean_uint64_xor(v_fold_612_, v___x_614_);
v___x_616_ = lean_uint64_to_usize(v___x_615_);
v___x_617_ = lean_usize_of_nat(v___x_608_);
v___x_618_ = ((size_t)1ULL);
v___x_619_ = lean_usize_sub(v___x_617_, v___x_618_);
v___x_620_ = lean_usize_land(v___x_616_, v___x_619_);
v___x_621_ = lean_array_uget_borrowed(v_buckets_607_, v___x_620_);
v___x_622_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_606_, v___x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg___boxed(lean_object* v_m_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v_m_623_, v_a_624_);
lean_dec(v_a_624_);
lean_dec_ref(v_m_623_);
return v_res_625_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_instMonadEIO___redArg();
return v___x_626_;
}
}
lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(lean_object* v_msg_631_, uint8_t v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v_toApplicative_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_705_; 
v___x_639_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
v___x_640_ = l_StateRefT_x27_instMonad___redArg(v___x_639_);
v_toApplicative_641_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; 
v_unused_706_ = lean_ctor_get(v___x_640_, 1);
lean_dec(v_unused_706_);
v___x_643_ = v___x_640_;
v_isShared_644_ = v_isSharedCheck_705_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_toApplicative_641_);
lean_dec(v___x_640_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_705_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v_toFunctor_645_; lean_object* v_toSeq_646_; lean_object* v_toSeqLeft_647_; lean_object* v_toSeqRight_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_703_; 
v_toFunctor_645_ = lean_ctor_get(v_toApplicative_641_, 0);
v_toSeq_646_ = lean_ctor_get(v_toApplicative_641_, 2);
v_toSeqLeft_647_ = lean_ctor_get(v_toApplicative_641_, 3);
v_toSeqRight_648_ = lean_ctor_get(v_toApplicative_641_, 4);
v_isSharedCheck_703_ = !lean_is_exclusive(v_toApplicative_641_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v_toApplicative_641_, 1);
lean_dec(v_unused_704_);
v___x_650_ = v_toApplicative_641_;
v_isShared_651_ = v_isSharedCheck_703_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_toSeqRight_648_);
lean_inc(v_toSeqLeft_647_);
lean_inc(v_toSeq_646_);
lean_inc(v_toFunctor_645_);
lean_dec(v_toApplicative_641_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_703_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___f_652_; lean_object* v___f_653_; lean_object* v___f_654_; lean_object* v___f_655_; lean_object* v___x_656_; lean_object* v___f_657_; lean_object* v___f_658_; lean_object* v___f_659_; lean_object* v___x_661_; 
v___f_652_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
v___f_653_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_645_);
v___f_654_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_654_, 0, v_toFunctor_645_);
v___f_655_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_655_, 0, v_toFunctor_645_);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v___f_654_);
lean_ctor_set(v___x_656_, 1, v___f_655_);
v___f_657_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_657_, 0, v_toSeqRight_648_);
v___f_658_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_658_, 0, v_toSeqLeft_647_);
v___f_659_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_659_, 0, v_toSeq_646_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 4, v___f_657_);
lean_ctor_set(v___x_650_, 3, v___f_658_);
lean_ctor_set(v___x_650_, 2, v___f_659_);
lean_ctor_set(v___x_650_, 1, v___f_652_);
lean_ctor_set(v___x_650_, 0, v___x_656_);
v___x_661_ = v___x_650_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v___f_652_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v___f_659_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v___f_658_);
lean_ctor_set(v_reuseFailAlloc_702_, 4, v___f_657_);
v___x_661_ = v_reuseFailAlloc_702_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_663_; 
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v___f_653_);
lean_ctor_set(v___x_643_, 0, v___x_661_);
v___x_663_ = v___x_643_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___f_653_);
v___x_663_ = v_reuseFailAlloc_701_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_664_; lean_object* v_toApplicative_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_699_; 
v___x_664_ = l_StateRefT_x27_instMonad___redArg(v___x_663_);
v_toApplicative_665_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v___x_664_, 1);
lean_dec(v_unused_700_);
v___x_667_ = v___x_664_;
v_isShared_668_ = v_isSharedCheck_699_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_toApplicative_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_699_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_toFunctor_669_; lean_object* v_toSeq_670_; lean_object* v_toSeqLeft_671_; lean_object* v_toSeqRight_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_697_; 
v_toFunctor_669_ = lean_ctor_get(v_toApplicative_665_, 0);
v_toSeq_670_ = lean_ctor_get(v_toApplicative_665_, 2);
v_toSeqLeft_671_ = lean_ctor_get(v_toApplicative_665_, 3);
v_toSeqRight_672_ = lean_ctor_get(v_toApplicative_665_, 4);
v_isSharedCheck_697_ = !lean_is_exclusive(v_toApplicative_665_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v_toApplicative_665_, 1);
lean_dec(v_unused_698_);
v___x_674_ = v_toApplicative_665_;
v_isShared_675_ = v_isSharedCheck_697_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_toSeqRight_672_);
lean_inc(v_toSeqLeft_671_);
lean_inc(v_toSeq_670_);
lean_inc(v_toFunctor_669_);
lean_dec(v_toApplicative_665_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_697_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___f_676_; lean_object* v___f_677_; lean_object* v___f_678_; lean_object* v___f_679_; lean_object* v___x_680_; lean_object* v___f_681_; lean_object* v___f_682_; lean_object* v___f_683_; lean_object* v___x_685_; 
v___f_676_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
v___f_677_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(v_toFunctor_669_);
v___f_678_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_678_, 0, v_toFunctor_669_);
v___f_679_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_679_, 0, v_toFunctor_669_);
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v___f_678_);
lean_ctor_set(v___x_680_, 1, v___f_679_);
v___f_681_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_681_, 0, v_toSeqRight_672_);
v___f_682_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_682_, 0, v_toSeqLeft_671_);
v___f_683_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_683_, 0, v_toSeq_670_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 4, v___f_681_);
lean_ctor_set(v___x_674_, 3, v___f_682_);
lean_ctor_set(v___x_674_, 2, v___f_683_);
lean_ctor_set(v___x_674_, 1, v___f_676_);
lean_ctor_set(v___x_674_, 0, v___x_680_);
v___x_685_ = v___x_674_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v___f_676_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v___f_683_);
lean_ctor_set(v_reuseFailAlloc_696_, 3, v___f_682_);
lean_ctor_set(v_reuseFailAlloc_696_, 4, v___f_681_);
v___x_685_ = v_reuseFailAlloc_696_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_687_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___f_677_);
lean_ctor_set(v___x_667_, 0, v___x_685_);
v___x_687_ = v___x_667_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v___f_677_);
v___x_687_ = v_reuseFailAlloc_695_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___f_691_; lean_object* v___x_7028__overap_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_688_ = l_StateRefT_x27_instMonad___redArg(v___x_687_);
v___x_689_ = l_Lean_instInhabitedExpr;
v___x_690_ = l_instInhabitedOfMonad___redArg(v___x_688_, v___x_689_);
v___f_691_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_691_, 0, v___x_690_);
v___x_7028__overap_692_ = lean_panic_fn_borrowed(v___f_691_, v_msg_631_);
lean_dec_ref(v___f_691_);
v___x_693_ = lean_box(v___y_632_);
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
lean_inc(v___y_635_);
lean_inc_ref(v___y_634_);
lean_inc(v___y_633_);
v___x_694_ = lean_apply_7(v___x_7028__overap_692_, v___x_693_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, lean_box(0));
return v___x_694_;
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
LEAN_EXPORT void l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_631_ = stack[0].m_obj;
uint8_t v___y_632_ = stack[1].m_num;
lean_object* v___y_633_ = stack[2].m_obj;
lean_object* v___y_634_ = stack[3].m_obj;
lean_object* v___y_635_ = stack[4].m_obj;
lean_object* v___y_636_ = stack[5].m_obj;
lean_object* v___y_637_ = stack[6].m_obj;
lean_object* v_res_707_;
v_res_707_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v_msg_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
stack->m_obj
 = v_res_707_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___boxed(lean_object* v_msg_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
uint8_t v___y_7201__boxed_716_; lean_object* v_res_717_; 
v___y_7201__boxed_716_ = lean_unbox(v___y_709_);
v_res_717_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v_msg_708_, v___y_7201__boxed_716_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
return v_res_717_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_721_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_722_ = lean_unsigned_to_nat(20u);
v___x_723_ = lean_unsigned_to_nat(88u);
v___x_724_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__1));
v___x_725_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_726_ = l_mkPanicMessageWithDecl(v___x_725_, v___x_724_, v___x_723_, v___x_722_, v___x_721_);
return v___x_726_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(uint8_t v_pu_727_, lean_object* v_e_728_, uint8_t v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
uint8_t v___x_736_; 
v___x_736_ = l_Lean_Expr_hasFVar(v_e_728_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v_e_728_);
return v___x_737_;
}
else
{
switch(lean_obj_tag(v_e_728_))
{
case 1:
{
lean_object* v_fvarId_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v_fvarId_738_ = lean_ctor_get(v_e_728_, 0);
v___x_739_ = lean_st_ref_get(v_a_730_);
v___x_740_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v___x_739_, v_fvarId_738_);
lean_dec(v___x_739_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v___x_741_; 
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v_e_728_);
return v___x_741_;
}
else
{
lean_object* v_val_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_787_; 
lean_dec_ref_known(v_e_728_, 1);
v_val_742_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_787_ == 0)
{
v___x_744_ = v___x_740_;
v_isShared_745_ = v_isSharedCheck_787_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_val_742_);
lean_dec(v___x_740_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_787_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
switch(lean_obj_tag(v_val_742_))
{
case 0:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_746_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_745_ == 0)
{
lean_ctor_set_tag(v___x_744_, 0);
lean_ctor_set(v___x_744_, 0, v___x_746_);
v___x_748_ = v___x_744_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
case 1:
{
lean_object* v_fvarId_750_; lean_object* v___x_751_; 
lean_del_object(v___x_744_);
v_fvarId_750_ = lean_ctor_get(v_val_742_, 0);
lean_inc(v_fvarId_750_);
lean_dec_ref_known(v_val_742_, 1);
v___x_751_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_727_, v_fvarId_750_, v_a_732_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_770_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_770_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_770_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_770_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
if (lean_obj_tag(v_a_752_) == 0)
{
lean_dec(v_fvarId_750_);
goto v___jp_756_;
}
else
{
lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_768_; 
v_isSharedCheck_768_ = !lean_is_exclusive(v_a_752_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; 
v_unused_769_ = lean_ctor_get(v_a_752_, 0);
lean_dec(v_unused_769_);
v___x_762_ = v_a_752_;
v_isShared_763_ = v_isSharedCheck_768_;
goto v_resetjp_761_;
}
else
{
lean_dec(v_a_752_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_768_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
if (v___x_736_ == 0)
{
lean_del_object(v___x_762_);
lean_dec(v_fvarId_750_);
goto v___jp_756_;
}
else
{
lean_object* v___x_764_; lean_object* v___x_766_; 
lean_del_object(v___x_754_);
v___x_764_ = l_Lean_Expr_fvar___override(v_fvarId_750_);
if (v_isShared_763_ == 0)
{
lean_ctor_set_tag(v___x_762_, 0);
lean_ctor_set(v___x_762_, 0, v___x_764_);
v___x_766_ = v___x_762_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
v___jp_756_:
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_757_);
v___x_759_ = v___x_754_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec(v_fvarId_750_);
v_a_771_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_751_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_751_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
default: 
{
lean_object* v_expr_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_del_object(v___x_744_);
v_expr_779_ = lean_ctor_get(v_val_742_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v_val_742_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v_val_742_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_expr_779_);
lean_dec(v_val_742_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set_tag(v___x_781_, 0);
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_expr_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_788_; lean_object* v_arg_789_; lean_object* v___x_790_; 
v_fn_788_ = lean_ctor_get(v_e_728_, 0);
v_arg_789_ = lean_ctor_get(v_e_728_, 1);
lean_inc_ref(v_fn_788_);
v___x_790_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_727_, v_fn_788_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v___x_792_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
lean_dec_ref_known(v___x_790_, 1);
lean_inc_ref(v_arg_789_);
v___x_792_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_727_, v_arg_789_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_811_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_811_ == 0)
{
v___x_795_ = v___x_792_;
v_isShared_796_ = v_isSharedCheck_811_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_811_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___y_798_; size_t v___x_803_; size_t v___x_804_; uint8_t v___x_805_; 
v___x_803_ = lean_ptr_addr(v_fn_788_);
v___x_804_ = lean_ptr_addr(v_a_791_);
v___x_805_ = lean_usize_dec_eq(v___x_803_, v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; 
lean_dec_ref_known(v_e_728_, 2);
v___x_806_ = l_Lean_Expr_app___override(v_a_791_, v_a_793_);
v___y_798_ = v___x_806_;
goto v___jp_797_;
}
else
{
size_t v___x_807_; size_t v___x_808_; uint8_t v___x_809_; 
v___x_807_ = lean_ptr_addr(v_arg_789_);
v___x_808_ = lean_ptr_addr(v_a_793_);
v___x_809_ = lean_usize_dec_eq(v___x_807_, v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; 
lean_dec_ref_known(v_e_728_, 2);
v___x_810_ = l_Lean_Expr_app___override(v_a_791_, v_a_793_);
v___y_798_ = v___x_810_;
goto v___jp_797_;
}
else
{
lean_dec(v_a_793_);
lean_dec(v_a_791_);
v___y_798_ = v_e_728_;
goto v___jp_797_;
}
}
v___jp_797_:
{
lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_799_ = l_Lean_Expr_headBeta(v___y_798_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_799_);
v___x_801_ = v___x_795_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_799_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
else
{
lean_dec(v_a_791_);
lean_dec_ref_known(v_e_728_, 2);
return v___x_792_;
}
}
else
{
lean_dec_ref_known(v_e_728_, 2);
return v___x_790_;
}
}
case 6:
{
lean_object* v_binderName_812_; lean_object* v_binderType_813_; lean_object* v_body_814_; uint8_t v_binderInfo_815_; lean_object* v___x_816_; 
v_binderName_812_ = lean_ctor_get(v_e_728_, 0);
v_binderType_813_ = lean_ctor_get(v_e_728_, 1);
v_body_814_ = lean_ctor_get(v_e_728_, 2);
v_binderInfo_815_ = lean_ctor_get_uint8(v_e_728_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_813_);
v___x_816_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_727_, v_binderType_813_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_818_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_816_, 1);
lean_inc_ref(v_body_814_);
v___x_818_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_727_, v_body_814_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_845_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_845_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_845_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_845_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
size_t v___x_823_; size_t v___x_824_; uint8_t v___x_825_; 
v___x_823_ = lean_ptr_addr(v_binderType_813_);
v___x_824_ = lean_ptr_addr(v_a_817_);
v___x_825_ = lean_usize_dec_eq(v___x_823_, v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_828_; 
lean_inc(v_binderName_812_);
lean_dec_ref_known(v_e_728_, 3);
v___x_826_ = l_Lean_Expr_lam___override(v_binderName_812_, v_a_817_, v_a_819_, v_binderInfo_815_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_826_);
v___x_828_ = v___x_821_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
else
{
size_t v___x_830_; size_t v___x_831_; uint8_t v___x_832_; 
v___x_830_ = lean_ptr_addr(v_body_814_);
v___x_831_ = lean_ptr_addr(v_a_819_);
v___x_832_ = lean_usize_dec_eq(v___x_830_, v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_835_; 
lean_inc(v_binderName_812_);
lean_dec_ref_known(v_e_728_, 3);
v___x_833_ = l_Lean_Expr_lam___override(v_binderName_812_, v_a_817_, v_a_819_, v_binderInfo_815_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_833_);
v___x_835_ = v___x_821_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
else
{
uint8_t v___x_837_; 
v___x_837_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_815_, v_binderInfo_815_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_840_; 
lean_inc(v_binderName_812_);
lean_dec_ref_known(v_e_728_, 3);
v___x_838_ = l_Lean_Expr_lam___override(v_binderName_812_, v_a_817_, v_a_819_, v_binderInfo_815_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_838_);
v___x_840_ = v___x_821_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
else
{
lean_object* v___x_843_; 
lean_dec(v_a_819_);
lean_dec(v_a_817_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v_e_728_);
v___x_843_ = v___x_821_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_e_728_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
}
else
{
lean_dec(v_a_817_);
lean_dec_ref_known(v_e_728_, 3);
return v___x_818_;
}
}
else
{
lean_dec_ref_known(v_e_728_, 3);
return v___x_816_;
}
}
case 7:
{
lean_object* v_binderName_846_; lean_object* v_binderType_847_; lean_object* v_body_848_; uint8_t v_binderInfo_849_; lean_object* v___x_850_; 
v_binderName_846_ = lean_ctor_get(v_e_728_, 0);
v_binderType_847_ = lean_ctor_get(v_e_728_, 1);
v_body_848_ = lean_ctor_get(v_e_728_, 2);
v_binderInfo_849_ = lean_ctor_get_uint8(v_e_728_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_847_);
v___x_850_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_727_, v_binderType_847_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_852_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
lean_inc_ref(v_body_848_);
v___x_852_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_727_, v_body_848_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_879_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_879_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_879_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_879_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
size_t v___x_857_; size_t v___x_858_; uint8_t v___x_859_; 
v___x_857_ = lean_ptr_addr(v_binderType_847_);
v___x_858_ = lean_ptr_addr(v_a_851_);
v___x_859_ = lean_usize_dec_eq(v___x_857_, v___x_858_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; lean_object* v___x_862_; 
lean_inc(v_binderName_846_);
lean_dec_ref_known(v_e_728_, 3);
v___x_860_ = l_Lean_Expr_forallE___override(v_binderName_846_, v_a_851_, v_a_853_, v_binderInfo_849_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_860_);
v___x_862_ = v___x_855_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
else
{
size_t v___x_864_; size_t v___x_865_; uint8_t v___x_866_; 
v___x_864_ = lean_ptr_addr(v_body_848_);
v___x_865_ = lean_ptr_addr(v_a_853_);
v___x_866_ = lean_usize_dec_eq(v___x_864_, v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_869_; 
lean_inc(v_binderName_846_);
lean_dec_ref_known(v_e_728_, 3);
v___x_867_ = l_Lean_Expr_forallE___override(v_binderName_846_, v_a_851_, v_a_853_, v_binderInfo_849_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_867_);
v___x_869_ = v___x_855_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
else
{
uint8_t v___x_871_; 
v___x_871_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_849_, v_binderInfo_849_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_874_; 
lean_inc(v_binderName_846_);
lean_dec_ref_known(v_e_728_, 3);
v___x_872_ = l_Lean_Expr_forallE___override(v_binderName_846_, v_a_851_, v_a_853_, v_binderInfo_849_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_872_);
v___x_874_ = v___x_855_;
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
lean_dec(v_a_853_);
lean_dec(v_a_851_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v_e_728_);
v___x_877_ = v___x_855_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_e_728_);
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
}
}
else
{
lean_dec(v_a_851_);
lean_dec_ref_known(v_e_728_, 3);
return v___x_852_;
}
}
else
{
lean_dec_ref_known(v_e_728_, 3);
return v___x_850_;
}
}
case 8:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec_ref_known(v_e_728_, 4);
v___x_880_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3, &l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3);
v___x_881_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v___x_880_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
return v___x_881_;
}
case 10:
{
lean_object* v_data_882_; lean_object* v_expr_883_; lean_object* v___x_884_; 
v_data_882_ = lean_ctor_get(v_e_728_, 0);
v_expr_883_ = lean_ctor_get(v_e_728_, 1);
lean_inc_ref(v_expr_883_);
v___x_884_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_727_, v_expr_883_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
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
v___x_889_ = lean_ptr_addr(v_expr_883_);
v___x_890_ = lean_ptr_addr(v_a_885_);
v___x_891_ = lean_usize_dec_eq(v___x_889_, v___x_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; lean_object* v___x_894_; 
lean_inc(v_data_882_);
lean_dec_ref_known(v_e_728_, 2);
v___x_892_ = l_Lean_Expr_mdata___override(v_data_882_, v_a_885_);
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
lean_ctor_set(v___x_887_, 0, v_e_728_);
v___x_897_ = v___x_887_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_e_728_);
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
lean_dec_ref_known(v_e_728_, 2);
return v___x_884_;
}
}
case 11:
{
lean_object* v_typeName_900_; lean_object* v_idx_901_; lean_object* v_struct_902_; lean_object* v___x_903_; 
v_typeName_900_ = lean_ctor_get(v_e_728_, 0);
v_idx_901_ = lean_ctor_get(v_e_728_, 1);
v_struct_902_ = lean_ctor_get(v_e_728_, 2);
lean_inc_ref(v_struct_902_);
v___x_903_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_727_, v_struct_902_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_918_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_918_ == 0)
{
v___x_906_ = v___x_903_;
v_isShared_907_ = v_isSharedCheck_918_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_903_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_918_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
size_t v___x_908_; size_t v___x_909_; uint8_t v___x_910_; 
v___x_908_ = lean_ptr_addr(v_struct_902_);
v___x_909_ = lean_ptr_addr(v_a_904_);
v___x_910_ = lean_usize_dec_eq(v___x_908_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_913_; 
lean_inc(v_idx_901_);
lean_inc(v_typeName_900_);
lean_dec_ref_known(v_e_728_, 3);
v___x_911_ = l_Lean_Expr_proj___override(v_typeName_900_, v_idx_901_, v_a_904_);
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
lean_object* v___x_916_; 
lean_dec(v_a_904_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v_e_728_);
v___x_916_ = v___x_906_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_e_728_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_728_, 3);
return v___x_903_;
}
}
default: 
{
lean_object* v___x_919_; 
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v_e_728_);
return v___x_919_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_727_ = stack[0].m_num;
lean_object* v_e_728_ = stack[1].m_obj;
uint8_t v_a_729_ = stack[2].m_num;
lean_object* v_a_730_ = stack[3].m_obj;
lean_object* v_a_731_ = stack[4].m_obj;
lean_object* v_a_732_ = stack[5].m_obj;
lean_object* v_a_733_ = stack[6].m_obj;
lean_object* v_a_734_ = stack[7].m_obj;
lean_object* v_res_920_;
v_res_920_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_727_, v_e_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
stack->m_obj
 = v_res_920_;
}
lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(uint8_t v_pu_921_, lean_object* v_e_922_, uint8_t v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
if (lean_obj_tag(v_e_922_) == 5)
{
lean_object* v_fn_930_; lean_object* v_arg_931_; lean_object* v___x_932_; 
v_fn_930_ = lean_ctor_get(v_e_922_, 0);
v_arg_931_ = lean_ctor_get(v_e_922_, 1);
lean_inc_ref(v_fn_930_);
v___x_932_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_921_, v_fn_930_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_934_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 1);
lean_inc_ref(v_arg_931_);
v___x_934_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_921_, v_arg_931_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_956_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_956_ == 0)
{
v___x_937_ = v___x_934_;
v_isShared_938_ = v_isSharedCheck_956_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_934_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_956_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
size_t v___x_939_; size_t v___x_940_; uint8_t v___x_941_; 
v___x_939_ = lean_ptr_addr(v_fn_930_);
v___x_940_ = lean_ptr_addr(v_a_933_);
v___x_941_ = lean_usize_dec_eq(v___x_939_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; lean_object* v___x_944_; 
lean_dec_ref_known(v_e_922_, 2);
v___x_942_ = l_Lean_Expr_app___override(v_a_933_, v_a_935_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_942_);
v___x_944_ = v___x_937_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
else
{
size_t v___x_946_; size_t v___x_947_; uint8_t v___x_948_; 
v___x_946_ = lean_ptr_addr(v_arg_931_);
v___x_947_ = lean_ptr_addr(v_a_935_);
v___x_948_ = lean_usize_dec_eq(v___x_946_, v___x_947_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; lean_object* v___x_951_; 
lean_dec_ref_known(v_e_922_, 2);
v___x_949_ = l_Lean_Expr_app___override(v_a_933_, v_a_935_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_949_);
v___x_951_ = v___x_937_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
else
{
lean_object* v___x_954_; 
lean_dec(v_a_935_);
lean_dec(v_a_933_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v_e_922_);
v___x_954_ = v___x_937_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_e_922_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
else
{
lean_dec(v_a_933_);
lean_dec_ref_known(v_e_922_, 2);
return v___x_934_;
}
}
else
{
lean_dec_ref_known(v_e_922_, 2);
return v___x_932_;
}
}
else
{
lean_object* v___x_957_; 
v___x_957_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_921_, v_e_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
return v___x_957_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_921_ = stack[0].m_num;
lean_object* v_e_922_ = stack[1].m_obj;
uint8_t v_a_923_ = stack[2].m_num;
lean_object* v_a_924_ = stack[3].m_obj;
lean_object* v_a_925_ = stack[4].m_obj;
lean_object* v_a_926_ = stack[5].m_obj;
lean_object* v_a_927_ = stack[6].m_obj;
lean_object* v_a_928_ = stack[7].m_obj;
lean_object* v_res_958_;
v_res_958_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_921_, v_e_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
stack->m_obj
 = v_res_958_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp___boxed(lean_object* v_pu_959_, lean_object* v_e_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
uint8_t v_pu_boxed_968_; uint8_t v_a_boxed_969_; lean_object* v_res_970_; 
v_pu_boxed_968_ = lean_unbox(v_pu_959_);
v_a_boxed_969_ = lean_unbox(v_a_961_);
v_res_970_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_boxed_968_, v_e_960_, v_a_boxed_969_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___boxed(lean_object* v_pu_971_, lean_object* v_e_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
uint8_t v_pu_boxed_980_; uint8_t v_a_boxed_981_; lean_object* v_res_982_; 
v_pu_boxed_980_ = lean_unbox(v_pu_971_);
v_a_boxed_981_ = lean_unbox(v_a_973_);
v_res_982_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_boxed_980_, v_e_972_, v_a_boxed_981_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(lean_object* v_00_u03b2_983_, lean_object* v_m_984_, lean_object* v_a_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v_m_984_, v_a_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___boxed(lean_object* v_00_u03b2_987_, lean_object* v_m_988_, lean_object* v_a_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(v_00_u03b2_987_, v_m_988_, v_a_989_);
lean_dec(v_a_989_);
lean_dec_ref(v_m_988_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(lean_object* v_00_u03b2_991_, lean_object* v_a_992_, lean_object* v_x_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_992_, v_x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_995_, lean_object* v_a_996_, lean_object* v_x_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(v_00_u03b2_995_, v_a_996_, v_x_997_);
lean_dec(v_x_997_);
lean_dec(v_a_996_);
return v_res_998_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(uint8_t v_pu_999_, lean_object* v_e_1000_, uint8_t v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1008_ = lean_box(v_pu_999_);
v___x_1009_ = lean_obj_tag_nat(v___x_1008_);
lean_dec(v___x_1008_);
v___x_1010_ = lean_unsigned_to_nat(1u);
v___x_1011_ = lean_nat_dec_eq(v___x_1009_, v___x_1010_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; 
v___x_1012_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_999_, v_e_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
return v___x_1012_;
}
else
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v_e_1000_);
return v___x_1013_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_999_ = stack[0].m_num;
lean_object* v_e_1000_ = stack[1].m_obj;
uint8_t v_a_1001_ = stack[2].m_num;
lean_object* v_a_1002_ = stack[3].m_obj;
lean_object* v_a_1003_ = stack[4].m_obj;
lean_object* v_a_1004_ = stack[5].m_obj;
lean_object* v_a_1005_ = stack[6].m_obj;
lean_object* v_a_1006_ = stack[7].m_obj;
lean_object* v_res_1014_;
v_res_1014_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_999_, v_e_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
stack->m_obj
 = v_res_1014_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___boxed(lean_object* v_pu_1015_, lean_object* v_e_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
uint8_t v_pu_boxed_1024_; uint8_t v_a_boxed_1025_; lean_object* v_res_1026_; 
v_pu_boxed_1024_ = lean_unbox(v_pu_1015_);
v_a_boxed_1025_ = lean_unbox(v_a_1017_);
v_res_1026_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_boxed_1024_, v_e_1016_, v_a_boxed_1025_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
return v_res_1026_;
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t v_pu_1027_, lean_object* v_p_1028_, uint8_t v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_fvarId_1036_; lean_object* v_binderName_1037_; lean_object* v_type_1038_; uint8_t v_borrow_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1087_; 
v_fvarId_1036_ = lean_ctor_get(v_p_1028_, 0);
v_binderName_1037_ = lean_ctor_get(v_p_1028_, 1);
v_type_1038_ = lean_ctor_get(v_p_1028_, 2);
v_borrow_1039_ = lean_ctor_get_uint8(v_p_1028_, sizeof(void*)*3);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_p_1028_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1041_ = v_p_1028_;
v_isShared_1042_ = v_isSharedCheck_1087_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_type_1038_);
lean_inc(v_binderName_1037_);
lean_inc(v_fvarId_1036_);
lean_dec(v_p_1028_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1087_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v_a_1044_; lean_object* v___x_1045_; 
v___x_1043_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_1037_, v_a_1029_, v_a_1032_);
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref(v___x_1043_);
v___x_1045_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1027_, v_type_1038_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1047_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v___x_1047_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_1036_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1070_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1050_ = v___x_1047_;
v_isShared_1051_ = v_isSharedCheck_1070_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1047_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1070_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 2, v_a_1046_);
lean_ctor_set(v___x_1041_, 1, v_a_1044_);
lean_ctor_set(v___x_1041_, 0, v_a_1048_);
v___x_1053_ = v___x_1041_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1048_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_a_1044_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v_a_1046_);
lean_ctor_set_uint8(v_reuseFailAlloc_1069_, sizeof(void*)*3, v_borrow_1039_);
v___x_1053_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1054_; lean_object* v_lctx_1055_; lean_object* v_nextIdx_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1068_; 
v___x_1054_ = lean_st_ref_take(v_a_1032_);
v_lctx_1055_ = lean_ctor_get(v___x_1054_, 0);
v_nextIdx_1056_ = lean_ctor_get(v___x_1054_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1058_ = v___x_1054_;
v_isShared_1059_ = v_isSharedCheck_1068_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_nextIdx_1056_);
lean_inc(v_lctx_1055_);
lean_dec(v___x_1054_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1068_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
lean_inc_ref(v___x_1053_);
v___x_1060_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_1027_, v_lctx_1055_, v___x_1053_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v___x_1060_);
v___x_1062_ = v___x_1058_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1060_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_nextIdx_1056_);
v___x_1062_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1063_ = lean_st_ref_put(v_a_1032_, v___x_1062_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v___x_1053_);
v___x_1065_ = v___x_1050_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1053_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_dec(v_a_1046_);
lean_dec(v_a_1044_);
lean_del_object(v___x_1041_);
v_a_1071_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1047_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1047_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec(v_a_1044_);
lean_del_object(v___x_1041_);
lean_dec(v_fvarId_1036_);
v_a_1079_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1045_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1045_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Internalize_internalizeParam_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1027_ = stack[0].m_num;
lean_object* v_p_1028_ = stack[1].m_obj;
uint8_t v_a_1029_ = stack[2].m_num;
lean_object* v_a_1030_ = stack[3].m_obj;
lean_object* v_a_1031_ = stack[4].m_obj;
lean_object* v_a_1032_ = stack[5].m_obj;
lean_object* v_a_1033_ = stack[6].m_obj;
lean_object* v_a_1034_ = stack[7].m_obj;
lean_object* v_res_1088_;
v_res_1088_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_1027_, v_p_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
stack->m_obj
 = v_res_1088_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(lean_object* v_pu_1089_, lean_object* v_p_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
uint8_t v_pu_boxed_1098_; uint8_t v_a_boxed_1099_; lean_object* v_res_1100_; 
v_pu_boxed_1098_ = lean_unbox(v_pu_1089_);
v_a_boxed_1099_ = lean_unbox(v_a_1091_);
v_res_1100_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_boxed_1098_, v_p_1090_, v_a_boxed_1099_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
lean_dec(v_a_1092_);
return v_res_1100_;
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg(uint8_t v_pu_1101_, lean_object* v_arg_1102_, uint8_t v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
switch(lean_obj_tag(v_arg_1102_))
{
case 0:
{
lean_object* v___x_1110_; 
v___x_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1110_, 0, v_arg_1102_);
return v___x_1110_;
}
case 1:
{
lean_object* v_fvarId_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v_fvarId_1111_ = lean_ctor_get(v_arg_1102_, 0);
v___x_1112_ = lean_st_ref_get(v_a_1104_);
v___x_1113_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v___x_1112_, v_fvarId_1111_);
lean_dec(v___x_1112_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v_arg_1102_);
return v___x_1114_;
}
else
{
lean_object* v_val_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1145_; 
lean_dec_ref_known(v_arg_1102_, 1);
v_val_1115_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1117_ = v___x_1113_;
v_isShared_1118_ = v_isSharedCheck_1145_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_val_1115_);
lean_dec(v___x_1113_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1145_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
switch(lean_obj_tag(v_val_1115_))
{
case 0:
{
lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1119_ = lean_box(0);
if (v_isShared_1118_ == 0)
{
lean_ctor_set_tag(v___x_1117_, 0);
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
case 1:
{
lean_object* v_fvarId_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1133_; 
v_fvarId_1123_ = lean_ctor_get(v_val_1115_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_val_1115_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1125_ = v_val_1115_;
v_isShared_1126_ = v_isSharedCheck_1133_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_fvarId_1123_);
lean_dec(v_val_1115_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1133_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_fvarId_1123_);
v___x_1128_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
lean_object* v___x_1130_; 
if (v_isShared_1118_ == 0)
{
lean_ctor_set_tag(v___x_1117_, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1128_);
v___x_1130_ = v___x_1117_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
default: 
{
lean_object* v_expr_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1144_; 
v_expr_1134_ = lean_ctor_get(v_val_1115_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_val_1115_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1136_ = v_val_1115_;
v_isShared_1137_ = v_isSharedCheck_1144_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_expr_1134_);
lean_dec(v_val_1115_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1144_;
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
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_expr_1134_);
v___x_1139_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1141_; 
if (v_isShared_1118_ == 0)
{
lean_ctor_set_tag(v___x_1117_, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1139_);
v___x_1141_ = v___x_1117_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
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
lean_object* v_expr_1146_; lean_object* v___x_1147_; 
v_expr_1146_ = lean_ctor_get(v_arg_1102_, 0);
lean_inc_ref(v_expr_1146_);
v___x_1147_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1101_, v_expr_1146_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1156_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1101_, v_arg_1102_, v_a_1148_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1152_);
v___x_1154_ = v___x_1150_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec_ref_known(v_arg_1102_, 1);
v_a_1157_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1147_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1147_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Internalize_internalizeArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1101_ = stack[0].m_num;
lean_object* v_arg_1102_ = stack[1].m_obj;
uint8_t v_a_1103_ = stack[2].m_num;
lean_object* v_a_1104_ = stack[3].m_obj;
lean_object* v_a_1105_ = stack[4].m_obj;
lean_object* v_a_1106_ = stack[5].m_obj;
lean_object* v_a_1107_ = stack[6].m_obj;
lean_object* v_a_1108_ = stack[7].m_obj;
lean_object* v_res_1165_;
v_res_1165_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_1101_, v_arg_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
stack->m_obj
 = v_res_1165_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg___boxed(lean_object* v_pu_1166_, lean_object* v_arg_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
uint8_t v_pu_boxed_1175_; uint8_t v_a_boxed_1176_; lean_object* v_res_1177_; 
v_pu_boxed_1175_ = lean_unbox(v_pu_1166_);
v_a_boxed_1176_ = lean_unbox(v_a_1168_);
v_res_1177_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_boxed_1175_, v_arg_1167_, v_a_boxed_1176_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
lean_dec(v_a_1169_);
return v_res_1177_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(uint8_t v_pu_1178_, size_t v_sz_1179_, size_t v_i_1180_, lean_object* v_bs_1181_, uint8_t v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_usize_dec_lt(v_i_1180_, v_sz_1179_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v_bs_1181_);
return v___x_1190_;
}
else
{
lean_object* v_v_1191_; lean_object* v___x_1192_; lean_object* v_bs_x27_1193_; lean_object* v___x_1194_; 
v_v_1191_ = lean_array_uget(v_bs_1181_, v_i_1180_);
v___x_1192_ = lean_unsigned_to_nat(0u);
v_bs_x27_1193_ = lean_array_uset(v_bs_1181_, v_i_1180_, v___x_1192_);
v___x_1194_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_1178_, v_v_1191_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; size_t v___x_1196_; size_t v___x_1197_; lean_object* v___x_1198_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v___x_1196_ = ((size_t)1ULL);
v___x_1197_ = lean_usize_add(v_i_1180_, v___x_1196_);
v___x_1198_ = lean_array_uset(v_bs_x27_1193_, v_i_1180_, v_a_1195_);
v_i_1180_ = v___x_1197_;
v_bs_1181_ = v___x_1198_;
goto _start;
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v_bs_x27_1193_);
v_a_1200_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1194_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1194_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1178_ = stack[0].m_num;
size_t v_sz_1179_ = stack[1].m_num;
size_t v_i_1180_ = stack[2].m_num;
lean_object* v_bs_1181_ = stack[3].m_obj;
uint8_t v___y_1182_ = stack[4].m_num;
lean_object* v___y_1183_ = stack[5].m_obj;
lean_object* v___y_1184_ = stack[6].m_obj;
lean_object* v___y_1185_ = stack[7].m_obj;
lean_object* v___y_1186_ = stack[8].m_obj;
lean_object* v___y_1187_ = stack[9].m_obj;
lean_object* v_res_1208_;
v_res_1208_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_1178_, v_sz_1179_, v_i_1180_, v_bs_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
stack->m_obj
 = v_res_1208_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0___boxed(lean_object* v_pu_1209_, lean_object* v_sz_1210_, lean_object* v_i_1211_, lean_object* v_bs_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
uint8_t v_pu_boxed_1220_; size_t v_sz_boxed_1221_; size_t v_i_boxed_1222_; uint8_t v___y_339__boxed_1223_; lean_object* v_res_1224_; 
v_pu_boxed_1220_ = lean_unbox(v_pu_1209_);
v_sz_boxed_1221_ = lean_unbox_usize(v_sz_1210_);
lean_dec(v_sz_1210_);
v_i_boxed_1222_ = lean_unbox_usize(v_i_1211_);
lean_dec(v_i_1211_);
v___y_339__boxed_1223_ = lean_unbox(v___y_1213_);
v_res_1224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_boxed_1220_, v_sz_boxed_1221_, v_i_boxed_1222_, v_bs_1212_, v___y_339__boxed_1223_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
return v_res_1224_;
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs(uint8_t v_pu_1225_, lean_object* v_args_1226_, uint8_t v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
size_t v_sz_1234_; size_t v___x_1235_; lean_object* v___x_1236_; 
v_sz_1234_ = lean_array_size(v_args_1226_);
v___x_1235_ = ((size_t)0ULL);
v___x_1236_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_1225_, v_sz_1234_, v___x_1235_, v_args_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
return v___x_1236_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Internalize_internalizeArgs_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1225_ = stack[0].m_num;
lean_object* v_args_1226_ = stack[1].m_obj;
uint8_t v_a_1227_ = stack[2].m_num;
lean_object* v_a_1228_ = stack[3].m_obj;
lean_object* v_a_1229_ = stack[4].m_obj;
lean_object* v_a_1230_ = stack[5].m_obj;
lean_object* v_a_1231_ = stack[6].m_obj;
lean_object* v_a_1232_ = stack[7].m_obj;
lean_object* v_res_1237_;
v_res_1237_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1225_, v_args_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
stack->m_obj
 = v_res_1237_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs___boxed(lean_object* v_pu_1238_, lean_object* v_args_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
uint8_t v_pu_boxed_1247_; uint8_t v_a_boxed_1248_; lean_object* v_res_1249_; 
v_pu_boxed_1247_ = lean_unbox(v_pu_1238_);
v_a_boxed_1248_ = lean_unbox(v_a_1240_);
v_res_1249_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_boxed_1247_, v_args_1239_, v_a_boxed_1248_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
return v_res_1249_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(uint8_t v_pu_1250_, lean_object* v_e_1251_, uint8_t v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v_fvarId_1260_; lean_object* v___y_1261_; lean_object* v_args_1277_; uint8_t v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; 
switch(lean_obj_tag(v_e_1251_))
{
case 2:
{
lean_object* v_struct_1302_; uint8_t v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v_struct_1302_ = lean_ctor_get(v_e_1251_, 2);
v___x_1303_ = 1;
v___x_1304_ = lean_st_ref_get(v_a_1253_);
lean_inc(v_struct_1302_);
v___x_1305_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1304_, v_struct_1302_, v___x_1303_);
lean_dec(v___x_1304_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_fvarId_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1314_; 
v_fvarId_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1314_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_fvarId_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1314_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1310_; lean_object* v___x_1312_; 
v___x_1310_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1250_, v_e_1251_, v_fvarId_1306_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1310_);
v___x_1312_ = v___x_1308_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec_ref_known(v_e_1251_, 3);
v___x_1315_ = lean_box(1);
v___x_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
return v___x_1316_;
}
}
case 3:
{
lean_object* v_args_1317_; lean_object* v___x_1318_; 
v_args_1317_ = lean_ctor_get(v_e_1251_, 2);
lean_inc_ref(v_args_1317_);
v___x_1318_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1250_, v_args_1317_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1327_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1323_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1251_, v_a_1319_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1323_);
v___x_1325_ = v___x_1321_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref_known(v_e_1251_, 3);
v_a_1328_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1318_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1318_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
case 4:
{
lean_object* v_fvarId_1336_; lean_object* v_args_1337_; uint8_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v_fvarId_1336_ = lean_ctor_get(v_e_1251_, 0);
v_args_1337_ = lean_ctor_get(v_e_1251_, 1);
v___x_1338_ = 1;
v___x_1339_ = lean_st_ref_get(v_a_1253_);
lean_inc(v_fvarId_1336_);
v___x_1340_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1339_, v_fvarId_1336_, v___x_1338_);
lean_dec(v___x_1339_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_fvarId_1341_; lean_object* v___x_1342_; 
v_fvarId_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_fvarId_1341_);
lean_dec_ref_known(v___x_1340_, 1);
lean_inc_ref(v_args_1337_);
v___x_1342_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1250_, v_args_1337_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1351_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1347_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___redArg(v_e_1251_, v_fvarId_1341_, v_a_1343_);
lean_dec_ref_known(v_e_1251_, 2);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1347_);
v___x_1349_ = v___x_1345_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec(v_fvarId_1341_);
lean_dec_ref_known(v_e_1251_, 2);
v_a_1352_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1342_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1342_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_dec_ref_known(v_e_1251_, 2);
v___x_1360_ = lean_box(1);
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
return v___x_1361_;
}
}
case 5:
{
lean_object* v_args_1362_; lean_object* v___x_1363_; 
v_args_1362_ = lean_ctor_get(v_e_1251_, 1);
lean_inc_ref(v_args_1362_);
v___x_1363_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1250_, v_args_1362_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1372_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1372_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1372_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1368_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1251_, v_a_1364_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1368_);
v___x_1370_ = v___x_1366_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_dec_ref_known(v_e_1251_, 2);
v_a_1373_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1363_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1363_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
case 6:
{
lean_object* v_var_1381_; 
v_var_1381_ = lean_ctor_get(v_e_1251_, 1);
lean_inc(v_var_1381_);
v_fvarId_1260_ = v_var_1381_;
v___y_1261_ = v_a_1253_;
goto v___jp_1259_;
}
case 7:
{
lean_object* v_var_1382_; 
v_var_1382_ = lean_ctor_get(v_e_1251_, 1);
lean_inc(v_var_1382_);
v_fvarId_1260_ = v_var_1382_;
v___y_1261_ = v_a_1253_;
goto v___jp_1259_;
}
case 8:
{
lean_object* v_var_1383_; uint8_t v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v_var_1383_ = lean_ctor_get(v_e_1251_, 2);
v___x_1384_ = 1;
v___x_1385_ = lean_st_ref_get(v_a_1253_);
lean_inc(v_var_1383_);
v___x_1386_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1385_, v_var_1383_, v___x_1384_);
lean_dec(v___x_1385_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_fvarId_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1395_; 
v_fvarId_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1395_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_fvarId_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1395_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1250_, v_e_1251_, v_fvarId_1387_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1391_);
v___x_1393_ = v___x_1389_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
lean_dec_ref_known(v_e_1251_, 3);
v___x_1396_ = lean_box(1);
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
return v___x_1397_;
}
}
case 9:
{
lean_object* v_args_1398_; 
v_args_1398_ = lean_ctor_get(v_e_1251_, 1);
lean_inc_ref(v_args_1398_);
v_args_1277_ = v_args_1398_;
v___y_1278_ = v_a_1252_;
v___y_1279_ = v_a_1253_;
v___y_1280_ = v_a_1254_;
v___y_1281_ = v_a_1255_;
v___y_1282_ = v_a_1256_;
v___y_1283_ = v_a_1257_;
goto v___jp_1276_;
}
case 10:
{
lean_object* v_args_1399_; 
v_args_1399_ = lean_ctor_get(v_e_1251_, 1);
lean_inc_ref(v_args_1399_);
v_args_1277_ = v_args_1399_;
v___y_1278_ = v_a_1252_;
v___y_1279_ = v_a_1253_;
v___y_1280_ = v_a_1254_;
v___y_1281_ = v_a_1255_;
v___y_1282_ = v_a_1256_;
v___y_1283_ = v_a_1257_;
goto v___jp_1276_;
}
case 11:
{
lean_object* v_n_1400_; lean_object* v_var_1401_; uint8_t v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v_n_1400_ = lean_ctor_get(v_e_1251_, 0);
lean_inc(v_n_1400_);
v_var_1401_ = lean_ctor_get(v_e_1251_, 1);
v___x_1402_ = 1;
v___x_1403_ = lean_st_ref_get(v_a_1253_);
lean_inc(v_var_1401_);
v___x_1404_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1403_, v_var_1401_, v___x_1402_);
lean_dec(v___x_1403_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_fvarId_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1413_; 
v_fvarId_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1413_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_fvarId_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1413_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1409_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp___redArg(v_e_1251_, v_n_1400_, v_fvarId_1405_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v___x_1409_);
v___x_1411_ = v___x_1407_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
else
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
lean_dec(v_n_1400_);
lean_dec_ref_known(v_e_1251_, 2);
v___x_1414_ = lean_box(1);
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
return v___x_1415_;
}
}
case 12:
{
lean_object* v_var_1416_; lean_object* v_i_1417_; uint8_t v_updateHeader_1418_; lean_object* v_args_1419_; uint8_t v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v_var_1416_ = lean_ctor_get(v_e_1251_, 0);
v_i_1417_ = lean_ctor_get(v_e_1251_, 1);
lean_inc_ref(v_i_1417_);
v_updateHeader_1418_ = lean_ctor_get_uint8(v_e_1251_, sizeof(void*)*3);
v_args_1419_ = lean_ctor_get(v_e_1251_, 2);
v___x_1420_ = 1;
v___x_1421_ = lean_st_ref_get(v_a_1253_);
lean_inc(v_var_1416_);
v___x_1422_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1421_, v_var_1416_, v___x_1420_);
lean_dec(v___x_1421_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_fvarId_1423_; lean_object* v___x_1424_; 
v_fvarId_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_fvarId_1423_);
lean_dec_ref_known(v___x_1422_, 1);
lean_inc_ref(v_args_1419_);
v___x_1424_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1250_, v_args_1419_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1433_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1427_ = v___x_1424_;
v_isShared_1428_ = v_isSharedCheck_1433_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1424_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1433_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1429_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp___redArg(v_e_1251_, v_fvarId_1423_, v_i_1417_, v_updateHeader_1418_, v_a_1425_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1429_);
v___x_1431_ = v___x_1427_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec(v_fvarId_1423_);
lean_dec_ref(v_i_1417_);
lean_dec_ref_known(v_e_1251_, 3);
v_a_1434_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1424_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1424_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
else
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
lean_dec_ref(v_i_1417_);
lean_dec_ref_known(v_e_1251_, 3);
v___x_1442_ = lean_box(1);
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
return v___x_1443_;
}
}
case 13:
{
lean_object* v_ty_1444_; lean_object* v_fvarId_1445_; uint8_t v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v_ty_1444_ = lean_ctor_get(v_e_1251_, 0);
lean_inc_ref(v_ty_1444_);
v_fvarId_1445_ = lean_ctor_get(v_e_1251_, 1);
v___x_1446_ = 1;
v___x_1447_ = lean_st_ref_get(v_a_1253_);
lean_inc(v_fvarId_1445_);
v___x_1448_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1447_, v_fvarId_1445_, v___x_1446_);
lean_dec(v___x_1447_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_fvarId_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1457_; 
v_fvarId_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1457_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_fvarId_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1457_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1453_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp___redArg(v_e_1251_, v_ty_1444_, v_fvarId_1449_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1453_);
v___x_1455_ = v___x_1451_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_dec_ref(v_ty_1444_);
lean_dec_ref_known(v_e_1251_, 2);
v___x_1458_ = lean_box(1);
v___x_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
return v___x_1459_;
}
}
case 14:
{
lean_object* v_fvarId_1460_; uint8_t v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v_fvarId_1460_ = lean_ctor_get(v_e_1251_, 0);
v___x_1461_ = 1;
v___x_1462_ = lean_st_ref_get(v_a_1253_);
lean_inc(v_fvarId_1460_);
v___x_1463_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1462_, v_fvarId_1460_, v___x_1461_);
lean_dec(v___x_1462_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_fvarId_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1472_; 
v_fvarId_1464_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1466_ = v___x_1463_;
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_fvarId_1464_);
lean_dec(v___x_1463_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1468_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp___redArg(v_e_1251_, v_fvarId_1464_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v___x_1468_);
v___x_1470_ = v___x_1466_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
else
{
lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1480_; 
v_isSharedCheck_1480_ = !lean_is_exclusive(v_e_1251_);
if (v_isSharedCheck_1480_ == 0)
{
lean_object* v_unused_1481_; 
v_unused_1481_ = lean_ctor_get(v_e_1251_, 0);
lean_dec(v_unused_1481_);
v___x_1474_ = v_e_1251_;
v_isShared_1475_ = v_isSharedCheck_1480_;
goto v_resetjp_1473_;
}
else
{
lean_dec(v_e_1251_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1480_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1476_ = lean_box(1);
if (v_isShared_1475_ == 0)
{
lean_ctor_set_tag(v___x_1474_, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1476_);
v___x_1478_ = v___x_1474_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
case 15:
{
lean_object* v_fvarId_1482_; uint8_t v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v_fvarId_1482_ = lean_ctor_get(v_e_1251_, 0);
v___x_1483_ = 1;
v___x_1484_ = lean_st_ref_get(v_a_1253_);
lean_inc(v_fvarId_1482_);
v___x_1485_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1484_, v_fvarId_1482_, v___x_1483_);
lean_dec(v___x_1484_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_fvarId_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1494_; 
v_fvarId_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_fvarId_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1490_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp___redArg(v_e_1251_, v_fvarId_1486_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1490_);
v___x_1492_ = v___x_1488_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
else
{
lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1502_; 
v_isSharedCheck_1502_ = !lean_is_exclusive(v_e_1251_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; 
v_unused_1503_ = lean_ctor_get(v_e_1251_, 0);
lean_dec(v_unused_1503_);
v___x_1496_ = v_e_1251_;
v_isShared_1497_ = v_isSharedCheck_1502_;
goto v_resetjp_1495_;
}
else
{
lean_dec(v_e_1251_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1502_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1498_ = lean_box(1);
if (v_isShared_1497_ == 0)
{
lean_ctor_set_tag(v___x_1496_, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1498_);
v___x_1500_ = v___x_1496_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
default: 
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1504_, 0, v_e_1251_);
return v___x_1504_;
}
}
v___jp_1259_:
{
uint8_t v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = 1;
v___x_1263_ = lean_st_ref_get(v___y_1261_);
v___x_1264_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1263_, v_fvarId_1260_, v___x_1262_);
lean_dec(v___x_1263_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_fvarId_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1273_; 
v_fvarId_1265_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1267_ = v___x_1264_;
v_isShared_1268_ = v_isSharedCheck_1273_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_fvarId_1265_);
lean_dec(v___x_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1273_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1269_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1250_, v_e_1251_, v_fvarId_1265_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1269_);
v___x_1271_ = v___x_1267_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
lean_dec(v_e_1251_);
v___x_1274_ = lean_box(1);
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
return v___x_1275_;
}
}
v___jp_1276_:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1250_, v_args_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1293_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1289_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1251_, v_a_1285_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1289_);
v___x_1291_ = v___x_1287_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec(v_e_1251_);
v_a_1294_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1284_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1284_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1250_ = stack[0].m_num;
lean_object* v_e_1251_ = stack[1].m_obj;
uint8_t v_a_1252_ = stack[2].m_num;
lean_object* v_a_1253_ = stack[3].m_obj;
lean_object* v_a_1254_ = stack[4].m_obj;
lean_object* v_a_1255_ = stack[5].m_obj;
lean_object* v_a_1256_ = stack[6].m_obj;
lean_object* v_a_1257_ = stack[7].m_obj;
lean_object* v_res_1505_;
v_res_1505_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_1250_, v_e_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
stack->m_obj
 = v_res_1505_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue___boxed(lean_object* v_pu_1506_, lean_object* v_e_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
uint8_t v_pu_boxed_1515_; uint8_t v_a_boxed_1516_; lean_object* v_res_1517_; 
v_pu_boxed_1515_ = lean_unbox(v_pu_1506_);
v_a_boxed_1516_ = lean_unbox(v_a_1508_);
v_res_1517_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_boxed_1515_, v_e_1507_, v_a_boxed_1516_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
lean_dec(v_a_1513_);
lean_dec_ref(v_a_1512_);
lean_dec(v_a_1511_);
lean_dec_ref(v_a_1510_);
lean_dec(v_a_1509_);
return v_res_1517_;
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(uint8_t v_pu_1518_, lean_object* v_decl_1519_, uint8_t v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v_fvarId_1527_; lean_object* v_binderName_1528_; lean_object* v_type_1529_; lean_object* v_value_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1588_; 
v_fvarId_1527_ = lean_ctor_get(v_decl_1519_, 0);
v_binderName_1528_ = lean_ctor_get(v_decl_1519_, 1);
v_type_1529_ = lean_ctor_get(v_decl_1519_, 2);
v_value_1530_ = lean_ctor_get(v_decl_1519_, 3);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_decl_1519_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1532_ = v_decl_1519_;
v_isShared_1533_ = v_isSharedCheck_1588_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_value_1530_);
lean_inc(v_type_1529_);
lean_inc(v_binderName_1528_);
lean_inc(v_fvarId_1527_);
lean_dec(v_decl_1519_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1588_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v_a_1535_; lean_object* v___x_1536_; 
v___x_1534_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_1528_, v_a_1520_, v_a_1523_);
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref(v___x_1534_);
v___x_1536_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1518_, v_type_1529_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1538_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1536_, 1);
v___x_1538_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_1518_, v_value_1530_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1540_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1538_, 1);
v___x_1540_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_1527_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1563_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1563_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1563_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 3, v_a_1539_);
lean_ctor_set(v___x_1532_, 2, v_a_1537_);
lean_ctor_set(v___x_1532_, 1, v_a_1535_);
lean_ctor_set(v___x_1532_, 0, v_a_1541_);
v___x_1546_ = v___x_1532_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1541_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_a_1535_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_a_1537_);
lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_a_1539_);
v___x_1546_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1547_; lean_object* v_lctx_1548_; lean_object* v_nextIdx_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1561_; 
v___x_1547_ = lean_st_ref_take(v_a_1523_);
v_lctx_1548_ = lean_ctor_get(v___x_1547_, 0);
v_nextIdx_1549_ = lean_ctor_get(v___x_1547_, 1);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1551_ = v___x_1547_;
v_isShared_1552_ = v_isSharedCheck_1561_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_nextIdx_1549_);
lean_inc(v_lctx_1548_);
lean_dec(v___x_1547_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1561_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; lean_object* v___x_1555_; 
lean_inc_ref(v___x_1546_);
v___x_1553_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_1518_, v_lctx_1548_, v___x_1546_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1553_);
v___x_1555_ = v___x_1551_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_nextIdx_1549_);
v___x_1555_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1556_ = lean_st_ref_put(v_a_1523_, v___x_1555_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v___x_1546_);
v___x_1558_ = v___x_1543_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1546_);
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
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec(v_a_1539_);
lean_dec(v_a_1537_);
lean_dec(v_a_1535_);
lean_del_object(v___x_1532_);
v_a_1564_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1540_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1540_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec(v_a_1537_);
lean_dec(v_a_1535_);
lean_del_object(v___x_1532_);
lean_dec(v_fvarId_1527_);
v_a_1572_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1538_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1538_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec(v_a_1535_);
lean_del_object(v___x_1532_);
lean_dec(v_value_1530_);
lean_dec(v_fvarId_1527_);
v_a_1580_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1536_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1536_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1518_ = stack[0].m_num;
lean_object* v_decl_1519_ = stack[1].m_obj;
uint8_t v_a_1520_ = stack[2].m_num;
lean_object* v_a_1521_ = stack[3].m_obj;
lean_object* v_a_1522_ = stack[4].m_obj;
lean_object* v_a_1523_ = stack[5].m_obj;
lean_object* v_a_1524_ = stack[6].m_obj;
lean_object* v_a_1525_ = stack[7].m_obj;
lean_object* v_res_1589_;
v_res_1589_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_1518_, v_decl_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
stack->m_obj
 = v_res_1589_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(lean_object* v_pu_1590_, lean_object* v_decl_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
uint8_t v_pu_boxed_1599_; uint8_t v_a_boxed_1600_; lean_object* v_res_1601_; 
v_pu_boxed_1599_ = lean_unbox(v_pu_1590_);
v_a_boxed_1600_ = lean_unbox(v_a_1592_);
v_res_1601_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_boxed_1599_, v_decl_1591_, v_a_boxed_1600_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
lean_dec(v_a_1595_);
lean_dec_ref(v_a_1594_);
lean_dec(v_a_1593_);
return v_res_1601_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(uint8_t v_pu_1602_, size_t v_sz_1603_, size_t v_i_1604_, lean_object* v_bs_1605_, uint8_t v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
uint8_t v___x_1613_; 
v___x_1613_ = lean_usize_dec_lt(v_i_1604_, v_sz_1603_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1614_, 0, v_bs_1605_);
return v___x_1614_;
}
else
{
lean_object* v_v_1615_; lean_object* v___x_1616_; lean_object* v_bs_x27_1617_; lean_object* v___x_1618_; 
v_v_1615_ = lean_array_uget(v_bs_1605_, v_i_1604_);
v___x_1616_ = lean_unsigned_to_nat(0u);
v_bs_x27_1617_ = lean_array_uset(v_bs_1605_, v_i_1604_, v___x_1616_);
v___x_1618_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_1602_, v_v_1615_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; size_t v___x_1620_; size_t v___x_1621_; lean_object* v___x_1622_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref_known(v___x_1618_, 1);
v___x_1620_ = ((size_t)1ULL);
v___x_1621_ = lean_usize_add(v_i_1604_, v___x_1620_);
v___x_1622_ = lean_array_uset(v_bs_x27_1617_, v_i_1604_, v_a_1619_);
v_i_1604_ = v___x_1621_;
v_bs_1605_ = v___x_1622_;
goto _start;
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec_ref(v_bs_x27_1617_);
v_a_1624_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1618_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1618_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1602_ = stack[0].m_num;
size_t v_sz_1603_ = stack[1].m_num;
size_t v_i_1604_ = stack[2].m_num;
lean_object* v_bs_1605_ = stack[3].m_obj;
uint8_t v___y_1606_ = stack[4].m_num;
lean_object* v___y_1607_ = stack[5].m_obj;
lean_object* v___y_1608_ = stack[6].m_obj;
lean_object* v___y_1609_ = stack[7].m_obj;
lean_object* v___y_1610_ = stack[8].m_obj;
lean_object* v___y_1611_ = stack[9].m_obj;
lean_object* v_res_1632_;
v_res_1632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_1602_, v_sz_1603_, v_i_1604_, v_bs_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
stack->m_obj
 = v_res_1632_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0___boxed(lean_object* v_pu_1633_, lean_object* v_sz_1634_, lean_object* v_i_1635_, lean_object* v_bs_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
uint8_t v_pu_boxed_1644_; size_t v_sz_boxed_1645_; size_t v_i_boxed_1646_; uint8_t v___y_26361__boxed_1647_; lean_object* v_res_1648_; 
v_pu_boxed_1644_ = lean_unbox(v_pu_1633_);
v_sz_boxed_1645_ = lean_unbox_usize(v_sz_1634_);
lean_dec(v_sz_1634_);
v_i_boxed_1646_ = lean_unbox_usize(v_i_1635_);
lean_dec(v_i_1635_);
v___y_26361__boxed_1647_ = lean_unbox(v___y_1637_);
v_res_1648_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_boxed_1644_, v_sz_boxed_1645_, v_i_boxed_1646_, v_bs_1636_, v___y_26361__boxed_1647_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
return v_res_1648_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(uint8_t v_pu_1649_, size_t v_sz_1650_, size_t v_i_1651_, lean_object* v_bs_1652_, uint8_t v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
uint8_t v___x_1660_; 
v___x_1660_ = lean_usize_dec_lt(v_i_1651_, v_sz_1650_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1661_, 0, v_bs_1652_);
return v___x_1661_;
}
else
{
lean_object* v_v_1662_; lean_object* v___x_1663_; lean_object* v_bs_x27_1664_; lean_object* v_a_1666_; 
v_v_1662_ = lean_array_uget(v_bs_1652_, v_i_1651_);
v___x_1663_ = lean_unsigned_to_nat(0u);
v_bs_x27_1664_ = lean_array_uset(v_bs_1652_, v_i_1651_, v___x_1663_);
switch(lean_obj_tag(v_v_1662_))
{
case 0:
{
lean_object* v_ctorName_1671_; lean_object* v_params_1672_; lean_object* v_code_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1694_; 
v_ctorName_1671_ = lean_ctor_get(v_v_1662_, 0);
v_params_1672_ = lean_ctor_get(v_v_1662_, 1);
v_code_1673_ = lean_ctor_get(v_v_1662_, 2);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_v_1662_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1675_ = v_v_1662_;
v_isShared_1676_ = v_isSharedCheck_1694_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_code_1673_);
lean_inc(v_params_1672_);
lean_inc(v_ctorName_1671_);
lean_dec(v_v_1662_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1694_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
size_t v_sz_1677_; size_t v___x_1678_; lean_object* v___x_1679_; 
v_sz_1677_ = lean_array_size(v_params_1672_);
v___x_1678_ = ((size_t)0ULL);
v___x_1679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_1649_, v_sz_1677_, v___x_1678_, v_params_1672_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1681_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1679_, 1);
v___x_1681_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1649_, v_code_1673_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v___x_1684_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___x_1681_, 1);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 2, v_a_1682_);
lean_ctor_set(v___x_1675_, 1, v_a_1680_);
v___x_1684_ = v___x_1675_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_ctorName_1671_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_a_1680_);
lean_ctor_set(v_reuseFailAlloc_1685_, 2, v_a_1682_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
v_a_1666_ = v___x_1684_;
goto v___jp_1665_;
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_a_1680_);
lean_del_object(v___x_1675_);
lean_dec(v_ctorName_1671_);
lean_dec_ref(v_bs_x27_1664_);
v_a_1686_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1681_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1681_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
else
{
lean_del_object(v___x_1675_);
lean_dec_ref(v_code_1673_);
lean_dec(v_ctorName_1671_);
lean_dec_ref(v_bs_x27_1664_);
return v___x_1679_;
}
}
}
case 1:
{
lean_object* v_info_1695_; lean_object* v_code_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1713_; 
v_info_1695_ = lean_ctor_get(v_v_1662_, 0);
v_code_1696_ = lean_ctor_get(v_v_1662_, 1);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_v_1662_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1698_ = v_v_1662_;
v_isShared_1699_ = v_isSharedCheck_1713_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_code_1696_);
lean_inc(v_info_1695_);
lean_dec(v_v_1662_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1713_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1649_, v_code_1696_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1703_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1701_);
lean_dec_ref_known(v___x_1700_, 1);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 1, v_a_1701_);
v___x_1703_ = v___x_1698_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_info_1695_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_a_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
v_a_1666_ = v___x_1703_;
goto v___jp_1665_;
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_del_object(v___x_1698_);
lean_dec_ref(v_info_1695_);
lean_dec_ref(v_bs_x27_1664_);
v_a_1705_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1700_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1700_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
default: 
{
lean_object* v_code_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1731_; 
v_code_1714_ = lean_ctor_get(v_v_1662_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_v_1662_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1716_ = v_v_1662_;
v_isShared_1717_ = v_isSharedCheck_1731_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_code_1714_);
lean_dec(v_v_1662_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1731_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1649_, v_code_1714_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1721_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v_a_1719_);
v___x_1721_ = v___x_1716_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1719_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
v_a_1666_ = v___x_1721_;
goto v___jp_1665_;
}
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_del_object(v___x_1716_);
lean_dec_ref(v_bs_x27_1664_);
v_a_1723_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1718_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1718_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
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
}
}
v___jp_1665_:
{
size_t v___x_1667_; size_t v___x_1668_; lean_object* v___x_1669_; 
v___x_1667_ = ((size_t)1ULL);
v___x_1668_ = lean_usize_add(v_i_1651_, v___x_1667_);
v___x_1669_ = lean_array_uset(v_bs_x27_1664_, v_i_1651_, v_a_1666_);
v_i_1651_ = v___x_1668_;
v_bs_1652_ = v___x_1669_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1649_ = stack[0].m_num;
size_t v_sz_1650_ = stack[1].m_num;
size_t v_i_1651_ = stack[2].m_num;
lean_object* v_bs_1652_ = stack[3].m_obj;
uint8_t v___y_1653_ = stack[4].m_num;
lean_object* v___y_1654_ = stack[5].m_obj;
lean_object* v___y_1655_ = stack[6].m_obj;
lean_object* v___y_1656_ = stack[7].m_obj;
lean_object* v___y_1657_ = stack[8].m_obj;
lean_object* v___y_1658_ = stack[9].m_obj;
lean_object* v_res_1732_;
v_res_1732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_1649_, v_sz_1650_, v_i_1651_, v_bs_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
stack->m_obj
 = v_res_1732_;
}
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t v_pu_1733_, lean_object* v_code_1734_, uint8_t v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
switch(lean_obj_tag(v_code_1734_))
{
case 0:
{
lean_object* v_decl_1742_; lean_object* v_k_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1769_; 
v_decl_1742_ = lean_ctor_get(v_code_1734_, 0);
v_k_1743_ = lean_ctor_get(v_code_1734_, 1);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_code_1734_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1745_ = v_code_1734_;
v_isShared_1746_ = v_isSharedCheck_1769_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_k_1743_);
lean_inc(v_decl_1742_);
lean_dec(v_code_1734_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1769_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_1733_, v_decl_1742_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1749_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref_known(v___x_1747_, 1);
v___x_1749_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1733_, v_k_1743_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1760_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1760_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1760_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v_a_1750_);
lean_ctor_set(v___x_1745_, 0, v_a_1748_);
v___x_1755_ = v___x_1745_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1748_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1757_; 
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1755_);
v___x_1757_ = v___x_1752_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
else
{
lean_dec(v_a_1748_);
lean_del_object(v___x_1745_);
return v___x_1749_;
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_del_object(v___x_1745_);
lean_dec_ref(v_k_1743_);
v_a_1761_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1747_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1747_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_1770_; lean_object* v_k_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1797_; 
v_decl_1770_ = lean_ctor_get(v_code_1734_, 0);
v_k_1771_ = lean_ctor_get(v_code_1734_, 1);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_code_1734_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1773_ = v_code_1734_;
v_isShared_1774_ = v_isSharedCheck_1797_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_k_1771_);
lean_inc(v_decl_1770_);
lean_dec(v_code_1734_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1797_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1733_, v_decl_1770_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1777_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref_known(v___x_1775_, 1);
v___x_1777_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1733_, v_k_1771_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1788_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1788_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1788_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 1, v_a_1778_);
lean_ctor_set(v___x_1773_, 0, v_a_1776_);
v___x_1783_ = v___x_1773_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1776_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1785_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1783_);
v___x_1785_ = v___x_1780_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
else
{
lean_dec(v_a_1776_);
lean_del_object(v___x_1773_);
return v___x_1777_;
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_del_object(v___x_1773_);
lean_dec_ref(v_k_1771_);
v_a_1789_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1775_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1775_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
case 2:
{
lean_object* v_decl_1798_; lean_object* v_k_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1825_; 
v_decl_1798_ = lean_ctor_get(v_code_1734_, 0);
v_k_1799_ = lean_ctor_get(v_code_1734_, 1);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_code_1734_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1801_ = v_code_1734_;
v_isShared_1802_ = v_isSharedCheck_1825_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_k_1799_);
lean_inc(v_decl_1798_);
lean_dec(v_code_1734_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1825_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1733_, v_decl_1798_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1805_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1804_);
lean_dec_ref_known(v___x_1803_, 1);
v___x_1805_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1733_, v_k_1799_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
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
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v_a_1806_);
lean_ctor_set(v___x_1801_, 0, v_a_1804_);
v___x_1811_ = v___x_1801_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1804_);
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
lean_dec(v_a_1804_);
lean_del_object(v___x_1801_);
return v___x_1805_;
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_del_object(v___x_1801_);
lean_dec_ref(v_k_1799_);
v_a_1817_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1803_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1803_);
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
}
case 3:
{
lean_object* v_fvarId_1826_; lean_object* v_args_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1856_; 
v_fvarId_1826_ = lean_ctor_get(v_code_1734_, 0);
v_args_1827_ = lean_ctor_get(v_code_1734_, 1);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_code_1734_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1829_ = v_code_1734_;
v_isShared_1830_ = v_isSharedCheck_1856_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_args_1827_);
lean_inc(v_fvarId_1826_);
lean_dec(v_code_1734_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1856_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
uint8_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1831_ = 1;
v___x_1832_ = lean_st_ref_get(v_a_1736_);
v___x_1833_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1832_, v_fvarId_1826_, v___x_1831_);
lean_dec(v___x_1832_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_fvarId_1834_; lean_object* v___x_1835_; 
v_fvarId_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_fvarId_1834_);
lean_dec_ref_known(v___x_1833_, 1);
v___x_1835_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1733_, v_args_1827_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1846_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1846_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1846_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 1, v_a_1836_);
lean_ctor_set(v___x_1829_, 0, v_fvarId_1834_);
v___x_1841_ = v___x_1829_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_fvarId_1834_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1843_; 
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1841_);
v___x_1843_ = v___x_1838_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v_fvarId_1834_);
lean_del_object(v___x_1829_);
v_a_1847_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1835_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1835_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
else
{
lean_object* v___x_1855_; 
lean_del_object(v___x_1829_);
lean_dec_ref(v_args_1827_);
v___x_1855_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1733_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_1855_;
}
}
}
case 4:
{
lean_object* v_cases_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1909_; 
v_cases_1857_ = lean_ctor_get(v_code_1734_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_code_1734_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1859_ = v_code_1734_;
v_isShared_1860_ = v_isSharedCheck_1909_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_cases_1857_);
lean_dec(v_code_1734_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1909_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v_typeName_1861_; lean_object* v_resultType_1862_; lean_object* v_discr_1863_; lean_object* v_alts_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1908_; 
v_typeName_1861_ = lean_ctor_get(v_cases_1857_, 0);
v_resultType_1862_ = lean_ctor_get(v_cases_1857_, 1);
v_discr_1863_ = lean_ctor_get(v_cases_1857_, 2);
v_alts_1864_ = lean_ctor_get(v_cases_1857_, 3);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_cases_1857_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1866_ = v_cases_1857_;
v_isShared_1867_ = v_isSharedCheck_1908_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_alts_1864_);
lean_inc(v_discr_1863_);
lean_inc(v_resultType_1862_);
lean_inc(v_typeName_1861_);
lean_dec(v_cases_1857_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1908_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
uint8_t v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1868_ = 1;
v___x_1869_ = lean_st_ref_get(v_a_1736_);
v___x_1870_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1869_, v_discr_1863_, v___x_1868_);
lean_dec(v___x_1869_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_fvarId_1871_; lean_object* v___x_1872_; 
v_fvarId_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_fvarId_1871_);
lean_dec_ref_known(v___x_1870_, 1);
v___x_1872_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1733_, v_resultType_1862_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; size_t v_sz_1874_; size_t v___x_1875_; lean_object* v___x_1876_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
v_sz_1874_ = lean_array_size(v_alts_1864_);
v___x_1875_ = ((size_t)0ULL);
v___x_1876_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_1733_, v_sz_1874_, v___x_1875_, v_alts_1864_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1890_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1890_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1890_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 3, v_a_1877_);
lean_ctor_set(v___x_1866_, 2, v_fvarId_1871_);
lean_ctor_set(v___x_1866_, 1, v_a_1873_);
v___x_1882_ = v___x_1866_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_typeName_1861_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_a_1873_);
lean_ctor_set(v_reuseFailAlloc_1889_, 2, v_fvarId_1871_);
lean_ctor_set(v_reuseFailAlloc_1889_, 3, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1884_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1882_);
v___x_1884_ = v___x_1859_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1886_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1884_);
v___x_1886_ = v___x_1879_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec(v_a_1873_);
lean_dec(v_fvarId_1871_);
lean_del_object(v___x_1866_);
lean_dec(v_typeName_1861_);
lean_del_object(v___x_1859_);
v_a_1891_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1876_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1876_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec(v_fvarId_1871_);
lean_del_object(v___x_1866_);
lean_dec_ref(v_alts_1864_);
lean_dec(v_typeName_1861_);
lean_del_object(v___x_1859_);
v_a_1899_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1872_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1872_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
else
{
lean_object* v___x_1907_; 
lean_del_object(v___x_1866_);
lean_dec_ref(v_alts_1864_);
lean_dec_ref(v_resultType_1862_);
lean_dec(v_typeName_1861_);
lean_del_object(v___x_1859_);
v___x_1907_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1733_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_1907_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1929_; 
v_fvarId_1910_ = lean_ctor_get(v_code_1734_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_code_1734_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1912_ = v_code_1734_;
v_isShared_1913_ = v_isSharedCheck_1929_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_fvarId_1910_);
lean_dec(v_code_1734_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1929_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
uint8_t v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = 1;
v___x_1915_ = lean_st_ref_get(v_a_1736_);
v___x_1916_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1915_, v_fvarId_1910_, v___x_1914_);
lean_dec(v___x_1915_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_fvarId_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1927_; 
v_fvarId_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1927_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_fvarId_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1927_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 0, v_fvarId_1917_);
v___x_1922_ = v___x_1912_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_fvarId_1917_);
v___x_1922_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1924_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1922_);
v___x_1924_ = v___x_1919_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
else
{
lean_object* v___x_1928_; 
lean_del_object(v___x_1912_);
v___x_1928_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1733_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_1928_;
}
}
}
case 6:
{
lean_object* v_type_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1954_; 
v_type_1930_ = lean_ctor_get(v_code_1734_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v_code_1734_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1932_ = v_code_1734_;
v_isShared_1933_ = v_isSharedCheck_1954_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_type_1930_);
lean_dec(v_code_1734_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1954_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; 
v___x_1934_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1733_, v_type_1930_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1945_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_1945_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1945_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v_a_1935_);
v___x_1940_ = v___x_1932_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___x_1942_; 
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v___x_1940_);
v___x_1942_ = v___x_1937_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_del_object(v___x_1932_);
v_a_1946_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1934_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1934_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_1955_; lean_object* v_i_1956_; lean_object* v_y_1957_; lean_object* v_k_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1981_; 
v_fvarId_1955_ = lean_ctor_get(v_code_1734_, 0);
v_i_1956_ = lean_ctor_get(v_code_1734_, 1);
v_y_1957_ = lean_ctor_get(v_code_1734_, 2);
v_k_1958_ = lean_ctor_get(v_code_1734_, 3);
v_isSharedCheck_1981_ = !lean_is_exclusive(v_code_1734_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1960_ = v_code_1734_;
v_isShared_1961_ = v_isSharedCheck_1981_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_k_1958_);
lean_inc(v_y_1957_);
lean_inc(v_i_1956_);
lean_inc(v_fvarId_1955_);
lean_dec(v_code_1734_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1981_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
uint8_t v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1962_ = 1;
v___x_1963_ = lean_st_ref_get(v_a_1736_);
v___x_1964_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1963_, v_fvarId_1955_, v___x_1962_);
lean_dec(v___x_1963_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_fvarId_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v_fvarId_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_fvarId_1965_);
lean_dec_ref_known(v___x_1964_, 1);
v___x_1966_ = lean_st_ref_get(v_a_1736_);
v___x_1967_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1733_, v___x_1966_, v_y_1957_, v___x_1962_);
lean_dec(v___x_1966_);
v___x_1968_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1733_, v_k_1958_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1979_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_1979_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1979_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 3, v_a_1969_);
lean_ctor_set(v___x_1960_, 2, v___x_1967_);
lean_ctor_set(v___x_1960_, 0, v_fvarId_1965_);
v___x_1974_ = v___x_1960_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_fvarId_1965_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_i_1956_);
lean_ctor_set(v_reuseFailAlloc_1978_, 2, v___x_1967_);
lean_ctor_set(v_reuseFailAlloc_1978_, 3, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
lean_object* v___x_1976_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v___x_1974_);
v___x_1976_ = v___x_1971_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1974_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
else
{
lean_dec(v___x_1967_);
lean_dec(v_fvarId_1965_);
lean_del_object(v___x_1960_);
lean_dec(v_i_1956_);
return v___x_1968_;
}
}
else
{
lean_object* v___x_1980_; 
lean_del_object(v___x_1960_);
lean_dec_ref(v_k_1958_);
lean_dec(v_y_1957_);
lean_dec(v_i_1956_);
v___x_1980_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1733_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_1980_;
}
}
}
case 8:
{
lean_object* v_fvarId_1982_; lean_object* v_i_1983_; lean_object* v_y_1984_; lean_object* v_k_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2010_; 
v_fvarId_1982_ = lean_ctor_get(v_code_1734_, 0);
v_i_1983_ = lean_ctor_get(v_code_1734_, 1);
v_y_1984_ = lean_ctor_get(v_code_1734_, 2);
v_k_1985_ = lean_ctor_get(v_code_1734_, 3);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_code_1734_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1987_ = v_code_1734_;
v_isShared_1988_ = v_isSharedCheck_2010_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_k_1985_);
lean_inc(v_y_1984_);
lean_inc(v_i_1983_);
lean_inc(v_fvarId_1982_);
lean_dec(v_code_1734_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2010_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
uint8_t v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = 1;
v___x_1990_ = lean_st_ref_get(v_a_1736_);
v___x_1991_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1990_, v_fvarId_1982_, v___x_1989_);
lean_dec(v___x_1990_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_fvarId_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v_fvarId_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_fvarId_1992_);
lean_dec_ref_known(v___x_1991_, 1);
v___x_1993_ = lean_st_ref_get(v_a_1736_);
v___x_1994_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1993_, v_y_1984_, v___x_1989_);
lean_dec(v___x_1993_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_fvarId_1995_; lean_object* v___x_1996_; 
v_fvarId_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_fvarId_1995_);
lean_dec_ref_known(v___x_1994_, 1);
v___x_1996_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1733_, v_k_1985_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2007_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1999_ = v___x_1996_;
v_isShared_2000_ = v_isSharedCheck_2007_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1996_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2007_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 3, v_a_1997_);
lean_ctor_set(v___x_1987_, 2, v_fvarId_1995_);
lean_ctor_set(v___x_1987_, 0, v_fvarId_1992_);
v___x_2002_ = v___x_1987_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_fvarId_1992_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_i_1983_);
lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_fvarId_1995_);
lean_ctor_set(v_reuseFailAlloc_2006_, 3, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2004_; 
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v___x_2002_);
v___x_2004_ = v___x_1999_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
else
{
lean_dec(v_fvarId_1995_);
lean_dec(v_fvarId_1992_);
lean_del_object(v___x_1987_);
lean_dec(v_i_1983_);
return v___x_1996_;
}
}
else
{
lean_object* v___x_2008_; 
lean_dec(v_fvarId_1992_);
lean_del_object(v___x_1987_);
lean_dec_ref(v_k_1985_);
lean_dec(v_i_1983_);
v___x_2008_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1733_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_2008_;
}
}
else
{
lean_object* v___x_2009_; 
lean_del_object(v___x_1987_);
lean_dec_ref(v_k_1985_);
lean_dec(v_y_1984_);
lean_dec(v_i_1983_);
v___x_2009_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1733_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_2009_;
}
}
}
case 9:
{
lean_object* v_fvarId_2011_; lean_object* v_i_2012_; lean_object* v_offset_2013_; lean_object* v_y_2014_; lean_object* v_ty_2015_; lean_object* v_k_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2051_; 
v_fvarId_2011_ = lean_ctor_get(v_code_1734_, 0);
v_i_2012_ = lean_ctor_get(v_code_1734_, 1);
v_offset_2013_ = lean_ctor_get(v_code_1734_, 2);
v_y_2014_ = lean_ctor_get(v_code_1734_, 3);
v_ty_2015_ = lean_ctor_get(v_code_1734_, 4);
v_k_2016_ = lean_ctor_get(v_code_1734_, 5);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_code_1734_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2018_ = v_code_1734_;
v_isShared_2019_ = v_isSharedCheck_2051_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_k_2016_);
lean_inc(v_ty_2015_);
lean_inc(v_y_2014_);
lean_inc(v_offset_2013_);
lean_inc(v_i_2012_);
lean_inc(v_fvarId_2011_);
lean_dec(v_code_1734_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2051_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
uint8_t v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2020_ = 1;
v___x_2021_ = lean_st_ref_get(v_a_1736_);
v___x_2022_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2021_, v_fvarId_2011_, v___x_2020_);
lean_dec(v___x_2021_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_fvarId_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v_fvarId_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_fvarId_2023_);
lean_dec_ref_known(v___x_2022_, 1);
v___x_2024_ = lean_st_ref_get(v_a_1736_);
v___x_2025_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2024_, v_y_2014_, v___x_2020_);
lean_dec(v___x_2024_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_fvarId_2026_; lean_object* v___x_2027_; 
v_fvarId_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_fvarId_2026_);
lean_dec_ref_known(v___x_2025_, 1);
v___x_2027_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1733_, v_ty_2015_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2029_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2027_, 1);
v___x_2029_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1733_, v_k_2016_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2040_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2032_ = v___x_2029_;
v_isShared_2033_ = v_isSharedCheck_2040_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2029_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2040_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 5, v_a_2030_);
lean_ctor_set(v___x_2018_, 4, v_a_2028_);
lean_ctor_set(v___x_2018_, 3, v_fvarId_2026_);
lean_ctor_set(v___x_2018_, 0, v_fvarId_2023_);
v___x_2035_ = v___x_2018_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_fvarId_2023_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_i_2012_);
lean_ctor_set(v_reuseFailAlloc_2039_, 2, v_offset_2013_);
lean_ctor_set(v_reuseFailAlloc_2039_, 3, v_fvarId_2026_);
lean_ctor_set(v_reuseFailAlloc_2039_, 4, v_a_2028_);
lean_ctor_set(v_reuseFailAlloc_2039_, 5, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2037_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v___x_2035_);
v___x_2037_ = v___x_2032_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
else
{
lean_dec(v_a_2028_);
lean_dec(v_fvarId_2026_);
lean_dec(v_fvarId_2023_);
lean_del_object(v___x_2018_);
lean_dec(v_offset_2013_);
lean_dec(v_i_2012_);
return v___x_2029_;
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec(v_fvarId_2026_);
lean_dec(v_fvarId_2023_);
lean_del_object(v___x_2018_);
lean_dec_ref(v_k_2016_);
lean_dec(v_offset_2013_);
lean_dec(v_i_2012_);
v_a_2041_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2027_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2027_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
else
{
lean_object* v___x_2049_; 
lean_dec(v_fvarId_2023_);
lean_del_object(v___x_2018_);
lean_dec_ref(v_k_2016_);
lean_dec_ref(v_ty_2015_);
lean_dec(v_offset_2013_);
lean_dec(v_i_2012_);
v___x_2049_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1733_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_2049_;
}
}
else
{
lean_object* v___x_2050_; 
lean_del_object(v___x_2018_);
lean_dec_ref(v_k_2016_);
lean_dec_ref(v_ty_2015_);
lean_dec(v_y_2014_);
lean_dec(v_offset_2013_);
lean_dec(v_i_2012_);
v___x_2050_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1733_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_2050_;
}
}
}
case 10:
{
lean_object* v_fvarId_2052_; lean_object* v_cidx_2053_; lean_object* v_k_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2075_; 
v_fvarId_2052_ = lean_ctor_get(v_code_1734_, 0);
v_cidx_2053_ = lean_ctor_get(v_code_1734_, 1);
v_k_2054_ = lean_ctor_get(v_code_1734_, 2);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_code_1734_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2056_ = v_code_1734_;
v_isShared_2057_ = v_isSharedCheck_2075_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_k_2054_);
lean_inc(v_cidx_2053_);
lean_inc(v_fvarId_2052_);
lean_dec(v_code_1734_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2075_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
uint8_t v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2058_ = 1;
v___x_2059_ = lean_st_ref_get(v_a_1736_);
v___x_2060_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2059_, v_fvarId_2052_, v___x_2058_);
lean_dec(v___x_2059_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_fvarId_2061_; lean_object* v___x_2062_; 
v_fvarId_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_fvarId_2061_);
lean_dec_ref_known(v___x_2060_, 1);
v___x_2062_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1733_, v_k_2054_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2073_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2073_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2073_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 2, v_a_2063_);
lean_ctor_set(v___x_2056_, 0, v_fvarId_2061_);
v___x_2068_ = v___x_2056_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_fvarId_2061_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_cidx_2053_);
lean_ctor_set(v_reuseFailAlloc_2072_, 2, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2070_; 
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2068_);
v___x_2070_ = v___x_2065_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
else
{
lean_dec(v_fvarId_2061_);
lean_del_object(v___x_2056_);
lean_dec(v_cidx_2053_);
return v___x_2062_;
}
}
else
{
lean_object* v___x_2074_; 
lean_del_object(v___x_2056_);
lean_dec_ref(v_k_2054_);
lean_dec(v_cidx_2053_);
v___x_2074_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1733_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_2074_;
}
}
}
case 11:
{
lean_object* v_fvarId_2076_; lean_object* v_n_2077_; uint8_t v_check_2078_; uint8_t v_persistent_2079_; lean_object* v_k_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2101_; 
v_fvarId_2076_ = lean_ctor_get(v_code_1734_, 0);
v_n_2077_ = lean_ctor_get(v_code_1734_, 1);
v_check_2078_ = lean_ctor_get_uint8(v_code_1734_, sizeof(void*)*3);
v_persistent_2079_ = lean_ctor_get_uint8(v_code_1734_, sizeof(void*)*3 + 1);
v_k_2080_ = lean_ctor_get(v_code_1734_, 2);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_code_1734_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2082_ = v_code_1734_;
v_isShared_2083_ = v_isSharedCheck_2101_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_k_2080_);
lean_inc(v_n_2077_);
lean_inc(v_fvarId_2076_);
lean_dec(v_code_1734_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2101_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
uint8_t v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2084_ = 1;
v___x_2085_ = lean_st_ref_get(v_a_1736_);
v___x_2086_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2085_, v_fvarId_2076_, v___x_2084_);
lean_dec(v___x_2085_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_fvarId_2087_; lean_object* v___x_2088_; 
v_fvarId_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_fvarId_2087_);
lean_dec_ref_known(v___x_2086_, 1);
v___x_2088_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1733_, v_k_2080_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2099_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2099_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2099_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 2, v_a_2089_);
lean_ctor_set(v___x_2082_, 0, v_fvarId_2087_);
v___x_2094_ = v___x_2082_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_fvarId_2087_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_n_2077_);
lean_ctor_set(v_reuseFailAlloc_2098_, 2, v_a_2089_);
lean_ctor_set_uint8(v_reuseFailAlloc_2098_, sizeof(void*)*3, v_check_2078_);
lean_ctor_set_uint8(v_reuseFailAlloc_2098_, sizeof(void*)*3 + 1, v_persistent_2079_);
v___x_2094_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
lean_object* v___x_2096_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2094_);
v___x_2096_ = v___x_2091_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
else
{
lean_dec(v_fvarId_2087_);
lean_del_object(v___x_2082_);
lean_dec(v_n_2077_);
return v___x_2088_;
}
}
else
{
lean_object* v___x_2100_; 
lean_del_object(v___x_2082_);
lean_dec_ref(v_k_2080_);
lean_dec(v_n_2077_);
v___x_2100_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1733_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_2100_;
}
}
}
case 12:
{
lean_object* v_fvarId_2102_; lean_object* v_n_2103_; uint8_t v_check_2104_; uint8_t v_persistent_2105_; lean_object* v_objs_x3f_2106_; lean_object* v_k_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2128_; 
v_fvarId_2102_ = lean_ctor_get(v_code_1734_, 0);
v_n_2103_ = lean_ctor_get(v_code_1734_, 1);
v_check_2104_ = lean_ctor_get_uint8(v_code_1734_, sizeof(void*)*4);
v_persistent_2105_ = lean_ctor_get_uint8(v_code_1734_, sizeof(void*)*4 + 1);
v_objs_x3f_2106_ = lean_ctor_get(v_code_1734_, 2);
v_k_2107_ = lean_ctor_get(v_code_1734_, 3);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_code_1734_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2109_ = v_code_1734_;
v_isShared_2110_ = v_isSharedCheck_2128_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_k_2107_);
lean_inc(v_objs_x3f_2106_);
lean_inc(v_n_2103_);
lean_inc(v_fvarId_2102_);
lean_dec(v_code_1734_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2128_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
uint8_t v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = 1;
v___x_2112_ = lean_st_ref_get(v_a_1736_);
v___x_2113_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2112_, v_fvarId_2102_, v___x_2111_);
lean_dec(v___x_2112_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_fvarId_2114_; lean_object* v___x_2115_; 
v_fvarId_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_fvarId_2114_);
lean_dec_ref_known(v___x_2113_, 1);
v___x_2115_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1733_, v_k_2107_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2126_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2118_ = v___x_2115_;
v_isShared_2119_ = v_isSharedCheck_2126_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2126_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 3, v_a_2116_);
lean_ctor_set(v___x_2109_, 0, v_fvarId_2114_);
v___x_2121_ = v___x_2109_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_fvarId_2114_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_n_2103_);
lean_ctor_set(v_reuseFailAlloc_2125_, 2, v_objs_x3f_2106_);
lean_ctor_set(v_reuseFailAlloc_2125_, 3, v_a_2116_);
lean_ctor_set_uint8(v_reuseFailAlloc_2125_, sizeof(void*)*4, v_check_2104_);
lean_ctor_set_uint8(v_reuseFailAlloc_2125_, sizeof(void*)*4 + 1, v_persistent_2105_);
v___x_2121_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2123_; 
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2121_);
v___x_2123_ = v___x_2118_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2121_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
else
{
lean_dec(v_fvarId_2114_);
lean_del_object(v___x_2109_);
lean_dec(v_objs_x3f_2106_);
lean_dec(v_n_2103_);
return v___x_2115_;
}
}
else
{
lean_object* v___x_2127_; 
lean_del_object(v___x_2109_);
lean_dec_ref(v_k_2107_);
lean_dec(v_objs_x3f_2106_);
lean_dec(v_n_2103_);
v___x_2127_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1733_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_2127_;
}
}
}
default: 
{
lean_object* v_fvarId_2129_; lean_object* v_k_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2151_; 
v_fvarId_2129_ = lean_ctor_get(v_code_1734_, 0);
v_k_2130_ = lean_ctor_get(v_code_1734_, 1);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_code_1734_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2132_ = v_code_1734_;
v_isShared_2133_ = v_isSharedCheck_2151_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_k_2130_);
lean_inc(v_fvarId_2129_);
lean_dec(v_code_1734_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2151_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
uint8_t v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2134_ = 1;
v___x_2135_ = lean_st_ref_get(v_a_1736_);
v___x_2136_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2135_, v_fvarId_2129_, v___x_2134_);
lean_dec(v___x_2135_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_fvarId_2137_; lean_object* v___x_2138_; 
v_fvarId_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_fvarId_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v___x_2138_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1733_, v_k_2130_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2149_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2141_ = v___x_2138_;
v_isShared_2142_ = v_isSharedCheck_2149_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2138_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2149_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 1, v_a_2139_);
lean_ctor_set(v___x_2132_, 0, v_fvarId_2137_);
v___x_2144_ = v___x_2132_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_fvarId_2137_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v___x_2146_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 0, v___x_2144_);
v___x_2146_ = v___x_2141_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
else
{
lean_dec(v_fvarId_2137_);
lean_del_object(v___x_2132_);
return v___x_2138_;
}
}
else
{
lean_object* v___x_2150_; 
lean_del_object(v___x_2132_);
lean_dec_ref(v_k_2130_);
v___x_2150_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1733_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_2150_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Internalize_internalizeCode_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1733_ = stack[0].m_num;
lean_object* v_code_1734_ = stack[1].m_obj;
uint8_t v_a_1735_ = stack[2].m_num;
lean_object* v_a_1736_ = stack[3].m_obj;
lean_object* v_a_1737_ = stack[4].m_obj;
lean_object* v_a_1738_ = stack[5].m_obj;
lean_object* v_a_1739_ = stack[6].m_obj;
lean_object* v_a_1740_ = stack[7].m_obj;
lean_object* v_res_2152_;
v_res_2152_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1733_, v_code_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
stack->m_obj
 = v_res_2152_;
}
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(uint8_t v_pu_2153_, lean_object* v_decl_2154_, uint8_t v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v_fvarId_2162_; lean_object* v_binderName_2163_; lean_object* v_params_2164_; lean_object* v_type_2165_; lean_object* v_value_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2244_; 
v_fvarId_2162_ = lean_ctor_get(v_decl_2154_, 0);
v_binderName_2163_ = lean_ctor_get(v_decl_2154_, 1);
v_params_2164_ = lean_ctor_get(v_decl_2154_, 2);
v_type_2165_ = lean_ctor_get(v_decl_2154_, 3);
v_value_2166_ = lean_ctor_get(v_decl_2154_, 4);
v_isSharedCheck_2244_ = !lean_is_exclusive(v_decl_2154_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2168_ = v_decl_2154_;
v_isShared_2169_ = v_isSharedCheck_2244_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_value_2166_);
lean_inc(v_type_2165_);
lean_inc(v_params_2164_);
lean_inc(v_binderName_2163_);
lean_inc(v_fvarId_2162_);
lean_dec(v_decl_2154_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2244_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; 
v___x_2170_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2153_, v_type_2165_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2172_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2170_, 1);
v___x_2172_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_2163_, v_a_2155_, v_a_2158_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; size_t v_sz_2174_; size_t v___x_2175_; lean_object* v___x_2176_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2172_, 1);
v_sz_2174_ = lean_array_size(v_params_2164_);
v___x_2175_ = ((size_t)0ULL);
v___x_2176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2153_, v_sz_2174_, v___x_2175_, v_params_2164_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2178_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2176_, 1);
v___x_2178_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2153_, v_value_2166_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2180_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___x_2178_, 1);
v___x_2180_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_2162_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2203_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2183_ = v___x_2180_;
v_isShared_2184_ = v_isSharedCheck_2203_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2203_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 4, v_a_2179_);
lean_ctor_set(v___x_2168_, 3, v_a_2171_);
lean_ctor_set(v___x_2168_, 2, v_a_2177_);
lean_ctor_set(v___x_2168_, 1, v_a_2173_);
lean_ctor_set(v___x_2168_, 0, v_a_2181_);
v___x_2186_ = v___x_2168_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2181_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_a_2173_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v_a_2177_);
lean_ctor_set(v_reuseFailAlloc_2202_, 3, v_a_2171_);
lean_ctor_set(v_reuseFailAlloc_2202_, 4, v_a_2179_);
v___x_2186_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
lean_object* v___x_2187_; lean_object* v_lctx_2188_; lean_object* v_nextIdx_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2201_; 
v___x_2187_ = lean_st_ref_take(v_a_2158_);
v_lctx_2188_ = lean_ctor_get(v___x_2187_, 0);
v_nextIdx_2189_ = lean_ctor_get(v___x_2187_, 1);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2191_ = v___x_2187_;
v_isShared_2192_ = v_isSharedCheck_2201_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_nextIdx_2189_);
lean_inc(v_lctx_2188_);
lean_dec(v___x_2187_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2201_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v___x_2195_; 
lean_inc_ref(v___x_2186_);
v___x_2193_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2153_, v_lctx_2188_, v___x_2186_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 0, v___x_2193_);
v___x_2195_ = v___x_2191_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2193_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_nextIdx_2189_);
v___x_2195_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2196_ = lean_st_ref_put(v_a_2158_, v___x_2195_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2186_);
v___x_2198_ = v___x_2183_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2186_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec(v_a_2179_);
lean_dec(v_a_2177_);
lean_dec(v_a_2173_);
lean_dec(v_a_2171_);
lean_del_object(v___x_2168_);
v_a_2204_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2180_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2180_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec(v_a_2177_);
lean_dec(v_a_2173_);
lean_dec(v_a_2171_);
lean_del_object(v___x_2168_);
lean_dec(v_fvarId_2162_);
v_a_2212_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2178_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2178_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec(v_a_2173_);
lean_dec(v_a_2171_);
lean_del_object(v___x_2168_);
lean_dec_ref(v_value_2166_);
lean_dec(v_fvarId_2162_);
v_a_2220_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2176_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2176_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec(v_a_2171_);
lean_del_object(v___x_2168_);
lean_dec_ref(v_value_2166_);
lean_dec_ref(v_params_2164_);
lean_dec(v_fvarId_2162_);
v_a_2228_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2172_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2172_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_del_object(v___x_2168_);
lean_dec_ref(v_value_2166_);
lean_dec_ref(v_params_2164_);
lean_dec(v_binderName_2163_);
lean_dec(v_fvarId_2162_);
v_a_2236_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2170_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2170_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2153_ = stack[0].m_num;
lean_object* v_decl_2154_ = stack[1].m_obj;
uint8_t v_a_2155_ = stack[2].m_num;
lean_object* v_a_2156_ = stack[3].m_obj;
lean_object* v_a_2157_ = stack[4].m_obj;
lean_object* v_a_2158_ = stack[5].m_obj;
lean_object* v_a_2159_ = stack[6].m_obj;
lean_object* v_a_2160_ = stack[7].m_obj;
lean_object* v_res_2245_;
v_res_2245_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2153_, v_decl_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
stack->m_obj
 = v_res_2245_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(lean_object* v_pu_2246_, lean_object* v_decl_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
uint8_t v_pu_boxed_2255_; uint8_t v_a_boxed_2256_; lean_object* v_res_2257_; 
v_pu_boxed_2255_ = lean_unbox(v_pu_2246_);
v_a_boxed_2256_ = lean_unbox(v_a_2248_);
v_res_2257_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_boxed_2255_, v_decl_2247_, v_a_boxed_2256_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_);
lean_dec(v_a_2253_);
lean_dec_ref(v_a_2252_);
lean_dec(v_a_2251_);
lean_dec_ref(v_a_2250_);
lean_dec(v_a_2249_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2___boxed(lean_object* v_pu_2258_, lean_object* v_sz_2259_, lean_object* v_i_2260_, lean_object* v_bs_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
uint8_t v_pu_boxed_2269_; size_t v_sz_boxed_2270_; size_t v_i_boxed_2271_; uint8_t v___y_26480__boxed_2272_; lean_object* v_res_2273_; 
v_pu_boxed_2269_ = lean_unbox(v_pu_2258_);
v_sz_boxed_2270_ = lean_unbox_usize(v_sz_2259_);
lean_dec(v_sz_2259_);
v_i_boxed_2271_ = lean_unbox_usize(v_i_2260_);
lean_dec(v_i_2260_);
v___y_26480__boxed_2272_ = lean_unbox(v___y_2262_);
v_res_2273_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_boxed_2269_, v_sz_boxed_2270_, v_i_boxed_2271_, v_bs_2261_, v___y_26480__boxed_2272_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(lean_object* v_pu_2274_, lean_object* v_code_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
uint8_t v_pu_boxed_2283_; uint8_t v_a_boxed_2284_; lean_object* v_res_2285_; 
v_pu_boxed_2283_ = lean_unbox(v_pu_2274_);
v_a_boxed_2284_ = lean_unbox(v_a_2276_);
v_res_2285_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_boxed_2283_, v_code_2275_, v_a_boxed_2284_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_);
lean_dec(v_a_2281_);
lean_dec_ref(v_a_2280_);
lean_dec(v_a_2279_);
lean_dec_ref(v_a_2278_);
lean_dec(v_a_2277_);
return v_res_2285_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
return v___x_2286_;
}
}
lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(lean_object* v_msg_2287_, uint8_t v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v_toApplicative_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2361_; 
v___x_2295_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
v___x_2296_ = l_StateRefT_x27_instMonad___redArg(v___x_2295_);
v_toApplicative_2297_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2361_ == 0)
{
lean_object* v_unused_2362_; 
v_unused_2362_ = lean_ctor_get(v___x_2296_, 1);
lean_dec(v_unused_2362_);
v___x_2299_ = v___x_2296_;
v_isShared_2300_ = v_isSharedCheck_2361_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_toApplicative_2297_);
lean_dec(v___x_2296_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2361_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v_toFunctor_2301_; lean_object* v_toSeq_2302_; lean_object* v_toSeqLeft_2303_; lean_object* v_toSeqRight_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2359_; 
v_toFunctor_2301_ = lean_ctor_get(v_toApplicative_2297_, 0);
v_toSeq_2302_ = lean_ctor_get(v_toApplicative_2297_, 2);
v_toSeqLeft_2303_ = lean_ctor_get(v_toApplicative_2297_, 3);
v_toSeqRight_2304_ = lean_ctor_get(v_toApplicative_2297_, 4);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_toApplicative_2297_);
if (v_isSharedCheck_2359_ == 0)
{
lean_object* v_unused_2360_; 
v_unused_2360_ = lean_ctor_get(v_toApplicative_2297_, 1);
lean_dec(v_unused_2360_);
v___x_2306_ = v_toApplicative_2297_;
v_isShared_2307_ = v_isSharedCheck_2359_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_toSeqRight_2304_);
lean_inc(v_toSeqLeft_2303_);
lean_inc(v_toSeq_2302_);
lean_inc(v_toFunctor_2301_);
lean_dec(v_toApplicative_2297_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2359_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___f_2308_; lean_object* v___f_2309_; lean_object* v___f_2310_; lean_object* v___f_2311_; lean_object* v___x_2312_; lean_object* v___f_2313_; lean_object* v___f_2314_; lean_object* v___f_2315_; lean_object* v___x_2317_; 
v___f_2308_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
v___f_2309_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_2301_);
v___f_2310_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2310_, 0, v_toFunctor_2301_);
v___f_2311_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2311_, 0, v_toFunctor_2301_);
v___x_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___f_2310_);
lean_ctor_set(v___x_2312_, 1, v___f_2311_);
v___f_2313_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2313_, 0, v_toSeqRight_2304_);
v___f_2314_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2314_, 0, v_toSeqLeft_2303_);
v___f_2315_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2315_, 0, v_toSeq_2302_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 4, v___f_2313_);
lean_ctor_set(v___x_2306_, 3, v___f_2314_);
lean_ctor_set(v___x_2306_, 2, v___f_2315_);
lean_ctor_set(v___x_2306_, 1, v___f_2308_);
lean_ctor_set(v___x_2306_, 0, v___x_2312_);
v___x_2317_ = v___x_2306_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2312_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v___f_2308_);
lean_ctor_set(v_reuseFailAlloc_2358_, 2, v___f_2315_);
lean_ctor_set(v_reuseFailAlloc_2358_, 3, v___f_2314_);
lean_ctor_set(v_reuseFailAlloc_2358_, 4, v___f_2313_);
v___x_2317_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
lean_object* v___x_2319_; 
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 1, v___f_2309_);
lean_ctor_set(v___x_2299_, 0, v___x_2317_);
v___x_2319_ = v___x_2299_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v___f_2309_);
v___x_2319_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
lean_object* v___x_2320_; lean_object* v_toApplicative_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2355_; 
v___x_2320_ = l_StateRefT_x27_instMonad___redArg(v___x_2319_);
v_toApplicative_2321_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2355_ == 0)
{
lean_object* v_unused_2356_; 
v_unused_2356_ = lean_ctor_get(v___x_2320_, 1);
lean_dec(v_unused_2356_);
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2355_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_toApplicative_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2355_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v_toFunctor_2325_; lean_object* v_toSeq_2326_; lean_object* v_toSeqLeft_2327_; lean_object* v_toSeqRight_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2353_; 
v_toFunctor_2325_ = lean_ctor_get(v_toApplicative_2321_, 0);
v_toSeq_2326_ = lean_ctor_get(v_toApplicative_2321_, 2);
v_toSeqLeft_2327_ = lean_ctor_get(v_toApplicative_2321_, 3);
v_toSeqRight_2328_ = lean_ctor_get(v_toApplicative_2321_, 4);
v_isSharedCheck_2353_ = !lean_is_exclusive(v_toApplicative_2321_);
if (v_isSharedCheck_2353_ == 0)
{
lean_object* v_unused_2354_; 
v_unused_2354_ = lean_ctor_get(v_toApplicative_2321_, 1);
lean_dec(v_unused_2354_);
v___x_2330_ = v_toApplicative_2321_;
v_isShared_2331_ = v_isSharedCheck_2353_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_toSeqRight_2328_);
lean_inc(v_toSeqLeft_2327_);
lean_inc(v_toSeq_2326_);
lean_inc(v_toFunctor_2325_);
lean_dec(v_toApplicative_2321_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2353_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___f_2332_; lean_object* v___f_2333_; lean_object* v___f_2334_; lean_object* v___f_2335_; lean_object* v___x_2336_; lean_object* v___f_2337_; lean_object* v___f_2338_; lean_object* v___f_2339_; lean_object* v___x_2341_; 
v___f_2332_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
v___f_2333_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(v_toFunctor_2325_);
v___f_2334_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2334_, 0, v_toFunctor_2325_);
v___f_2335_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2335_, 0, v_toFunctor_2325_);
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___f_2334_);
lean_ctor_set(v___x_2336_, 1, v___f_2335_);
v___f_2337_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2337_, 0, v_toSeqRight_2328_);
v___f_2338_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2338_, 0, v_toSeqLeft_2327_);
v___f_2339_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2339_, 0, v_toSeq_2326_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 4, v___f_2337_);
lean_ctor_set(v___x_2330_, 3, v___f_2338_);
lean_ctor_set(v___x_2330_, 2, v___f_2339_);
lean_ctor_set(v___x_2330_, 1, v___f_2332_);
lean_ctor_set(v___x_2330_, 0, v___x_2336_);
v___x_2341_ = v___x_2330_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2336_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v___f_2332_);
lean_ctor_set(v_reuseFailAlloc_2352_, 2, v___f_2339_);
lean_ctor_set(v_reuseFailAlloc_2352_, 3, v___f_2338_);
lean_ctor_set(v_reuseFailAlloc_2352_, 4, v___f_2337_);
v___x_2341_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2343_; 
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 1, v___f_2333_);
lean_ctor_set(v___x_2323_, 0, v___x_2341_);
v___x_2343_ = v___x_2323_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2341_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v___f_2333_);
v___x_2343_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___f_2347_; lean_object* v___x_10574__overap_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2344_ = l_StateRefT_x27_instMonad___redArg(v___x_2343_);
v___x_2345_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___closed__0);
v___x_2346_ = l_instInhabitedOfMonad___redArg(v___x_2344_, v___x_2345_);
v___f_2347_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2347_, 0, v___x_2346_);
v___x_10574__overap_2348_ = lean_panic_fn_borrowed(v___f_2347_, v_msg_2287_);
lean_dec_ref(v___f_2347_);
v___x_2349_ = lean_box(v___y_2288_);
lean_inc(v___y_2293_);
lean_inc_ref(v___y_2292_);
lean_inc(v___y_2291_);
lean_inc_ref(v___y_2290_);
lean_inc(v___y_2289_);
v___x_2350_ = lean_apply_7(v___x_10574__overap_2348_, v___x_2349_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, lean_box(0));
return v___x_2350_;
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
LEAN_EXPORT void l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2287_ = stack[0].m_obj;
uint8_t v___y_2288_ = stack[1].m_num;
lean_object* v___y_2289_ = stack[2].m_obj;
lean_object* v___y_2290_ = stack[3].m_obj;
lean_object* v___y_2291_ = stack[4].m_obj;
lean_object* v___y_2292_ = stack[5].m_obj;
lean_object* v___y_2293_ = stack[6].m_obj;
lean_object* v_res_2363_;
v_res_2363_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v_msg_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
stack->m_obj
 = v_res_2363_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___boxed(lean_object* v_msg_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
uint8_t v___y_10635__boxed_2372_; lean_object* v_res_2373_; 
v___y_10635__boxed_2372_ = lean_unbox(v___y_2365_);
v_res_2373_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v_msg_2364_, v___y_10635__boxed_2372_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
return v_res_2373_;
}
}
lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(uint8_t v_pu_2374_, lean_object* v_msg_2375_, uint8_t v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v_msg_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
return v___x_2383_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2374_ = stack[0].m_num;
lean_object* v_msg_2375_ = stack[1].m_obj;
uint8_t v___y_2376_ = stack[2].m_num;
lean_object* v___y_2377_ = stack[3].m_obj;
lean_object* v___y_2378_ = stack[4].m_obj;
lean_object* v___y_2379_ = stack[5].m_obj;
lean_object* v___y_2380_ = stack[6].m_obj;
lean_object* v___y_2381_ = stack[7].m_obj;
lean_object* v_res_2384_;
v_res_2384_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2374_, v_msg_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
stack->m_obj
 = v_res_2384_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___boxed(lean_object* v_pu_2385_, lean_object* v_msg_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
uint8_t v_pu_boxed_2394_; uint8_t v___y_10843__boxed_2395_; lean_object* v_res_2396_; 
v_pu_boxed_2394_ = lean_unbox(v_pu_2385_);
v___y_10843__boxed_2395_ = lean_unbox(v___y_2387_);
v_res_2396_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_boxed_2394_, v_msg_2386_, v___y_10843__boxed_2395_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
return v_res_2396_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1(void){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2398_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2399_ = lean_unsigned_to_nat(41u);
v___x_2400_ = lean_unsigned_to_nat(217u);
v___x_2401_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2402_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2403_ = l_mkPanicMessageWithDecl(v___x_2402_, v___x_2401_, v___x_2400_, v___x_2399_, v___x_2398_);
return v___x_2403_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2(void){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2404_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2405_ = lean_unsigned_to_nat(31u);
v___x_2406_ = lean_unsigned_to_nat(222u);
v___x_2407_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2408_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2409_ = l_mkPanicMessageWithDecl(v___x_2408_, v___x_2407_, v___x_2406_, v___x_2405_, v___x_2404_);
return v___x_2409_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2410_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2411_ = lean_unsigned_to_nat(41u);
v___x_2412_ = lean_unsigned_to_nat(221u);
v___x_2413_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2414_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2415_ = l_mkPanicMessageWithDecl(v___x_2414_, v___x_2413_, v___x_2412_, v___x_2411_, v___x_2410_);
return v___x_2415_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4(void){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2416_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2417_ = lean_unsigned_to_nat(31u);
v___x_2418_ = lean_unsigned_to_nat(226u);
v___x_2419_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2420_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2421_ = l_mkPanicMessageWithDecl(v___x_2420_, v___x_2419_, v___x_2418_, v___x_2417_, v___x_2416_);
return v___x_2421_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5(void){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2422_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2423_ = lean_unsigned_to_nat(41u);
v___x_2424_ = lean_unsigned_to_nat(225u);
v___x_2425_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2426_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2427_ = l_mkPanicMessageWithDecl(v___x_2426_, v___x_2425_, v___x_2424_, v___x_2423_, v___x_2422_);
return v___x_2427_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6(void){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2428_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2429_ = lean_unsigned_to_nat(41u);
v___x_2430_ = lean_unsigned_to_nat(230u);
v___x_2431_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2432_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2433_ = l_mkPanicMessageWithDecl(v___x_2432_, v___x_2431_, v___x_2430_, v___x_2429_, v___x_2428_);
return v___x_2433_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2434_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2435_ = lean_unsigned_to_nat(41u);
v___x_2436_ = lean_unsigned_to_nat(233u);
v___x_2437_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2438_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2439_ = l_mkPanicMessageWithDecl(v___x_2438_, v___x_2437_, v___x_2436_, v___x_2435_, v___x_2434_);
return v___x_2439_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8(void){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2440_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2441_ = lean_unsigned_to_nat(41u);
v___x_2442_ = lean_unsigned_to_nat(236u);
v___x_2443_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2444_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2445_ = l_mkPanicMessageWithDecl(v___x_2444_, v___x_2443_, v___x_2442_, v___x_2441_, v___x_2440_);
return v___x_2445_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2446_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2447_ = lean_unsigned_to_nat(41u);
v___x_2448_ = lean_unsigned_to_nat(239u);
v___x_2449_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2450_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2451_ = l_mkPanicMessageWithDecl(v___x_2450_, v___x_2449_, v___x_2448_, v___x_2447_, v___x_2446_);
return v___x_2451_;
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t v_pu_2452_, lean_object* v_decl_2453_, uint8_t v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_){
_start:
{
switch(lean_obj_tag(v_decl_2453_))
{
case 0:
{
lean_object* v_decl_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2485_; 
v_decl_2461_ = lean_ctor_get(v_decl_2453_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v_decl_2453_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2463_ = v_decl_2453_;
v_isShared_2464_ = v_isSharedCheck_2485_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_decl_2461_);
lean_dec(v_decl_2453_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2485_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_2452_, v_decl_2461_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2476_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2468_ = v___x_2465_;
v_isShared_2469_ = v_isSharedCheck_2476_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2465_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2476_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 0, v_a_2466_);
v___x_2471_ = v___x_2463_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2473_; 
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 0, v___x_2471_);
v___x_2473_ = v___x_2468_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2471_);
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
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_del_object(v___x_2463_);
v_a_2477_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2465_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2465_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2510_; 
v_decl_2486_ = lean_ctor_get(v_decl_2453_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_decl_2453_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2488_ = v_decl_2453_;
v_isShared_2489_ = v_isSharedCheck_2510_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_decl_2486_);
lean_dec(v_decl_2453_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2510_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2452_, v_decl_2486_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2501_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2493_ = v___x_2490_;
v_isShared_2494_ = v_isSharedCheck_2501_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2490_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2501_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 0, v_a_2491_);
v___x_2496_ = v___x_2488_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2498_; 
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v___x_2496_);
v___x_2498_ = v___x_2493_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2496_);
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
else
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
lean_del_object(v___x_2488_);
v_a_2502_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v___x_2490_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2490_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
}
}
case 2:
{
lean_object* v_decl_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2535_; 
v_decl_2511_ = lean_ctor_get(v_decl_2453_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v_decl_2453_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2513_ = v_decl_2453_;
v_isShared_2514_ = v_isSharedCheck_2535_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_decl_2511_);
lean_dec(v_decl_2453_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2535_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2452_, v_decl_2511_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2526_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2526_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2526_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 0, v_a_2516_);
v___x_2521_ = v___x_2513_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2523_; 
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2521_);
v___x_2523_ = v___x_2518_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_del_object(v___x_2513_);
v_a_2527_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2515_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2515_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_2536_; lean_object* v_i_2537_; lean_object* v_y_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2560_; 
v_fvarId_2536_ = lean_ctor_get(v_decl_2453_, 0);
v_i_2537_ = lean_ctor_get(v_decl_2453_, 1);
v_y_2538_ = lean_ctor_get(v_decl_2453_, 2);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_decl_2453_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2540_ = v_decl_2453_;
v_isShared_2541_ = v_isSharedCheck_2560_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_y_2538_);
lean_inc(v_i_2537_);
lean_inc(v_fvarId_2536_);
lean_dec(v_decl_2453_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2560_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
uint8_t v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = 1;
v___x_2543_ = lean_st_ref_get(v_a_2455_);
v___x_2544_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2543_, v_fvarId_2536_, v___x_2542_);
lean_dec(v___x_2543_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_fvarId_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2557_; 
v_fvarId_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2557_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_fvarId_2545_);
lean_dec(v___x_2544_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2557_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2552_; 
v___x_2549_ = lean_st_ref_get(v_a_2455_);
v___x_2550_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2452_, v___x_2549_, v_y_2538_, v___x_2542_);
lean_dec(v___x_2549_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 2, v___x_2550_);
lean_ctor_set(v___x_2540_, 0, v_fvarId_2545_);
v___x_2552_ = v___x_2540_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_fvarId_2545_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v_i_2537_);
lean_ctor_set(v_reuseFailAlloc_2556_, 2, v___x_2550_);
v___x_2552_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
lean_object* v___x_2554_; 
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v___x_2552_);
v___x_2554_ = v___x_2547_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2552_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
else
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
lean_dec(v___x_2544_);
lean_del_object(v___x_2540_);
lean_dec(v_y_2538_);
lean_dec(v_i_2537_);
v___x_2558_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1);
v___x_2559_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2558_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
return v___x_2559_;
}
}
}
case 4:
{
lean_object* v_fvarId_2561_; lean_object* v_i_2562_; lean_object* v_y_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2588_; 
v_fvarId_2561_ = lean_ctor_get(v_decl_2453_, 0);
v_i_2562_ = lean_ctor_get(v_decl_2453_, 1);
v_y_2563_ = lean_ctor_get(v_decl_2453_, 2);
v_isSharedCheck_2588_ = !lean_is_exclusive(v_decl_2453_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2565_ = v_decl_2453_;
v_isShared_2566_ = v_isSharedCheck_2588_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_y_2563_);
lean_inc(v_i_2562_);
lean_inc(v_fvarId_2561_);
lean_dec(v_decl_2453_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2588_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
uint8_t v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2567_ = 1;
v___x_2568_ = lean_st_ref_get(v_a_2455_);
v___x_2569_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2568_, v_fvarId_2561_, v___x_2567_);
lean_dec(v___x_2568_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_fvarId_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v_fvarId_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_fvarId_2570_);
lean_dec_ref_known(v___x_2569_, 1);
v___x_2571_ = lean_st_ref_get(v_a_2455_);
v___x_2572_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2571_, v_y_2563_, v___x_2567_);
lean_dec(v___x_2571_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_fvarId_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2583_; 
v_fvarId_2573_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2575_ = v___x_2572_;
v_isShared_2576_ = v_isSharedCheck_2583_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_fvarId_2573_);
lean_dec(v___x_2572_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2583_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 2, v_fvarId_2573_);
lean_ctor_set(v___x_2565_, 0, v_fvarId_2570_);
v___x_2578_ = v___x_2565_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_fvarId_2570_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_i_2562_);
lean_ctor_set(v_reuseFailAlloc_2582_, 2, v_fvarId_2573_);
v___x_2578_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2580_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2578_);
v___x_2580_ = v___x_2575_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
lean_dec(v___x_2572_);
lean_dec(v_fvarId_2570_);
lean_del_object(v___x_2565_);
lean_dec(v_i_2562_);
v___x_2584_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2);
v___x_2585_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2584_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
return v___x_2585_;
}
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
lean_dec(v___x_2569_);
lean_del_object(v___x_2565_);
lean_dec(v_y_2563_);
lean_dec(v_i_2562_);
v___x_2586_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3);
v___x_2587_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2586_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
return v___x_2587_;
}
}
}
case 5:
{
lean_object* v_fvarId_2589_; lean_object* v_i_2590_; lean_object* v_offset_2591_; lean_object* v_y_2592_; lean_object* v_ty_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2620_; 
v_fvarId_2589_ = lean_ctor_get(v_decl_2453_, 0);
v_i_2590_ = lean_ctor_get(v_decl_2453_, 1);
v_offset_2591_ = lean_ctor_get(v_decl_2453_, 2);
v_y_2592_ = lean_ctor_get(v_decl_2453_, 3);
v_ty_2593_ = lean_ctor_get(v_decl_2453_, 4);
v_isSharedCheck_2620_ = !lean_is_exclusive(v_decl_2453_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2595_ = v_decl_2453_;
v_isShared_2596_ = v_isSharedCheck_2620_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_ty_2593_);
lean_inc(v_y_2592_);
lean_inc(v_offset_2591_);
lean_inc(v_i_2590_);
lean_inc(v_fvarId_2589_);
lean_dec(v_decl_2453_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2620_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
uint8_t v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2597_ = 1;
v___x_2598_ = lean_st_ref_get(v_a_2455_);
v___x_2599_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2598_, v_fvarId_2589_, v___x_2597_);
lean_dec(v___x_2598_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_fvarId_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v_fvarId_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_fvarId_2600_);
lean_dec_ref_known(v___x_2599_, 1);
v___x_2601_ = lean_st_ref_get(v_a_2455_);
v___x_2602_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2601_, v_y_2592_, v___x_2597_);
lean_dec(v___x_2601_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_fvarId_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2615_; 
v_fvarId_2603_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2605_ = v___x_2602_;
v_isShared_2606_ = v_isSharedCheck_2615_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_fvarId_2603_);
lean_dec(v___x_2602_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2615_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2610_; 
v___x_2607_ = lean_st_ref_get(v_a_2455_);
v___x_2608_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2452_, v___x_2607_, v___x_2597_, v_ty_2593_);
lean_dec(v___x_2607_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 4, v___x_2608_);
lean_ctor_set(v___x_2595_, 3, v_fvarId_2603_);
lean_ctor_set(v___x_2595_, 0, v_fvarId_2600_);
v___x_2610_ = v___x_2595_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_fvarId_2600_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v_i_2590_);
lean_ctor_set(v_reuseFailAlloc_2614_, 2, v_offset_2591_);
lean_ctor_set(v_reuseFailAlloc_2614_, 3, v_fvarId_2603_);
lean_ctor_set(v_reuseFailAlloc_2614_, 4, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2612_; 
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v___x_2610_);
v___x_2612_ = v___x_2605_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2610_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
else
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
lean_dec(v___x_2602_);
lean_dec(v_fvarId_2600_);
lean_del_object(v___x_2595_);
lean_dec_ref(v_ty_2593_);
lean_dec(v_offset_2591_);
lean_dec(v_i_2590_);
v___x_2616_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4);
v___x_2617_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2616_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
return v___x_2617_;
}
}
else
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
lean_dec(v___x_2599_);
lean_del_object(v___x_2595_);
lean_dec_ref(v_ty_2593_);
lean_dec(v_y_2592_);
lean_dec(v_offset_2591_);
lean_dec(v_i_2590_);
v___x_2618_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5);
v___x_2619_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2618_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
return v___x_2619_;
}
}
}
case 6:
{
lean_object* v_fvarId_2621_; lean_object* v_cidx_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2642_; 
v_fvarId_2621_ = lean_ctor_get(v_decl_2453_, 0);
v_cidx_2622_ = lean_ctor_get(v_decl_2453_, 1);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_decl_2453_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2624_ = v_decl_2453_;
v_isShared_2625_ = v_isSharedCheck_2642_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_cidx_2622_);
lean_inc(v_fvarId_2621_);
lean_dec(v_decl_2453_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2642_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
uint8_t v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2626_ = 1;
v___x_2627_ = lean_st_ref_get(v_a_2455_);
v___x_2628_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2627_, v_fvarId_2621_, v___x_2626_);
lean_dec(v___x_2627_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_fvarId_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2639_; 
v_fvarId_2629_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2631_ = v___x_2628_;
v_isShared_2632_ = v_isSharedCheck_2639_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_fvarId_2629_);
lean_dec(v___x_2628_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2639_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v_fvarId_2629_);
v___x_2634_ = v___x_2624_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_fvarId_2629_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v_cidx_2622_);
v___x_2634_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_object* v___x_2636_; 
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v___x_2634_);
v___x_2636_ = v___x_2631_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
else
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
lean_dec(v___x_2628_);
lean_del_object(v___x_2624_);
lean_dec(v_cidx_2622_);
v___x_2640_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6);
v___x_2641_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2640_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
return v___x_2641_;
}
}
}
case 7:
{
lean_object* v_fvarId_2643_; lean_object* v_n_2644_; uint8_t v_check_2645_; uint8_t v_persistent_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2666_; 
v_fvarId_2643_ = lean_ctor_get(v_decl_2453_, 0);
v_n_2644_ = lean_ctor_get(v_decl_2453_, 1);
v_check_2645_ = lean_ctor_get_uint8(v_decl_2453_, sizeof(void*)*2);
v_persistent_2646_ = lean_ctor_get_uint8(v_decl_2453_, sizeof(void*)*2 + 1);
v_isSharedCheck_2666_ = !lean_is_exclusive(v_decl_2453_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2648_ = v_decl_2453_;
v_isShared_2649_ = v_isSharedCheck_2666_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_n_2644_);
lean_inc(v_fvarId_2643_);
lean_dec(v_decl_2453_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2666_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
uint8_t v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2650_ = 1;
v___x_2651_ = lean_st_ref_get(v_a_2455_);
v___x_2652_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2651_, v_fvarId_2643_, v___x_2650_);
lean_dec(v___x_2651_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_fvarId_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2663_; 
v_fvarId_2653_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2655_ = v___x_2652_;
v_isShared_2656_ = v_isSharedCheck_2663_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_fvarId_2653_);
lean_dec(v___x_2652_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2663_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v_fvarId_2653_);
v___x_2658_ = v___x_2648_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_fvarId_2653_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v_n_2644_);
lean_ctor_set_uint8(v_reuseFailAlloc_2662_, sizeof(void*)*2, v_check_2645_);
lean_ctor_set_uint8(v_reuseFailAlloc_2662_, sizeof(void*)*2 + 1, v_persistent_2646_);
v___x_2658_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
lean_object* v___x_2660_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v___x_2658_);
v___x_2660_ = v___x_2655_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
else
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
lean_dec(v___x_2652_);
lean_del_object(v___x_2648_);
lean_dec(v_n_2644_);
v___x_2664_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7);
v___x_2665_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2664_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
return v___x_2665_;
}
}
}
case 8:
{
lean_object* v_fvarId_2667_; lean_object* v_n_2668_; uint8_t v_check_2669_; uint8_t v_persistent_2670_; lean_object* v_objs_x3f_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2691_; 
v_fvarId_2667_ = lean_ctor_get(v_decl_2453_, 0);
v_n_2668_ = lean_ctor_get(v_decl_2453_, 1);
v_check_2669_ = lean_ctor_get_uint8(v_decl_2453_, sizeof(void*)*3);
v_persistent_2670_ = lean_ctor_get_uint8(v_decl_2453_, sizeof(void*)*3 + 1);
v_objs_x3f_2671_ = lean_ctor_get(v_decl_2453_, 2);
v_isSharedCheck_2691_ = !lean_is_exclusive(v_decl_2453_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2673_ = v_decl_2453_;
v_isShared_2674_ = v_isSharedCheck_2691_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_objs_x3f_2671_);
lean_inc(v_n_2668_);
lean_inc(v_fvarId_2667_);
lean_dec(v_decl_2453_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2691_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
uint8_t v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2675_ = 1;
v___x_2676_ = lean_st_ref_get(v_a_2455_);
v___x_2677_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2676_, v_fvarId_2667_, v___x_2675_);
lean_dec(v___x_2676_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_fvarId_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2688_; 
v_fvarId_2678_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2680_ = v___x_2677_;
v_isShared_2681_ = v_isSharedCheck_2688_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_fvarId_2678_);
lean_dec(v___x_2677_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2688_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 0, v_fvarId_2678_);
v___x_2683_ = v___x_2673_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(8, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_fvarId_2678_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_n_2668_);
lean_ctor_set(v_reuseFailAlloc_2687_, 2, v_objs_x3f_2671_);
lean_ctor_set_uint8(v_reuseFailAlloc_2687_, sizeof(void*)*3, v_check_2669_);
lean_ctor_set_uint8(v_reuseFailAlloc_2687_, sizeof(void*)*3 + 1, v_persistent_2670_);
v___x_2683_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2685_; 
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v___x_2683_);
v___x_2685_ = v___x_2680_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2683_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
lean_dec(v___x_2677_);
lean_del_object(v___x_2673_);
lean_dec(v_objs_x3f_2671_);
lean_dec(v_n_2668_);
v___x_2689_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8);
v___x_2690_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2689_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
return v___x_2690_;
}
}
}
default: 
{
lean_object* v_fvarId_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2712_; 
v_fvarId_2692_ = lean_ctor_get(v_decl_2453_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_decl_2453_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2694_ = v_decl_2453_;
v_isShared_2695_ = v_isSharedCheck_2712_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_fvarId_2692_);
lean_dec(v_decl_2453_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2712_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
uint8_t v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2696_ = 1;
v___x_2697_ = lean_st_ref_get(v_a_2455_);
v___x_2698_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2697_, v_fvarId_2692_, v___x_2696_);
lean_dec(v___x_2697_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_fvarId_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2709_; 
v_fvarId_2699_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2701_ = v___x_2698_;
v_isShared_2702_ = v_isSharedCheck_2709_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_fvarId_2699_);
lean_dec(v___x_2698_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2709_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v_fvarId_2699_);
v___x_2704_ = v___x_2694_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_fvarId_2699_);
v___x_2704_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2706_; 
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 0, v___x_2704_);
v___x_2706_ = v___x_2701_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
else
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
lean_dec(v___x_2698_);
lean_del_object(v___x_2694_);
v___x_2710_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9);
v___x_2711_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2710_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
return v___x_2711_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2452_ = stack[0].m_num;
lean_object* v_decl_2453_ = stack[1].m_obj;
uint8_t v_a_2454_ = stack[2].m_num;
lean_object* v_a_2455_ = stack[3].m_obj;
lean_object* v_a_2456_ = stack[4].m_obj;
lean_object* v_a_2457_ = stack[5].m_obj;
lean_object* v_a_2458_ = stack[6].m_obj;
lean_object* v_a_2459_ = stack[7].m_obj;
lean_object* v_res_2713_;
v_res_2713_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v_pu_2452_, v_decl_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
stack->m_obj
 = v_res_2713_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(lean_object* v_pu_2714_, lean_object* v_decl_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
uint8_t v_pu_boxed_2723_; uint8_t v_a_boxed_2724_; lean_object* v_res_2725_; 
v_pu_boxed_2723_ = lean_unbox(v_pu_2714_);
v_a_boxed_2724_ = lean_unbox(v_a_2716_);
v_res_2725_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v_pu_boxed_2723_, v_decl_2715_, v_a_boxed_2724_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
return v_res_2725_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t v_pu_2726_, lean_object* v_code_2727_, lean_object* v_s_2728_, uint8_t v_uniqueIdents_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = lean_st_mk_ref(v_s_2728_);
v___x_2736_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2726_, v_code_2727_, v_uniqueIdents_2729_, v___x_2735_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2745_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2739_ = v___x_2736_;
v_isShared_2740_ = v_isSharedCheck_2745_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2736_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2745_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2741_ = lean_st_ref_get(v___x_2735_);
lean_dec(v___x_2735_);
lean_dec(v___x_2741_);
if (v_isShared_2740_ == 0)
{
v___x_2743_ = v___x_2739_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2737_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
else
{
lean_dec(v___x_2735_);
return v___x_2736_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_internalize_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2726_ = stack[0].m_num;
lean_object* v_code_2727_ = stack[1].m_obj;
lean_object* v_s_2728_ = stack[2].m_obj;
uint8_t v_uniqueIdents_2729_ = stack[3].m_num;
lean_object* v_a_2730_ = stack[4].m_obj;
lean_object* v_a_2731_ = stack[5].m_obj;
lean_object* v_a_2732_ = stack[6].m_obj;
lean_object* v_a_2733_ = stack[7].m_obj;
lean_object* v_res_2746_;
v_res_2746_ = l_Lean_Compiler_LCNF_Code_internalize(v_pu_2726_, v_code_2727_, v_s_2728_, v_uniqueIdents_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_);
stack->m_obj
 = v_res_2746_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize___boxed(lean_object* v_pu_2747_, lean_object* v_code_2748_, lean_object* v_s_2749_, lean_object* v_uniqueIdents_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_){
_start:
{
uint8_t v_pu_boxed_2756_; uint8_t v_uniqueIdents_boxed_2757_; lean_object* v_res_2758_; 
v_pu_boxed_2756_ = lean_unbox(v_pu_2747_);
v_uniqueIdents_boxed_2757_ = lean_unbox(v_uniqueIdents_2750_);
v_res_2758_ = l_Lean_Compiler_LCNF_Code_internalize(v_pu_boxed_2756_, v_code_2748_, v_s_2749_, v_uniqueIdents_boxed_2757_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_);
lean_dec(v_a_2754_);
lean_dec_ref(v_a_2753_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
return v_res_2758_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(lean_object* v_f_2759_, lean_object* v_v_2760_, uint8_t v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
if (lean_obj_tag(v_v_2760_) == 0)
{
lean_object* v_code_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2793_; 
v_code_2768_ = lean_ctor_get(v_v_2760_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_v_2760_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2770_ = v_v_2760_;
v_isShared_2771_ = v_isSharedCheck_2793_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_code_2768_);
lean_dec(v_v_2760_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2793_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = lean_box(v___y_2761_);
lean_inc(v___y_2766_);
lean_inc_ref(v___y_2765_);
lean_inc(v___y_2764_);
lean_inc_ref(v___y_2763_);
lean_inc(v___y_2762_);
v___x_2773_ = lean_apply_8(v_f_2759_, v_code_2768_, v___x_2772_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, lean_box(0));
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2784_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2776_ = v___x_2773_;
v_isShared_2777_ = v_isSharedCheck_2784_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2773_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2784_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 0, v_a_2774_);
v___x_2779_ = v___x_2770_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
lean_object* v___x_2781_; 
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 0, v___x_2779_);
v___x_2781_ = v___x_2776_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_del_object(v___x_2770_);
v_a_2785_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2773_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2773_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
}
else
{
lean_object* v___x_2794_; 
lean_dec_ref(v_f_2759_);
v___x_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2794_, 0, v_v_2760_);
return v___x_2794_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2759_ = stack[0].m_obj;
lean_object* v_v_2760_ = stack[1].m_obj;
uint8_t v___y_2761_ = stack[2].m_num;
lean_object* v___y_2762_ = stack[3].m_obj;
lean_object* v___y_2763_ = stack[4].m_obj;
lean_object* v___y_2764_ = stack[5].m_obj;
lean_object* v___y_2765_ = stack[6].m_obj;
lean_object* v___y_2766_ = stack[7].m_obj;
lean_object* v_res_2795_;
v_res_2795_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2759_, v_v_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
stack->m_obj
 = v_res_2795_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg___boxed(lean_object* v_f_2796_, lean_object* v_v_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
uint8_t v___y_1412__boxed_2805_; lean_object* v_res_2806_; 
v___y_1412__boxed_2805_ = lean_unbox(v___y_2798_);
v_res_2806_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2796_, v_v_2797_, v___y_1412__boxed_2805_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
return v_res_2806_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(uint8_t v_pu_2807_, lean_object* v_f_2808_, lean_object* v_v_2809_, uint8_t v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2808_, v_v_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
return v___x_2817_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2807_ = stack[0].m_num;
lean_object* v_f_2808_ = stack[1].m_obj;
lean_object* v_v_2809_ = stack[2].m_obj;
uint8_t v___y_2810_ = stack[3].m_num;
lean_object* v___y_2811_ = stack[4].m_obj;
lean_object* v___y_2812_ = stack[5].m_obj;
lean_object* v___y_2813_ = stack[6].m_obj;
lean_object* v___y_2814_ = stack[7].m_obj;
lean_object* v___y_2815_ = stack[8].m_obj;
lean_object* v_res_2818_;
v_res_2818_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(v_pu_2807_, v_f_2808_, v_v_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
stack->m_obj
 = v_res_2818_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___boxed(lean_object* v_pu_2819_, lean_object* v_f_2820_, lean_object* v_v_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
uint8_t v_pu_boxed_2829_; uint8_t v___y_1529__boxed_2830_; lean_object* v_res_2831_; 
v_pu_boxed_2829_ = lean_unbox(v_pu_2819_);
v___y_1529__boxed_2830_ = lean_unbox(v___y_2822_);
v_res_2831_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(v_pu_boxed_2829_, v_f_2820_, v_v_2821_, v___y_1529__boxed_2830_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v___y_2823_);
return v_res_2831_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(uint8_t v_pu_2832_, lean_object* v_decl_2833_, uint8_t v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v_toSignature_2841_; lean_object* v_value_2842_; uint8_t v_recursive_2843_; lean_object* v_inlineAttr_x3f_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2904_; 
v_toSignature_2841_ = lean_ctor_get(v_decl_2833_, 0);
v_value_2842_ = lean_ctor_get(v_decl_2833_, 1);
v_recursive_2843_ = lean_ctor_get_uint8(v_decl_2833_, sizeof(void*)*3);
v_inlineAttr_x3f_2844_ = lean_ctor_get(v_decl_2833_, 2);
v_isSharedCheck_2904_ = !lean_is_exclusive(v_decl_2833_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2846_ = v_decl_2833_;
v_isShared_2847_ = v_isSharedCheck_2904_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_inlineAttr_x3f_2844_);
lean_inc(v_value_2842_);
lean_inc(v_toSignature_2841_);
lean_dec(v_decl_2833_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2904_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v_name_2848_; lean_object* v_levelParams_2849_; lean_object* v_type_2850_; lean_object* v_params_2851_; uint8_t v_safe_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2903_; 
v_name_2848_ = lean_ctor_get(v_toSignature_2841_, 0);
v_levelParams_2849_ = lean_ctor_get(v_toSignature_2841_, 1);
v_type_2850_ = lean_ctor_get(v_toSignature_2841_, 2);
v_params_2851_ = lean_ctor_get(v_toSignature_2841_, 3);
v_safe_2852_ = lean_ctor_get_uint8(v_toSignature_2841_, sizeof(void*)*4);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_toSignature_2841_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2854_ = v_toSignature_2841_;
v_isShared_2855_ = v_isSharedCheck_2903_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_params_2851_);
lean_inc(v_type_2850_);
lean_inc(v_levelParams_2849_);
lean_inc(v_name_2848_);
lean_dec(v_toSignature_2841_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2903_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2856_; 
v___x_2856_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2832_, v_type_2850_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; size_t v_sz_2858_; size_t v___x_2859_; lean_object* v___x_2860_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2857_);
lean_dec_ref_known(v___x_2856_, 1);
v_sz_2858_ = lean_array_size(v_params_2851_);
v___x_2859_ = ((size_t)0ULL);
v___x_2860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2832_, v_sz_2858_, v___x_2859_, v_params_2851_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___x_2860_, 1);
v___x_2862_ = lean_box(v_pu_2832_);
v___x_2863_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed), 9, 1);
lean_closure_set(v___x_2863_, 0, v___x_2862_);
v___x_2864_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v___x_2863_, v_value_2842_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2878_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2867_ = v___x_2864_;
v_isShared_2868_ = v_isSharedCheck_2878_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2864_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2878_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 3, v_a_2861_);
lean_ctor_set(v___x_2854_, 2, v_a_2857_);
v___x_2870_ = v___x_2854_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_name_2848_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_levelParams_2849_);
lean_ctor_set(v_reuseFailAlloc_2877_, 2, v_a_2857_);
lean_ctor_set(v_reuseFailAlloc_2877_, 3, v_a_2861_);
lean_ctor_set_uint8(v_reuseFailAlloc_2877_, sizeof(void*)*4, v_safe_2852_);
v___x_2870_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2872_; 
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 1, v_a_2865_);
lean_ctor_set(v___x_2846_, 0, v___x_2870_);
v___x_2872_ = v___x_2846_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2870_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_a_2865_);
lean_ctor_set(v_reuseFailAlloc_2876_, 2, v_inlineAttr_x3f_2844_);
lean_ctor_set_uint8(v_reuseFailAlloc_2876_, sizeof(void*)*3, v_recursive_2843_);
v___x_2872_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v___x_2874_; 
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 0, v___x_2872_);
v___x_2874_ = v___x_2867_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec(v_a_2861_);
lean_dec(v_a_2857_);
lean_del_object(v___x_2854_);
lean_dec(v_levelParams_2849_);
lean_dec(v_name_2848_);
lean_del_object(v___x_2846_);
lean_dec(v_inlineAttr_x3f_2844_);
v_a_2879_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2864_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2864_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec(v_a_2857_);
lean_del_object(v___x_2854_);
lean_dec(v_levelParams_2849_);
lean_dec(v_name_2848_);
lean_del_object(v___x_2846_);
lean_dec(v_inlineAttr_x3f_2844_);
lean_dec_ref(v_value_2842_);
v_a_2887_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2860_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2860_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_del_object(v___x_2854_);
lean_dec_ref(v_params_2851_);
lean_dec(v_levelParams_2849_);
lean_dec(v_name_2848_);
lean_del_object(v___x_2846_);
lean_dec(v_inlineAttr_x3f_2844_);
lean_dec_ref(v_value_2842_);
v_a_2895_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2856_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2856_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2832_ = stack[0].m_num;
lean_object* v_decl_2833_ = stack[1].m_obj;
uint8_t v_a_2834_ = stack[2].m_num;
lean_object* v_a_2835_ = stack[3].m_obj;
lean_object* v_a_2836_ = stack[4].m_obj;
lean_object* v_a_2837_ = stack[5].m_obj;
lean_object* v_a_2838_ = stack[6].m_obj;
lean_object* v_a_2839_ = stack[7].m_obj;
lean_object* v_res_2905_;
v_res_2905_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_2832_, v_decl_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
stack->m_obj
 = v_res_2905_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go___boxed(lean_object* v_pu_2906_, lean_object* v_decl_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_){
_start:
{
uint8_t v_pu_boxed_2915_; uint8_t v_a_boxed_2916_; lean_object* v_res_2917_; 
v_pu_boxed_2915_ = lean_unbox(v_pu_2906_);
v_a_boxed_2916_ = lean_unbox(v_a_2908_);
v_res_2917_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_boxed_2915_, v_decl_2907_, v_a_boxed_2916_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
lean_dec(v_a_2913_);
lean_dec_ref(v_a_2912_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
lean_dec(v_a_2909_);
return v_res_2917_;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t v_pu_2918_, lean_object* v_decl_2919_, lean_object* v_s_2920_, uint8_t v_uniqueIdents_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = lean_st_mk_ref(v_s_2920_);
v___x_2928_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_2918_, v_decl_2919_, v_uniqueIdents_2921_, v___x_2927_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2937_; 
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2931_ = v___x_2928_;
v_isShared_2932_ = v_isSharedCheck_2937_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2928_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2937_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2933_; lean_object* v___x_2935_; 
v___x_2933_ = lean_st_ref_get(v___x_2927_);
lean_dec(v___x_2927_);
lean_dec(v___x_2933_);
if (v_isShared_2932_ == 0)
{
v___x_2935_ = v___x_2931_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2929_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
else
{
lean_dec(v___x_2927_);
return v___x_2928_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Decl_internalize_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2918_ = stack[0].m_num;
lean_object* v_decl_2919_ = stack[1].m_obj;
lean_object* v_s_2920_ = stack[2].m_obj;
uint8_t v_uniqueIdents_2921_ = stack[3].m_num;
lean_object* v_a_2922_ = stack[4].m_obj;
lean_object* v_a_2923_ = stack[5].m_obj;
lean_object* v_a_2924_ = stack[6].m_obj;
lean_object* v_a_2925_ = stack[7].m_obj;
lean_object* v_res_2938_;
v_res_2938_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_2918_, v_decl_2919_, v_s_2920_, v_uniqueIdents_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_);
stack->m_obj
 = v_res_2938_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize___boxed(lean_object* v_pu_2939_, lean_object* v_decl_2940_, lean_object* v_s_2941_, lean_object* v_uniqueIdents_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
uint8_t v_pu_boxed_2948_; uint8_t v_uniqueIdents_boxed_2949_; lean_object* v_res_2950_; 
v_pu_boxed_2948_ = lean_unbox(v_pu_2939_);
v_uniqueIdents_boxed_2949_ = lean_unbox(v_uniqueIdents_2942_);
v_res_2950_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_boxed_2948_, v_decl_2940_, v_s_2941_, v_uniqueIdents_boxed_2949_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
return v_res_2950_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = lean_box(0);
v___x_2952_ = lean_unsigned_to_nat(16u);
v___x_2953_ = lean_mk_array(v___x_2952_, v___x_2951_);
return v___x_2953_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2954_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0);
v___x_2955_ = lean_unsigned_to_nat(0u);
v___x_2956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
lean_ctor_set(v___x_2956_, 1, v___x_2954_);
return v___x_2956_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(uint8_t v_pu_2957_, size_t v_sz_2958_, size_t v_i_2959_, lean_object* v_bs_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
uint8_t v___x_2966_; 
v___x_2966_ = lean_usize_dec_lt(v_i_2959_, v_sz_2958_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2967_, 0, v_bs_2960_);
return v___x_2967_;
}
else
{
lean_object* v_v_2968_; lean_object* v___x_2969_; lean_object* v_bs_x27_2970_; lean_object* v___x_2971_; lean_object* v_lctx_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2997_; 
v_v_2968_ = lean_array_uget(v_bs_2960_, v_i_2959_);
v___x_2969_ = lean_unsigned_to_nat(0u);
v_bs_x27_2970_ = lean_array_uset(v_bs_2960_, v_i_2959_, v___x_2969_);
v___x_2971_ = lean_st_ref_take(v___y_2962_);
v_lctx_2972_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2997_ == 0)
{
lean_object* v_unused_2998_; 
v_unused_2998_ = lean_ctor_get(v___x_2971_, 1);
lean_dec(v_unused_2998_);
v___x_2974_ = v___x_2971_;
v_isShared_2975_ = v_isSharedCheck_2997_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_lctx_2972_);
lean_dec(v___x_2971_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2997_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2976_ = lean_unsigned_to_nat(1u);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 1, v___x_2976_);
v___x_2978_ = v___x_2974_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_lctx_2972_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; lean_object* v___x_2982_; 
v___x_2979_ = lean_st_ref_put(v___y_2962_, v___x_2978_);
v___x_2980_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_2981_ = 0;
v___x_2982_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_2957_, v_v_2968_, v___x_2980_, v___x_2981_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; size_t v___x_2984_; size_t v___x_2985_; lean_object* v___x_2986_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref_known(v___x_2982_, 1);
v___x_2984_ = ((size_t)1ULL);
v___x_2985_ = lean_usize_add(v_i_2959_, v___x_2984_);
v___x_2986_ = lean_array_uset(v_bs_x27_2970_, v_i_2959_, v_a_2983_);
v_i_2959_ = v___x_2985_;
v_bs_2960_ = v___x_2986_;
goto _start;
}
else
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
lean_dec_ref(v_bs_x27_2970_);
v_a_2988_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2990_ = v___x_2982_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2982_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2957_ = stack[0].m_num;
size_t v_sz_2958_ = stack[1].m_num;
size_t v_i_2959_ = stack[2].m_num;
lean_object* v_bs_2960_ = stack[3].m_obj;
lean_object* v___y_2961_ = stack[4].m_obj;
lean_object* v___y_2962_ = stack[5].m_obj;
lean_object* v___y_2963_ = stack[6].m_obj;
lean_object* v___y_2964_ = stack[7].m_obj;
lean_object* v_res_2999_;
v_res_2999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_2957_, v_sz_2958_, v_i_2959_, v_bs_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
stack->m_obj
 = v_res_2999_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___boxed(lean_object* v_pu_3000_, lean_object* v_sz_3001_, lean_object* v_i_3002_, lean_object* v_bs_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
uint8_t v_pu_boxed_3009_; size_t v_sz_boxed_3010_; size_t v_i_boxed_3011_; lean_object* v_res_3012_; 
v_pu_boxed_3009_ = lean_unbox(v_pu_3000_);
v_sz_boxed_3010_ = lean_unbox_usize(v_sz_3001_);
lean_dec(v_sz_3001_);
v_i_boxed_3011_ = lean_unbox_usize(v_i_3002_);
lean_dec(v_i_3002_);
v_res_3012_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_boxed_3009_, v_sz_boxed_3010_, v_i_boxed_3011_, v_bs_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
return v_res_3012_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__0(void){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_3014_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
lean_ctor_set(v___x_3014_, 1, v___x_3013_);
lean_ctor_set(v___x_3014_, 2, v___x_3013_);
lean_ctor_set(v___x_3014_, 3, v___x_3013_);
lean_ctor_set(v___x_3014_, 4, v___x_3013_);
lean_ctor_set(v___x_3014_, 5, v___x_3013_);
return v___x_3014_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__1(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = lean_unsigned_to_nat(1u);
v___x_3016_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__0, &l_Lean_Compiler_LCNF_cleanup___closed__0_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__0);
v___x_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
lean_ctor_set(v___x_3017_, 1, v___x_3015_);
return v___x_3017_;
}
}
lean_object* l_Lean_Compiler_LCNF_cleanup(uint8_t v_pu_3018_, lean_object* v_decl_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; size_t v_sz_3028_; size_t v___x_3029_; lean_object* v___x_3030_; 
v___x_3025_ = lean_st_ref_take(v_a_3021_);
lean_dec(v___x_3025_);
v___x_3026_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
v___x_3027_ = lean_st_ref_put(v_a_3021_, v___x_3026_);
v_sz_3028_ = lean_array_size(v_decl_3019_);
v___x_3029_ = ((size_t)0ULL);
v___x_3030_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_3018_, v_sz_3028_, v___x_3029_, v_decl_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
return v___x_3030_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_cleanup_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3018_ = stack[0].m_num;
lean_object* v_decl_3019_ = stack[1].m_obj;
lean_object* v_a_3020_ = stack[2].m_obj;
lean_object* v_a_3021_ = stack[3].m_obj;
lean_object* v_a_3022_ = stack[4].m_obj;
lean_object* v_a_3023_ = stack[5].m_obj;
lean_object* v_res_3031_;
v_res_3031_ = l_Lean_Compiler_LCNF_cleanup(v_pu_3018_, v_decl_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
stack->m_obj
 = v_res_3031_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup___boxed(lean_object* v_pu_3032_, lean_object* v_decl_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
uint8_t v_pu_boxed_3039_; lean_object* v_res_3040_; 
v_pu_boxed_3039_ = lean_unbox(v_pu_3032_);
v_res_3040_ = l_Lean_Compiler_LCNF_cleanup(v_pu_boxed_3039_, v_decl_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
lean_dec(v_a_3037_);
lean_dec_ref(v_a_3036_);
lean_dec(v_a_3035_);
lean_dec_ref(v_a_3034_);
return v_res_3040_;
}
}
lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(lean_object* v_a_3041_, lean_object* v_ngen_3042_, lean_object* v_a_x3f_3043_){
_start:
{
lean_object* v___x_3045_; lean_object* v_env_3046_; lean_object* v_nextMacroScope_3047_; lean_object* v_auxDeclNGen_3048_; lean_object* v_traceState_3049_; lean_object* v_cache_3050_; lean_object* v_recordedDeps_3051_; lean_object* v_messages_3052_; lean_object* v_infoState_3053_; lean_object* v_snapshotTasks_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3064_; 
v___x_3045_ = lean_st_ref_take(v_a_3041_);
v_env_3046_ = lean_ctor_get(v___x_3045_, 0);
v_nextMacroScope_3047_ = lean_ctor_get(v___x_3045_, 1);
v_auxDeclNGen_3048_ = lean_ctor_get(v___x_3045_, 3);
v_traceState_3049_ = lean_ctor_get(v___x_3045_, 4);
v_cache_3050_ = lean_ctor_get(v___x_3045_, 5);
v_recordedDeps_3051_ = lean_ctor_get(v___x_3045_, 6);
v_messages_3052_ = lean_ctor_get(v___x_3045_, 7);
v_infoState_3053_ = lean_ctor_get(v___x_3045_, 8);
v_snapshotTasks_3054_ = lean_ctor_get(v___x_3045_, 9);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3064_ == 0)
{
lean_object* v_unused_3065_; 
v_unused_3065_ = lean_ctor_get(v___x_3045_, 2);
lean_dec(v_unused_3065_);
v___x_3056_ = v___x_3045_;
v_isShared_3057_ = v_isSharedCheck_3064_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_snapshotTasks_3054_);
lean_inc(v_infoState_3053_);
lean_inc(v_messages_3052_);
lean_inc(v_recordedDeps_3051_);
lean_inc(v_cache_3050_);
lean_inc(v_traceState_3049_);
lean_inc(v_auxDeclNGen_3048_);
lean_inc(v_nextMacroScope_3047_);
lean_inc(v_env_3046_);
lean_dec(v___x_3045_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3064_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3058_; lean_object* v___x_3060_; 
v___x_3058_ = lean_box(0);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 2, v_ngen_3042_);
v___x_3060_ = v___x_3056_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_env_3046_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v_nextMacroScope_3047_);
lean_ctor_set(v_reuseFailAlloc_3063_, 2, v_ngen_3042_);
lean_ctor_set(v_reuseFailAlloc_3063_, 3, v_auxDeclNGen_3048_);
lean_ctor_set(v_reuseFailAlloc_3063_, 4, v_traceState_3049_);
lean_ctor_set(v_reuseFailAlloc_3063_, 5, v_cache_3050_);
lean_ctor_set(v_reuseFailAlloc_3063_, 6, v_recordedDeps_3051_);
lean_ctor_set(v_reuseFailAlloc_3063_, 7, v_messages_3052_);
lean_ctor_set(v_reuseFailAlloc_3063_, 8, v_infoState_3053_);
lean_ctor_set(v_reuseFailAlloc_3063_, 9, v_snapshotTasks_3054_);
v___x_3060_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = lean_st_ref_put(v_a_3041_, v___x_3060_);
v___x_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3058_);
return v___x_3062_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3041_ = stack[0].m_obj;
lean_object* v_ngen_3042_ = stack[1].m_obj;
lean_object* v_a_x3f_3043_ = stack[2].m_obj;
lean_object* v_res_3066_;
v_res_3066_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3041_, v_ngen_3042_, v_a_x3f_3043_);
stack->m_obj
 = v_res_3066_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0___boxed(lean_object* v_a_3067_, lean_object* v_ngen_3068_, lean_object* v_a_x3f_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3067_, v_ngen_3068_, v_a_x3f_3069_);
lean_dec(v_a_x3f_3069_);
lean_dec(v_a_3067_);
return v_res_3071_;
}
}
lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(uint8_t v_pu_3078_, lean_object* v_decl_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v___x_3083_; lean_object* v_ngen_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v_env_3087_; lean_object* v_nextMacroScope_3088_; lean_object* v_auxDeclNGen_3089_; lean_object* v_traceState_3090_; lean_object* v_cache_3091_; lean_object* v_recordedDeps_3092_; lean_object* v_messages_3093_; lean_object* v_infoState_3094_; lean_object* v_snapshotTasks_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3139_; 
v___x_3083_ = lean_st_ref_get(v_a_3081_);
v_ngen_3084_ = lean_ctor_get(v___x_3083_, 2);
lean_inc_ref(v_ngen_3084_);
lean_dec(v___x_3083_);
v___x_3085_ = ((lean_object*)(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2));
v___x_3086_ = lean_st_ref_take(v_a_3081_);
v_env_3087_ = lean_ctor_get(v___x_3086_, 0);
v_nextMacroScope_3088_ = lean_ctor_get(v___x_3086_, 1);
v_auxDeclNGen_3089_ = lean_ctor_get(v___x_3086_, 3);
v_traceState_3090_ = lean_ctor_get(v___x_3086_, 4);
v_cache_3091_ = lean_ctor_get(v___x_3086_, 5);
v_recordedDeps_3092_ = lean_ctor_get(v___x_3086_, 6);
v_messages_3093_ = lean_ctor_get(v___x_3086_, 7);
v_infoState_3094_ = lean_ctor_get(v___x_3086_, 8);
v_snapshotTasks_3095_ = lean_ctor_get(v___x_3086_, 9);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3139_ == 0)
{
lean_object* v_unused_3140_; 
v_unused_3140_ = lean_ctor_get(v___x_3086_, 2);
lean_dec(v_unused_3140_);
v___x_3097_ = v___x_3086_;
v_isShared_3098_ = v_isSharedCheck_3139_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_snapshotTasks_3095_);
lean_inc(v_infoState_3094_);
lean_inc(v_messages_3093_);
lean_inc(v_recordedDeps_3092_);
lean_inc(v_cache_3091_);
lean_inc(v_traceState_3090_);
lean_inc(v_auxDeclNGen_3089_);
lean_inc(v_nextMacroScope_3088_);
lean_inc(v_env_3087_);
lean_dec(v___x_3086_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3139_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 2, v___x_3085_);
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_env_3087_);
lean_ctor_set(v_reuseFailAlloc_3138_, 1, v_nextMacroScope_3088_);
lean_ctor_set(v_reuseFailAlloc_3138_, 2, v___x_3085_);
lean_ctor_set(v_reuseFailAlloc_3138_, 3, v_auxDeclNGen_3089_);
lean_ctor_set(v_reuseFailAlloc_3138_, 4, v_traceState_3090_);
lean_ctor_set(v_reuseFailAlloc_3138_, 5, v_cache_3091_);
lean_ctor_set(v_reuseFailAlloc_3138_, 6, v_recordedDeps_3092_);
lean_ctor_set(v_reuseFailAlloc_3138_, 7, v_messages_3093_);
lean_ctor_set(v_reuseFailAlloc_3138_, 8, v_infoState_3094_);
lean_ctor_set(v_reuseFailAlloc_3138_, 9, v_snapshotTasks_3095_);
v___x_3100_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; lean_object* v_r_3109_; 
v___x_3101_ = lean_st_ref_put(v_a_3081_, v___x_3100_);
v___x_3102_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_3103_ = 0;
v___x_3104_ = lean_box(v_pu_3078_);
v___x_3105_ = lean_box(v___x_3103_);
v___x_3106_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_internalize___boxed), 9, 4);
lean_closure_set(v___x_3106_, 0, v___x_3104_);
lean_closure_set(v___x_3106_, 1, v_decl_3079_);
lean_closure_set(v___x_3106_, 2, v___x_3102_);
lean_closure_set(v___x_3106_, 3, v___x_3105_);
v___x_3107_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
v___x_3108_ = 0;
v_r_3109_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v___x_3106_, v___x_3107_, v___x_3108_, v_a_3080_, v_a_3081_);
if (lean_obj_tag(v_r_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3126_; 
v_a_3110_ = lean_ctor_get(v_r_3109_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v_r_3109_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3112_ = v_r_3109_;
v_isShared_3113_ = v_isSharedCheck_3126_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v_r_3109_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3126_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
lean_inc(v_a_3110_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set_tag(v___x_3112_, 1);
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
lean_object* v___x_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
v___x_3116_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3081_, v_ngen_3084_, v___x_3115_);
lean_dec_ref(v___x_3115_);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3123_ == 0)
{
lean_object* v_unused_3124_; 
v_unused_3124_ = lean_ctor_get(v___x_3116_, 0);
lean_dec(v_unused_3124_);
v___x_3118_ = v___x_3116_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_dec(v___x_3116_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v_a_3110_);
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3110_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
v_a_3127_ = lean_ctor_get(v_r_3109_, 0);
lean_inc(v_a_3127_);
lean_dec_ref_known(v_r_3109_, 1);
v___x_3128_ = lean_box(0);
v___x_3129_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3081_, v_ngen_3084_, v___x_3128_);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; 
v_unused_3137_ = lean_ctor_get(v___x_3129_, 0);
lean_dec(v_unused_3137_);
v___x_3131_ = v___x_3129_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_dec(v___x_3129_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
lean_ctor_set_tag(v___x_3131_, 1);
lean_ctor_set(v___x_3131_, 0, v_a_3127_);
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3127_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normalizeFVarIds_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3078_ = stack[0].m_num;
lean_object* v_decl_3079_ = stack[1].m_obj;
lean_object* v_a_3080_ = stack[2].m_obj;
lean_object* v_a_3081_ = stack[3].m_obj;
lean_object* v_res_3141_;
v_res_3141_ = l_Lean_Compiler_LCNF_normalizeFVarIds(v_pu_3078_, v_decl_3079_, v_a_3080_, v_a_3081_);
stack->m_obj
 = v_res_3141_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___boxed(lean_object* v_pu_3142_, lean_object* v_decl_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_){
_start:
{
uint8_t v_pu_boxed_3147_; lean_object* v_res_3148_; 
v_pu_boxed_3147_ = lean_unbox(v_pu_3142_);
v_res_3148_ = l_Lean_Compiler_LCNF_normalizeFVarIds(v_pu_boxed_3147_, v_decl_3143_, v_a_3144_, v_a_3145_);
lean_dec(v_a_3145_);
lean_dec_ref(v_a_3144_);
return v_res_3148_;
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
