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
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___f_673_; lean_object* v___x_7038__overap_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_670_ = l_StateRefT_x27_instMonad___redArg(v___x_669_);
v___x_671_ = l_Lean_instInhabitedExpr;
v___x_672_ = l_instInhabitedOfMonad___redArg(v___x_670_, v___x_671_);
v___f_673_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_673_, 0, v___x_672_);
v___x_7038__overap_674_ = lean_panic_fn_borrowed(v___f_673_, v_msg_613_);
lean_dec_ref(v___f_673_);
v___x_675_ = lean_box(v___y_614_);
lean_inc(v___y_619_);
lean_inc_ref(v___y_618_);
lean_inc(v___y_617_);
lean_inc_ref(v___y_616_);
lean_inc(v___y_615_);
v___x_676_ = lean_apply_7(v___x_7038__overap_674_, v___x_675_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, lean_box(0));
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
uint8_t v___y_7187__boxed_697_; lean_object* v_res_698_; 
v___y_7187__boxed_697_ = lean_unbox(v___y_690_);
v_res_698_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v_msg_689_, v___y_7187__boxed_697_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
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
lean_object* v_val_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_762_; 
lean_dec_ref_known(v_e_709_, 1);
v_val_723_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_762_ == 0)
{
v___x_725_ = v___x_721_;
v_isShared_726_ = v_isSharedCheck_762_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_val_723_);
lean_dec(v___x_721_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_762_;
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
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_745_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_745_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_745_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_745_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
if (lean_obj_tag(v_a_733_) == 0)
{
lean_object* v___x_737_; lean_object* v___x_739_; 
lean_dec(v_fvarId_731_);
v___x_737_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_737_);
v___x_739_ = v___x_735_;
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
else
{
lean_object* v___x_741_; lean_object* v___x_743_; 
lean_dec_ref_known(v_a_733_, 1);
v___x_741_ = l_Lean_Expr_fvar___override(v_fvarId_731_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_741_);
v___x_743_ = v___x_735_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec(v_fvarId_731_);
v_a_746_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_732_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_732_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
default: 
{
lean_object* v_expr_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_del_object(v___x_725_);
v_expr_754_ = lean_ctor_get(v_val_723_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v_val_723_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v_val_723_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_expr_754_);
lean_dec(v_val_723_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set_tag(v___x_756_, 0);
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_expr_754_);
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
}
}
}
case 5:
{
lean_object* v_fn_763_; lean_object* v_arg_764_; lean_object* v___x_765_; 
v_fn_763_ = lean_ctor_get(v_e_709_, 0);
v_arg_764_ = lean_ctor_get(v_e_709_, 1);
lean_inc_ref(v_fn_763_);
v___x_765_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_708_, v_fn_763_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_767_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
lean_inc_ref(v_arg_764_);
v___x_767_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_708_, v_arg_764_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_786_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_786_ == 0)
{
v___x_770_ = v___x_767_;
v_isShared_771_ = v_isSharedCheck_786_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_786_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___y_773_; size_t v___x_778_; size_t v___x_779_; uint8_t v___x_780_; 
v___x_778_ = lean_ptr_addr(v_fn_763_);
v___x_779_ = lean_ptr_addr(v_a_766_);
v___x_780_ = lean_usize_dec_eq(v___x_778_, v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
lean_dec_ref_known(v_e_709_, 2);
v___x_781_ = l_Lean_Expr_app___override(v_a_766_, v_a_768_);
v___y_773_ = v___x_781_;
goto v___jp_772_;
}
else
{
size_t v___x_782_; size_t v___x_783_; uint8_t v___x_784_; 
v___x_782_ = lean_ptr_addr(v_arg_764_);
v___x_783_ = lean_ptr_addr(v_a_768_);
v___x_784_ = lean_usize_dec_eq(v___x_782_, v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_dec_ref_known(v_e_709_, 2);
v___x_785_ = l_Lean_Expr_app___override(v_a_766_, v_a_768_);
v___y_773_ = v___x_785_;
goto v___jp_772_;
}
else
{
lean_dec(v_a_768_);
lean_dec(v_a_766_);
v___y_773_ = v_e_709_;
goto v___jp_772_;
}
}
v___jp_772_:
{
lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_774_ = l_Lean_Expr_headBeta(v___y_773_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_774_);
v___x_776_ = v___x_770_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
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
else
{
lean_dec(v_a_766_);
lean_dec_ref_known(v_e_709_, 2);
return v___x_767_;
}
}
else
{
lean_dec_ref_known(v_e_709_, 2);
return v___x_765_;
}
}
case 6:
{
lean_object* v_binderName_787_; lean_object* v_binderType_788_; lean_object* v_body_789_; uint8_t v_binderInfo_790_; lean_object* v___x_791_; 
v_binderName_787_ = lean_ctor_get(v_e_709_, 0);
v_binderType_788_ = lean_ctor_get(v_e_709_, 1);
v_body_789_ = lean_ctor_get(v_e_709_, 2);
v_binderInfo_790_ = lean_ctor_get_uint8(v_e_709_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_788_);
v___x_791_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_708_, v_binderType_788_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_793_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
lean_inc_ref(v_body_789_);
v___x_793_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_708_, v_body_789_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_820_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_820_ == 0)
{
v___x_796_ = v___x_793_;
v_isShared_797_ = v_isSharedCheck_820_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_820_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
size_t v___x_798_; size_t v___x_799_; uint8_t v___x_800_; 
v___x_798_ = lean_ptr_addr(v_binderType_788_);
v___x_799_ = lean_ptr_addr(v_a_792_);
v___x_800_ = lean_usize_dec_eq(v___x_798_, v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v___x_803_; 
lean_inc(v_binderName_787_);
lean_dec_ref_known(v_e_709_, 3);
v___x_801_ = l_Lean_Expr_lam___override(v_binderName_787_, v_a_792_, v_a_794_, v_binderInfo_790_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_801_);
v___x_803_ = v___x_796_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
else
{
size_t v___x_805_; size_t v___x_806_; uint8_t v___x_807_; 
v___x_805_ = lean_ptr_addr(v_body_789_);
v___x_806_ = lean_ptr_addr(v_a_794_);
v___x_807_ = lean_usize_dec_eq(v___x_805_, v___x_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_810_; 
lean_inc(v_binderName_787_);
lean_dec_ref_known(v_e_709_, 3);
v___x_808_ = l_Lean_Expr_lam___override(v_binderName_787_, v_a_792_, v_a_794_, v_binderInfo_790_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_808_);
v___x_810_ = v___x_796_;
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
uint8_t v___x_812_; 
v___x_812_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_790_, v_binderInfo_790_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_815_; 
lean_inc(v_binderName_787_);
lean_dec_ref_known(v_e_709_, 3);
v___x_813_ = l_Lean_Expr_lam___override(v_binderName_787_, v_a_792_, v_a_794_, v_binderInfo_790_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_813_);
v___x_815_ = v___x_796_;
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
lean_object* v___x_818_; 
lean_dec(v_a_794_);
lean_dec(v_a_792_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v_e_709_);
v___x_818_ = v___x_796_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_e_709_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
}
else
{
lean_dec(v_a_792_);
lean_dec_ref_known(v_e_709_, 3);
return v___x_793_;
}
}
else
{
lean_dec_ref_known(v_e_709_, 3);
return v___x_791_;
}
}
case 7:
{
lean_object* v_binderName_821_; lean_object* v_binderType_822_; lean_object* v_body_823_; uint8_t v_binderInfo_824_; lean_object* v___x_825_; 
v_binderName_821_ = lean_ctor_get(v_e_709_, 0);
v_binderType_822_ = lean_ctor_get(v_e_709_, 1);
v_body_823_ = lean_ctor_get(v_e_709_, 2);
v_binderInfo_824_ = lean_ctor_get_uint8(v_e_709_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_822_);
v___x_825_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_708_, v_binderType_822_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_827_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref_known(v___x_825_, 1);
lean_inc_ref(v_body_823_);
v___x_827_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_708_, v_body_823_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_854_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_854_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_854_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_854_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
size_t v___x_832_; size_t v___x_833_; uint8_t v___x_834_; 
v___x_832_ = lean_ptr_addr(v_binderType_822_);
v___x_833_ = lean_ptr_addr(v_a_826_);
v___x_834_ = lean_usize_dec_eq(v___x_832_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_837_; 
lean_inc(v_binderName_821_);
lean_dec_ref_known(v_e_709_, 3);
v___x_835_ = l_Lean_Expr_forallE___override(v_binderName_821_, v_a_826_, v_a_828_, v_binderInfo_824_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_835_);
v___x_837_ = v___x_830_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
else
{
size_t v___x_839_; size_t v___x_840_; uint8_t v___x_841_; 
v___x_839_ = lean_ptr_addr(v_body_823_);
v___x_840_ = lean_ptr_addr(v_a_828_);
v___x_841_ = lean_usize_dec_eq(v___x_839_, v___x_840_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; lean_object* v___x_844_; 
lean_inc(v_binderName_821_);
lean_dec_ref_known(v_e_709_, 3);
v___x_842_ = l_Lean_Expr_forallE___override(v_binderName_821_, v_a_826_, v_a_828_, v_binderInfo_824_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_842_);
v___x_844_ = v___x_830_;
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
uint8_t v___x_846_; 
v___x_846_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_824_, v_binderInfo_824_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_849_; 
lean_inc(v_binderName_821_);
lean_dec_ref_known(v_e_709_, 3);
v___x_847_ = l_Lean_Expr_forallE___override(v_binderName_821_, v_a_826_, v_a_828_, v_binderInfo_824_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_847_);
v___x_849_ = v___x_830_;
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
lean_object* v___x_852_; 
lean_dec(v_a_828_);
lean_dec(v_a_826_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v_e_709_);
v___x_852_ = v___x_830_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_e_709_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
}
else
{
lean_dec(v_a_826_);
lean_dec_ref_known(v_e_709_, 3);
return v___x_827_;
}
}
else
{
lean_dec_ref_known(v_e_709_, 3);
return v___x_825_;
}
}
case 8:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
lean_dec_ref_known(v_e_709_, 4);
v___x_855_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3, &l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3);
v___x_856_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v___x_855_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
return v___x_856_;
}
case 10:
{
lean_object* v_data_857_; lean_object* v_expr_858_; lean_object* v___x_859_; 
v_data_857_ = lean_ctor_get(v_e_709_, 0);
v_expr_858_ = lean_ctor_get(v_e_709_, 1);
lean_inc_ref(v_expr_858_);
v___x_859_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_708_, v_expr_858_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_874_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_874_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_874_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_874_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
size_t v___x_864_; size_t v___x_865_; uint8_t v___x_866_; 
v___x_864_ = lean_ptr_addr(v_expr_858_);
v___x_865_ = lean_ptr_addr(v_a_860_);
v___x_866_ = lean_usize_dec_eq(v___x_864_, v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_869_; 
lean_inc(v_data_857_);
lean_dec_ref_known(v_e_709_, 2);
v___x_867_ = l_Lean_Expr_mdata___override(v_data_857_, v_a_860_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_867_);
v___x_869_ = v___x_862_;
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
lean_object* v___x_872_; 
lean_dec(v_a_860_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v_e_709_);
v___x_872_ = v___x_862_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_e_709_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_709_, 2);
return v___x_859_;
}
}
case 11:
{
lean_object* v_typeName_875_; lean_object* v_idx_876_; lean_object* v_struct_877_; lean_object* v___x_878_; 
v_typeName_875_ = lean_ctor_get(v_e_709_, 0);
v_idx_876_ = lean_ctor_get(v_e_709_, 1);
v_struct_877_ = lean_ctor_get(v_e_709_, 2);
lean_inc_ref(v_struct_877_);
v___x_878_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_708_, v_struct_877_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_893_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_893_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_893_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_893_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
size_t v___x_883_; size_t v___x_884_; uint8_t v___x_885_; 
v___x_883_ = lean_ptr_addr(v_struct_877_);
v___x_884_ = lean_ptr_addr(v_a_879_);
v___x_885_ = lean_usize_dec_eq(v___x_883_, v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_888_; 
lean_inc(v_idx_876_);
lean_inc(v_typeName_875_);
lean_dec_ref_known(v_e_709_, 3);
v___x_886_ = l_Lean_Expr_proj___override(v_typeName_875_, v_idx_876_, v_a_879_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_886_);
v___x_888_ = v___x_881_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
else
{
lean_object* v___x_891_; 
lean_dec(v_a_879_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v_e_709_);
v___x_891_ = v___x_881_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_e_709_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_709_, 3);
return v___x_878_;
}
}
default: 
{
lean_object* v___x_894_; 
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v_e_709_);
return v___x_894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(uint8_t v_pu_895_, lean_object* v_e_896_, uint8_t v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
if (lean_obj_tag(v_e_896_) == 5)
{
lean_object* v_fn_904_; lean_object* v_arg_905_; lean_object* v___x_906_; 
v_fn_904_ = lean_ctor_get(v_e_896_, 0);
v_arg_905_ = lean_ctor_get(v_e_896_, 1);
lean_inc_ref(v_fn_904_);
v___x_906_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_895_, v_fn_904_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_908_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_907_);
lean_dec_ref_known(v___x_906_, 1);
lean_inc_ref(v_arg_905_);
v___x_908_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_895_, v_arg_905_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_930_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_930_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_930_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_930_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
size_t v___x_913_; size_t v___x_914_; uint8_t v___x_915_; 
v___x_913_ = lean_ptr_addr(v_fn_904_);
v___x_914_ = lean_ptr_addr(v_a_907_);
v___x_915_ = lean_usize_dec_eq(v___x_913_, v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_918_; 
lean_dec_ref_known(v_e_896_, 2);
v___x_916_ = l_Lean_Expr_app___override(v_a_907_, v_a_909_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_916_);
v___x_918_ = v___x_911_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
else
{
size_t v___x_920_; size_t v___x_921_; uint8_t v___x_922_; 
v___x_920_ = lean_ptr_addr(v_arg_905_);
v___x_921_ = lean_ptr_addr(v_a_909_);
v___x_922_ = lean_usize_dec_eq(v___x_920_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v___x_925_; 
lean_dec_ref_known(v_e_896_, 2);
v___x_923_ = l_Lean_Expr_app___override(v_a_907_, v_a_909_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_923_);
v___x_925_ = v___x_911_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
else
{
lean_object* v___x_928_; 
lean_dec(v_a_909_);
lean_dec(v_a_907_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v_e_896_);
v___x_928_ = v___x_911_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_e_896_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
else
{
lean_dec(v_a_907_);
lean_dec_ref_known(v_e_896_, 2);
return v___x_908_;
}
}
else
{
lean_dec_ref_known(v_e_896_, 2);
return v___x_906_;
}
}
else
{
lean_object* v___x_931_; 
v___x_931_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_895_, v_e_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp___boxed(lean_object* v_pu_932_, lean_object* v_e_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
uint8_t v_pu_boxed_941_; uint8_t v_a_boxed_942_; lean_object* v_res_943_; 
v_pu_boxed_941_ = lean_unbox(v_pu_932_);
v_a_boxed_942_ = lean_unbox(v_a_934_);
v_res_943_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_boxed_941_, v_e_933_, v_a_boxed_942_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
lean_dec(v_a_935_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___boxed(lean_object* v_pu_944_, lean_object* v_e_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
uint8_t v_pu_boxed_953_; uint8_t v_a_boxed_954_; lean_object* v_res_955_; 
v_pu_boxed_953_ = lean_unbox(v_pu_944_);
v_a_boxed_954_ = lean_unbox(v_a_946_);
v_res_955_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_boxed_953_, v_e_945_, v_a_boxed_954_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(lean_object* v_00_u03b2_956_, lean_object* v_m_957_, lean_object* v_a_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v_m_957_, v_a_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___boxed(lean_object* v_00_u03b2_960_, lean_object* v_m_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(v_00_u03b2_960_, v_m_961_, v_a_962_);
lean_dec(v_a_962_);
lean_dec_ref(v_m_961_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(lean_object* v_00_u03b2_964_, lean_object* v_a_965_, lean_object* v_x_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_965_, v_x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_968_, lean_object* v_a_969_, lean_object* v_x_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(v_00_u03b2_968_, v_a_969_, v_x_970_);
lean_dec(v_x_970_);
lean_dec(v_a_969_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(uint8_t v_pu_972_, lean_object* v_e_973_, uint8_t v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_981_ = lean_box(v_pu_972_);
v___x_982_ = lean_obj_tag_nat(v___x_981_);
lean_dec(v___x_981_);
v___x_983_ = lean_unsigned_to_nat(1u);
v___x_984_ = lean_nat_dec_eq(v___x_982_, v___x_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
v___x_985_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_972_, v_e_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
return v___x_985_;
}
else
{
lean_object* v___x_986_; 
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v_e_973_);
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___boxed(lean_object* v_pu_987_, lean_object* v_e_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
uint8_t v_pu_boxed_996_; uint8_t v_a_boxed_997_; lean_object* v_res_998_; 
v_pu_boxed_996_ = lean_unbox(v_pu_987_);
v_a_boxed_997_ = lean_unbox(v_a_989_);
v_res_998_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_boxed_996_, v_e_988_, v_a_boxed_997_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t v_pu_999_, lean_object* v_p_1000_, uint8_t v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v_fvarId_1008_; lean_object* v_binderName_1009_; lean_object* v_type_1010_; uint8_t v_borrow_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1059_; 
v_fvarId_1008_ = lean_ctor_get(v_p_1000_, 0);
v_binderName_1009_ = lean_ctor_get(v_p_1000_, 1);
v_type_1010_ = lean_ctor_get(v_p_1000_, 2);
v_borrow_1011_ = lean_ctor_get_uint8(v_p_1000_, sizeof(void*)*3);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_p_1000_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1013_ = v_p_1000_;
v_isShared_1014_ = v_isSharedCheck_1059_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_type_1010_);
lean_inc(v_binderName_1009_);
lean_inc(v_fvarId_1008_);
lean_dec(v_p_1000_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1059_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v_a_1016_; lean_object* v___x_1017_; 
v___x_1015_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_1009_, v_a_1001_, v_a_1004_);
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref(v___x_1015_);
v___x_1017_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_999_, v_type_1010_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1019_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1017_, 1);
v___x_1019_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_1008_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1042_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1042_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1042_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 2, v_a_1018_);
lean_ctor_set(v___x_1013_, 1, v_a_1016_);
lean_ctor_set(v___x_1013_, 0, v_a_1020_);
v___x_1025_ = v___x_1013_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1020_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_a_1016_);
lean_ctor_set(v_reuseFailAlloc_1041_, 2, v_a_1018_);
lean_ctor_set_uint8(v_reuseFailAlloc_1041_, sizeof(void*)*3, v_borrow_1011_);
v___x_1025_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; lean_object* v_lctx_1027_; lean_object* v_nextIdx_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1040_; 
v___x_1026_ = lean_st_ref_take(v_a_1004_);
v_lctx_1027_ = lean_ctor_get(v___x_1026_, 0);
v_nextIdx_1028_ = lean_ctor_get(v___x_1026_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1030_ = v___x_1026_;
v_isShared_1031_ = v_isSharedCheck_1040_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_nextIdx_1028_);
lean_inc(v_lctx_1027_);
lean_dec(v___x_1026_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1040_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; lean_object* v___x_1034_; 
lean_inc_ref(v___x_1025_);
v___x_1032_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_999_, v_lctx_1027_, v___x_1025_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1032_);
v___x_1034_ = v___x_1030_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_nextIdx_1028_);
v___x_1034_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1035_ = lean_st_ref_put(v_a_1004_, v___x_1034_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1025_);
v___x_1037_ = v___x_1022_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1025_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec(v_a_1018_);
lean_dec(v_a_1016_);
lean_del_object(v___x_1013_);
v_a_1043_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1019_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1019_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec(v_a_1016_);
lean_del_object(v___x_1013_);
lean_dec(v_fvarId_1008_);
v_a_1051_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1017_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1017_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(lean_object* v_pu_1060_, lean_object* v_p_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
uint8_t v_pu_boxed_1069_; uint8_t v_a_boxed_1070_; lean_object* v_res_1071_; 
v_pu_boxed_1069_ = lean_unbox(v_pu_1060_);
v_a_boxed_1070_ = lean_unbox(v_a_1062_);
v_res_1071_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_boxed_1069_, v_p_1061_, v_a_boxed_1070_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_a_1063_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg(uint8_t v_pu_1072_, lean_object* v_arg_1073_, uint8_t v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
switch(lean_obj_tag(v_arg_1073_))
{
case 0:
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_arg_1073_);
return v___x_1081_;
}
case 1:
{
lean_object* v_fvarId_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_fvarId_1082_ = lean_ctor_get(v_arg_1073_, 0);
v___x_1083_ = lean_st_ref_get(v_a_1075_);
v___x_1084_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v___x_1083_, v_fvarId_1082_);
lean_dec(v___x_1083_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v_arg_1073_);
return v___x_1085_;
}
else
{
lean_object* v_val_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1116_; 
lean_dec_ref_known(v_arg_1073_, 1);
v_val_1086_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1088_ = v___x_1084_;
v_isShared_1089_ = v_isSharedCheck_1116_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_val_1086_);
lean_dec(v___x_1084_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1116_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
switch(lean_obj_tag(v_val_1086_))
{
case 0:
{
lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1090_ = lean_box(0);
if (v_isShared_1089_ == 0)
{
lean_ctor_set_tag(v___x_1088_, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1090_);
v___x_1092_ = v___x_1088_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
case 1:
{
lean_object* v_fvarId_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1104_; 
v_fvarId_1094_ = lean_ctor_get(v_val_1086_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_val_1086_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1096_ = v_val_1086_;
v_isShared_1097_ = v_isSharedCheck_1104_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_fvarId_1094_);
lean_dec(v_val_1086_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1104_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_fvarId_1094_);
v___x_1099_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1101_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set_tag(v___x_1088_, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1099_);
v___x_1101_ = v___x_1088_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
default: 
{
lean_object* v_expr_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1115_; 
v_expr_1105_ = lean_ctor_get(v_val_1086_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_val_1086_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1107_ = v_val_1086_;
v_isShared_1108_ = v_isSharedCheck_1115_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_expr_1105_);
lean_dec(v_val_1086_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1115_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_expr_1105_);
v___x_1110_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1112_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set_tag(v___x_1088_, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1110_);
v___x_1112_ = v___x_1088_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
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
lean_object* v_expr_1117_; lean_object* v___x_1118_; 
v_expr_1117_ = lean_ctor_get(v_arg_1073_, 0);
lean_inc_ref(v_expr_1117_);
v___x_1118_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1072_, v_expr_1117_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1127_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1125_; 
v___x_1123_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1072_, v_arg_1073_, v_a_1119_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1123_);
v___x_1125_ = v___x_1121_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec_ref_known(v_arg_1073_, 1);
v_a_1128_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1118_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1118_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg___boxed(lean_object* v_pu_1136_, lean_object* v_arg_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
uint8_t v_pu_boxed_1145_; uint8_t v_a_boxed_1146_; lean_object* v_res_1147_; 
v_pu_boxed_1145_ = lean_unbox(v_pu_1136_);
v_a_boxed_1146_ = lean_unbox(v_a_1138_);
v_res_1147_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_boxed_1145_, v_arg_1137_, v_a_boxed_1146_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(uint8_t v_pu_1148_, size_t v_sz_1149_, size_t v_i_1150_, lean_object* v_bs_1151_, uint8_t v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
uint8_t v___x_1159_; 
v___x_1159_ = lean_usize_dec_lt(v_i_1150_, v_sz_1149_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v_bs_1151_);
return v___x_1160_;
}
else
{
lean_object* v_v_1161_; lean_object* v___x_1162_; lean_object* v_bs_x27_1163_; lean_object* v___x_1164_; 
v_v_1161_ = lean_array_uget(v_bs_1151_, v_i_1150_);
v___x_1162_ = lean_unsigned_to_nat(0u);
v_bs_x27_1163_ = lean_array_uset(v_bs_1151_, v_i_1150_, v___x_1162_);
v___x_1164_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_1148_, v_v_1161_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; size_t v___x_1166_; size_t v___x_1167_; lean_object* v___x_1168_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref_known(v___x_1164_, 1);
v___x_1166_ = ((size_t)1ULL);
v___x_1167_ = lean_usize_add(v_i_1150_, v___x_1166_);
v___x_1168_ = lean_array_uset(v_bs_x27_1163_, v_i_1150_, v_a_1165_);
v_i_1150_ = v___x_1167_;
v_bs_1151_ = v___x_1168_;
goto _start;
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec_ref(v_bs_x27_1163_);
v_a_1170_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1164_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1164_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0___boxed(lean_object* v_pu_1178_, lean_object* v_sz_1179_, lean_object* v_i_1180_, lean_object* v_bs_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
uint8_t v_pu_boxed_1189_; size_t v_sz_boxed_1190_; size_t v_i_boxed_1191_; uint8_t v___y_339__boxed_1192_; lean_object* v_res_1193_; 
v_pu_boxed_1189_ = lean_unbox(v_pu_1178_);
v_sz_boxed_1190_ = lean_unbox_usize(v_sz_1179_);
lean_dec(v_sz_1179_);
v_i_boxed_1191_ = lean_unbox_usize(v_i_1180_);
lean_dec(v_i_1180_);
v___y_339__boxed_1192_ = lean_unbox(v___y_1182_);
v_res_1193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_boxed_1189_, v_sz_boxed_1190_, v_i_boxed_1191_, v_bs_1181_, v___y_339__boxed_1192_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs(uint8_t v_pu_1194_, lean_object* v_args_1195_, uint8_t v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
size_t v_sz_1203_; size_t v___x_1204_; lean_object* v___x_1205_; 
v_sz_1203_ = lean_array_size(v_args_1195_);
v___x_1204_ = ((size_t)0ULL);
v___x_1205_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_1194_, v_sz_1203_, v___x_1204_, v_args_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs___boxed(lean_object* v_pu_1206_, lean_object* v_args_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
uint8_t v_pu_boxed_1215_; uint8_t v_a_boxed_1216_; lean_object* v_res_1217_; 
v_pu_boxed_1215_ = lean_unbox(v_pu_1206_);
v_a_boxed_1216_ = lean_unbox(v_a_1208_);
v_res_1217_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_boxed_1215_, v_args_1207_, v_a_boxed_1216_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(uint8_t v_pu_1218_, lean_object* v_e_1219_, uint8_t v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_){
_start:
{
lean_object* v_fvarId_1228_; lean_object* v___y_1229_; lean_object* v_args_1245_; uint8_t v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; 
switch(lean_obj_tag(v_e_1219_))
{
case 2:
{
lean_object* v_struct_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v_struct_1270_ = lean_ctor_get(v_e_1219_, 2);
v___x_1271_ = 1;
v___x_1272_ = lean_st_ref_get(v_a_1221_);
lean_inc(v_struct_1270_);
v___x_1273_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1272_, v_struct_1270_, v___x_1271_);
lean_dec(v___x_1272_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_fvarId_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1282_; 
v_fvarId_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1282_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_fvarId_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1282_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1278_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1218_, v_e_1219_, v_fvarId_1274_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1278_);
v___x_1280_ = v___x_1276_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
else
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
lean_dec_ref_known(v_e_1219_, 3);
v___x_1283_ = lean_box(1);
v___x_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
return v___x_1284_;
}
}
case 3:
{
lean_object* v_args_1285_; lean_object* v___x_1286_; 
v_args_1285_ = lean_ctor_get(v_e_1219_, 2);
lean_inc_ref(v_args_1285_);
v___x_1286_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1218_, v_args_1285_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1295_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1295_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1295_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1291_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1219_, v_a_1287_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1291_);
v___x_1293_ = v___x_1289_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref_known(v_e_1219_, 3);
v_a_1296_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1286_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1286_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
case 4:
{
lean_object* v_fvarId_1304_; lean_object* v_args_1305_; uint8_t v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v_fvarId_1304_ = lean_ctor_get(v_e_1219_, 0);
v_args_1305_ = lean_ctor_get(v_e_1219_, 1);
v___x_1306_ = 1;
v___x_1307_ = lean_st_ref_get(v_a_1221_);
lean_inc(v_fvarId_1304_);
v___x_1308_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1307_, v_fvarId_1304_, v___x_1306_);
lean_dec(v___x_1307_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_fvarId_1309_; lean_object* v___x_1310_; 
v_fvarId_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_fvarId_1309_);
lean_dec_ref_known(v___x_1308_, 1);
lean_inc_ref(v_args_1305_);
v___x_1310_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1218_, v_args_1305_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1319_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1319_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1319_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1315_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___redArg(v_e_1219_, v_fvarId_1309_, v_a_1311_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1315_);
v___x_1317_ = v___x_1313_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec(v_fvarId_1309_);
lean_dec_ref_known(v_e_1219_, 2);
v_a_1320_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1310_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1310_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_dec_ref_known(v_e_1219_, 2);
v___x_1328_ = lean_box(1);
v___x_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
return v___x_1329_;
}
}
case 5:
{
lean_object* v_args_1330_; lean_object* v___x_1331_; 
v_args_1330_ = lean_ctor_get(v_e_1219_, 1);
lean_inc_ref(v_args_1330_);
v___x_1331_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1218_, v_args_1330_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1340_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1340_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1340_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1336_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1219_, v_a_1332_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1336_);
v___x_1338_ = v___x_1334_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref_known(v_e_1219_, 2);
v_a_1341_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1331_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1331_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
case 6:
{
lean_object* v_var_1349_; 
v_var_1349_ = lean_ctor_get(v_e_1219_, 1);
lean_inc(v_var_1349_);
v_fvarId_1228_ = v_var_1349_;
v___y_1229_ = v_a_1221_;
goto v___jp_1227_;
}
case 7:
{
lean_object* v_var_1350_; 
v_var_1350_ = lean_ctor_get(v_e_1219_, 1);
lean_inc(v_var_1350_);
v_fvarId_1228_ = v_var_1350_;
v___y_1229_ = v_a_1221_;
goto v___jp_1227_;
}
case 8:
{
lean_object* v_var_1351_; uint8_t v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v_var_1351_ = lean_ctor_get(v_e_1219_, 2);
v___x_1352_ = 1;
v___x_1353_ = lean_st_ref_get(v_a_1221_);
lean_inc(v_var_1351_);
v___x_1354_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1353_, v_var_1351_, v___x_1352_);
lean_dec(v___x_1353_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_fvarId_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1363_; 
v_fvarId_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1363_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_fvarId_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1363_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1359_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1218_, v_e_1219_, v_fvarId_1355_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1359_);
v___x_1361_ = v___x_1357_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_dec_ref_known(v_e_1219_, 3);
v___x_1364_ = lean_box(1);
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
return v___x_1365_;
}
}
case 9:
{
lean_object* v_args_1366_; 
v_args_1366_ = lean_ctor_get(v_e_1219_, 1);
lean_inc_ref(v_args_1366_);
v_args_1245_ = v_args_1366_;
v___y_1246_ = v_a_1220_;
v___y_1247_ = v_a_1221_;
v___y_1248_ = v_a_1222_;
v___y_1249_ = v_a_1223_;
v___y_1250_ = v_a_1224_;
v___y_1251_ = v_a_1225_;
goto v___jp_1244_;
}
case 10:
{
lean_object* v_args_1367_; 
v_args_1367_ = lean_ctor_get(v_e_1219_, 1);
lean_inc_ref(v_args_1367_);
v_args_1245_ = v_args_1367_;
v___y_1246_ = v_a_1220_;
v___y_1247_ = v_a_1221_;
v___y_1248_ = v_a_1222_;
v___y_1249_ = v_a_1223_;
v___y_1250_ = v_a_1224_;
v___y_1251_ = v_a_1225_;
goto v___jp_1244_;
}
case 11:
{
lean_object* v_n_1368_; lean_object* v_var_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v_n_1368_ = lean_ctor_get(v_e_1219_, 0);
lean_inc(v_n_1368_);
v_var_1369_ = lean_ctor_get(v_e_1219_, 1);
v___x_1370_ = 1;
v___x_1371_ = lean_st_ref_get(v_a_1221_);
lean_inc(v_var_1369_);
v___x_1372_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1371_, v_var_1369_, v___x_1370_);
lean_dec(v___x_1371_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_fvarId_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1381_; 
v_fvarId_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1381_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_fvarId_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1381_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1377_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp___redArg(v_e_1219_, v_n_1368_, v_fvarId_1373_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1377_);
v___x_1379_ = v___x_1375_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec_ref_known(v_e_1219_, 2);
lean_dec(v_n_1368_);
v___x_1382_ = lean_box(1);
v___x_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
return v___x_1383_;
}
}
case 12:
{
lean_object* v_var_1384_; lean_object* v_i_1385_; uint8_t v_updateHeader_1386_; lean_object* v_args_1387_; uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v_var_1384_ = lean_ctor_get(v_e_1219_, 0);
v_i_1385_ = lean_ctor_get(v_e_1219_, 1);
lean_inc_ref(v_i_1385_);
v_updateHeader_1386_ = lean_ctor_get_uint8(v_e_1219_, sizeof(void*)*3);
v_args_1387_ = lean_ctor_get(v_e_1219_, 2);
v___x_1388_ = 1;
v___x_1389_ = lean_st_ref_get(v_a_1221_);
lean_inc(v_var_1384_);
v___x_1390_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1389_, v_var_1384_, v___x_1388_);
lean_dec(v___x_1389_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_fvarId_1391_; lean_object* v___x_1392_; 
v_fvarId_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_fvarId_1391_);
lean_dec_ref_known(v___x_1390_, 1);
lean_inc_ref(v_args_1387_);
v___x_1392_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1218_, v_args_1387_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1401_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1395_ = v___x_1392_;
v_isShared_1396_ = v_isSharedCheck_1401_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1392_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1401_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1397_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp___redArg(v_e_1219_, v_fvarId_1391_, v_i_1385_, v_updateHeader_1386_, v_a_1393_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1397_);
v___x_1399_ = v___x_1395_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_dec(v_fvarId_1391_);
lean_dec_ref(v_i_1385_);
lean_dec_ref_known(v_e_1219_, 3);
v_a_1402_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1392_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1392_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
else
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
lean_dec_ref(v_i_1385_);
lean_dec_ref_known(v_e_1219_, 3);
v___x_1410_ = lean_box(1);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
return v___x_1411_;
}
}
case 13:
{
lean_object* v_ty_1412_; lean_object* v_fvarId_1413_; uint8_t v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v_ty_1412_ = lean_ctor_get(v_e_1219_, 0);
lean_inc_ref(v_ty_1412_);
v_fvarId_1413_ = lean_ctor_get(v_e_1219_, 1);
v___x_1414_ = 1;
v___x_1415_ = lean_st_ref_get(v_a_1221_);
lean_inc(v_fvarId_1413_);
v___x_1416_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1415_, v_fvarId_1413_, v___x_1414_);
lean_dec(v___x_1415_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_fvarId_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1425_; 
v_fvarId_1417_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1425_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_fvarId_1417_);
lean_dec(v___x_1416_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1425_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1421_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp___redArg(v_e_1219_, v_ty_1412_, v_fvarId_1417_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1421_);
v___x_1423_ = v___x_1419_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec_ref_known(v_e_1219_, 2);
lean_dec_ref(v_ty_1412_);
v___x_1426_ = lean_box(1);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
}
case 14:
{
lean_object* v_fvarId_1428_; uint8_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v_fvarId_1428_ = lean_ctor_get(v_e_1219_, 0);
v___x_1429_ = 1;
v___x_1430_ = lean_st_ref_get(v_a_1221_);
lean_inc(v_fvarId_1428_);
v___x_1431_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1430_, v_fvarId_1428_, v___x_1429_);
lean_dec(v___x_1430_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_fvarId_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1440_; 
v_fvarId_1432_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1434_ = v___x_1431_;
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_fvarId_1432_);
lean_dec(v___x_1431_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp___redArg(v_e_1219_, v_fvarId_1432_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1436_);
v___x_1438_ = v___x_1434_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
else
{
lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1448_; 
v_isSharedCheck_1448_ = !lean_is_exclusive(v_e_1219_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; 
v_unused_1449_ = lean_ctor_get(v_e_1219_, 0);
lean_dec(v_unused_1449_);
v___x_1442_ = v_e_1219_;
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
else
{
lean_dec(v_e_1219_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = lean_box(1);
if (v_isShared_1443_ == 0)
{
lean_ctor_set_tag(v___x_1442_, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1444_);
v___x_1446_ = v___x_1442_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
case 15:
{
lean_object* v_fvarId_1450_; uint8_t v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v_fvarId_1450_ = lean_ctor_get(v_e_1219_, 0);
v___x_1451_ = 1;
v___x_1452_ = lean_st_ref_get(v_a_1221_);
lean_inc(v_fvarId_1450_);
v___x_1453_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1452_, v_fvarId_1450_, v___x_1451_);
lean_dec(v___x_1452_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_fvarId_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1462_; 
v_fvarId_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1462_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_fvarId_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1462_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1458_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp___redArg(v_e_1219_, v_fvarId_1454_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1458_);
v___x_1460_ = v___x_1456_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
else
{
lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1470_; 
v_isSharedCheck_1470_ = !lean_is_exclusive(v_e_1219_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v_e_1219_, 0);
lean_dec(v_unused_1471_);
v___x_1464_ = v_e_1219_;
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
else
{
lean_dec(v_e_1219_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1466_ = lean_box(1);
if (v_isShared_1465_ == 0)
{
lean_ctor_set_tag(v___x_1464_, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1466_);
v___x_1468_ = v___x_1464_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
default: 
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v_e_1219_);
return v___x_1472_;
}
}
v___jp_1227_:
{
uint8_t v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1230_ = 1;
v___x_1231_ = lean_st_ref_get(v___y_1229_);
v___x_1232_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1231_, v_fvarId_1228_, v___x_1230_);
lean_dec(v___x_1231_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_fvarId_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1241_; 
v_fvarId_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1241_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_fvarId_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1241_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1237_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1218_, v_e_1219_, v_fvarId_1233_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1237_);
v___x_1239_ = v___x_1235_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec(v_e_1219_);
v___x_1242_ = lean_box(1);
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
return v___x_1243_;
}
}
v___jp_1244_:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1218_, v_args_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1261_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1255_ = v___x_1252_;
v_isShared_1256_ = v_isSharedCheck_1261_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1261_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1257_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1219_, v_a_1253_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1257_);
v___x_1259_ = v___x_1255_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v_e_1219_);
v_a_1262_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1252_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1252_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue___boxed(lean_object* v_pu_1473_, lean_object* v_e_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
uint8_t v_pu_boxed_1482_; uint8_t v_a_boxed_1483_; lean_object* v_res_1484_; 
v_pu_boxed_1482_ = lean_unbox(v_pu_1473_);
v_a_boxed_1483_ = lean_unbox(v_a_1475_);
v_res_1484_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_boxed_1482_, v_e_1474_, v_a_boxed_1483_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
lean_dec(v_a_1476_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(uint8_t v_pu_1485_, lean_object* v_decl_1486_, uint8_t v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_){
_start:
{
lean_object* v_fvarId_1494_; lean_object* v_binderName_1495_; lean_object* v_type_1496_; lean_object* v_value_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1555_; 
v_fvarId_1494_ = lean_ctor_get(v_decl_1486_, 0);
v_binderName_1495_ = lean_ctor_get(v_decl_1486_, 1);
v_type_1496_ = lean_ctor_get(v_decl_1486_, 2);
v_value_1497_ = lean_ctor_get(v_decl_1486_, 3);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_decl_1486_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1499_ = v_decl_1486_;
v_isShared_1500_ = v_isSharedCheck_1555_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_value_1497_);
lean_inc(v_type_1496_);
lean_inc(v_binderName_1495_);
lean_inc(v_fvarId_1494_);
lean_dec(v_decl_1486_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1555_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v_a_1502_; lean_object* v___x_1503_; 
v___x_1501_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_1495_, v_a_1487_, v_a_1490_);
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_a_1502_);
lean_dec_ref(v___x_1501_);
v___x_1503_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1485_, v_type_1496_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1505_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___x_1503_, 1);
v___x_1505_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_1485_, v_value_1497_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1507_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref_known(v___x_1505_, 1);
v___x_1507_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_1494_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1530_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1510_ = v___x_1507_;
v_isShared_1511_ = v_isSharedCheck_1530_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1507_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1530_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 3, v_a_1506_);
lean_ctor_set(v___x_1499_, 2, v_a_1504_);
lean_ctor_set(v___x_1499_, 1, v_a_1502_);
lean_ctor_set(v___x_1499_, 0, v_a_1508_);
v___x_1513_ = v___x_1499_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1508_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_a_1502_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_a_1504_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v_a_1506_);
v___x_1513_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1514_; lean_object* v_lctx_1515_; lean_object* v_nextIdx_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1528_; 
v___x_1514_ = lean_st_ref_take(v_a_1490_);
v_lctx_1515_ = lean_ctor_get(v___x_1514_, 0);
v_nextIdx_1516_ = lean_ctor_get(v___x_1514_, 1);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1518_ = v___x_1514_;
v_isShared_1519_ = v_isSharedCheck_1528_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_nextIdx_1516_);
lean_inc(v_lctx_1515_);
lean_dec(v___x_1514_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1528_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
lean_inc_ref(v___x_1513_);
v___x_1520_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_1485_, v_lctx_1515_, v___x_1513_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v___x_1520_);
v___x_1522_ = v___x_1518_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1520_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_nextIdx_1516_);
v___x_1522_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1523_ = lean_st_ref_put(v_a_1490_, v___x_1522_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v___x_1513_);
v___x_1525_ = v___x_1510_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1513_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec(v_a_1506_);
lean_dec(v_a_1504_);
lean_dec(v_a_1502_);
lean_del_object(v___x_1499_);
v_a_1531_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1507_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1507_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_dec(v_a_1504_);
lean_dec(v_a_1502_);
lean_del_object(v___x_1499_);
lean_dec(v_fvarId_1494_);
v_a_1539_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1505_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1505_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec(v_a_1502_);
lean_del_object(v___x_1499_);
lean_dec(v_value_1497_);
lean_dec(v_fvarId_1494_);
v_a_1547_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1503_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1503_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(lean_object* v_pu_1556_, lean_object* v_decl_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
uint8_t v_pu_boxed_1565_; uint8_t v_a_boxed_1566_; lean_object* v_res_1567_; 
v_pu_boxed_1565_ = lean_unbox(v_pu_1556_);
v_a_boxed_1566_ = lean_unbox(v_a_1558_);
v_res_1567_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_boxed_1565_, v_decl_1557_, v_a_boxed_1566_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
lean_dec(v_a_1559_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(uint8_t v_pu_1568_, size_t v_sz_1569_, size_t v_i_1570_, lean_object* v_bs_1571_, uint8_t v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
uint8_t v___x_1579_; 
v___x_1579_ = lean_usize_dec_lt(v_i_1570_, v_sz_1569_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1580_, 0, v_bs_1571_);
return v___x_1580_;
}
else
{
lean_object* v_v_1581_; lean_object* v___x_1582_; lean_object* v_bs_x27_1583_; lean_object* v___x_1584_; 
v_v_1581_ = lean_array_uget(v_bs_1571_, v_i_1570_);
v___x_1582_ = lean_unsigned_to_nat(0u);
v_bs_x27_1583_ = lean_array_uset(v_bs_1571_, v_i_1570_, v___x_1582_);
v___x_1584_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_1568_, v_v_1581_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; size_t v___x_1586_; size_t v___x_1587_; lean_object* v___x_1588_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = ((size_t)1ULL);
v___x_1587_ = lean_usize_add(v_i_1570_, v___x_1586_);
v___x_1588_ = lean_array_uset(v_bs_x27_1583_, v_i_1570_, v_a_1585_);
v_i_1570_ = v___x_1587_;
v_bs_1571_ = v___x_1588_;
goto _start;
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec_ref(v_bs_x27_1583_);
v_a_1590_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1584_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1584_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0___boxed(lean_object* v_pu_1598_, lean_object* v_sz_1599_, lean_object* v_i_1600_, lean_object* v_bs_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
uint8_t v_pu_boxed_1609_; size_t v_sz_boxed_1610_; size_t v_i_boxed_1611_; uint8_t v___y_26361__boxed_1612_; lean_object* v_res_1613_; 
v_pu_boxed_1609_ = lean_unbox(v_pu_1598_);
v_sz_boxed_1610_ = lean_unbox_usize(v_sz_1599_);
lean_dec(v_sz_1599_);
v_i_boxed_1611_ = lean_unbox_usize(v_i_1600_);
lean_dec(v_i_1600_);
v___y_26361__boxed_1612_ = lean_unbox(v___y_1602_);
v_res_1613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_boxed_1609_, v_sz_boxed_1610_, v_i_boxed_1611_, v_bs_1601_, v___y_26361__boxed_1612_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(uint8_t v_pu_1614_, size_t v_sz_1615_, size_t v_i_1616_, lean_object* v_bs_1617_, uint8_t v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
uint8_t v___x_1625_; 
v___x_1625_ = lean_usize_dec_lt(v_i_1616_, v_sz_1615_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1626_, 0, v_bs_1617_);
return v___x_1626_;
}
else
{
lean_object* v_v_1627_; lean_object* v___x_1628_; lean_object* v_bs_x27_1629_; lean_object* v_a_1631_; 
v_v_1627_ = lean_array_uget(v_bs_1617_, v_i_1616_);
v___x_1628_ = lean_unsigned_to_nat(0u);
v_bs_x27_1629_ = lean_array_uset(v_bs_1617_, v_i_1616_, v___x_1628_);
switch(lean_obj_tag(v_v_1627_))
{
case 0:
{
lean_object* v_ctorName_1636_; lean_object* v_params_1637_; lean_object* v_code_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1659_; 
v_ctorName_1636_ = lean_ctor_get(v_v_1627_, 0);
v_params_1637_ = lean_ctor_get(v_v_1627_, 1);
v_code_1638_ = lean_ctor_get(v_v_1627_, 2);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_v_1627_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1640_ = v_v_1627_;
v_isShared_1641_ = v_isSharedCheck_1659_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_code_1638_);
lean_inc(v_params_1637_);
lean_inc(v_ctorName_1636_);
lean_dec(v_v_1627_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1659_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
size_t v_sz_1642_; size_t v___x_1643_; lean_object* v___x_1644_; 
v_sz_1642_ = lean_array_size(v_params_1637_);
v___x_1643_ = ((size_t)0ULL);
v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_1614_, v_sz_1642_, v___x_1643_, v_params_1637_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1646_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v___x_1644_, 1);
v___x_1646_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1614_, v_code_1638_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1647_);
lean_dec_ref_known(v___x_1646_, 1);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 2, v_a_1647_);
lean_ctor_set(v___x_1640_, 1, v_a_1645_);
v___x_1649_ = v___x_1640_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_ctorName_1636_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_a_1645_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_a_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
v_a_1631_ = v___x_1649_;
goto v___jp_1630_;
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec(v_a_1645_);
lean_del_object(v___x_1640_);
lean_dec(v_ctorName_1636_);
lean_dec_ref(v_bs_x27_1629_);
v_a_1651_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1646_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1646_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
else
{
lean_del_object(v___x_1640_);
lean_dec_ref(v_code_1638_);
lean_dec(v_ctorName_1636_);
lean_dec_ref(v_bs_x27_1629_);
return v___x_1644_;
}
}
}
case 1:
{
lean_object* v_info_1660_; lean_object* v_code_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1678_; 
v_info_1660_ = lean_ctor_get(v_v_1627_, 0);
v_code_1661_ = lean_ctor_get(v_v_1627_, 1);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_v_1627_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1663_ = v_v_1627_;
v_isShared_1664_ = v_isSharedCheck_1678_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_code_1661_);
lean_inc(v_info_1660_);
lean_dec(v_v_1627_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1678_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1614_, v_code_1661_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1665_, 1);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 1, v_a_1666_);
v___x_1668_ = v___x_1663_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_info_1660_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_a_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
v_a_1631_ = v___x_1668_;
goto v___jp_1630_;
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_del_object(v___x_1663_);
lean_dec_ref(v_info_1660_);
lean_dec_ref(v_bs_x27_1629_);
v_a_1670_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1665_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1665_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
default: 
{
lean_object* v_code_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1696_; 
v_code_1679_ = lean_ctor_get(v_v_1627_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_v_1627_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1681_ = v_v_1627_;
v_isShared_1682_ = v_isSharedCheck_1696_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_code_1679_);
lean_dec(v_v_1627_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1696_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1614_, v_code_1679_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1686_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref_known(v___x_1683_, 1);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v_a_1684_);
v___x_1686_ = v___x_1681_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
v_a_1631_ = v___x_1686_;
goto v___jp_1630_;
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_del_object(v___x_1681_);
lean_dec_ref(v_bs_x27_1629_);
v_a_1688_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1683_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1683_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
}
v___jp_1630_:
{
size_t v___x_1632_; size_t v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = ((size_t)1ULL);
v___x_1633_ = lean_usize_add(v_i_1616_, v___x_1632_);
v___x_1634_ = lean_array_uset(v_bs_x27_1629_, v_i_1616_, v_a_1631_);
v_i_1616_ = v___x_1633_;
v_bs_1617_ = v___x_1634_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t v_pu_1697_, lean_object* v_code_1698_, uint8_t v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
switch(lean_obj_tag(v_code_1698_))
{
case 0:
{
lean_object* v_decl_1706_; lean_object* v_k_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1733_; 
v_decl_1706_ = lean_ctor_get(v_code_1698_, 0);
v_k_1707_ = lean_ctor_get(v_code_1698_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_code_1698_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1709_ = v_code_1698_;
v_isShared_1710_ = v_isSharedCheck_1733_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_k_1707_);
lean_inc(v_decl_1706_);
lean_dec(v_code_1698_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1733_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_1697_, v_decl_1706_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1713_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_a_1712_);
lean_dec_ref_known(v___x_1711_, 1);
v___x_1713_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1697_, v_k_1707_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1724_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1716_ = v___x_1713_;
v_isShared_1717_ = v_isSharedCheck_1724_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1724_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 1, v_a_1714_);
lean_ctor_set(v___x_1709_, 0, v_a_1712_);
v___x_1719_ = v___x_1709_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1712_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1721_; 
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v___x_1719_);
v___x_1721_ = v___x_1716_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
else
{
lean_dec(v_a_1712_);
lean_del_object(v___x_1709_);
return v___x_1713_;
}
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_del_object(v___x_1709_);
lean_dec_ref(v_k_1707_);
v_a_1725_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1711_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1711_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_1734_; lean_object* v_k_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1761_; 
v_decl_1734_ = lean_ctor_get(v_code_1698_, 0);
v_k_1735_ = lean_ctor_get(v_code_1698_, 1);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_code_1698_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1737_ = v_code_1698_;
v_isShared_1738_ = v_isSharedCheck_1761_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_k_1735_);
lean_inc(v_decl_1734_);
lean_dec(v_code_1698_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1761_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1697_, v_decl_1734_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1741_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v___x_1741_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1697_, v_k_1735_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1752_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1744_ = v___x_1741_;
v_isShared_1745_ = v_isSharedCheck_1752_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1741_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1752_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 1, v_a_1742_);
lean_ctor_set(v___x_1737_, 0, v_a_1740_);
v___x_1747_ = v___x_1737_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1740_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
lean_object* v___x_1749_; 
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1747_);
v___x_1749_ = v___x_1744_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
else
{
lean_dec(v_a_1740_);
lean_del_object(v___x_1737_);
return v___x_1741_;
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_del_object(v___x_1737_);
lean_dec_ref(v_k_1735_);
v_a_1753_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1739_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1739_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
case 2:
{
lean_object* v_decl_1762_; lean_object* v_k_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1789_; 
v_decl_1762_ = lean_ctor_get(v_code_1698_, 0);
v_k_1763_ = lean_ctor_get(v_code_1698_, 1);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_code_1698_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1765_ = v_code_1698_;
v_isShared_1766_ = v_isSharedCheck_1789_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_k_1763_);
lean_inc(v_decl_1762_);
lean_dec(v_code_1698_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1789_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1697_, v_decl_1762_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1769_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1768_);
lean_dec_ref_known(v___x_1767_, 1);
v___x_1769_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1697_, v_k_1763_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1780_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1780_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1780_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 1, v_a_1770_);
lean_ctor_set(v___x_1765_, 0, v_a_1768_);
v___x_1775_ = v___x_1765_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1768_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1777_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1775_);
v___x_1777_ = v___x_1772_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
else
{
lean_dec(v_a_1768_);
lean_del_object(v___x_1765_);
return v___x_1769_;
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_del_object(v___x_1765_);
lean_dec_ref(v_k_1763_);
v_a_1781_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1767_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1767_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_1790_; lean_object* v_args_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1820_; 
v_fvarId_1790_ = lean_ctor_get(v_code_1698_, 0);
v_args_1791_ = lean_ctor_get(v_code_1698_, 1);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_code_1698_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1793_ = v_code_1698_;
v_isShared_1794_ = v_isSharedCheck_1820_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_args_1791_);
lean_inc(v_fvarId_1790_);
lean_dec(v_code_1698_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1820_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
uint8_t v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1795_ = 1;
v___x_1796_ = lean_st_ref_get(v_a_1700_);
v___x_1797_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1796_, v_fvarId_1790_, v___x_1795_);
lean_dec(v___x_1796_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_fvarId_1798_; lean_object* v___x_1799_; 
v_fvarId_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_fvarId_1798_);
lean_dec_ref_known(v___x_1797_, 1);
v___x_1799_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1697_, v_args_1791_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1810_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1802_ = v___x_1799_;
v_isShared_1803_ = v_isSharedCheck_1810_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1799_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1810_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 1, v_a_1800_);
lean_ctor_set(v___x_1793_, 0, v_fvarId_1798_);
v___x_1805_ = v___x_1793_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_fvarId_1798_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1807_; 
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1805_);
v___x_1807_ = v___x_1802_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec(v_fvarId_1798_);
lean_del_object(v___x_1793_);
v_a_1811_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1799_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1799_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
else
{
lean_object* v___x_1819_; 
lean_del_object(v___x_1793_);
lean_dec_ref(v_args_1791_);
v___x_1819_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1697_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_1819_;
}
}
}
case 4:
{
lean_object* v_cases_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1873_; 
v_cases_1821_ = lean_ctor_get(v_code_1698_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_code_1698_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1823_ = v_code_1698_;
v_isShared_1824_ = v_isSharedCheck_1873_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_cases_1821_);
lean_dec(v_code_1698_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1873_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v_typeName_1825_; lean_object* v_resultType_1826_; lean_object* v_discr_1827_; lean_object* v_alts_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1872_; 
v_typeName_1825_ = lean_ctor_get(v_cases_1821_, 0);
v_resultType_1826_ = lean_ctor_get(v_cases_1821_, 1);
v_discr_1827_ = lean_ctor_get(v_cases_1821_, 2);
v_alts_1828_ = lean_ctor_get(v_cases_1821_, 3);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_cases_1821_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1830_ = v_cases_1821_;
v_isShared_1831_ = v_isSharedCheck_1872_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_alts_1828_);
lean_inc(v_discr_1827_);
lean_inc(v_resultType_1826_);
lean_inc(v_typeName_1825_);
lean_dec(v_cases_1821_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1872_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
uint8_t v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = 1;
v___x_1833_ = lean_st_ref_get(v_a_1700_);
v___x_1834_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1833_, v_discr_1827_, v___x_1832_);
lean_dec(v___x_1833_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_fvarId_1835_; lean_object* v___x_1836_; 
v_fvarId_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_fvarId_1835_);
lean_dec_ref_known(v___x_1834_, 1);
v___x_1836_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1697_, v_resultType_1826_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; size_t v_sz_1838_; size_t v___x_1839_; lean_object* v___x_1840_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref_known(v___x_1836_, 1);
v_sz_1838_ = lean_array_size(v_alts_1828_);
v___x_1839_ = ((size_t)0ULL);
v___x_1840_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_1697_, v_sz_1838_, v___x_1839_, v_alts_1828_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1854_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1854_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1854_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 3, v_a_1841_);
lean_ctor_set(v___x_1830_, 2, v_fvarId_1835_);
lean_ctor_set(v___x_1830_, 1, v_a_1837_);
v___x_1846_ = v___x_1830_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_typeName_1825_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_a_1837_);
lean_ctor_set(v_reuseFailAlloc_1853_, 2, v_fvarId_1835_);
lean_ctor_set(v_reuseFailAlloc_1853_, 3, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1848_; 
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1846_);
v___x_1848_ = v___x_1823_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1850_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1848_);
v___x_1850_ = v___x_1843_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec(v_a_1837_);
lean_dec(v_fvarId_1835_);
lean_del_object(v___x_1830_);
lean_dec(v_typeName_1825_);
lean_del_object(v___x_1823_);
v_a_1855_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1840_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1840_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec(v_fvarId_1835_);
lean_del_object(v___x_1830_);
lean_dec_ref(v_alts_1828_);
lean_dec(v_typeName_1825_);
lean_del_object(v___x_1823_);
v_a_1863_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1836_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1836_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
else
{
lean_object* v___x_1871_; 
lean_del_object(v___x_1830_);
lean_dec_ref(v_alts_1828_);
lean_dec_ref(v_resultType_1826_);
lean_dec(v_typeName_1825_);
lean_del_object(v___x_1823_);
v___x_1871_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1697_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_1871_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1893_; 
v_fvarId_1874_ = lean_ctor_get(v_code_1698_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_code_1698_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1876_ = v_code_1698_;
v_isShared_1877_ = v_isSharedCheck_1893_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_fvarId_1874_);
lean_dec(v_code_1698_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1893_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
uint8_t v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1878_ = 1;
v___x_1879_ = lean_st_ref_get(v_a_1700_);
v___x_1880_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1879_, v_fvarId_1874_, v___x_1878_);
lean_dec(v___x_1879_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_fvarId_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1891_; 
v_fvarId_1881_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1883_ = v___x_1880_;
v_isShared_1884_ = v_isSharedCheck_1891_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_fvarId_1881_);
lean_dec(v___x_1880_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1891_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v_fvarId_1881_);
v___x_1886_ = v___x_1876_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_fvarId_1881_);
v___x_1886_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1888_; 
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1886_);
v___x_1888_ = v___x_1883_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
else
{
lean_object* v___x_1892_; 
lean_del_object(v___x_1876_);
v___x_1892_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1697_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_1892_;
}
}
}
case 6:
{
lean_object* v_type_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1918_; 
v_type_1894_ = lean_ctor_get(v_code_1698_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v_code_1698_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1896_ = v_code_1698_;
v_isShared_1897_ = v_isSharedCheck_1918_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_type_1894_);
lean_dec(v_code_1698_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1918_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; 
v___x_1898_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1697_, v_type_1894_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1909_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1909_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1909_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v_a_1899_);
v___x_1904_ = v___x_1896_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1906_; 
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v___x_1904_);
v___x_1906_ = v___x_1901_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_del_object(v___x_1896_);
v_a_1910_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1898_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1898_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_1919_; lean_object* v_i_1920_; lean_object* v_y_1921_; lean_object* v_k_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1945_; 
v_fvarId_1919_ = lean_ctor_get(v_code_1698_, 0);
v_i_1920_ = lean_ctor_get(v_code_1698_, 1);
v_y_1921_ = lean_ctor_get(v_code_1698_, 2);
v_k_1922_ = lean_ctor_get(v_code_1698_, 3);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_code_1698_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1924_ = v_code_1698_;
v_isShared_1925_ = v_isSharedCheck_1945_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_k_1922_);
lean_inc(v_y_1921_);
lean_inc(v_i_1920_);
lean_inc(v_fvarId_1919_);
lean_dec(v_code_1698_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1945_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
uint8_t v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1926_ = 1;
v___x_1927_ = lean_st_ref_get(v_a_1700_);
v___x_1928_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1927_, v_fvarId_1919_, v___x_1926_);
lean_dec(v___x_1927_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_fvarId_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_fvarId_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_fvarId_1929_);
lean_dec_ref_known(v___x_1928_, 1);
v___x_1930_ = lean_st_ref_get(v_a_1700_);
v___x_1931_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1697_, v___x_1930_, v_y_1921_, v___x_1926_);
lean_dec(v___x_1930_);
v___x_1932_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1697_, v_k_1922_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1943_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1935_ = v___x_1932_;
v_isShared_1936_ = v_isSharedCheck_1943_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1932_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1943_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 3, v_a_1933_);
lean_ctor_set(v___x_1924_, 2, v___x_1931_);
lean_ctor_set(v___x_1924_, 0, v_fvarId_1929_);
v___x_1938_ = v___x_1924_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_fvarId_1929_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_i_1920_);
lean_ctor_set(v_reuseFailAlloc_1942_, 2, v___x_1931_);
lean_ctor_set(v_reuseFailAlloc_1942_, 3, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
lean_object* v___x_1940_; 
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v___x_1938_);
v___x_1940_ = v___x_1935_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1938_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
else
{
lean_dec(v___x_1931_);
lean_dec(v_fvarId_1929_);
lean_del_object(v___x_1924_);
lean_dec(v_i_1920_);
return v___x_1932_;
}
}
else
{
lean_object* v___x_1944_; 
lean_del_object(v___x_1924_);
lean_dec_ref(v_k_1922_);
lean_dec(v_y_1921_);
lean_dec(v_i_1920_);
v___x_1944_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1697_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_1944_;
}
}
}
case 8:
{
lean_object* v_fvarId_1946_; lean_object* v_i_1947_; lean_object* v_y_1948_; lean_object* v_k_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1974_; 
v_fvarId_1946_ = lean_ctor_get(v_code_1698_, 0);
v_i_1947_ = lean_ctor_get(v_code_1698_, 1);
v_y_1948_ = lean_ctor_get(v_code_1698_, 2);
v_k_1949_ = lean_ctor_get(v_code_1698_, 3);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_code_1698_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1951_ = v_code_1698_;
v_isShared_1952_ = v_isSharedCheck_1974_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_k_1949_);
lean_inc(v_y_1948_);
lean_inc(v_i_1947_);
lean_inc(v_fvarId_1946_);
lean_dec(v_code_1698_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1974_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
uint8_t v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1953_ = 1;
v___x_1954_ = lean_st_ref_get(v_a_1700_);
v___x_1955_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1954_, v_fvarId_1946_, v___x_1953_);
lean_dec(v___x_1954_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_fvarId_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v_fvarId_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_fvarId_1956_);
lean_dec_ref_known(v___x_1955_, 1);
v___x_1957_ = lean_st_ref_get(v_a_1700_);
v___x_1958_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1957_, v_y_1948_, v___x_1953_);
lean_dec(v___x_1957_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_fvarId_1959_; lean_object* v___x_1960_; 
v_fvarId_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_fvarId_1959_);
lean_dec_ref_known(v___x_1958_, 1);
v___x_1960_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1697_, v_k_1949_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1971_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_1971_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1971_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 3, v_a_1961_);
lean_ctor_set(v___x_1951_, 2, v_fvarId_1959_);
lean_ctor_set(v___x_1951_, 0, v_fvarId_1956_);
v___x_1966_ = v___x_1951_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_fvarId_1956_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_i_1947_);
lean_ctor_set(v_reuseFailAlloc_1970_, 2, v_fvarId_1959_);
lean_ctor_set(v_reuseFailAlloc_1970_, 3, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1968_; 
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1966_);
v___x_1968_ = v___x_1963_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1966_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
else
{
lean_dec(v_fvarId_1959_);
lean_dec(v_fvarId_1956_);
lean_del_object(v___x_1951_);
lean_dec(v_i_1947_);
return v___x_1960_;
}
}
else
{
lean_object* v___x_1972_; 
lean_dec(v_fvarId_1956_);
lean_del_object(v___x_1951_);
lean_dec_ref(v_k_1949_);
lean_dec(v_i_1947_);
v___x_1972_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1697_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_1972_;
}
}
else
{
lean_object* v___x_1973_; 
lean_del_object(v___x_1951_);
lean_dec_ref(v_k_1949_);
lean_dec(v_y_1948_);
lean_dec(v_i_1947_);
v___x_1973_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1697_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_1973_;
}
}
}
case 9:
{
lean_object* v_fvarId_1975_; lean_object* v_i_1976_; lean_object* v_offset_1977_; lean_object* v_y_1978_; lean_object* v_ty_1979_; lean_object* v_k_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2015_; 
v_fvarId_1975_ = lean_ctor_get(v_code_1698_, 0);
v_i_1976_ = lean_ctor_get(v_code_1698_, 1);
v_offset_1977_ = lean_ctor_get(v_code_1698_, 2);
v_y_1978_ = lean_ctor_get(v_code_1698_, 3);
v_ty_1979_ = lean_ctor_get(v_code_1698_, 4);
v_k_1980_ = lean_ctor_get(v_code_1698_, 5);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_code_1698_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_1982_ = v_code_1698_;
v_isShared_1983_ = v_isSharedCheck_2015_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_k_1980_);
lean_inc(v_ty_1979_);
lean_inc(v_y_1978_);
lean_inc(v_offset_1977_);
lean_inc(v_i_1976_);
lean_inc(v_fvarId_1975_);
lean_dec(v_code_1698_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2015_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
uint8_t v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1984_ = 1;
v___x_1985_ = lean_st_ref_get(v_a_1700_);
v___x_1986_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1985_, v_fvarId_1975_, v___x_1984_);
lean_dec(v___x_1985_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_fvarId_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v_fvarId_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_fvarId_1987_);
lean_dec_ref_known(v___x_1986_, 1);
v___x_1988_ = lean_st_ref_get(v_a_1700_);
v___x_1989_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1988_, v_y_1978_, v___x_1984_);
lean_dec(v___x_1988_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_fvarId_1990_; lean_object* v___x_1991_; 
v_fvarId_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_fvarId_1990_);
lean_dec_ref_known(v___x_1989_, 1);
v___x_1991_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1697_, v_ty_1979_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1993_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1991_, 1);
v___x_1993_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1697_, v_k_1980_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2004_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2004_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2004_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 5, v_a_1994_);
lean_ctor_set(v___x_1982_, 4, v_a_1992_);
lean_ctor_set(v___x_1982_, 3, v_fvarId_1990_);
lean_ctor_set(v___x_1982_, 0, v_fvarId_1987_);
v___x_1999_ = v___x_1982_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_fvarId_1987_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_i_1976_);
lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_offset_1977_);
lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_fvarId_1990_);
lean_ctor_set(v_reuseFailAlloc_2003_, 4, v_a_1992_);
lean_ctor_set(v_reuseFailAlloc_2003_, 5, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2001_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v___x_1999_);
v___x_2001_ = v___x_1996_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
else
{
lean_dec(v_a_1992_);
lean_dec(v_fvarId_1990_);
lean_dec(v_fvarId_1987_);
lean_del_object(v___x_1982_);
lean_dec(v_offset_1977_);
lean_dec(v_i_1976_);
return v___x_1993_;
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec(v_fvarId_1990_);
lean_dec(v_fvarId_1987_);
lean_del_object(v___x_1982_);
lean_dec_ref(v_k_1980_);
lean_dec(v_offset_1977_);
lean_dec(v_i_1976_);
v_a_2005_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1991_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1991_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
else
{
lean_object* v___x_2013_; 
lean_dec(v_fvarId_1987_);
lean_del_object(v___x_1982_);
lean_dec_ref(v_k_1980_);
lean_dec_ref(v_ty_1979_);
lean_dec(v_offset_1977_);
lean_dec(v_i_1976_);
v___x_2013_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1697_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_2013_;
}
}
else
{
lean_object* v___x_2014_; 
lean_del_object(v___x_1982_);
lean_dec_ref(v_k_1980_);
lean_dec_ref(v_ty_1979_);
lean_dec(v_y_1978_);
lean_dec(v_offset_1977_);
lean_dec(v_i_1976_);
v___x_2014_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1697_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_2014_;
}
}
}
case 10:
{
lean_object* v_fvarId_2016_; lean_object* v_cidx_2017_; lean_object* v_k_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2039_; 
v_fvarId_2016_ = lean_ctor_get(v_code_1698_, 0);
v_cidx_2017_ = lean_ctor_get(v_code_1698_, 1);
v_k_2018_ = lean_ctor_get(v_code_1698_, 2);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_code_1698_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2020_ = v_code_1698_;
v_isShared_2021_ = v_isSharedCheck_2039_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_k_2018_);
lean_inc(v_cidx_2017_);
lean_inc(v_fvarId_2016_);
lean_dec(v_code_1698_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2039_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
uint8_t v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2022_ = 1;
v___x_2023_ = lean_st_ref_get(v_a_1700_);
v___x_2024_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2023_, v_fvarId_2016_, v___x_2022_);
lean_dec(v___x_2023_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_fvarId_2025_; lean_object* v___x_2026_; 
v_fvarId_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_fvarId_2025_);
lean_dec_ref_known(v___x_2024_, 1);
v___x_2026_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1697_, v_k_2018_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2037_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2029_ = v___x_2026_;
v_isShared_2030_ = v_isSharedCheck_2037_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2026_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2037_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 2, v_a_2027_);
lean_ctor_set(v___x_2020_, 0, v_fvarId_2025_);
v___x_2032_ = v___x_2020_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_fvarId_2025_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_cidx_2017_);
lean_ctor_set(v_reuseFailAlloc_2036_, 2, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
lean_object* v___x_2034_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 0, v___x_2032_);
v___x_2034_ = v___x_2029_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
else
{
lean_dec(v_fvarId_2025_);
lean_del_object(v___x_2020_);
lean_dec(v_cidx_2017_);
return v___x_2026_;
}
}
else
{
lean_object* v___x_2038_; 
lean_del_object(v___x_2020_);
lean_dec_ref(v_k_2018_);
lean_dec(v_cidx_2017_);
v___x_2038_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1697_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_2038_;
}
}
}
case 11:
{
lean_object* v_fvarId_2040_; lean_object* v_n_2041_; uint8_t v_check_2042_; uint8_t v_persistent_2043_; lean_object* v_k_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2065_; 
v_fvarId_2040_ = lean_ctor_get(v_code_1698_, 0);
v_n_2041_ = lean_ctor_get(v_code_1698_, 1);
v_check_2042_ = lean_ctor_get_uint8(v_code_1698_, sizeof(void*)*3);
v_persistent_2043_ = lean_ctor_get_uint8(v_code_1698_, sizeof(void*)*3 + 1);
v_k_2044_ = lean_ctor_get(v_code_1698_, 2);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_code_1698_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2046_ = v_code_1698_;
v_isShared_2047_ = v_isSharedCheck_2065_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_k_2044_);
lean_inc(v_n_2041_);
lean_inc(v_fvarId_2040_);
lean_dec(v_code_1698_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2065_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
uint8_t v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2048_ = 1;
v___x_2049_ = lean_st_ref_get(v_a_1700_);
v___x_2050_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2049_, v_fvarId_2040_, v___x_2048_);
lean_dec(v___x_2049_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_fvarId_2051_; lean_object* v___x_2052_; 
v_fvarId_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_fvarId_2051_);
lean_dec_ref_known(v___x_2050_, 1);
v___x_2052_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1697_, v_k_2044_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2063_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2055_ = v___x_2052_;
v_isShared_2056_ = v_isSharedCheck_2063_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2052_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2063_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 2, v_a_2053_);
lean_ctor_set(v___x_2046_, 0, v_fvarId_2051_);
v___x_2058_ = v___x_2046_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_fvarId_2051_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_n_2041_);
lean_ctor_set(v_reuseFailAlloc_2062_, 2, v_a_2053_);
lean_ctor_set_uint8(v_reuseFailAlloc_2062_, sizeof(void*)*3, v_check_2042_);
lean_ctor_set_uint8(v_reuseFailAlloc_2062_, sizeof(void*)*3 + 1, v_persistent_2043_);
v___x_2058_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2060_; 
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v___x_2058_);
v___x_2060_ = v___x_2055_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
else
{
lean_dec(v_fvarId_2051_);
lean_del_object(v___x_2046_);
lean_dec(v_n_2041_);
return v___x_2052_;
}
}
else
{
lean_object* v___x_2064_; 
lean_del_object(v___x_2046_);
lean_dec_ref(v_k_2044_);
lean_dec(v_n_2041_);
v___x_2064_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1697_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_2064_;
}
}
}
case 12:
{
lean_object* v_fvarId_2066_; lean_object* v_n_2067_; uint8_t v_check_2068_; uint8_t v_persistent_2069_; lean_object* v_objs_x3f_2070_; lean_object* v_k_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2092_; 
v_fvarId_2066_ = lean_ctor_get(v_code_1698_, 0);
v_n_2067_ = lean_ctor_get(v_code_1698_, 1);
v_check_2068_ = lean_ctor_get_uint8(v_code_1698_, sizeof(void*)*4);
v_persistent_2069_ = lean_ctor_get_uint8(v_code_1698_, sizeof(void*)*4 + 1);
v_objs_x3f_2070_ = lean_ctor_get(v_code_1698_, 2);
v_k_2071_ = lean_ctor_get(v_code_1698_, 3);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_code_1698_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2073_ = v_code_1698_;
v_isShared_2074_ = v_isSharedCheck_2092_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_k_2071_);
lean_inc(v_objs_x3f_2070_);
lean_inc(v_n_2067_);
lean_inc(v_fvarId_2066_);
lean_dec(v_code_1698_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2092_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
uint8_t v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = 1;
v___x_2076_ = lean_st_ref_get(v_a_1700_);
v___x_2077_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2076_, v_fvarId_2066_, v___x_2075_);
lean_dec(v___x_2076_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_fvarId_2078_; lean_object* v___x_2079_; 
v_fvarId_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_fvarId_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v___x_2079_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1697_, v_k_2071_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2090_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2082_ = v___x_2079_;
v_isShared_2083_ = v_isSharedCheck_2090_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2079_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2090_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 3, v_a_2080_);
lean_ctor_set(v___x_2073_, 0, v_fvarId_2078_);
v___x_2085_ = v___x_2073_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_fvarId_2078_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_n_2067_);
lean_ctor_set(v_reuseFailAlloc_2089_, 2, v_objs_x3f_2070_);
lean_ctor_set(v_reuseFailAlloc_2089_, 3, v_a_2080_);
lean_ctor_set_uint8(v_reuseFailAlloc_2089_, sizeof(void*)*4, v_check_2068_);
lean_ctor_set_uint8(v_reuseFailAlloc_2089_, sizeof(void*)*4 + 1, v_persistent_2069_);
v___x_2085_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
lean_object* v___x_2087_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___x_2085_);
v___x_2087_ = v___x_2082_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
else
{
lean_dec(v_fvarId_2078_);
lean_del_object(v___x_2073_);
lean_dec(v_objs_x3f_2070_);
lean_dec(v_n_2067_);
return v___x_2079_;
}
}
else
{
lean_object* v___x_2091_; 
lean_del_object(v___x_2073_);
lean_dec_ref(v_k_2071_);
lean_dec(v_objs_x3f_2070_);
lean_dec(v_n_2067_);
v___x_2091_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1697_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_2091_;
}
}
}
default: 
{
lean_object* v_fvarId_2093_; lean_object* v_k_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2115_; 
v_fvarId_2093_ = lean_ctor_get(v_code_1698_, 0);
v_k_2094_ = lean_ctor_get(v_code_1698_, 1);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_code_1698_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2096_ = v_code_1698_;
v_isShared_2097_ = v_isSharedCheck_2115_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_k_2094_);
lean_inc(v_fvarId_2093_);
lean_dec(v_code_1698_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2115_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
uint8_t v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = 1;
v___x_2099_ = lean_st_ref_get(v_a_1700_);
v___x_2100_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2099_, v_fvarId_2093_, v___x_2098_);
lean_dec(v___x_2099_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_fvarId_2101_; lean_object* v___x_2102_; 
v_fvarId_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_fvarId_2101_);
lean_dec_ref_known(v___x_2100_, 1);
v___x_2102_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1697_, v_k_2094_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2113_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2105_ = v___x_2102_;
v_isShared_2106_ = v_isSharedCheck_2113_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2113_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 1, v_a_2103_);
lean_ctor_set(v___x_2096_, 0, v_fvarId_2101_);
v___x_2108_ = v___x_2096_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_fvarId_2101_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2110_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v___x_2108_);
v___x_2110_ = v___x_2105_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
else
{
lean_dec(v_fvarId_2101_);
lean_del_object(v___x_2096_);
return v___x_2102_;
}
}
else
{
lean_object* v___x_2114_; 
lean_del_object(v___x_2096_);
lean_dec_ref(v_k_2094_);
v___x_2114_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1697_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_2114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(uint8_t v_pu_2116_, lean_object* v_decl_2117_, uint8_t v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_){
_start:
{
lean_object* v_fvarId_2125_; lean_object* v_binderName_2126_; lean_object* v_params_2127_; lean_object* v_type_2128_; lean_object* v_value_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2207_; 
v_fvarId_2125_ = lean_ctor_get(v_decl_2117_, 0);
v_binderName_2126_ = lean_ctor_get(v_decl_2117_, 1);
v_params_2127_ = lean_ctor_get(v_decl_2117_, 2);
v_type_2128_ = lean_ctor_get(v_decl_2117_, 3);
v_value_2129_ = lean_ctor_get(v_decl_2117_, 4);
v_isSharedCheck_2207_ = !lean_is_exclusive(v_decl_2117_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2131_ = v_decl_2117_;
v_isShared_2132_ = v_isSharedCheck_2207_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_value_2129_);
lean_inc(v_type_2128_);
lean_inc(v_params_2127_);
lean_inc(v_binderName_2126_);
lean_inc(v_fvarId_2125_);
lean_dec(v_decl_2117_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2207_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; 
v___x_2133_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2116_, v_type_2128_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2135_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2133_, 1);
v___x_2135_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_2126_, v_a_2118_, v_a_2121_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; size_t v_sz_2137_; size_t v___x_2138_; lean_object* v___x_2139_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v_sz_2137_ = lean_array_size(v_params_2127_);
v___x_2138_ = ((size_t)0ULL);
v___x_2139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2116_, v_sz_2137_, v___x_2138_, v_params_2127_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2141_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2116_, v_value_2129_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2143_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
v___x_2143_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_2125_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2166_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2146_ = v___x_2143_;
v_isShared_2147_ = v_isSharedCheck_2166_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2166_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 4, v_a_2142_);
lean_ctor_set(v___x_2131_, 3, v_a_2134_);
lean_ctor_set(v___x_2131_, 2, v_a_2140_);
lean_ctor_set(v___x_2131_, 1, v_a_2136_);
lean_ctor_set(v___x_2131_, 0, v_a_2144_);
v___x_2149_ = v___x_2131_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2144_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_a_2136_);
lean_ctor_set(v_reuseFailAlloc_2165_, 2, v_a_2140_);
lean_ctor_set(v_reuseFailAlloc_2165_, 3, v_a_2134_);
lean_ctor_set(v_reuseFailAlloc_2165_, 4, v_a_2142_);
v___x_2149_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2150_; lean_object* v_lctx_2151_; lean_object* v_nextIdx_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2164_; 
v___x_2150_ = lean_st_ref_take(v_a_2121_);
v_lctx_2151_ = lean_ctor_get(v___x_2150_, 0);
v_nextIdx_2152_ = lean_ctor_get(v___x_2150_, 1);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2154_ = v___x_2150_;
v_isShared_2155_ = v_isSharedCheck_2164_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_nextIdx_2152_);
lean_inc(v_lctx_2151_);
lean_dec(v___x_2150_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2164_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
lean_inc_ref(v___x_2149_);
v___x_2156_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2116_, v_lctx_2151_, v___x_2149_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v___x_2156_);
v___x_2158_ = v___x_2154_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_nextIdx_2152_);
v___x_2158_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2159_ = lean_st_ref_put(v_a_2121_, v___x_2158_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2149_);
v___x_2161_ = v___x_2146_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2149_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v_a_2142_);
lean_dec(v_a_2140_);
lean_dec(v_a_2136_);
lean_dec(v_a_2134_);
lean_del_object(v___x_2131_);
v_a_2167_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2143_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2143_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_dec(v_a_2140_);
lean_dec(v_a_2136_);
lean_dec(v_a_2134_);
lean_del_object(v___x_2131_);
lean_dec(v_fvarId_2125_);
v_a_2175_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2141_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2141_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_dec(v_a_2136_);
lean_dec(v_a_2134_);
lean_del_object(v___x_2131_);
lean_dec_ref(v_value_2129_);
lean_dec(v_fvarId_2125_);
v_a_2183_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2139_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2139_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec(v_a_2134_);
lean_del_object(v___x_2131_);
lean_dec_ref(v_value_2129_);
lean_dec_ref(v_params_2127_);
lean_dec(v_fvarId_2125_);
v_a_2191_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2135_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2135_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_del_object(v___x_2131_);
lean_dec_ref(v_value_2129_);
lean_dec_ref(v_params_2127_);
lean_dec(v_binderName_2126_);
lean_dec(v_fvarId_2125_);
v_a_2199_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2133_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2133_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(lean_object* v_pu_2208_, lean_object* v_decl_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_){
_start:
{
uint8_t v_pu_boxed_2217_; uint8_t v_a_boxed_2218_; lean_object* v_res_2219_; 
v_pu_boxed_2217_ = lean_unbox(v_pu_2208_);
v_a_boxed_2218_ = lean_unbox(v_a_2210_);
v_res_2219_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_boxed_2217_, v_decl_2209_, v_a_boxed_2218_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
lean_dec(v_a_2215_);
lean_dec_ref(v_a_2214_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
lean_dec(v_a_2211_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2___boxed(lean_object* v_pu_2220_, lean_object* v_sz_2221_, lean_object* v_i_2222_, lean_object* v_bs_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
uint8_t v_pu_boxed_2231_; size_t v_sz_boxed_2232_; size_t v_i_boxed_2233_; uint8_t v___y_26449__boxed_2234_; lean_object* v_res_2235_; 
v_pu_boxed_2231_ = lean_unbox(v_pu_2220_);
v_sz_boxed_2232_ = lean_unbox_usize(v_sz_2221_);
lean_dec(v_sz_2221_);
v_i_boxed_2233_ = lean_unbox_usize(v_i_2222_);
lean_dec(v_i_2222_);
v___y_26449__boxed_2234_ = lean_unbox(v___y_2224_);
v_res_2235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_boxed_2231_, v_sz_boxed_2232_, v_i_boxed_2233_, v_bs_2223_, v___y_26449__boxed_2234_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(lean_object* v_pu_2236_, lean_object* v_code_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
uint8_t v_pu_boxed_2245_; uint8_t v_a_boxed_2246_; lean_object* v_res_2247_; 
v_pu_boxed_2245_ = lean_unbox(v_pu_2236_);
v_a_boxed_2246_ = lean_unbox(v_a_2238_);
v_res_2247_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_boxed_2245_, v_code_2237_, v_a_boxed_2246_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
lean_dec(v_a_2241_);
lean_dec_ref(v_a_2240_);
lean_dec(v_a_2239_);
return v_res_2247_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(lean_object* v_msg_2249_, uint8_t v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v_toApplicative_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2323_; 
v___x_2257_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
v___x_2258_ = l_StateRefT_x27_instMonad___redArg(v___x_2257_);
v_toApplicative_2259_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2323_ == 0)
{
lean_object* v_unused_2324_; 
v_unused_2324_ = lean_ctor_get(v___x_2258_, 1);
lean_dec(v_unused_2324_);
v___x_2261_ = v___x_2258_;
v_isShared_2262_ = v_isSharedCheck_2323_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_toApplicative_2259_);
lean_dec(v___x_2258_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2323_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v_toFunctor_2263_; lean_object* v_toSeq_2264_; lean_object* v_toSeqLeft_2265_; lean_object* v_toSeqRight_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2321_; 
v_toFunctor_2263_ = lean_ctor_get(v_toApplicative_2259_, 0);
v_toSeq_2264_ = lean_ctor_get(v_toApplicative_2259_, 2);
v_toSeqLeft_2265_ = lean_ctor_get(v_toApplicative_2259_, 3);
v_toSeqRight_2266_ = lean_ctor_get(v_toApplicative_2259_, 4);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_toApplicative_2259_);
if (v_isSharedCheck_2321_ == 0)
{
lean_object* v_unused_2322_; 
v_unused_2322_ = lean_ctor_get(v_toApplicative_2259_, 1);
lean_dec(v_unused_2322_);
v___x_2268_ = v_toApplicative_2259_;
v_isShared_2269_ = v_isSharedCheck_2321_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_toSeqRight_2266_);
lean_inc(v_toSeqLeft_2265_);
lean_inc(v_toSeq_2264_);
lean_inc(v_toFunctor_2263_);
lean_dec(v_toApplicative_2259_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2321_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___f_2270_; lean_object* v___f_2271_; lean_object* v___f_2272_; lean_object* v___f_2273_; lean_object* v___x_2274_; lean_object* v___f_2275_; lean_object* v___f_2276_; lean_object* v___f_2277_; lean_object* v___x_2279_; 
v___f_2270_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
v___f_2271_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_2263_);
v___f_2272_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2272_, 0, v_toFunctor_2263_);
v___f_2273_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2273_, 0, v_toFunctor_2263_);
v___x_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___f_2272_);
lean_ctor_set(v___x_2274_, 1, v___f_2273_);
v___f_2275_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2275_, 0, v_toSeqRight_2266_);
v___f_2276_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2276_, 0, v_toSeqLeft_2265_);
v___f_2277_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2277_, 0, v_toSeq_2264_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 4, v___f_2275_);
lean_ctor_set(v___x_2268_, 3, v___f_2276_);
lean_ctor_set(v___x_2268_, 2, v___f_2277_);
lean_ctor_set(v___x_2268_, 1, v___f_2270_);
lean_ctor_set(v___x_2268_, 0, v___x_2274_);
v___x_2279_ = v___x_2268_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2274_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v___f_2270_);
lean_ctor_set(v_reuseFailAlloc_2320_, 2, v___f_2277_);
lean_ctor_set(v_reuseFailAlloc_2320_, 3, v___f_2276_);
lean_ctor_set(v_reuseFailAlloc_2320_, 4, v___f_2275_);
v___x_2279_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
lean_object* v___x_2281_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 1, v___f_2271_);
lean_ctor_set(v___x_2261_, 0, v___x_2279_);
v___x_2281_ = v___x_2261_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2279_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v___f_2271_);
v___x_2281_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
lean_object* v___x_2282_; lean_object* v_toApplicative_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2317_; 
v___x_2282_ = l_StateRefT_x27_instMonad___redArg(v___x_2281_);
v_toApplicative_2283_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2317_ == 0)
{
lean_object* v_unused_2318_; 
v_unused_2318_ = lean_ctor_get(v___x_2282_, 1);
lean_dec(v_unused_2318_);
v___x_2285_ = v___x_2282_;
v_isShared_2286_ = v_isSharedCheck_2317_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_toApplicative_2283_);
lean_dec(v___x_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2317_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v_toFunctor_2287_; lean_object* v_toSeq_2288_; lean_object* v_toSeqLeft_2289_; lean_object* v_toSeqRight_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2315_; 
v_toFunctor_2287_ = lean_ctor_get(v_toApplicative_2283_, 0);
v_toSeq_2288_ = lean_ctor_get(v_toApplicative_2283_, 2);
v_toSeqLeft_2289_ = lean_ctor_get(v_toApplicative_2283_, 3);
v_toSeqRight_2290_ = lean_ctor_get(v_toApplicative_2283_, 4);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_toApplicative_2283_);
if (v_isSharedCheck_2315_ == 0)
{
lean_object* v_unused_2316_; 
v_unused_2316_ = lean_ctor_get(v_toApplicative_2283_, 1);
lean_dec(v_unused_2316_);
v___x_2292_ = v_toApplicative_2283_;
v_isShared_2293_ = v_isSharedCheck_2315_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_toSeqRight_2290_);
lean_inc(v_toSeqLeft_2289_);
lean_inc(v_toSeq_2288_);
lean_inc(v_toFunctor_2287_);
lean_dec(v_toApplicative_2283_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2315_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___f_2294_; lean_object* v___f_2295_; lean_object* v___f_2296_; lean_object* v___f_2297_; lean_object* v___x_2298_; lean_object* v___f_2299_; lean_object* v___f_2300_; lean_object* v___f_2301_; lean_object* v___x_2303_; 
v___f_2294_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
v___f_2295_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(v_toFunctor_2287_);
v___f_2296_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2296_, 0, v_toFunctor_2287_);
v___f_2297_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2297_, 0, v_toFunctor_2287_);
v___x_2298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___f_2296_);
lean_ctor_set(v___x_2298_, 1, v___f_2297_);
v___f_2299_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2299_, 0, v_toSeqRight_2290_);
v___f_2300_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2300_, 0, v_toSeqLeft_2289_);
v___f_2301_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2301_, 0, v_toSeq_2288_);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 4, v___f_2299_);
lean_ctor_set(v___x_2292_, 3, v___f_2300_);
lean_ctor_set(v___x_2292_, 2, v___f_2301_);
lean_ctor_set(v___x_2292_, 1, v___f_2294_);
lean_ctor_set(v___x_2292_, 0, v___x_2298_);
v___x_2303_ = v___x_2292_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2298_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v___f_2294_);
lean_ctor_set(v_reuseFailAlloc_2314_, 2, v___f_2301_);
lean_ctor_set(v_reuseFailAlloc_2314_, 3, v___f_2300_);
lean_ctor_set(v_reuseFailAlloc_2314_, 4, v___f_2299_);
v___x_2303_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2305_; 
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 1, v___f_2295_);
lean_ctor_set(v___x_2285_, 0, v___x_2303_);
v___x_2305_ = v___x_2285_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2303_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v___f_2295_);
v___x_2305_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___f_2309_; lean_object* v___x_10574__overap_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2306_ = l_StateRefT_x27_instMonad___redArg(v___x_2305_);
v___x_2307_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___closed__0);
v___x_2308_ = l_instInhabitedOfMonad___redArg(v___x_2306_, v___x_2307_);
v___f_2309_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2309_, 0, v___x_2308_);
v___x_10574__overap_2310_ = lean_panic_fn_borrowed(v___f_2309_, v_msg_2249_);
lean_dec_ref(v___f_2309_);
v___x_2311_ = lean_box(v___y_2250_);
lean_inc(v___y_2255_);
lean_inc_ref(v___y_2254_);
lean_inc(v___y_2253_);
lean_inc_ref(v___y_2252_);
lean_inc(v___y_2251_);
v___x_2312_ = lean_apply_7(v___x_10574__overap_2310_, v___x_2311_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, lean_box(0));
return v___x_2312_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg___boxed(lean_object* v_msg_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
uint8_t v___y_10635__boxed_2333_; lean_object* v_res_2334_; 
v___y_10635__boxed_2333_ = lean_unbox(v___y_2326_);
v_res_2334_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v_msg_2325_, v___y_10635__boxed_2333_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(uint8_t v_pu_2335_, lean_object* v_msg_2336_, uint8_t v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v_msg_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___boxed(lean_object* v_pu_2345_, lean_object* v_msg_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
uint8_t v_pu_boxed_2354_; uint8_t v___y_10771__boxed_2355_; lean_object* v_res_2356_; 
v_pu_boxed_2354_ = lean_unbox(v_pu_2345_);
v___y_10771__boxed_2355_ = lean_unbox(v___y_2347_);
v_res_2356_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_boxed_2354_, v_msg_2346_, v___y_10771__boxed_2355_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
return v_res_2356_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1(void){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2358_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2359_ = lean_unsigned_to_nat(41u);
v___x_2360_ = lean_unsigned_to_nat(217u);
v___x_2361_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2362_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2363_ = l_mkPanicMessageWithDecl(v___x_2362_, v___x_2361_, v___x_2360_, v___x_2359_, v___x_2358_);
return v___x_2363_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2(void){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2364_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2365_ = lean_unsigned_to_nat(31u);
v___x_2366_ = lean_unsigned_to_nat(222u);
v___x_2367_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2368_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2369_ = l_mkPanicMessageWithDecl(v___x_2368_, v___x_2367_, v___x_2366_, v___x_2365_, v___x_2364_);
return v___x_2369_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3(void){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2370_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2371_ = lean_unsigned_to_nat(41u);
v___x_2372_ = lean_unsigned_to_nat(221u);
v___x_2373_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2374_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2375_ = l_mkPanicMessageWithDecl(v___x_2374_, v___x_2373_, v___x_2372_, v___x_2371_, v___x_2370_);
return v___x_2375_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4(void){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2376_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2377_ = lean_unsigned_to_nat(31u);
v___x_2378_ = lean_unsigned_to_nat(226u);
v___x_2379_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2380_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2381_ = l_mkPanicMessageWithDecl(v___x_2380_, v___x_2379_, v___x_2378_, v___x_2377_, v___x_2376_);
return v___x_2381_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2382_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2383_ = lean_unsigned_to_nat(41u);
v___x_2384_ = lean_unsigned_to_nat(225u);
v___x_2385_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2386_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2387_ = l_mkPanicMessageWithDecl(v___x_2386_, v___x_2385_, v___x_2384_, v___x_2383_, v___x_2382_);
return v___x_2387_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6(void){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2388_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2389_ = lean_unsigned_to_nat(41u);
v___x_2390_ = lean_unsigned_to_nat(230u);
v___x_2391_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2392_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2393_ = l_mkPanicMessageWithDecl(v___x_2392_, v___x_2391_, v___x_2390_, v___x_2389_, v___x_2388_);
return v___x_2393_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2394_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2395_ = lean_unsigned_to_nat(41u);
v___x_2396_ = lean_unsigned_to_nat(233u);
v___x_2397_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2398_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2399_ = l_mkPanicMessageWithDecl(v___x_2398_, v___x_2397_, v___x_2396_, v___x_2395_, v___x_2394_);
return v___x_2399_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8(void){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2400_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2401_ = lean_unsigned_to_nat(41u);
v___x_2402_ = lean_unsigned_to_nat(236u);
v___x_2403_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2404_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2405_ = l_mkPanicMessageWithDecl(v___x_2404_, v___x_2403_, v___x_2402_, v___x_2401_, v___x_2400_);
return v___x_2405_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9(void){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2406_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2407_ = lean_unsigned_to_nat(41u);
v___x_2408_ = lean_unsigned_to_nat(239u);
v___x_2409_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2410_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2411_ = l_mkPanicMessageWithDecl(v___x_2410_, v___x_2409_, v___x_2408_, v___x_2407_, v___x_2406_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t v_pu_2412_, lean_object* v_decl_2413_, uint8_t v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_){
_start:
{
switch(lean_obj_tag(v_decl_2413_))
{
case 0:
{
lean_object* v_decl_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2445_; 
v_decl_2421_ = lean_ctor_get(v_decl_2413_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_decl_2413_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2423_ = v_decl_2413_;
v_isShared_2424_ = v_isSharedCheck_2445_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_decl_2421_);
lean_dec(v_decl_2413_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2445_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_2412_, v_decl_2421_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2436_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2436_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2436_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v_a_2426_);
v___x_2431_ = v___x_2423_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
lean_object* v___x_2433_; 
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v___x_2431_);
v___x_2433_ = v___x_2428_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_del_object(v___x_2423_);
v_a_2437_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2425_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2425_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2470_; 
v_decl_2446_ = lean_ctor_get(v_decl_2413_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v_decl_2413_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2448_ = v_decl_2413_;
v_isShared_2449_ = v_isSharedCheck_2470_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_decl_2446_);
lean_dec(v_decl_2413_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2470_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2412_, v_decl_2446_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2461_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2461_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2461_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v_a_2451_);
v___x_2456_ = v___x_2448_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2458_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2456_);
v___x_2458_ = v___x_2453_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v___x_2456_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_del_object(v___x_2448_);
v_a_2462_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2450_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2450_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
case 2:
{
lean_object* v_decl_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2495_; 
v_decl_2471_ = lean_ctor_get(v_decl_2413_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v_decl_2413_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2473_ = v_decl_2413_;
v_isShared_2474_ = v_isSharedCheck_2495_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_decl_2471_);
lean_dec(v_decl_2413_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2495_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2412_, v_decl_2471_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2486_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2478_ = v___x_2475_;
v_isShared_2479_ = v_isSharedCheck_2486_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2475_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2486_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 0, v_a_2476_);
v___x_2481_ = v___x_2473_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
lean_object* v___x_2483_; 
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 0, v___x_2481_);
v___x_2483_ = v___x_2478_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_del_object(v___x_2473_);
v_a_2487_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2475_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2475_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_2496_; lean_object* v_i_2497_; lean_object* v_y_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2520_; 
v_fvarId_2496_ = lean_ctor_get(v_decl_2413_, 0);
v_i_2497_ = lean_ctor_get(v_decl_2413_, 1);
v_y_2498_ = lean_ctor_get(v_decl_2413_, 2);
v_isSharedCheck_2520_ = !lean_is_exclusive(v_decl_2413_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2500_ = v_decl_2413_;
v_isShared_2501_ = v_isSharedCheck_2520_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_y_2498_);
lean_inc(v_i_2497_);
lean_inc(v_fvarId_2496_);
lean_dec(v_decl_2413_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2520_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
uint8_t v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = 1;
v___x_2503_ = lean_st_ref_get(v_a_2415_);
v___x_2504_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2503_, v_fvarId_2496_, v___x_2502_);
lean_dec(v___x_2503_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_fvarId_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2517_; 
v_fvarId_2505_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2507_ = v___x_2504_;
v_isShared_2508_ = v_isSharedCheck_2517_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_fvarId_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2517_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2509_ = lean_st_ref_get(v_a_2415_);
v___x_2510_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2412_, v___x_2509_, v_y_2498_, v___x_2502_);
lean_dec(v___x_2509_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 2, v___x_2510_);
lean_ctor_set(v___x_2500_, 0, v_fvarId_2505_);
v___x_2512_ = v___x_2500_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_fvarId_2505_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v_i_2497_);
lean_ctor_set(v_reuseFailAlloc_2516_, 2, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
lean_object* v___x_2514_; 
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 0, v___x_2512_);
v___x_2514_ = v___x_2507_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2512_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
else
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_dec(v___x_2504_);
lean_del_object(v___x_2500_);
lean_dec(v_y_2498_);
lean_dec(v_i_2497_);
v___x_2518_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1);
v___x_2519_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2518_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
return v___x_2519_;
}
}
}
case 4:
{
lean_object* v_fvarId_2521_; lean_object* v_i_2522_; lean_object* v_y_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2548_; 
v_fvarId_2521_ = lean_ctor_get(v_decl_2413_, 0);
v_i_2522_ = lean_ctor_get(v_decl_2413_, 1);
v_y_2523_ = lean_ctor_get(v_decl_2413_, 2);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_decl_2413_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2525_ = v_decl_2413_;
v_isShared_2526_ = v_isSharedCheck_2548_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_y_2523_);
lean_inc(v_i_2522_);
lean_inc(v_fvarId_2521_);
lean_dec(v_decl_2413_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2548_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
uint8_t v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2527_ = 1;
v___x_2528_ = lean_st_ref_get(v_a_2415_);
v___x_2529_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2528_, v_fvarId_2521_, v___x_2527_);
lean_dec(v___x_2528_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_fvarId_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v_fvarId_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_fvarId_2530_);
lean_dec_ref_known(v___x_2529_, 1);
v___x_2531_ = lean_st_ref_get(v_a_2415_);
v___x_2532_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2531_, v_y_2523_, v___x_2527_);
lean_dec(v___x_2531_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_fvarId_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2543_; 
v_fvarId_2533_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2535_ = v___x_2532_;
v_isShared_2536_ = v_isSharedCheck_2543_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_fvarId_2533_);
lean_dec(v___x_2532_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2543_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 2, v_fvarId_2533_);
lean_ctor_set(v___x_2525_, 0, v_fvarId_2530_);
v___x_2538_ = v___x_2525_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_fvarId_2530_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v_i_2522_);
lean_ctor_set(v_reuseFailAlloc_2542_, 2, v_fvarId_2533_);
v___x_2538_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
lean_object* v___x_2540_; 
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 0, v___x_2538_);
v___x_2540_ = v___x_2535_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
else
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
lean_dec(v___x_2532_);
lean_dec(v_fvarId_2530_);
lean_del_object(v___x_2525_);
lean_dec(v_i_2522_);
v___x_2544_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2);
v___x_2545_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2544_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
return v___x_2545_;
}
}
else
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
lean_dec(v___x_2529_);
lean_del_object(v___x_2525_);
lean_dec(v_y_2523_);
lean_dec(v_i_2522_);
v___x_2546_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3);
v___x_2547_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2546_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
return v___x_2547_;
}
}
}
case 5:
{
lean_object* v_fvarId_2549_; lean_object* v_i_2550_; lean_object* v_offset_2551_; lean_object* v_y_2552_; lean_object* v_ty_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2580_; 
v_fvarId_2549_ = lean_ctor_get(v_decl_2413_, 0);
v_i_2550_ = lean_ctor_get(v_decl_2413_, 1);
v_offset_2551_ = lean_ctor_get(v_decl_2413_, 2);
v_y_2552_ = lean_ctor_get(v_decl_2413_, 3);
v_ty_2553_ = lean_ctor_get(v_decl_2413_, 4);
v_isSharedCheck_2580_ = !lean_is_exclusive(v_decl_2413_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2555_ = v_decl_2413_;
v_isShared_2556_ = v_isSharedCheck_2580_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_ty_2553_);
lean_inc(v_y_2552_);
lean_inc(v_offset_2551_);
lean_inc(v_i_2550_);
lean_inc(v_fvarId_2549_);
lean_dec(v_decl_2413_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2580_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
uint8_t v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2557_ = 1;
v___x_2558_ = lean_st_ref_get(v_a_2415_);
v___x_2559_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2558_, v_fvarId_2549_, v___x_2557_);
lean_dec(v___x_2558_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_fvarId_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v_fvarId_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_fvarId_2560_);
lean_dec_ref_known(v___x_2559_, 1);
v___x_2561_ = lean_st_ref_get(v_a_2415_);
v___x_2562_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2561_, v_y_2552_, v___x_2557_);
lean_dec(v___x_2561_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_fvarId_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2575_; 
v_fvarId_2563_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2565_ = v___x_2562_;
v_isShared_2566_ = v_isSharedCheck_2575_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_fvarId_2563_);
lean_dec(v___x_2562_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2575_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2570_; 
v___x_2567_ = lean_st_ref_get(v_a_2415_);
v___x_2568_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2412_, v___x_2567_, v___x_2557_, v_ty_2553_);
lean_dec(v___x_2567_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 4, v___x_2568_);
lean_ctor_set(v___x_2555_, 3, v_fvarId_2563_);
lean_ctor_set(v___x_2555_, 0, v_fvarId_2560_);
v___x_2570_ = v___x_2555_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_fvarId_2560_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_i_2550_);
lean_ctor_set(v_reuseFailAlloc_2574_, 2, v_offset_2551_);
lean_ctor_set(v_reuseFailAlloc_2574_, 3, v_fvarId_2563_);
lean_ctor_set(v_reuseFailAlloc_2574_, 4, v___x_2568_);
v___x_2570_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
lean_object* v___x_2572_; 
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v___x_2570_);
v___x_2572_ = v___x_2565_;
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
lean_dec(v___x_2562_);
lean_dec(v_fvarId_2560_);
lean_del_object(v___x_2555_);
lean_dec_ref(v_ty_2553_);
lean_dec(v_offset_2551_);
lean_dec(v_i_2550_);
v___x_2576_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4);
v___x_2577_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2576_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
return v___x_2577_;
}
}
else
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
lean_dec(v___x_2559_);
lean_del_object(v___x_2555_);
lean_dec_ref(v_ty_2553_);
lean_dec(v_y_2552_);
lean_dec(v_offset_2551_);
lean_dec(v_i_2550_);
v___x_2578_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5);
v___x_2579_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2578_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
return v___x_2579_;
}
}
}
case 6:
{
lean_object* v_fvarId_2581_; lean_object* v_cidx_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2602_; 
v_fvarId_2581_ = lean_ctor_get(v_decl_2413_, 0);
v_cidx_2582_ = lean_ctor_get(v_decl_2413_, 1);
v_isSharedCheck_2602_ = !lean_is_exclusive(v_decl_2413_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2584_ = v_decl_2413_;
v_isShared_2585_ = v_isSharedCheck_2602_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_cidx_2582_);
lean_inc(v_fvarId_2581_);
lean_dec(v_decl_2413_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2602_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
uint8_t v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2586_ = 1;
v___x_2587_ = lean_st_ref_get(v_a_2415_);
v___x_2588_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2587_, v_fvarId_2581_, v___x_2586_);
lean_dec(v___x_2587_);
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
v_reuseFailAlloc_2598_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_fvarId_2589_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_cidx_2582_);
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
lean_dec(v_cidx_2582_);
v___x_2600_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6);
v___x_2601_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2600_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
return v___x_2601_;
}
}
}
case 7:
{
lean_object* v_fvarId_2603_; lean_object* v_n_2604_; uint8_t v_check_2605_; uint8_t v_persistent_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2626_; 
v_fvarId_2603_ = lean_ctor_get(v_decl_2413_, 0);
v_n_2604_ = lean_ctor_get(v_decl_2413_, 1);
v_check_2605_ = lean_ctor_get_uint8(v_decl_2413_, sizeof(void*)*2);
v_persistent_2606_ = lean_ctor_get_uint8(v_decl_2413_, sizeof(void*)*2 + 1);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_decl_2413_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2608_ = v_decl_2413_;
v_isShared_2609_ = v_isSharedCheck_2626_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_n_2604_);
lean_inc(v_fvarId_2603_);
lean_dec(v_decl_2413_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2626_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
uint8_t v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2610_ = 1;
v___x_2611_ = lean_st_ref_get(v_a_2415_);
v___x_2612_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2611_, v_fvarId_2603_, v___x_2610_);
lean_dec(v___x_2611_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_fvarId_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2623_; 
v_fvarId_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2623_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_fvarId_2613_);
lean_dec(v___x_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2623_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v_fvarId_2613_);
v___x_2618_ = v___x_2608_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_fvarId_2613_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_n_2604_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, sizeof(void*)*2, v_check_2605_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, sizeof(void*)*2 + 1, v_persistent_2606_);
v___x_2618_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
lean_object* v___x_2620_; 
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___x_2618_);
v___x_2620_ = v___x_2615_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2618_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
else
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
lean_dec(v___x_2612_);
lean_del_object(v___x_2608_);
lean_dec(v_n_2604_);
v___x_2624_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7);
v___x_2625_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2624_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
return v___x_2625_;
}
}
}
case 8:
{
lean_object* v_fvarId_2627_; lean_object* v_n_2628_; uint8_t v_check_2629_; uint8_t v_persistent_2630_; lean_object* v_objs_x3f_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2651_; 
v_fvarId_2627_ = lean_ctor_get(v_decl_2413_, 0);
v_n_2628_ = lean_ctor_get(v_decl_2413_, 1);
v_check_2629_ = lean_ctor_get_uint8(v_decl_2413_, sizeof(void*)*3);
v_persistent_2630_ = lean_ctor_get_uint8(v_decl_2413_, sizeof(void*)*3 + 1);
v_objs_x3f_2631_ = lean_ctor_get(v_decl_2413_, 2);
v_isSharedCheck_2651_ = !lean_is_exclusive(v_decl_2413_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2633_ = v_decl_2413_;
v_isShared_2634_ = v_isSharedCheck_2651_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_objs_x3f_2631_);
lean_inc(v_n_2628_);
lean_inc(v_fvarId_2627_);
lean_dec(v_decl_2413_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2651_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
uint8_t v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2635_ = 1;
v___x_2636_ = lean_st_ref_get(v_a_2415_);
v___x_2637_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2636_, v_fvarId_2627_, v___x_2635_);
lean_dec(v___x_2636_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_fvarId_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2648_; 
v_fvarId_2638_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2640_ = v___x_2637_;
v_isShared_2641_ = v_isSharedCheck_2648_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_fvarId_2638_);
lean_dec(v___x_2637_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2648_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v_fvarId_2638_);
v___x_2643_ = v___x_2633_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(8, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_fvarId_2638_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v_n_2628_);
lean_ctor_set(v_reuseFailAlloc_2647_, 2, v_objs_x3f_2631_);
lean_ctor_set_uint8(v_reuseFailAlloc_2647_, sizeof(void*)*3, v_check_2629_);
lean_ctor_set_uint8(v_reuseFailAlloc_2647_, sizeof(void*)*3 + 1, v_persistent_2630_);
v___x_2643_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
lean_object* v___x_2645_; 
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 0, v___x_2643_);
v___x_2645_ = v___x_2640_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
lean_dec(v___x_2637_);
lean_del_object(v___x_2633_);
lean_dec(v_objs_x3f_2631_);
lean_dec(v_n_2628_);
v___x_2649_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8);
v___x_2650_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2649_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
return v___x_2650_;
}
}
}
default: 
{
lean_object* v_fvarId_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2672_; 
v_fvarId_2652_ = lean_ctor_get(v_decl_2413_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v_decl_2413_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2654_ = v_decl_2413_;
v_isShared_2655_ = v_isSharedCheck_2672_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_fvarId_2652_);
lean_dec(v_decl_2413_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2672_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
uint8_t v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2656_ = 1;
v___x_2657_ = lean_st_ref_get(v_a_2415_);
v___x_2658_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2657_, v_fvarId_2652_, v___x_2656_);
lean_dec(v___x_2657_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_fvarId_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2669_; 
v_fvarId_2659_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2661_ = v___x_2658_;
v_isShared_2662_ = v_isSharedCheck_2669_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_fvarId_2659_);
lean_dec(v___x_2658_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2669_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 0, v_fvarId_2659_);
v___x_2664_ = v___x_2654_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_fvarId_2659_);
v___x_2664_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2666_; 
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2664_);
v___x_2666_ = v___x_2661_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2664_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
else
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
lean_dec(v___x_2658_);
lean_del_object(v___x_2654_);
v___x_2670_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9);
v___x_2671_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___redArg(v___x_2670_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
return v___x_2671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(lean_object* v_pu_2673_, lean_object* v_decl_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
uint8_t v_pu_boxed_2682_; uint8_t v_a_boxed_2683_; lean_object* v_res_2684_; 
v_pu_boxed_2682_ = lean_unbox(v_pu_2673_);
v_a_boxed_2683_ = lean_unbox(v_a_2675_);
v_res_2684_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v_pu_boxed_2682_, v_decl_2674_, v_a_boxed_2683_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t v_pu_2685_, lean_object* v_code_2686_, lean_object* v_s_2687_, uint8_t v_uniqueIdents_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = lean_st_mk_ref(v_s_2687_);
v___x_2695_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2685_, v_code_2686_, v_uniqueIdents_2688_, v___x_2694_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2704_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2698_ = v___x_2695_;
v_isShared_2699_ = v_isSharedCheck_2704_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2695_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2704_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2700_ = lean_st_ref_get(v___x_2694_);
lean_dec(v___x_2694_);
lean_dec(v___x_2700_);
if (v_isShared_2699_ == 0)
{
v___x_2702_ = v___x_2698_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2696_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
else
{
lean_dec(v___x_2694_);
return v___x_2695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize___boxed(lean_object* v_pu_2705_, lean_object* v_code_2706_, lean_object* v_s_2707_, lean_object* v_uniqueIdents_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_){
_start:
{
uint8_t v_pu_boxed_2714_; uint8_t v_uniqueIdents_boxed_2715_; lean_object* v_res_2716_; 
v_pu_boxed_2714_ = lean_unbox(v_pu_2705_);
v_uniqueIdents_boxed_2715_ = lean_unbox(v_uniqueIdents_2708_);
v_res_2716_ = l_Lean_Compiler_LCNF_Code_internalize(v_pu_boxed_2714_, v_code_2706_, v_s_2707_, v_uniqueIdents_boxed_2715_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(lean_object* v_f_2717_, lean_object* v_v_2718_, uint8_t v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
if (lean_obj_tag(v_v_2718_) == 0)
{
lean_object* v_code_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2751_; 
v_code_2726_ = lean_ctor_get(v_v_2718_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v_v_2718_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2728_ = v_v_2718_;
v_isShared_2729_ = v_isSharedCheck_2751_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_code_2726_);
lean_dec(v_v_2718_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2751_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2730_ = lean_box(v___y_2719_);
lean_inc(v___y_2724_);
lean_inc_ref(v___y_2723_);
lean_inc(v___y_2722_);
lean_inc_ref(v___y_2721_);
lean_inc(v___y_2720_);
v___x_2731_ = lean_apply_8(v_f_2717_, v_code_2726_, v___x_2730_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, lean_box(0));
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2742_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2734_ = v___x_2731_;
v_isShared_2735_ = v_isSharedCheck_2742_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2731_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2742_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v_a_2732_);
v___x_2737_ = v___x_2728_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2739_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 0, v___x_2737_);
v___x_2739_ = v___x_2734_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2737_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_del_object(v___x_2728_);
v_a_2743_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2731_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2731_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
}
else
{
lean_object* v___x_2752_; 
lean_dec_ref(v_f_2717_);
v___x_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2752_, 0, v_v_2718_);
return v___x_2752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg___boxed(lean_object* v_f_2753_, lean_object* v_v_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
uint8_t v___y_1412__boxed_2762_; lean_object* v_res_2763_; 
v___y_1412__boxed_2762_ = lean_unbox(v___y_2755_);
v_res_2763_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2753_, v_v_2754_, v___y_1412__boxed_2762_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(uint8_t v_pu_2764_, lean_object* v_f_2765_, lean_object* v_v_2766_, uint8_t v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v___x_2774_; 
v___x_2774_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2765_, v_v_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___boxed(lean_object* v_pu_2775_, lean_object* v_f_2776_, lean_object* v_v_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
uint8_t v_pu_boxed_2785_; uint8_t v___y_1488__boxed_2786_; lean_object* v_res_2787_; 
v_pu_boxed_2785_ = lean_unbox(v_pu_2775_);
v___y_1488__boxed_2786_ = lean_unbox(v___y_2778_);
v_res_2787_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(v_pu_boxed_2785_, v_f_2776_, v_v_2777_, v___y_1488__boxed_2786_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(uint8_t v_pu_2788_, lean_object* v_decl_2789_, uint8_t v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_){
_start:
{
lean_object* v_toSignature_2797_; lean_object* v_value_2798_; uint8_t v_recursive_2799_; lean_object* v_inlineAttr_x3f_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2860_; 
v_toSignature_2797_ = lean_ctor_get(v_decl_2789_, 0);
v_value_2798_ = lean_ctor_get(v_decl_2789_, 1);
v_recursive_2799_ = lean_ctor_get_uint8(v_decl_2789_, sizeof(void*)*3);
v_inlineAttr_x3f_2800_ = lean_ctor_get(v_decl_2789_, 2);
v_isSharedCheck_2860_ = !lean_is_exclusive(v_decl_2789_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2802_ = v_decl_2789_;
v_isShared_2803_ = v_isSharedCheck_2860_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_inlineAttr_x3f_2800_);
lean_inc(v_value_2798_);
lean_inc(v_toSignature_2797_);
lean_dec(v_decl_2789_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2860_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v_name_2804_; lean_object* v_levelParams_2805_; lean_object* v_type_2806_; lean_object* v_params_2807_; uint8_t v_safe_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2859_; 
v_name_2804_ = lean_ctor_get(v_toSignature_2797_, 0);
v_levelParams_2805_ = lean_ctor_get(v_toSignature_2797_, 1);
v_type_2806_ = lean_ctor_get(v_toSignature_2797_, 2);
v_params_2807_ = lean_ctor_get(v_toSignature_2797_, 3);
v_safe_2808_ = lean_ctor_get_uint8(v_toSignature_2797_, sizeof(void*)*4);
v_isSharedCheck_2859_ = !lean_is_exclusive(v_toSignature_2797_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2810_ = v_toSignature_2797_;
v_isShared_2811_ = v_isSharedCheck_2859_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_params_2807_);
lean_inc(v_type_2806_);
lean_inc(v_levelParams_2805_);
lean_inc(v_name_2804_);
lean_dec(v_toSignature_2797_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2859_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2812_; 
v___x_2812_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2788_, v_type_2806_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; size_t v_sz_2814_; size_t v___x_2815_; lean_object* v___x_2816_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2812_, 1);
v_sz_2814_ = lean_array_size(v_params_2807_);
v___x_2815_ = ((size_t)0ULL);
v___x_2816_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2788_, v_sz_2814_, v___x_2815_, v_params_2807_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2816_, 1);
v___x_2818_ = lean_box(v_pu_2788_);
v___x_2819_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed), 9, 1);
lean_closure_set(v___x_2819_, 0, v___x_2818_);
v___x_2820_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v___x_2819_, v_value_2798_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2834_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2823_ = v___x_2820_;
v_isShared_2824_ = v_isSharedCheck_2834_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2820_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2834_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2811_ == 0)
{
lean_ctor_set(v___x_2810_, 3, v_a_2817_);
lean_ctor_set(v___x_2810_, 2, v_a_2813_);
v___x_2826_ = v___x_2810_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_name_2804_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_levelParams_2805_);
lean_ctor_set(v_reuseFailAlloc_2833_, 2, v_a_2813_);
lean_ctor_set(v_reuseFailAlloc_2833_, 3, v_a_2817_);
lean_ctor_set_uint8(v_reuseFailAlloc_2833_, sizeof(void*)*4, v_safe_2808_);
v___x_2826_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2828_; 
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 1, v_a_2821_);
lean_ctor_set(v___x_2802_, 0, v___x_2826_);
v___x_2828_ = v___x_2802_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2826_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_a_2821_);
lean_ctor_set(v_reuseFailAlloc_2832_, 2, v_inlineAttr_x3f_2800_);
lean_ctor_set_uint8(v_reuseFailAlloc_2832_, sizeof(void*)*3, v_recursive_2799_);
v___x_2828_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2830_; 
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v___x_2828_);
v___x_2830_ = v___x_2823_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec(v_a_2817_);
lean_dec(v_a_2813_);
lean_del_object(v___x_2810_);
lean_dec(v_levelParams_2805_);
lean_dec(v_name_2804_);
lean_del_object(v___x_2802_);
lean_dec(v_inlineAttr_x3f_2800_);
v_a_2835_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2820_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2820_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec(v_a_2813_);
lean_del_object(v___x_2810_);
lean_dec(v_levelParams_2805_);
lean_dec(v_name_2804_);
lean_del_object(v___x_2802_);
lean_dec(v_inlineAttr_x3f_2800_);
lean_dec_ref(v_value_2798_);
v_a_2843_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2816_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2816_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_del_object(v___x_2810_);
lean_dec_ref(v_params_2807_);
lean_dec(v_levelParams_2805_);
lean_dec(v_name_2804_);
lean_del_object(v___x_2802_);
lean_dec(v_inlineAttr_x3f_2800_);
lean_dec_ref(v_value_2798_);
v_a_2851_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2812_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2812_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go___boxed(lean_object* v_pu_2861_, lean_object* v_decl_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_){
_start:
{
uint8_t v_pu_boxed_2870_; uint8_t v_a_boxed_2871_; lean_object* v_res_2872_; 
v_pu_boxed_2870_ = lean_unbox(v_pu_2861_);
v_a_boxed_2871_ = lean_unbox(v_a_2863_);
v_res_2872_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_boxed_2870_, v_decl_2862_, v_a_boxed_2871_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
lean_dec(v_a_2868_);
lean_dec_ref(v_a_2867_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
lean_dec(v_a_2864_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t v_pu_2873_, lean_object* v_decl_2874_, lean_object* v_s_2875_, uint8_t v_uniqueIdents_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2882_ = lean_st_mk_ref(v_s_2875_);
v___x_2883_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_2873_, v_decl_2874_, v_uniqueIdents_2876_, v___x_2882_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2892_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2886_ = v___x_2883_;
v_isShared_2887_ = v_isSharedCheck_2892_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2883_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2892_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2888_; lean_object* v___x_2890_; 
v___x_2888_ = lean_st_ref_get(v___x_2882_);
lean_dec(v___x_2882_);
lean_dec(v___x_2888_);
if (v_isShared_2887_ == 0)
{
v___x_2890_ = v___x_2886_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2884_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
else
{
lean_dec(v___x_2882_);
return v___x_2883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize___boxed(lean_object* v_pu_2893_, lean_object* v_decl_2894_, lean_object* v_s_2895_, lean_object* v_uniqueIdents_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_){
_start:
{
uint8_t v_pu_boxed_2902_; uint8_t v_uniqueIdents_boxed_2903_; lean_object* v_res_2904_; 
v_pu_boxed_2902_ = lean_unbox(v_pu_2893_);
v_uniqueIdents_boxed_2903_ = lean_unbox(v_uniqueIdents_2896_);
v_res_2904_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_boxed_2902_, v_decl_2894_, v_s_2895_, v_uniqueIdents_boxed_2903_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
return v_res_2904_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2905_ = lean_box(0);
v___x_2906_ = lean_unsigned_to_nat(16u);
v___x_2907_ = lean_mk_array(v___x_2906_, v___x_2905_);
return v___x_2907_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2908_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0);
v___x_2909_ = lean_unsigned_to_nat(0u);
v___x_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
lean_ctor_set(v___x_2910_, 1, v___x_2908_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(uint8_t v_pu_2911_, size_t v_sz_2912_, size_t v_i_2913_, lean_object* v_bs_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
uint8_t v___x_2920_; 
v___x_2920_ = lean_usize_dec_lt(v_i_2913_, v_sz_2912_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2921_; 
v___x_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2921_, 0, v_bs_2914_);
return v___x_2921_;
}
else
{
lean_object* v_v_2922_; lean_object* v___x_2923_; lean_object* v_bs_x27_2924_; lean_object* v___x_2925_; lean_object* v_lctx_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2951_; 
v_v_2922_ = lean_array_uget(v_bs_2914_, v_i_2913_);
v___x_2923_ = lean_unsigned_to_nat(0u);
v_bs_x27_2924_ = lean_array_uset(v_bs_2914_, v_i_2913_, v___x_2923_);
v___x_2925_ = lean_st_ref_take(v___y_2916_);
v_lctx_2926_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2951_ == 0)
{
lean_object* v_unused_2952_; 
v_unused_2952_ = lean_ctor_get(v___x_2925_, 1);
lean_dec(v_unused_2952_);
v___x_2928_ = v___x_2925_;
v_isShared_2929_ = v_isSharedCheck_2951_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_lctx_2926_);
lean_dec(v___x_2925_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2951_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2930_; lean_object* v___x_2932_; 
v___x_2930_ = lean_unsigned_to_nat(1u);
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 1, v___x_2930_);
v___x_2932_ = v___x_2928_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_lctx_2926_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v___x_2930_);
v___x_2932_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; uint8_t v___x_2935_; lean_object* v___x_2936_; 
v___x_2933_ = lean_st_ref_put(v___y_2916_, v___x_2932_);
v___x_2934_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_2935_ = 0;
v___x_2936_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_2911_, v_v_2922_, v___x_2934_, v___x_2935_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; size_t v___x_2938_; size_t v___x_2939_; lean_object* v___x_2940_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2937_);
lean_dec_ref_known(v___x_2936_, 1);
v___x_2938_ = ((size_t)1ULL);
v___x_2939_ = lean_usize_add(v_i_2913_, v___x_2938_);
v___x_2940_ = lean_array_uset(v_bs_x27_2924_, v_i_2913_, v_a_2937_);
v_i_2913_ = v___x_2939_;
v_bs_2914_ = v___x_2940_;
goto _start;
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_dec_ref(v_bs_x27_2924_);
v_a_2942_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2936_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2936_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___boxed(lean_object* v_pu_2953_, lean_object* v_sz_2954_, lean_object* v_i_2955_, lean_object* v_bs_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
uint8_t v_pu_boxed_2962_; size_t v_sz_boxed_2963_; size_t v_i_boxed_2964_; lean_object* v_res_2965_; 
v_pu_boxed_2962_ = lean_unbox(v_pu_2953_);
v_sz_boxed_2963_ = lean_unbox_usize(v_sz_2954_);
lean_dec(v_sz_2954_);
v_i_boxed_2964_ = lean_unbox_usize(v_i_2955_);
lean_dec(v_i_2955_);
v_res_2965_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_boxed_2962_, v_sz_boxed_2963_, v_i_boxed_2964_, v_bs_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
return v_res_2965_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__0(void){
_start:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2966_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_2967_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
lean_ctor_set(v___x_2967_, 1, v___x_2966_);
lean_ctor_set(v___x_2967_, 2, v___x_2966_);
lean_ctor_set(v___x_2967_, 3, v___x_2966_);
lean_ctor_set(v___x_2967_, 4, v___x_2966_);
lean_ctor_set(v___x_2967_, 5, v___x_2966_);
return v___x_2967_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__1(void){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2968_ = lean_unsigned_to_nat(1u);
v___x_2969_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__0, &l_Lean_Compiler_LCNF_cleanup___closed__0_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__0);
v___x_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
lean_ctor_set(v___x_2970_, 1, v___x_2968_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup(uint8_t v_pu_2971_, lean_object* v_decl_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; size_t v_sz_2981_; size_t v___x_2982_; lean_object* v___x_2983_; 
v___x_2978_ = lean_st_ref_take(v_a_2974_);
lean_dec(v___x_2978_);
v___x_2979_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
v___x_2980_ = lean_st_ref_put(v_a_2974_, v___x_2979_);
v_sz_2981_ = lean_array_size(v_decl_2972_);
v___x_2982_ = ((size_t)0ULL);
v___x_2983_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_2971_, v_sz_2981_, v___x_2982_, v_decl_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup___boxed(lean_object* v_pu_2984_, lean_object* v_decl_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_){
_start:
{
uint8_t v_pu_boxed_2991_; lean_object* v_res_2992_; 
v_pu_boxed_2991_ = lean_unbox(v_pu_2984_);
v_res_2992_ = l_Lean_Compiler_LCNF_cleanup(v_pu_boxed_2991_, v_decl_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_);
lean_dec(v_a_2989_);
lean_dec_ref(v_a_2988_);
lean_dec(v_a_2987_);
lean_dec_ref(v_a_2986_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(lean_object* v_a_2993_, lean_object* v_ngen_2994_, lean_object* v_a_x3f_2995_){
_start:
{
lean_object* v___x_2997_; lean_object* v_env_2998_; lean_object* v_nextMacroScope_2999_; lean_object* v_auxDeclNGen_3000_; lean_object* v_traceState_3001_; lean_object* v_cache_3002_; lean_object* v_recordedDeps_3003_; lean_object* v_messages_3004_; lean_object* v_infoState_3005_; lean_object* v_snapshotTasks_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3016_; 
v___x_2997_ = lean_st_ref_take(v_a_2993_);
v_env_2998_ = lean_ctor_get(v___x_2997_, 0);
v_nextMacroScope_2999_ = lean_ctor_get(v___x_2997_, 1);
v_auxDeclNGen_3000_ = lean_ctor_get(v___x_2997_, 3);
v_traceState_3001_ = lean_ctor_get(v___x_2997_, 4);
v_cache_3002_ = lean_ctor_get(v___x_2997_, 5);
v_recordedDeps_3003_ = lean_ctor_get(v___x_2997_, 6);
v_messages_3004_ = lean_ctor_get(v___x_2997_, 7);
v_infoState_3005_ = lean_ctor_get(v___x_2997_, 8);
v_snapshotTasks_3006_ = lean_ctor_get(v___x_2997_, 9);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3016_ == 0)
{
lean_object* v_unused_3017_; 
v_unused_3017_ = lean_ctor_get(v___x_2997_, 2);
lean_dec(v_unused_3017_);
v___x_3008_ = v___x_2997_;
v_isShared_3009_ = v_isSharedCheck_3016_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_snapshotTasks_3006_);
lean_inc(v_infoState_3005_);
lean_inc(v_messages_3004_);
lean_inc(v_recordedDeps_3003_);
lean_inc(v_cache_3002_);
lean_inc(v_traceState_3001_);
lean_inc(v_auxDeclNGen_3000_);
lean_inc(v_nextMacroScope_2999_);
lean_inc(v_env_2998_);
lean_dec(v___x_2997_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3016_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3010_; lean_object* v___x_3012_; 
v___x_3010_ = lean_box(0);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 2, v_ngen_2994_);
v___x_3012_ = v___x_3008_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_env_2998_);
lean_ctor_set(v_reuseFailAlloc_3015_, 1, v_nextMacroScope_2999_);
lean_ctor_set(v_reuseFailAlloc_3015_, 2, v_ngen_2994_);
lean_ctor_set(v_reuseFailAlloc_3015_, 3, v_auxDeclNGen_3000_);
lean_ctor_set(v_reuseFailAlloc_3015_, 4, v_traceState_3001_);
lean_ctor_set(v_reuseFailAlloc_3015_, 5, v_cache_3002_);
lean_ctor_set(v_reuseFailAlloc_3015_, 6, v_recordedDeps_3003_);
lean_ctor_set(v_reuseFailAlloc_3015_, 7, v_messages_3004_);
lean_ctor_set(v_reuseFailAlloc_3015_, 8, v_infoState_3005_);
lean_ctor_set(v_reuseFailAlloc_3015_, 9, v_snapshotTasks_3006_);
v___x_3012_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = lean_st_ref_put(v_a_2993_, v___x_3012_);
v___x_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3010_);
return v___x_3014_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0___boxed(lean_object* v_a_3018_, lean_object* v_ngen_3019_, lean_object* v_a_x3f_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3018_, v_ngen_3019_, v_a_x3f_3020_);
lean_dec(v_a_x3f_3020_);
lean_dec(v_a_3018_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(uint8_t v_pu_3029_, lean_object* v_decl_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v___x_3034_; lean_object* v_ngen_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v_env_3038_; lean_object* v_nextMacroScope_3039_; lean_object* v_auxDeclNGen_3040_; lean_object* v_traceState_3041_; lean_object* v_cache_3042_; lean_object* v_recordedDeps_3043_; lean_object* v_messages_3044_; lean_object* v_infoState_3045_; lean_object* v_snapshotTasks_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3090_; 
v___x_3034_ = lean_st_ref_get(v_a_3032_);
v_ngen_3035_ = lean_ctor_get(v___x_3034_, 2);
lean_inc_ref(v_ngen_3035_);
lean_dec(v___x_3034_);
v___x_3036_ = ((lean_object*)(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2));
v___x_3037_ = lean_st_ref_take(v_a_3032_);
v_env_3038_ = lean_ctor_get(v___x_3037_, 0);
v_nextMacroScope_3039_ = lean_ctor_get(v___x_3037_, 1);
v_auxDeclNGen_3040_ = lean_ctor_get(v___x_3037_, 3);
v_traceState_3041_ = lean_ctor_get(v___x_3037_, 4);
v_cache_3042_ = lean_ctor_get(v___x_3037_, 5);
v_recordedDeps_3043_ = lean_ctor_get(v___x_3037_, 6);
v_messages_3044_ = lean_ctor_get(v___x_3037_, 7);
v_infoState_3045_ = lean_ctor_get(v___x_3037_, 8);
v_snapshotTasks_3046_ = lean_ctor_get(v___x_3037_, 9);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3090_ == 0)
{
lean_object* v_unused_3091_; 
v_unused_3091_ = lean_ctor_get(v___x_3037_, 2);
lean_dec(v_unused_3091_);
v___x_3048_ = v___x_3037_;
v_isShared_3049_ = v_isSharedCheck_3090_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_snapshotTasks_3046_);
lean_inc(v_infoState_3045_);
lean_inc(v_messages_3044_);
lean_inc(v_recordedDeps_3043_);
lean_inc(v_cache_3042_);
lean_inc(v_traceState_3041_);
lean_inc(v_auxDeclNGen_3040_);
lean_inc(v_nextMacroScope_3039_);
lean_inc(v_env_3038_);
lean_dec(v___x_3037_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3090_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 2, v___x_3036_);
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_env_3038_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_nextMacroScope_3039_);
lean_ctor_set(v_reuseFailAlloc_3089_, 2, v___x_3036_);
lean_ctor_set(v_reuseFailAlloc_3089_, 3, v_auxDeclNGen_3040_);
lean_ctor_set(v_reuseFailAlloc_3089_, 4, v_traceState_3041_);
lean_ctor_set(v_reuseFailAlloc_3089_, 5, v_cache_3042_);
lean_ctor_set(v_reuseFailAlloc_3089_, 6, v_recordedDeps_3043_);
lean_ctor_set(v_reuseFailAlloc_3089_, 7, v_messages_3044_);
lean_ctor_set(v_reuseFailAlloc_3089_, 8, v_infoState_3045_);
lean_ctor_set(v_reuseFailAlloc_3089_, 9, v_snapshotTasks_3046_);
v___x_3051_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; uint8_t v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; uint8_t v___x_3059_; lean_object* v_r_3060_; 
v___x_3052_ = lean_st_ref_put(v_a_3032_, v___x_3051_);
v___x_3053_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_3054_ = 0;
v___x_3055_ = lean_box(v_pu_3029_);
v___x_3056_ = lean_box(v___x_3054_);
v___x_3057_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_internalize___boxed), 9, 4);
lean_closure_set(v___x_3057_, 0, v___x_3055_);
lean_closure_set(v___x_3057_, 1, v_decl_3030_);
lean_closure_set(v___x_3057_, 2, v___x_3053_);
lean_closure_set(v___x_3057_, 3, v___x_3056_);
v___x_3058_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
v___x_3059_ = 0;
v_r_3060_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v___x_3057_, v___x_3058_, v___x_3059_, v_a_3031_, v_a_3032_);
if (lean_obj_tag(v_r_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3077_; 
v_a_3061_ = lean_ctor_get(v_r_3060_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v_r_3060_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3063_ = v_r_3060_;
v_isShared_3064_ = v_isSharedCheck_3077_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v_r_3060_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3077_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
lean_inc(v_a_3061_);
if (v_isShared_3064_ == 0)
{
lean_ctor_set_tag(v___x_3063_, 1);
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
lean_object* v___x_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
v___x_3067_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3032_, v_ngen_3035_, v___x_3066_);
lean_dec_ref(v___x_3066_);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3074_ == 0)
{
lean_object* v_unused_3075_; 
v_unused_3075_ = lean_ctor_get(v___x_3067_, 0);
lean_dec(v_unused_3075_);
v___x_3069_ = v___x_3067_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_dec(v___x_3067_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v_a_3061_);
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3061_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
v_a_3078_ = lean_ctor_get(v_r_3060_, 0);
lean_inc(v_a_3078_);
lean_dec_ref_known(v_r_3060_, 1);
v___x_3079_ = lean_box(0);
v___x_3080_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3032_, v_ngen_3035_, v___x_3079_);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3087_ == 0)
{
lean_object* v_unused_3088_; 
v_unused_3088_ = lean_ctor_get(v___x_3080_, 0);
lean_dec(v_unused_3088_);
v___x_3082_ = v___x_3080_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_dec(v___x_3080_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
lean_ctor_set_tag(v___x_3082_, 1);
lean_ctor_set(v___x_3082_, 0, v_a_3078_);
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3078_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___boxed(lean_object* v_pu_3092_, lean_object* v_decl_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_){
_start:
{
uint8_t v_pu_boxed_3097_; lean_object* v_res_3098_; 
v_pu_boxed_3097_ = lean_unbox(v_pu_3092_);
v_res_3098_ = l_Lean_Compiler_LCNF_normalizeFVarIds(v_pu_boxed_3097_, v_decl_3093_, v_a_3094_, v_a_3095_);
lean_dec(v_a_3095_);
lean_dec_ref(v_a_3094_);
return v_res_3098_;
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
