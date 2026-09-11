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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v_nbuckets_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_345_ = lean_array_get_size(v_data_344_);
v___x_346_ = lean_unsigned_to_nat(2u);
v_nbuckets_347_ = lean_nat_mul(v___x_345_, v___x_346_);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_box(0);
v___x_350_ = lean_mk_array(v_nbuckets_347_, v___x_349_);
v___x_351_ = lean_array_propagate_mark(v_data_344_, v___x_350_);
v___x_352_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(v___x_348_, v_data_344_, v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(lean_object* v_m_353_, lean_object* v_a_354_, lean_object* v_b_355_){
_start:
{
lean_object* v_size_356_; lean_object* v_buckets_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_400_; 
v_size_356_ = lean_ctor_get(v_m_353_, 0);
v_buckets_357_ = lean_ctor_get(v_m_353_, 1);
v_isSharedCheck_400_ = !lean_is_exclusive(v_m_353_);
if (v_isSharedCheck_400_ == 0)
{
v___x_359_ = v_m_353_;
v_isShared_360_ = v_isSharedCheck_400_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_buckets_357_);
lean_inc(v_size_356_);
lean_dec(v_m_353_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_400_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; uint64_t v___x_362_; uint64_t v___x_363_; uint64_t v___x_364_; uint64_t v_fold_365_; uint64_t v___x_366_; uint64_t v___x_367_; uint64_t v___x_368_; size_t v___x_369_; size_t v___x_370_; size_t v___x_371_; size_t v___x_372_; size_t v___x_373_; lean_object* v_bkt_374_; uint8_t v___x_375_; 
v___x_361_ = lean_array_get_size(v_buckets_357_);
v___x_362_ = l_Lean_instHashableFVarId_hash(v_a_354_);
v___x_363_ = 32ULL;
v___x_364_ = lean_uint64_shift_right(v___x_362_, v___x_363_);
v_fold_365_ = lean_uint64_xor(v___x_362_, v___x_364_);
v___x_366_ = 16ULL;
v___x_367_ = lean_uint64_shift_right(v_fold_365_, v___x_366_);
v___x_368_ = lean_uint64_xor(v_fold_365_, v___x_367_);
v___x_369_ = lean_uint64_to_usize(v___x_368_);
v___x_370_ = lean_usize_of_nat(v___x_361_);
v___x_371_ = ((size_t)1ULL);
v___x_372_ = lean_usize_sub(v___x_370_, v___x_371_);
v___x_373_ = lean_usize_land(v___x_369_, v___x_372_);
v_bkt_374_ = lean_array_uget_borrowed(v_buckets_357_, v___x_373_);
v___x_375_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_a_354_, v_bkt_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; lean_object* v_size_x27_377_; lean_object* v___x_378_; lean_object* v_buckets_x27_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_376_ = lean_unsigned_to_nat(1u);
v_size_x27_377_ = lean_nat_add(v_size_356_, v___x_376_);
lean_dec(v_size_356_);
lean_inc(v_bkt_374_);
v___x_378_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_378_, 0, v_a_354_);
lean_ctor_set(v___x_378_, 1, v_b_355_);
lean_ctor_set(v___x_378_, 2, v_bkt_374_);
v_buckets_x27_379_ = lean_array_uset(v_buckets_357_, v___x_373_, v___x_378_);
v___x_380_ = lean_unsigned_to_nat(4u);
v___x_381_ = lean_nat_mul(v_size_x27_377_, v___x_380_);
v___x_382_ = lean_unsigned_to_nat(3u);
v___x_383_ = lean_nat_div(v___x_381_, v___x_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_array_get_size(v_buckets_x27_379_);
v___x_385_ = lean_nat_dec_le(v___x_383_, v___x_384_);
lean_dec(v___x_383_);
if (v___x_385_ == 0)
{
lean_object* v_val_386_; lean_object* v___x_388_; 
v_val_386_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(v_buckets_x27_379_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 1, v_val_386_);
lean_ctor_set(v___x_359_, 0, v_size_x27_377_);
v___x_388_ = v___x_359_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_size_x27_377_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_val_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
else
{
lean_object* v___x_391_; 
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 1, v_buckets_x27_379_);
lean_ctor_set(v___x_359_, 0, v_size_x27_377_);
v___x_391_ = v___x_359_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_size_x27_377_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_buckets_x27_379_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
else
{
lean_object* v___x_393_; lean_object* v_buckets_x27_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
lean_inc(v_bkt_374_);
v___x_393_ = lean_box(0);
v_buckets_x27_394_ = lean_array_uset(v_buckets_357_, v___x_373_, v___x_393_);
v___x_395_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(v_a_354_, v_b_355_, v_bkt_374_);
v___x_396_ = lean_array_uset(v_buckets_x27_394_, v___x_373_, v___x_395_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 1, v___x_396_);
v___x_398_ = v___x_359_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_size_356_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(lean_object* v___y_401_){
_start:
{
lean_object* v___x_403_; lean_object* v_ngen_404_; lean_object* v_namePrefix_405_; lean_object* v_idx_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_435_; 
v___x_403_ = lean_st_ref_get(v___y_401_);
v_ngen_404_ = lean_ctor_get(v___x_403_, 2);
lean_inc_ref(v_ngen_404_);
lean_dec(v___x_403_);
v_namePrefix_405_ = lean_ctor_get(v_ngen_404_, 0);
v_idx_406_ = lean_ctor_get(v_ngen_404_, 1);
v_isSharedCheck_435_ = !lean_is_exclusive(v_ngen_404_);
if (v_isSharedCheck_435_ == 0)
{
v___x_408_ = v_ngen_404_;
v_isShared_409_ = v_isSharedCheck_435_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_idx_406_);
lean_inc(v_namePrefix_405_);
lean_dec(v_ngen_404_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_435_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; lean_object* v_env_411_; lean_object* v_nextMacroScope_412_; lean_object* v_auxDeclNGen_413_; lean_object* v_traceState_414_; lean_object* v_cache_415_; lean_object* v_messages_416_; lean_object* v_infoState_417_; lean_object* v_snapshotTasks_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_433_; 
v___x_410_ = lean_st_ref_take(v___y_401_);
v_env_411_ = lean_ctor_get(v___x_410_, 0);
v_nextMacroScope_412_ = lean_ctor_get(v___x_410_, 1);
v_auxDeclNGen_413_ = lean_ctor_get(v___x_410_, 3);
v_traceState_414_ = lean_ctor_get(v___x_410_, 4);
v_cache_415_ = lean_ctor_get(v___x_410_, 5);
v_messages_416_ = lean_ctor_get(v___x_410_, 6);
v_infoState_417_ = lean_ctor_get(v___x_410_, 7);
v_snapshotTasks_418_ = lean_ctor_get(v___x_410_, 8);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; 
v_unused_434_ = lean_ctor_get(v___x_410_, 2);
lean_dec(v_unused_434_);
v___x_420_ = v___x_410_;
v_isShared_421_ = v_isSharedCheck_433_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_snapshotTasks_418_);
lean_inc(v_infoState_417_);
lean_inc(v_messages_416_);
lean_inc(v_cache_415_);
lean_inc(v_traceState_414_);
lean_inc(v_auxDeclNGen_413_);
lean_inc(v_nextMacroScope_412_);
lean_inc(v_env_411_);
lean_dec(v___x_410_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_433_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v_r_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
lean_inc(v_idx_406_);
lean_inc(v_namePrefix_405_);
v_r_422_ = l_Lean_Name_num___override(v_namePrefix_405_, v_idx_406_);
v___x_423_ = lean_unsigned_to_nat(1u);
v___x_424_ = lean_nat_add(v_idx_406_, v___x_423_);
lean_dec(v_idx_406_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 1, v___x_424_);
v___x_426_ = v___x_408_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_namePrefix_405_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v___x_424_);
v___x_426_ = v_reuseFailAlloc_432_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_428_; 
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 2, v___x_426_);
v___x_428_ = v___x_420_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_env_411_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_nextMacroScope_412_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v_auxDeclNGen_413_);
lean_ctor_set(v_reuseFailAlloc_431_, 4, v_traceState_414_);
lean_ctor_set(v_reuseFailAlloc_431_, 5, v_cache_415_);
lean_ctor_set(v_reuseFailAlloc_431_, 6, v_messages_416_);
lean_ctor_set(v_reuseFailAlloc_431_, 7, v_infoState_417_);
lean_ctor_set(v_reuseFailAlloc_431_, 8, v_snapshotTasks_418_);
v___x_428_ = v_reuseFailAlloc_431_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_st_ref_put(v___y_401_, v___x_428_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v_r_422_);
return v___x_430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg___boxed(lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_436_);
lean_dec(v___y_436_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(uint8_t v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
v___x_446_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_444_);
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0___boxed(lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
uint8_t v___y_3111__boxed_462_; lean_object* v_res_463_; 
v___y_3111__boxed_462_ = lean_unbox(v___y_455_);
v_res_463_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(v___y_3111__boxed_462_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(lean_object* v_fvarId_464_, uint8_t v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_484_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_484_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_484_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_484_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_482_; 
v___x_477_ = lean_st_ref_take(v_a_466_);
lean_inc(v_a_473_);
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v_a_473_);
v___x_479_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v___x_477_, v_fvarId_464_, v___x_478_);
v___x_480_ = lean_st_ref_put(v_a_466_, v___x_479_);
if (v_isShared_476_ == 0)
{
v___x_482_ = v___x_475_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_473_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
else
{
lean_dec(v_fvarId_464_);
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg___boxed(lean_object* v_fvarId_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_){
_start:
{
uint8_t v_a_boxed_493_; lean_object* v_res_494_; 
v_a_boxed_493_ = lean_unbox(v_a_486_);
v_res_494_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_485_, v_a_boxed_493_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(uint8_t v_pu_495_, lean_object* v_fvarId_496_, uint8_t v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___boxed(lean_object* v_pu_505_, lean_object* v_fvarId_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
uint8_t v_pu_boxed_514_; uint8_t v_a_boxed_515_; lean_object* v_res_516_; 
v_pu_boxed_514_ = lean_unbox(v_pu_505_);
v_a_boxed_515_ = lean_unbox(v_a_507_);
v_res_516_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(v_pu_boxed_514_, v_fvarId_506_, v_a_boxed_515_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
lean_dec(v_a_508_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(uint8_t v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_522_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___boxed(lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
uint8_t v___y_3186__boxed_532_; lean_object* v_res_533_; 
v___y_3186__boxed_532_ = lean_unbox(v___y_525_);
v_res_533_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(v___y_3186__boxed_532_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1(lean_object* v_00_u03b2_534_, lean_object* v_m_535_, lean_object* v_a_536_, lean_object* v_b_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v_m_535_, v_a_536_, v_b_537_);
return v___x_538_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(lean_object* v_00_u03b2_539_, lean_object* v_a_540_, lean_object* v_x_541_){
_start:
{
uint8_t v___x_542_; 
v___x_542_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_a_540_, v_x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___boxed(lean_object* v_00_u03b2_543_, lean_object* v_a_544_, lean_object* v_x_545_){
_start:
{
uint8_t v_res_546_; lean_object* v_r_547_; 
v_res_546_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(v_00_u03b2_543_, v_a_544_, v_x_545_);
lean_dec(v_x_545_);
lean_dec(v_a_544_);
v_r_547_ = lean_box(v_res_546_);
return v_r_547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3(lean_object* v_00_u03b2_548_, lean_object* v_data_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(v_data_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4(lean_object* v_00_u03b2_551_, lean_object* v_a_552_, lean_object* v_b_553_, lean_object* v_x_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(v_a_552_, v_b_553_, v_x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_556_, lean_object* v_i_557_, lean_object* v_source_558_, lean_object* v_target_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(v_i_557_, v_source_558_, v_target_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_561_, lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(v_x_562_, v_x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(lean_object* v_a_565_, lean_object* v_x_566_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
lean_object* v___x_567_; 
v___x_567_ = lean_box(0);
return v___x_567_;
}
else
{
lean_object* v_key_568_; lean_object* v_value_569_; lean_object* v_tail_570_; uint8_t v___x_571_; 
v_key_568_ = lean_ctor_get(v_x_566_, 0);
v_value_569_ = lean_ctor_get(v_x_566_, 1);
v_tail_570_ = lean_ctor_get(v_x_566_, 2);
v___x_571_ = l_Lean_instBEqFVarId_beq(v_key_568_, v_a_565_);
if (v___x_571_ == 0)
{
v_x_566_ = v_tail_570_;
goto _start;
}
else
{
lean_object* v___x_573_; 
lean_inc(v_value_569_);
v___x_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_573_, 0, v_value_569_);
return v___x_573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_574_, lean_object* v_x_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_574_, v_x_575_);
lean_dec(v_x_575_);
lean_dec(v_a_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(lean_object* v_m_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_buckets_579_; lean_object* v___x_580_; uint64_t v___x_581_; uint64_t v___x_582_; uint64_t v___x_583_; uint64_t v_fold_584_; uint64_t v___x_585_; uint64_t v___x_586_; uint64_t v___x_587_; size_t v___x_588_; size_t v___x_589_; size_t v___x_590_; size_t v___x_591_; size_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_buckets_579_ = lean_ctor_get(v_m_577_, 1);
v___x_580_ = lean_array_get_size(v_buckets_579_);
v___x_581_ = l_Lean_instHashableFVarId_hash(v_a_578_);
v___x_582_ = 32ULL;
v___x_583_ = lean_uint64_shift_right(v___x_581_, v___x_582_);
v_fold_584_ = lean_uint64_xor(v___x_581_, v___x_583_);
v___x_585_ = 16ULL;
v___x_586_ = lean_uint64_shift_right(v_fold_584_, v___x_585_);
v___x_587_ = lean_uint64_xor(v_fold_584_, v___x_586_);
v___x_588_ = lean_uint64_to_usize(v___x_587_);
v___x_589_ = lean_usize_of_nat(v___x_580_);
v___x_590_ = ((size_t)1ULL);
v___x_591_ = lean_usize_sub(v___x_589_, v___x_590_);
v___x_592_ = lean_usize_land(v___x_588_, v___x_591_);
v___x_593_ = lean_array_uget_borrowed(v_buckets_579_, v___x_592_);
v___x_594_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_578_, v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg___boxed(lean_object* v_m_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v_m_595_, v_a_596_);
lean_dec(v_a_596_);
lean_dec_ref(v_m_595_);
return v_res_597_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_instMonadEIO(lean_box(0));
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(lean_object* v_msg_603_, uint8_t v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v_toApplicative_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_677_; 
v___x_611_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
v___x_612_ = l_StateRefT_x27_instMonad___redArg(v___x_611_);
v_toApplicative_613_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; 
v_unused_678_ = lean_ctor_get(v___x_612_, 1);
lean_dec(v_unused_678_);
v___x_615_ = v___x_612_;
v_isShared_616_ = v_isSharedCheck_677_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_toApplicative_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_677_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v_toFunctor_617_; lean_object* v_toSeq_618_; lean_object* v_toSeqLeft_619_; lean_object* v_toSeqRight_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_675_; 
v_toFunctor_617_ = lean_ctor_get(v_toApplicative_613_, 0);
v_toSeq_618_ = lean_ctor_get(v_toApplicative_613_, 2);
v_toSeqLeft_619_ = lean_ctor_get(v_toApplicative_613_, 3);
v_toSeqRight_620_ = lean_ctor_get(v_toApplicative_613_, 4);
v_isSharedCheck_675_ = !lean_is_exclusive(v_toApplicative_613_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; 
v_unused_676_ = lean_ctor_get(v_toApplicative_613_, 1);
lean_dec(v_unused_676_);
v___x_622_ = v_toApplicative_613_;
v_isShared_623_ = v_isSharedCheck_675_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_toSeqRight_620_);
lean_inc(v_toSeqLeft_619_);
lean_inc(v_toSeq_618_);
lean_inc(v_toFunctor_617_);
lean_dec(v_toApplicative_613_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_675_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___f_624_; lean_object* v___f_625_; lean_object* v___f_626_; lean_object* v___f_627_; lean_object* v___x_628_; lean_object* v___f_629_; lean_object* v___f_630_; lean_object* v___f_631_; lean_object* v___x_633_; 
v___f_624_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
v___f_625_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_617_);
v___f_626_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_626_, 0, v_toFunctor_617_);
v___f_627_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_627_, 0, v_toFunctor_617_);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v___f_626_);
lean_ctor_set(v___x_628_, 1, v___f_627_);
v___f_629_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_629_, 0, v_toSeqRight_620_);
v___f_630_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_630_, 0, v_toSeqLeft_619_);
v___f_631_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_631_, 0, v_toSeq_618_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 4, v___f_629_);
lean_ctor_set(v___x_622_, 3, v___f_630_);
lean_ctor_set(v___x_622_, 2, v___f_631_);
lean_ctor_set(v___x_622_, 1, v___f_624_);
lean_ctor_set(v___x_622_, 0, v___x_628_);
v___x_633_ = v___x_622_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v___f_624_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v___f_631_);
lean_ctor_set(v_reuseFailAlloc_674_, 3, v___f_630_);
lean_ctor_set(v_reuseFailAlloc_674_, 4, v___f_629_);
v___x_633_ = v_reuseFailAlloc_674_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_635_; 
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 1, v___f_625_);
lean_ctor_set(v___x_615_, 0, v___x_633_);
v___x_635_ = v___x_615_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v___f_625_);
v___x_635_ = v_reuseFailAlloc_673_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_636_; lean_object* v_toApplicative_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_671_; 
v___x_636_ = l_StateRefT_x27_instMonad___redArg(v___x_635_);
v_toApplicative_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; 
v_unused_672_ = lean_ctor_get(v___x_636_, 1);
lean_dec(v_unused_672_);
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_671_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_toApplicative_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_671_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v_toFunctor_641_; lean_object* v_toSeq_642_; lean_object* v_toSeqLeft_643_; lean_object* v_toSeqRight_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_669_; 
v_toFunctor_641_ = lean_ctor_get(v_toApplicative_637_, 0);
v_toSeq_642_ = lean_ctor_get(v_toApplicative_637_, 2);
v_toSeqLeft_643_ = lean_ctor_get(v_toApplicative_637_, 3);
v_toSeqRight_644_ = lean_ctor_get(v_toApplicative_637_, 4);
v_isSharedCheck_669_ = !lean_is_exclusive(v_toApplicative_637_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; 
v_unused_670_ = lean_ctor_get(v_toApplicative_637_, 1);
lean_dec(v_unused_670_);
v___x_646_ = v_toApplicative_637_;
v_isShared_647_ = v_isSharedCheck_669_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_toSeqRight_644_);
lean_inc(v_toSeqLeft_643_);
lean_inc(v_toSeq_642_);
lean_inc(v_toFunctor_641_);
lean_dec(v_toApplicative_637_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_669_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___f_648_; lean_object* v___f_649_; lean_object* v___f_650_; lean_object* v___f_651_; lean_object* v___x_652_; lean_object* v___f_653_; lean_object* v___f_654_; lean_object* v___f_655_; lean_object* v___x_657_; 
v___f_648_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
v___f_649_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(v_toFunctor_641_);
v___f_650_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_650_, 0, v_toFunctor_641_);
v___f_651_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_651_, 0, v_toFunctor_641_);
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v___f_650_);
lean_ctor_set(v___x_652_, 1, v___f_651_);
v___f_653_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_653_, 0, v_toSeqRight_644_);
v___f_654_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_654_, 0, v_toSeqLeft_643_);
v___f_655_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_655_, 0, v_toSeq_642_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 4, v___f_653_);
lean_ctor_set(v___x_646_, 3, v___f_654_);
lean_ctor_set(v___x_646_, 2, v___f_655_);
lean_ctor_set(v___x_646_, 1, v___f_648_);
lean_ctor_set(v___x_646_, 0, v___x_652_);
v___x_657_ = v___x_646_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___f_648_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v___f_655_);
lean_ctor_set(v_reuseFailAlloc_668_, 3, v___f_654_);
lean_ctor_set(v_reuseFailAlloc_668_, 4, v___f_653_);
v___x_657_ = v_reuseFailAlloc_668_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_659_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 1, v___f_649_);
lean_ctor_set(v___x_639_, 0, v___x_657_);
v___x_659_ = v___x_639_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v___f_649_);
v___x_659_ = v_reuseFailAlloc_667_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___f_663_; lean_object* v___x_7100__overap_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_660_ = l_StateRefT_x27_instMonad___redArg(v___x_659_);
v___x_661_ = l_Lean_instInhabitedExpr;
v___x_662_ = l_instInhabitedOfMonad___redArg(v___x_660_, v___x_661_);
v___f_663_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_663_, 0, v___x_662_);
v___x_7100__overap_664_ = lean_panic_fn_borrowed(v___f_663_, v_msg_603_);
lean_dec_ref(v___f_663_);
v___x_665_ = lean_box(v___y_604_);
lean_inc(v___y_609_);
lean_inc_ref(v___y_608_);
lean_inc(v___y_607_);
lean_inc_ref(v___y_606_);
lean_inc(v___y_605_);
v___x_666_ = lean_apply_7(v___x_7100__overap_664_, v___x_665_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, lean_box(0));
return v___x_666_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___boxed(lean_object* v_msg_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
uint8_t v___y_7246__boxed_687_; lean_object* v_res_688_; 
v___y_7246__boxed_687_ = lean_unbox(v___y_680_);
v_res_688_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v_msg_679_, v___y_7246__boxed_687_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
return v_res_688_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_692_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_693_ = lean_unsigned_to_nat(20u);
v___x_694_ = lean_unsigned_to_nat(88u);
v___x_695_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__1));
v___x_696_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_697_ = l_mkPanicMessageWithDecl(v___x_696_, v___x_695_, v___x_694_, v___x_693_, v___x_692_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(uint8_t v_pu_698_, lean_object* v_e_699_, uint8_t v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
uint8_t v___x_707_; 
v___x_707_ = l_Lean_Expr_hasFVar(v_e_699_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; 
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v_e_699_);
return v___x_708_;
}
else
{
switch(lean_obj_tag(v_e_699_))
{
case 1:
{
lean_object* v_fvarId_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_fvarId_709_ = lean_ctor_get(v_e_699_, 0);
v___x_710_ = lean_st_ref_get(v_a_701_);
v___x_711_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v___x_710_, v_fvarId_709_);
lean_dec(v___x_710_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v___x_712_; 
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v_e_699_);
return v___x_712_;
}
else
{
lean_object* v_val_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_758_; 
lean_dec_ref_known(v_e_699_, 1);
v_val_713_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_758_ == 0)
{
v___x_715_ = v___x_711_;
v_isShared_716_ = v_isSharedCheck_758_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_val_713_);
lean_dec(v___x_711_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_758_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
switch(lean_obj_tag(v_val_713_))
{
case 0:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_716_ == 0)
{
lean_ctor_set_tag(v___x_715_, 0);
lean_ctor_set(v___x_715_, 0, v___x_717_);
v___x_719_ = v___x_715_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
case 1:
{
lean_object* v_fvarId_721_; lean_object* v___x_722_; 
lean_del_object(v___x_715_);
v_fvarId_721_ = lean_ctor_get(v_val_713_, 0);
lean_inc(v_fvarId_721_);
lean_dec_ref_known(v_val_713_, 1);
v___x_722_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_698_, v_fvarId_721_, v_a_703_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_741_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_741_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_741_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_741_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
if (lean_obj_tag(v_a_723_) == 0)
{
lean_dec(v_fvarId_721_);
goto v___jp_727_;
}
else
{
lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_739_; 
v_isSharedCheck_739_ = !lean_is_exclusive(v_a_723_);
if (v_isSharedCheck_739_ == 0)
{
lean_object* v_unused_740_; 
v_unused_740_ = lean_ctor_get(v_a_723_, 0);
lean_dec(v_unused_740_);
v___x_733_ = v_a_723_;
v_isShared_734_ = v_isSharedCheck_739_;
goto v_resetjp_732_;
}
else
{
lean_dec(v_a_723_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_739_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
if (v___x_707_ == 0)
{
lean_del_object(v___x_733_);
lean_dec(v_fvarId_721_);
goto v___jp_727_;
}
else
{
lean_object* v___x_735_; lean_object* v___x_737_; 
lean_del_object(v___x_725_);
v___x_735_ = l_Lean_Expr_fvar___override(v_fvarId_721_);
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 0);
lean_ctor_set(v___x_733_, 0, v___x_735_);
v___x_737_ = v___x_733_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
v___jp_727_:
{
lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_728_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_728_);
v___x_730_ = v___x_725_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec(v_fvarId_721_);
v_a_742_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_722_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_722_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
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
default: 
{
lean_object* v_expr_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_del_object(v___x_715_);
v_expr_750_ = lean_ctor_get(v_val_713_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v_val_713_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v_val_713_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_expr_750_);
lean_dec(v_val_713_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set_tag(v___x_752_, 0);
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_expr_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_759_; lean_object* v_arg_760_; lean_object* v___x_761_; 
v_fn_759_ = lean_ctor_get(v_e_699_, 0);
v_arg_760_ = lean_ctor_get(v_e_699_, 1);
lean_inc_ref(v_fn_759_);
v___x_761_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_698_, v_fn_759_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_763_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
lean_inc_ref(v_arg_760_);
v___x_763_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_698_, v_arg_760_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_782_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_782_ == 0)
{
v___x_766_ = v___x_763_;
v_isShared_767_ = v_isSharedCheck_782_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_763_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_782_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___y_769_; size_t v___x_774_; size_t v___x_775_; uint8_t v___x_776_; 
v___x_774_ = lean_ptr_addr(v_fn_759_);
v___x_775_ = lean_ptr_addr(v_a_762_);
v___x_776_ = lean_usize_dec_eq(v___x_774_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; 
lean_dec_ref_known(v_e_699_, 2);
v___x_777_ = l_Lean_Expr_app___override(v_a_762_, v_a_764_);
v___y_769_ = v___x_777_;
goto v___jp_768_;
}
else
{
size_t v___x_778_; size_t v___x_779_; uint8_t v___x_780_; 
v___x_778_ = lean_ptr_addr(v_arg_760_);
v___x_779_ = lean_ptr_addr(v_a_764_);
v___x_780_ = lean_usize_dec_eq(v___x_778_, v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
lean_dec_ref_known(v_e_699_, 2);
v___x_781_ = l_Lean_Expr_app___override(v_a_762_, v_a_764_);
v___y_769_ = v___x_781_;
goto v___jp_768_;
}
else
{
lean_dec(v_a_764_);
lean_dec(v_a_762_);
v___y_769_ = v_e_699_;
goto v___jp_768_;
}
}
v___jp_768_:
{
lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_770_ = l_Lean_Expr_headBeta(v___y_769_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_770_);
v___x_772_ = v___x_766_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
else
{
lean_dec(v_a_762_);
lean_dec_ref_known(v_e_699_, 2);
return v___x_763_;
}
}
else
{
lean_dec_ref_known(v_e_699_, 2);
return v___x_761_;
}
}
case 6:
{
lean_object* v_binderName_783_; lean_object* v_binderType_784_; lean_object* v_body_785_; uint8_t v_binderInfo_786_; lean_object* v___x_787_; 
v_binderName_783_ = lean_ctor_get(v_e_699_, 0);
v_binderType_784_ = lean_ctor_get(v_e_699_, 1);
v_body_785_ = lean_ctor_get(v_e_699_, 2);
v_binderInfo_786_ = lean_ctor_get_uint8(v_e_699_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_784_);
v___x_787_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_698_, v_binderType_784_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_789_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref_known(v___x_787_, 1);
lean_inc_ref(v_body_785_);
v___x_789_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_698_, v_body_785_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_816_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_816_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_816_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_816_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
size_t v___x_794_; size_t v___x_795_; uint8_t v___x_796_; 
v___x_794_ = lean_ptr_addr(v_binderType_784_);
v___x_795_ = lean_ptr_addr(v_a_788_);
v___x_796_ = lean_usize_dec_eq(v___x_794_, v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_799_; 
lean_inc(v_binderName_783_);
lean_dec_ref_known(v_e_699_, 3);
v___x_797_ = l_Lean_Expr_lam___override(v_binderName_783_, v_a_788_, v_a_790_, v_binderInfo_786_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_797_);
v___x_799_ = v___x_792_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
else
{
size_t v___x_801_; size_t v___x_802_; uint8_t v___x_803_; 
v___x_801_ = lean_ptr_addr(v_body_785_);
v___x_802_ = lean_ptr_addr(v_a_790_);
v___x_803_ = lean_usize_dec_eq(v___x_801_, v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_806_; 
lean_inc(v_binderName_783_);
lean_dec_ref_known(v_e_699_, 3);
v___x_804_ = l_Lean_Expr_lam___override(v_binderName_783_, v_a_788_, v_a_790_, v_binderInfo_786_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_804_);
v___x_806_ = v___x_792_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
else
{
uint8_t v___x_808_; 
v___x_808_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_786_, v_binderInfo_786_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_811_; 
lean_inc(v_binderName_783_);
lean_dec_ref_known(v_e_699_, 3);
v___x_809_ = l_Lean_Expr_lam___override(v_binderName_783_, v_a_788_, v_a_790_, v_binderInfo_786_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_809_);
v___x_811_ = v___x_792_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
else
{
lean_object* v___x_814_; 
lean_dec(v_a_790_);
lean_dec(v_a_788_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v_e_699_);
v___x_814_ = v___x_792_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_e_699_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
}
else
{
lean_dec(v_a_788_);
lean_dec_ref_known(v_e_699_, 3);
return v___x_789_;
}
}
else
{
lean_dec_ref_known(v_e_699_, 3);
return v___x_787_;
}
}
case 7:
{
lean_object* v_binderName_817_; lean_object* v_binderType_818_; lean_object* v_body_819_; uint8_t v_binderInfo_820_; lean_object* v___x_821_; 
v_binderName_817_ = lean_ctor_get(v_e_699_, 0);
v_binderType_818_ = lean_ctor_get(v_e_699_, 1);
v_body_819_ = lean_ctor_get(v_e_699_, 2);
v_binderInfo_820_ = lean_ctor_get_uint8(v_e_699_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_818_);
v___x_821_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_698_, v_binderType_818_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_823_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref_known(v___x_821_, 1);
lean_inc_ref(v_body_819_);
v___x_823_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_698_, v_body_819_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_850_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_850_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_850_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_850_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
size_t v___x_828_; size_t v___x_829_; uint8_t v___x_830_; 
v___x_828_ = lean_ptr_addr(v_binderType_818_);
v___x_829_ = lean_ptr_addr(v_a_822_);
v___x_830_ = lean_usize_dec_eq(v___x_828_, v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_833_; 
lean_inc(v_binderName_817_);
lean_dec_ref_known(v_e_699_, 3);
v___x_831_ = l_Lean_Expr_forallE___override(v_binderName_817_, v_a_822_, v_a_824_, v_binderInfo_820_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_831_);
v___x_833_ = v___x_826_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
else
{
size_t v___x_835_; size_t v___x_836_; uint8_t v___x_837_; 
v___x_835_ = lean_ptr_addr(v_body_819_);
v___x_836_ = lean_ptr_addr(v_a_824_);
v___x_837_ = lean_usize_dec_eq(v___x_835_, v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_840_; 
lean_inc(v_binderName_817_);
lean_dec_ref_known(v_e_699_, 3);
v___x_838_ = l_Lean_Expr_forallE___override(v_binderName_817_, v_a_822_, v_a_824_, v_binderInfo_820_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_838_);
v___x_840_ = v___x_826_;
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
uint8_t v___x_842_; 
v___x_842_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_820_, v_binderInfo_820_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; lean_object* v___x_845_; 
lean_inc(v_binderName_817_);
lean_dec_ref_known(v_e_699_, 3);
v___x_843_ = l_Lean_Expr_forallE___override(v_binderName_817_, v_a_822_, v_a_824_, v_binderInfo_820_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_843_);
v___x_845_ = v___x_826_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
else
{
lean_object* v___x_848_; 
lean_dec(v_a_824_);
lean_dec(v_a_822_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v_e_699_);
v___x_848_ = v___x_826_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_e_699_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
}
else
{
lean_dec(v_a_822_);
lean_dec_ref_known(v_e_699_, 3);
return v___x_823_;
}
}
else
{
lean_dec_ref_known(v_e_699_, 3);
return v___x_821_;
}
}
case 8:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec_ref_known(v_e_699_, 4);
v___x_851_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3, &l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3);
v___x_852_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v___x_851_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
return v___x_852_;
}
case 10:
{
lean_object* v_data_853_; lean_object* v_expr_854_; lean_object* v___x_855_; 
v_data_853_ = lean_ctor_get(v_e_699_, 0);
v_expr_854_ = lean_ctor_get(v_e_699_, 1);
lean_inc_ref(v_expr_854_);
v___x_855_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_698_, v_expr_854_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_870_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_870_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_870_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_870_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
size_t v___x_860_; size_t v___x_861_; uint8_t v___x_862_; 
v___x_860_ = lean_ptr_addr(v_expr_854_);
v___x_861_ = lean_ptr_addr(v_a_856_);
v___x_862_ = lean_usize_dec_eq(v___x_860_, v___x_861_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; lean_object* v___x_865_; 
lean_inc(v_data_853_);
lean_dec_ref_known(v_e_699_, 2);
v___x_863_ = l_Lean_Expr_mdata___override(v_data_853_, v_a_856_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_863_);
v___x_865_ = v___x_858_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
else
{
lean_object* v___x_868_; 
lean_dec(v_a_856_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v_e_699_);
v___x_868_ = v___x_858_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_e_699_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_699_, 2);
return v___x_855_;
}
}
case 11:
{
lean_object* v_typeName_871_; lean_object* v_idx_872_; lean_object* v_struct_873_; lean_object* v___x_874_; 
v_typeName_871_ = lean_ctor_get(v_e_699_, 0);
v_idx_872_ = lean_ctor_get(v_e_699_, 1);
v_struct_873_ = lean_ctor_get(v_e_699_, 2);
lean_inc_ref(v_struct_873_);
v___x_874_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_698_, v_struct_873_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_889_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_889_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_889_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_889_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
size_t v___x_879_; size_t v___x_880_; uint8_t v___x_881_; 
v___x_879_ = lean_ptr_addr(v_struct_873_);
v___x_880_ = lean_ptr_addr(v_a_875_);
v___x_881_ = lean_usize_dec_eq(v___x_879_, v___x_880_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_884_; 
lean_inc(v_idx_872_);
lean_inc(v_typeName_871_);
lean_dec_ref_known(v_e_699_, 3);
v___x_882_ = l_Lean_Expr_proj___override(v_typeName_871_, v_idx_872_, v_a_875_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_882_);
v___x_884_ = v___x_877_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
else
{
lean_object* v___x_887_; 
lean_dec(v_a_875_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v_e_699_);
v___x_887_ = v___x_877_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_e_699_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_699_, 3);
return v___x_874_;
}
}
default: 
{
lean_object* v___x_890_; 
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v_e_699_);
return v___x_890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(uint8_t v_pu_891_, lean_object* v_e_892_, uint8_t v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
if (lean_obj_tag(v_e_892_) == 5)
{
lean_object* v_fn_900_; lean_object* v_arg_901_; lean_object* v___x_902_; 
v_fn_900_ = lean_ctor_get(v_e_892_, 0);
v_arg_901_ = lean_ctor_get(v_e_892_, 1);
lean_inc_ref(v_fn_900_);
v___x_902_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_891_, v_fn_900_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_904_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref_known(v___x_902_, 1);
lean_inc_ref(v_arg_901_);
v___x_904_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_891_, v_arg_901_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_926_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_926_ == 0)
{
v___x_907_ = v___x_904_;
v_isShared_908_ = v_isSharedCheck_926_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_904_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_926_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
size_t v___x_909_; size_t v___x_910_; uint8_t v___x_911_; 
v___x_909_ = lean_ptr_addr(v_fn_900_);
v___x_910_ = lean_ptr_addr(v_a_903_);
v___x_911_ = lean_usize_dec_eq(v___x_909_, v___x_910_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; lean_object* v___x_914_; 
lean_dec_ref_known(v_e_892_, 2);
v___x_912_ = l_Lean_Expr_app___override(v_a_903_, v_a_905_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_912_);
v___x_914_ = v___x_907_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
else
{
size_t v___x_916_; size_t v___x_917_; uint8_t v___x_918_; 
v___x_916_ = lean_ptr_addr(v_arg_901_);
v___x_917_ = lean_ptr_addr(v_a_905_);
v___x_918_ = lean_usize_dec_eq(v___x_916_, v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; lean_object* v___x_921_; 
lean_dec_ref_known(v_e_892_, 2);
v___x_919_ = l_Lean_Expr_app___override(v_a_903_, v_a_905_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_919_);
v___x_921_ = v___x_907_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
else
{
lean_object* v___x_924_; 
lean_dec(v_a_905_);
lean_dec(v_a_903_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v_e_892_);
v___x_924_ = v___x_907_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_e_892_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
else
{
lean_dec(v_a_903_);
lean_dec_ref_known(v_e_892_, 2);
return v___x_904_;
}
}
else
{
lean_dec_ref_known(v_e_892_, 2);
return v___x_902_;
}
}
else
{
lean_object* v___x_927_; 
v___x_927_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_891_, v_e_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp___boxed(lean_object* v_pu_928_, lean_object* v_e_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
uint8_t v_pu_boxed_937_; uint8_t v_a_boxed_938_; lean_object* v_res_939_; 
v_pu_boxed_937_ = lean_unbox(v_pu_928_);
v_a_boxed_938_ = lean_unbox(v_a_930_);
v_res_939_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_boxed_937_, v_e_929_, v_a_boxed_938_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_a_931_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___boxed(lean_object* v_pu_940_, lean_object* v_e_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
uint8_t v_pu_boxed_949_; uint8_t v_a_boxed_950_; lean_object* v_res_951_; 
v_pu_boxed_949_ = lean_unbox(v_pu_940_);
v_a_boxed_950_ = lean_unbox(v_a_942_);
v_res_951_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_boxed_949_, v_e_941_, v_a_boxed_950_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(lean_object* v_00_u03b2_952_, lean_object* v_m_953_, lean_object* v_a_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v_m_953_, v_a_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___boxed(lean_object* v_00_u03b2_956_, lean_object* v_m_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(v_00_u03b2_956_, v_m_957_, v_a_958_);
lean_dec(v_a_958_);
lean_dec_ref(v_m_957_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(lean_object* v_00_u03b2_960_, lean_object* v_a_961_, lean_object* v_x_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_961_, v_x_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_964_, lean_object* v_a_965_, lean_object* v_x_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(v_00_u03b2_964_, v_a_965_, v_x_966_);
lean_dec(v_x_966_);
lean_dec(v_a_965_);
return v_res_967_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___closed__0(void){
_start:
{
uint8_t v___x_968_; lean_object* v___x_969_; 
v___x_968_ = 1;
v___x_969_ = l_Lean_Compiler_LCNF_Purity_ctorIdx(v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(uint8_t v_pu_970_, lean_object* v_e_971_, uint8_t v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_979_ = l_Lean_Compiler_LCNF_Purity_ctorIdx(v_pu_970_);
v___x_980_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___closed__0, &l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___closed__0);
v___x_981_ = lean_nat_dec_eq(v___x_979_, v___x_980_);
lean_dec(v___x_979_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
v___x_982_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_970_, v_e_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
return v___x_982_;
}
else
{
lean_object* v___x_983_; 
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v_e_971_);
return v___x_983_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___boxed(lean_object* v_pu_984_, lean_object* v_e_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
uint8_t v_pu_boxed_993_; uint8_t v_a_boxed_994_; lean_object* v_res_995_; 
v_pu_boxed_993_ = lean_unbox(v_pu_984_);
v_a_boxed_994_ = lean_unbox(v_a_986_);
v_res_995_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_boxed_993_, v_e_985_, v_a_boxed_994_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t v_pu_996_, lean_object* v_p_997_, uint8_t v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v_fvarId_1005_; lean_object* v_binderName_1006_; lean_object* v_type_1007_; uint8_t v_borrow_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1056_; 
v_fvarId_1005_ = lean_ctor_get(v_p_997_, 0);
v_binderName_1006_ = lean_ctor_get(v_p_997_, 1);
v_type_1007_ = lean_ctor_get(v_p_997_, 2);
v_borrow_1008_ = lean_ctor_get_uint8(v_p_997_, sizeof(void*)*3);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_p_997_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1010_ = v_p_997_;
v_isShared_1011_ = v_isSharedCheck_1056_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_type_1007_);
lean_inc(v_binderName_1006_);
lean_inc(v_fvarId_1005_);
lean_dec(v_p_997_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1056_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; lean_object* v_a_1013_; lean_object* v___x_1014_; 
v___x_1012_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_1006_, v_a_998_, v_a_1001_);
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref(v___x_1012_);
v___x_1014_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_996_, v_type_1007_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1016_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___x_1014_, 1);
v___x_1016_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_1005_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1039_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1019_ = v___x_1016_;
v_isShared_1020_ = v_isSharedCheck_1039_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1016_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1039_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v_lctx_1022_; lean_object* v_nextIdx_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1038_; 
v___x_1021_ = lean_st_ref_take(v_a_1001_);
v_lctx_1022_ = lean_ctor_get(v___x_1021_, 0);
v_nextIdx_1023_ = lean_ctor_get(v___x_1021_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1025_ = v___x_1021_;
v_isShared_1026_ = v_isSharedCheck_1038_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_nextIdx_1023_);
lean_inc(v_lctx_1022_);
lean_dec(v___x_1021_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1038_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 2, v_a_1015_);
lean_ctor_set(v___x_1010_, 1, v_a_1013_);
lean_ctor_set(v___x_1010_, 0, v_a_1017_);
v___x_1028_ = v___x_1010_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1017_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_a_1013_);
lean_ctor_set(v_reuseFailAlloc_1037_, 2, v_a_1015_);
lean_ctor_set_uint8(v_reuseFailAlloc_1037_, sizeof(void*)*3, v_borrow_1008_);
v___x_1028_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
lean_inc_ref(v___x_1028_);
v___x_1029_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_996_, v_lctx_1022_, v___x_1028_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1029_);
v___x_1031_ = v___x_1025_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_nextIdx_1023_);
v___x_1031_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1032_ = lean_st_ref_put(v_a_1001_, v___x_1031_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v___x_1028_);
v___x_1034_ = v___x_1019_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1028_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_dec(v_a_1015_);
lean_dec(v_a_1013_);
lean_del_object(v___x_1010_);
v_a_1040_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1016_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1016_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec(v_a_1013_);
lean_del_object(v___x_1010_);
lean_dec(v_fvarId_1005_);
v_a_1048_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1014_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1014_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(lean_object* v_pu_1057_, lean_object* v_p_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
uint8_t v_pu_boxed_1066_; uint8_t v_a_boxed_1067_; lean_object* v_res_1068_; 
v_pu_boxed_1066_ = lean_unbox(v_pu_1057_);
v_a_boxed_1067_ = lean_unbox(v_a_1059_);
v_res_1068_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_boxed_1066_, v_p_1058_, v_a_boxed_1067_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg(uint8_t v_pu_1069_, lean_object* v_arg_1070_, uint8_t v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
switch(lean_obj_tag(v_arg_1070_))
{
case 0:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_arg_1070_);
return v___x_1078_;
}
case 1:
{
lean_object* v_fvarId_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v_fvarId_1079_ = lean_ctor_get(v_arg_1070_, 0);
v___x_1080_ = lean_st_ref_get(v_a_1072_);
v___x_1081_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v___x_1080_, v_fvarId_1079_);
lean_dec(v___x_1080_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v_arg_1070_);
return v___x_1082_;
}
else
{
lean_object* v_val_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref_known(v_arg_1070_, 1);
v_val_1083_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1085_ = v___x_1081_;
v_isShared_1086_ = v_isSharedCheck_1113_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_val_1083_);
lean_dec(v___x_1081_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1113_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
switch(lean_obj_tag(v_val_1083_))
{
case 0:
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1087_ = lean_box(0);
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1087_);
v___x_1089_ = v___x_1085_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
case 1:
{
lean_object* v_fvarId_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1101_; 
v_fvarId_1091_ = lean_ctor_get(v_val_1083_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_val_1083_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1093_ = v_val_1083_;
v_isShared_1094_ = v_isSharedCheck_1101_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_fvarId_1091_);
lean_dec(v_val_1083_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1101_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_fvarId_1091_);
v___x_1096_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1098_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1096_);
v___x_1098_ = v___x_1085_;
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
}
}
default: 
{
lean_object* v_expr_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1112_; 
v_expr_1102_ = lean_ctor_get(v_val_1083_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_val_1083_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1104_ = v_val_1083_;
v_isShared_1105_ = v_isSharedCheck_1112_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_expr_1102_);
lean_dec(v_val_1083_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1112_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_expr_1102_);
v___x_1107_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1109_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1107_);
v___x_1109_ = v___x_1085_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
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
lean_object* v_expr_1114_; lean_object* v___x_1115_; 
v_expr_1114_ = lean_ctor_get(v_arg_1070_, 0);
lean_inc_ref(v_expr_1114_);
v___x_1115_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1069_, v_expr_1114_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1124_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1124_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1124_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1120_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1069_, v_arg_1070_, v_a_1116_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v___x_1120_);
v___x_1122_ = v___x_1118_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec_ref_known(v_arg_1070_, 1);
v_a_1125_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1115_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1115_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg___boxed(lean_object* v_pu_1133_, lean_object* v_arg_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
uint8_t v_pu_boxed_1142_; uint8_t v_a_boxed_1143_; lean_object* v_res_1144_; 
v_pu_boxed_1142_ = lean_unbox(v_pu_1133_);
v_a_boxed_1143_ = lean_unbox(v_a_1135_);
v_res_1144_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_boxed_1142_, v_arg_1134_, v_a_boxed_1143_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(uint8_t v_pu_1145_, size_t v_sz_1146_, size_t v_i_1147_, lean_object* v_bs_1148_, uint8_t v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
uint8_t v___x_1156_; 
v___x_1156_ = lean_usize_dec_lt(v_i_1147_, v_sz_1146_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v_bs_1148_);
return v___x_1157_;
}
else
{
lean_object* v_v_1158_; lean_object* v___x_1159_; 
v_v_1158_ = lean_array_uget_borrowed(v_bs_1148_, v_i_1147_);
lean_inc(v_v_1158_);
v___x_1159_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_1145_, v_v_1158_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1161_; lean_object* v_bs_x27_1162_; size_t v___x_1163_; size_t v___x_1164_; lean_object* v___x_1165_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
lean_dec_ref_known(v___x_1159_, 1);
v___x_1161_ = lean_unsigned_to_nat(0u);
v_bs_x27_1162_ = lean_array_uset(v_bs_1148_, v_i_1147_, v___x_1161_);
v___x_1163_ = ((size_t)1ULL);
v___x_1164_ = lean_usize_add(v_i_1147_, v___x_1163_);
v___x_1165_ = lean_array_uset(v_bs_x27_1162_, v_i_1147_, v_a_1160_);
v_i_1147_ = v___x_1164_;
v_bs_1148_ = v___x_1165_;
goto _start;
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec_ref(v_bs_1148_);
v_a_1167_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1159_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1159_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0___boxed(lean_object* v_pu_1175_, lean_object* v_sz_1176_, lean_object* v_i_1177_, lean_object* v_bs_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
uint8_t v_pu_boxed_1186_; size_t v_sz_boxed_1187_; size_t v_i_boxed_1188_; uint8_t v___y_339__boxed_1189_; lean_object* v_res_1190_; 
v_pu_boxed_1186_ = lean_unbox(v_pu_1175_);
v_sz_boxed_1187_ = lean_unbox_usize(v_sz_1176_);
lean_dec(v_sz_1176_);
v_i_boxed_1188_ = lean_unbox_usize(v_i_1177_);
lean_dec(v_i_1177_);
v___y_339__boxed_1189_ = lean_unbox(v___y_1179_);
v_res_1190_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_boxed_1186_, v_sz_boxed_1187_, v_i_boxed_1188_, v_bs_1178_, v___y_339__boxed_1189_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs(uint8_t v_pu_1191_, lean_object* v_args_1192_, uint8_t v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_){
_start:
{
size_t v_sz_1200_; size_t v___x_1201_; lean_object* v___x_1202_; 
v_sz_1200_ = lean_array_size(v_args_1192_);
v___x_1201_ = ((size_t)0ULL);
v___x_1202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_1191_, v_sz_1200_, v___x_1201_, v_args_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs___boxed(lean_object* v_pu_1203_, lean_object* v_args_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
uint8_t v_pu_boxed_1212_; uint8_t v_a_boxed_1213_; lean_object* v_res_1214_; 
v_pu_boxed_1212_ = lean_unbox(v_pu_1203_);
v_a_boxed_1213_ = lean_unbox(v_a_1205_);
v_res_1214_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_boxed_1212_, v_args_1204_, v_a_boxed_1213_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
lean_dec(v_a_1208_);
lean_dec_ref(v_a_1207_);
lean_dec(v_a_1206_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(uint8_t v_pu_1215_, lean_object* v_e_1216_, uint8_t v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v_fvarId_1225_; lean_object* v___y_1226_; lean_object* v_args_1242_; uint8_t v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; 
switch(lean_obj_tag(v_e_1216_))
{
case 2:
{
lean_object* v_struct_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; lean_object* v___x_1270_; 
v_struct_1267_ = lean_ctor_get(v_e_1216_, 2);
v___x_1268_ = lean_st_ref_get(v_a_1218_);
v___x_1269_ = 1;
lean_inc(v_struct_1267_);
v___x_1270_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1268_, v_struct_1267_, v___x_1269_);
lean_dec(v___x_1268_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_fvarId_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1279_; 
v_fvarId_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1279_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_fvarId_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1279_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1275_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1215_, v_e_1216_, v_fvarId_1271_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v___x_1275_);
v___x_1277_ = v___x_1273_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec_ref_known(v_e_1216_, 3);
v___x_1280_ = lean_box(1);
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
return v___x_1281_;
}
}
case 3:
{
lean_object* v_args_1282_; lean_object* v___x_1283_; 
v_args_1282_ = lean_ctor_get(v_e_1216_, 2);
lean_inc_ref(v_args_1282_);
v___x_1283_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1215_, v_args_1282_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1292_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1292_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1292_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1288_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1215_, v_e_1216_, v_a_1284_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1288_);
v___x_1290_ = v___x_1286_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec_ref_known(v_e_1216_, 3);
v_a_1293_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1283_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1283_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
case 4:
{
lean_object* v_fvarId_1301_; lean_object* v_args_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; lean_object* v___x_1305_; 
v_fvarId_1301_ = lean_ctor_get(v_e_1216_, 0);
v_args_1302_ = lean_ctor_get(v_e_1216_, 1);
v___x_1303_ = lean_st_ref_get(v_a_1218_);
v___x_1304_ = 1;
lean_inc(v_fvarId_1301_);
v___x_1305_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1303_, v_fvarId_1301_, v___x_1304_);
lean_dec(v___x_1303_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_fvarId_1306_; lean_object* v___x_1307_; 
v_fvarId_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_fvarId_1306_);
lean_dec_ref_known(v___x_1305_, 1);
lean_inc_ref(v_args_1302_);
v___x_1307_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1215_, v_args_1302_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1316_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_1215_, v_e_1216_, v_fvarId_1306_, v_a_1308_);
lean_dec_ref_known(v_e_1216_, 2);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1312_);
v___x_1314_ = v___x_1310_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec(v_fvarId_1306_);
lean_dec_ref_known(v_e_1216_, 2);
v_a_1317_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1307_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1307_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_dec_ref_known(v_e_1216_, 2);
v___x_1325_ = lean_box(1);
v___x_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
return v___x_1326_;
}
}
case 5:
{
lean_object* v_args_1327_; lean_object* v___x_1328_; 
v_args_1327_ = lean_ctor_get(v_e_1216_, 1);
lean_inc_ref(v_args_1327_);
v___x_1328_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1215_, v_args_1327_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1337_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1337_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1337_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1333_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1215_, v_e_1216_, v_a_1329_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1333_);
v___x_1335_ = v___x_1331_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec_ref_known(v_e_1216_, 2);
v_a_1338_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1328_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1328_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
case 6:
{
lean_object* v_var_1346_; 
v_var_1346_ = lean_ctor_get(v_e_1216_, 1);
lean_inc(v_var_1346_);
v_fvarId_1225_ = v_var_1346_;
v___y_1226_ = v_a_1218_;
goto v___jp_1224_;
}
case 7:
{
lean_object* v_var_1347_; 
v_var_1347_ = lean_ctor_get(v_e_1216_, 1);
lean_inc(v_var_1347_);
v_fvarId_1225_ = v_var_1347_;
v___y_1226_ = v_a_1218_;
goto v___jp_1224_;
}
case 8:
{
lean_object* v_var_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; lean_object* v___x_1351_; 
v_var_1348_ = lean_ctor_get(v_e_1216_, 2);
v___x_1349_ = lean_st_ref_get(v_a_1218_);
v___x_1350_ = 1;
lean_inc(v_var_1348_);
v___x_1351_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1349_, v_var_1348_, v___x_1350_);
lean_dec(v___x_1349_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_fvarId_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1360_; 
v_fvarId_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_fvarId_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1215_, v_e_1216_, v_fvarId_1352_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1356_);
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_dec_ref_known(v_e_1216_, 3);
v___x_1361_ = lean_box(1);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
return v___x_1362_;
}
}
case 9:
{
lean_object* v_args_1363_; 
v_args_1363_ = lean_ctor_get(v_e_1216_, 1);
lean_inc_ref(v_args_1363_);
v_args_1242_ = v_args_1363_;
v___y_1243_ = v_a_1217_;
v___y_1244_ = v_a_1218_;
v___y_1245_ = v_a_1219_;
v___y_1246_ = v_a_1220_;
v___y_1247_ = v_a_1221_;
v___y_1248_ = v_a_1222_;
goto v___jp_1241_;
}
case 10:
{
lean_object* v_args_1364_; 
v_args_1364_ = lean_ctor_get(v_e_1216_, 1);
lean_inc_ref(v_args_1364_);
v_args_1242_ = v_args_1364_;
v___y_1243_ = v_a_1217_;
v___y_1244_ = v_a_1218_;
v___y_1245_ = v_a_1219_;
v___y_1246_ = v_a_1220_;
v___y_1247_ = v_a_1221_;
v___y_1248_ = v_a_1222_;
goto v___jp_1241_;
}
case 11:
{
lean_object* v_n_1365_; lean_object* v_var_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; lean_object* v___x_1369_; 
v_n_1365_ = lean_ctor_get(v_e_1216_, 0);
lean_inc(v_n_1365_);
v_var_1366_ = lean_ctor_get(v_e_1216_, 1);
v___x_1367_ = lean_st_ref_get(v_a_1218_);
v___x_1368_ = 1;
lean_inc(v_var_1366_);
v___x_1369_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1367_, v_var_1366_, v___x_1368_);
lean_dec(v___x_1367_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_fvarId_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1378_; 
v_fvarId_1370_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1372_ = v___x_1369_;
v_isShared_1373_ = v_isSharedCheck_1378_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_fvarId_1370_);
lean_dec(v___x_1369_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1378_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1374_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_1215_, v_e_1216_, v_n_1365_, v_fvarId_1370_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1374_);
v___x_1376_ = v___x_1372_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
lean_dec(v_n_1365_);
lean_dec_ref_known(v_e_1216_, 2);
v___x_1379_ = lean_box(1);
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
return v___x_1380_;
}
}
case 12:
{
lean_object* v_var_1381_; lean_object* v_i_1382_; uint8_t v_updateHeader_1383_; lean_object* v_args_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; lean_object* v___x_1387_; 
v_var_1381_ = lean_ctor_get(v_e_1216_, 0);
v_i_1382_ = lean_ctor_get(v_e_1216_, 1);
lean_inc_ref(v_i_1382_);
v_updateHeader_1383_ = lean_ctor_get_uint8(v_e_1216_, sizeof(void*)*3);
v_args_1384_ = lean_ctor_get(v_e_1216_, 2);
v___x_1385_ = lean_st_ref_get(v_a_1218_);
v___x_1386_ = 1;
lean_inc(v_var_1381_);
v___x_1387_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1385_, v_var_1381_, v___x_1386_);
lean_dec(v___x_1385_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_fvarId_1388_; lean_object* v___x_1389_; 
v_fvarId_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_fvarId_1388_);
lean_dec_ref_known(v___x_1387_, 1);
lean_inc_ref(v_args_1384_);
v___x_1389_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1215_, v_args_1384_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1398_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1392_ = v___x_1389_;
v_isShared_1393_ = v_isSharedCheck_1398_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1398_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1394_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_1215_, v_e_1216_, v_fvarId_1388_, v_i_1382_, v_updateHeader_1383_, v_a_1390_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1394_);
v___x_1396_ = v___x_1392_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_dec(v_fvarId_1388_);
lean_dec_ref(v_i_1382_);
lean_dec_ref_known(v_e_1216_, 3);
v_a_1399_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1389_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1389_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
else
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
lean_dec_ref(v_i_1382_);
lean_dec_ref_known(v_e_1216_, 3);
v___x_1407_ = lean_box(1);
v___x_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
return v___x_1408_;
}
}
case 13:
{
lean_object* v_ty_1409_; lean_object* v_fvarId_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; lean_object* v___x_1413_; 
v_ty_1409_ = lean_ctor_get(v_e_1216_, 0);
lean_inc_ref(v_ty_1409_);
v_fvarId_1410_ = lean_ctor_get(v_e_1216_, 1);
v___x_1411_ = lean_st_ref_get(v_a_1218_);
v___x_1412_ = 1;
lean_inc(v_fvarId_1410_);
v___x_1413_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1411_, v_fvarId_1410_, v___x_1412_);
lean_dec(v___x_1411_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_fvarId_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1422_; 
v_fvarId_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_fvarId_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1418_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_1215_, v_e_1216_, v_ty_1409_, v_fvarId_1414_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1418_);
v___x_1420_ = v___x_1416_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_dec_ref(v_ty_1409_);
lean_dec_ref_known(v_e_1216_, 2);
v___x_1423_ = lean_box(1);
v___x_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
return v___x_1424_;
}
}
case 14:
{
lean_object* v_fvarId_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; lean_object* v___x_1428_; 
v_fvarId_1425_ = lean_ctor_get(v_e_1216_, 0);
v___x_1426_ = lean_st_ref_get(v_a_1218_);
v___x_1427_ = 1;
lean_inc(v_fvarId_1425_);
v___x_1428_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1426_, v_fvarId_1425_, v___x_1427_);
lean_dec(v___x_1426_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_fvarId_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1437_; 
v_fvarId_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_fvarId_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1433_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_1215_, v_e_1216_, v_fvarId_1429_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1433_);
v___x_1435_ = v___x_1431_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
else
{
lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1445_; 
v_isSharedCheck_1445_ = !lean_is_exclusive(v_e_1216_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; 
v_unused_1446_ = lean_ctor_get(v_e_1216_, 0);
lean_dec(v_unused_1446_);
v___x_1439_ = v_e_1216_;
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
else
{
lean_dec(v_e_1216_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1441_ = lean_box(1);
if (v_isShared_1440_ == 0)
{
lean_ctor_set_tag(v___x_1439_, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1441_);
v___x_1443_ = v___x_1439_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
case 15:
{
lean_object* v_fvarId_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; lean_object* v___x_1450_; 
v_fvarId_1447_ = lean_ctor_get(v_e_1216_, 0);
v___x_1448_ = lean_st_ref_get(v_a_1218_);
v___x_1449_ = 1;
lean_inc(v_fvarId_1447_);
v___x_1450_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1448_, v_fvarId_1447_, v___x_1449_);
lean_dec(v___x_1448_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_fvarId_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1459_; 
v_fvarId_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1459_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_fvarId_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1459_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1455_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_1215_, v_e_1216_, v_fvarId_1451_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1455_);
v___x_1457_ = v___x_1453_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
else
{
lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1467_; 
v_isSharedCheck_1467_ = !lean_is_exclusive(v_e_1216_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; 
v_unused_1468_ = lean_ctor_get(v_e_1216_, 0);
lean_dec(v_unused_1468_);
v___x_1461_ = v_e_1216_;
v_isShared_1462_ = v_isSharedCheck_1467_;
goto v_resetjp_1460_;
}
else
{
lean_dec(v_e_1216_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1467_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1463_ = lean_box(1);
if (v_isShared_1462_ == 0)
{
lean_ctor_set_tag(v___x_1461_, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1463_);
v___x_1465_ = v___x_1461_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
default: 
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v_e_1216_);
return v___x_1469_;
}
}
v___jp_1224_:
{
lean_object* v___x_1227_; uint8_t v___x_1228_; lean_object* v___x_1229_; 
v___x_1227_ = lean_st_ref_get(v___y_1226_);
v___x_1228_ = 1;
v___x_1229_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1227_, v_fvarId_1225_, v___x_1228_);
lean_dec(v___x_1227_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_fvarId_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1238_; 
v_fvarId_1230_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1232_ = v___x_1229_;
v_isShared_1233_ = v_isSharedCheck_1238_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_fvarId_1230_);
lean_dec(v___x_1229_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1238_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1234_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1215_, v_e_1216_, v_fvarId_1230_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___x_1234_);
v___x_1236_ = v___x_1232_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_dec(v_e_1216_);
v___x_1239_ = lean_box(1);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
}
v___jp_1241_:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1215_, v_args_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1258_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1258_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1258_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1254_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1215_, v_e_1216_, v_a_1250_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v___x_1254_);
v___x_1256_ = v___x_1252_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec(v_e_1216_);
v_a_1259_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1249_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1249_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue___boxed(lean_object* v_pu_1470_, lean_object* v_e_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
uint8_t v_pu_boxed_1479_; uint8_t v_a_boxed_1480_; lean_object* v_res_1481_; 
v_pu_boxed_1479_ = lean_unbox(v_pu_1470_);
v_a_boxed_1480_ = lean_unbox(v_a_1472_);
v_res_1481_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_boxed_1479_, v_e_1471_, v_a_boxed_1480_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
lean_dec(v_a_1473_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(uint8_t v_pu_1482_, lean_object* v_decl_1483_, uint8_t v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v_fvarId_1491_; lean_object* v_binderName_1492_; lean_object* v_type_1493_; lean_object* v_value_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1552_; 
v_fvarId_1491_ = lean_ctor_get(v_decl_1483_, 0);
v_binderName_1492_ = lean_ctor_get(v_decl_1483_, 1);
v_type_1493_ = lean_ctor_get(v_decl_1483_, 2);
v_value_1494_ = lean_ctor_get(v_decl_1483_, 3);
v_isSharedCheck_1552_ = !lean_is_exclusive(v_decl_1483_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1496_ = v_decl_1483_;
v_isShared_1497_ = v_isSharedCheck_1552_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_value_1494_);
lean_inc(v_type_1493_);
lean_inc(v_binderName_1492_);
lean_inc(v_fvarId_1491_);
lean_dec(v_decl_1483_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1552_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v_a_1499_; lean_object* v___x_1500_; 
v___x_1498_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_1492_, v_a_1484_, v_a_1487_);
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1499_);
lean_dec_ref(v___x_1498_);
v___x_1500_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1482_, v_type_1493_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1502_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
lean_dec_ref_known(v___x_1500_, 1);
v___x_1502_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_1482_, v_value_1494_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1504_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1503_);
lean_dec_ref_known(v___x_1502_, 1);
v___x_1504_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_1491_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1527_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1507_ = v___x_1504_;
v_isShared_1508_ = v_isSharedCheck_1527_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1504_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1527_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v_lctx_1510_; lean_object* v_nextIdx_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1526_; 
v___x_1509_ = lean_st_ref_take(v_a_1487_);
v_lctx_1510_ = lean_ctor_get(v___x_1509_, 0);
v_nextIdx_1511_ = lean_ctor_get(v___x_1509_, 1);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1513_ = v___x_1509_;
v_isShared_1514_ = v_isSharedCheck_1526_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_nextIdx_1511_);
lean_inc(v_lctx_1510_);
lean_dec(v___x_1509_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1526_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 3, v_a_1503_);
lean_ctor_set(v___x_1496_, 2, v_a_1501_);
lean_ctor_set(v___x_1496_, 1, v_a_1499_);
lean_ctor_set(v___x_1496_, 0, v_a_1505_);
v___x_1516_ = v___x_1496_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1505_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_a_1499_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_a_1501_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v_a_1503_);
v___x_1516_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1517_; lean_object* v___x_1519_; 
lean_inc_ref(v___x_1516_);
v___x_1517_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_1482_, v_lctx_1510_, v___x_1516_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1517_);
v___x_1519_ = v___x_1513_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_nextIdx_1511_);
v___x_1519_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1520_ = lean_st_ref_put(v_a_1487_, v___x_1519_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1516_);
v___x_1522_ = v___x_1507_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1516_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec(v_a_1503_);
lean_dec(v_a_1501_);
lean_dec(v_a_1499_);
lean_del_object(v___x_1496_);
v_a_1528_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1504_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1504_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
lean_dec(v_a_1501_);
lean_dec(v_a_1499_);
lean_del_object(v___x_1496_);
lean_dec(v_fvarId_1491_);
v_a_1536_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1502_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1502_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
lean_dec(v_a_1499_);
lean_del_object(v___x_1496_);
lean_dec(v_value_1494_);
lean_dec(v_fvarId_1491_);
v_a_1544_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1500_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1500_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(lean_object* v_pu_1553_, lean_object* v_decl_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
uint8_t v_pu_boxed_1562_; uint8_t v_a_boxed_1563_; lean_object* v_res_1564_; 
v_pu_boxed_1562_ = lean_unbox(v_pu_1553_);
v_a_boxed_1563_ = lean_unbox(v_a_1555_);
v_res_1564_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_boxed_1562_, v_decl_1554_, v_a_boxed_1563_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(uint8_t v_pu_1565_, size_t v_sz_1566_, size_t v_i_1567_, lean_object* v_bs_1568_, uint8_t v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
uint8_t v___x_1576_; 
v___x_1576_ = lean_usize_dec_lt(v_i_1567_, v_sz_1566_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1577_, 0, v_bs_1568_);
return v___x_1577_;
}
else
{
lean_object* v_v_1578_; lean_object* v___x_1579_; 
v_v_1578_ = lean_array_uget_borrowed(v_bs_1568_, v_i_1567_);
lean_inc(v_v_1578_);
v___x_1579_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_1565_, v_v_1578_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1581_; lean_object* v_bs_x27_1582_; size_t v___x_1583_; size_t v___x_1584_; lean_object* v___x_1585_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v___x_1581_ = lean_unsigned_to_nat(0u);
v_bs_x27_1582_ = lean_array_uset(v_bs_1568_, v_i_1567_, v___x_1581_);
v___x_1583_ = ((size_t)1ULL);
v___x_1584_ = lean_usize_add(v_i_1567_, v___x_1583_);
v___x_1585_ = lean_array_uset(v_bs_x27_1582_, v_i_1567_, v_a_1580_);
v_i_1567_ = v___x_1584_;
v_bs_1568_ = v___x_1585_;
goto _start;
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec_ref(v_bs_1568_);
v_a_1587_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1579_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1579_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0___boxed(lean_object* v_pu_1595_, lean_object* v_sz_1596_, lean_object* v_i_1597_, lean_object* v_bs_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
uint8_t v_pu_boxed_1606_; size_t v_sz_boxed_1607_; size_t v_i_boxed_1608_; uint8_t v___y_26864__boxed_1609_; lean_object* v_res_1610_; 
v_pu_boxed_1606_ = lean_unbox(v_pu_1595_);
v_sz_boxed_1607_ = lean_unbox_usize(v_sz_1596_);
lean_dec(v_sz_1596_);
v_i_boxed_1608_ = lean_unbox_usize(v_i_1597_);
lean_dec(v_i_1597_);
v___y_26864__boxed_1609_ = lean_unbox(v___y_1599_);
v_res_1610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_boxed_1606_, v_sz_boxed_1607_, v_i_boxed_1608_, v_bs_1598_, v___y_26864__boxed_1609_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(uint8_t v_pu_1611_, size_t v_sz_1612_, size_t v_i_1613_, lean_object* v_bs_1614_, uint8_t v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
uint8_t v___x_1622_; 
v___x_1622_ = lean_usize_dec_lt(v_i_1613_, v_sz_1612_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1623_, 0, v_bs_1614_);
return v___x_1623_;
}
else
{
lean_object* v_v_1624_; lean_object* v___x_1625_; lean_object* v_bs_x27_1626_; lean_object* v_a_1628_; 
v_v_1624_ = lean_array_uget(v_bs_1614_, v_i_1613_);
v___x_1625_ = lean_unsigned_to_nat(0u);
v_bs_x27_1626_ = lean_array_uset(v_bs_1614_, v_i_1613_, v___x_1625_);
switch(lean_obj_tag(v_v_1624_))
{
case 0:
{
lean_object* v_ctorName_1633_; lean_object* v_params_1634_; lean_object* v_code_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1656_; 
v_ctorName_1633_ = lean_ctor_get(v_v_1624_, 0);
v_params_1634_ = lean_ctor_get(v_v_1624_, 1);
v_code_1635_ = lean_ctor_get(v_v_1624_, 2);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_v_1624_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1637_ = v_v_1624_;
v_isShared_1638_ = v_isSharedCheck_1656_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_code_1635_);
lean_inc(v_params_1634_);
lean_inc(v_ctorName_1633_);
lean_dec(v_v_1624_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1656_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
size_t v_sz_1639_; size_t v___x_1640_; lean_object* v___x_1641_; 
v_sz_1639_ = lean_array_size(v_params_1634_);
v___x_1640_ = ((size_t)0ULL);
v___x_1641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_1611_, v_sz_1639_, v___x_1640_, v_params_1634_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1643_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1641_, 1);
v___x_1643_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1611_, v_code_1635_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1646_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref_known(v___x_1643_, 1);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 2, v_a_1644_);
lean_ctor_set(v___x_1637_, 1, v_a_1642_);
v___x_1646_ = v___x_1637_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_ctorName_1633_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_a_1642_);
lean_ctor_set(v_reuseFailAlloc_1647_, 2, v_a_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
v_a_1628_ = v___x_1646_;
goto v___jp_1627_;
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_dec(v_a_1642_);
lean_del_object(v___x_1637_);
lean_dec(v_ctorName_1633_);
lean_dec_ref(v_bs_x27_1626_);
v_a_1648_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1643_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1643_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
else
{
lean_del_object(v___x_1637_);
lean_dec_ref(v_code_1635_);
lean_dec(v_ctorName_1633_);
lean_dec_ref(v_bs_x27_1626_);
return v___x_1641_;
}
}
}
case 1:
{
lean_object* v_info_1657_; lean_object* v_code_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1675_; 
v_info_1657_ = lean_ctor_get(v_v_1624_, 0);
v_code_1658_ = lean_ctor_get(v_v_1624_, 1);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_v_1624_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1660_ = v_v_1624_;
v_isShared_1661_ = v_isSharedCheck_1675_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_code_1658_);
lean_inc(v_info_1657_);
lean_dec(v_v_1624_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1675_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1611_, v_code_1658_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1665_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
lean_dec_ref_known(v___x_1662_, 1);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 1, v_a_1663_);
v___x_1665_ = v___x_1660_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_info_1657_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_a_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
v_a_1628_ = v___x_1665_;
goto v___jp_1627_;
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_del_object(v___x_1660_);
lean_dec_ref(v_info_1657_);
lean_dec_ref(v_bs_x27_1626_);
v_a_1667_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1662_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1662_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
}
default: 
{
lean_object* v_code_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1693_; 
v_code_1676_ = lean_ctor_get(v_v_1624_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_v_1624_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1678_ = v_v_1624_;
v_isShared_1679_ = v_isSharedCheck_1693_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_code_1676_);
lean_dec(v_v_1624_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1693_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1611_, v_code_1676_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1683_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v___x_1680_, 1);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v_a_1681_);
v___x_1683_ = v___x_1678_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
v_a_1628_ = v___x_1683_;
goto v___jp_1627_;
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_del_object(v___x_1678_);
lean_dec_ref(v_bs_x27_1626_);
v_a_1685_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1680_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1680_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
}
v___jp_1627_:
{
size_t v___x_1629_; size_t v___x_1630_; lean_object* v___x_1631_; 
v___x_1629_ = ((size_t)1ULL);
v___x_1630_ = lean_usize_add(v_i_1613_, v___x_1629_);
v___x_1631_ = lean_array_uset(v_bs_x27_1626_, v_i_1613_, v_a_1628_);
v_i_1613_ = v___x_1630_;
v_bs_1614_ = v___x_1631_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t v_pu_1694_, lean_object* v_code_1695_, uint8_t v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
switch(lean_obj_tag(v_code_1695_))
{
case 0:
{
lean_object* v_decl_1703_; lean_object* v_k_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1730_; 
v_decl_1703_ = lean_ctor_get(v_code_1695_, 0);
v_k_1704_ = lean_ctor_get(v_code_1695_, 1);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_code_1695_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1706_ = v_code_1695_;
v_isShared_1707_ = v_isSharedCheck_1730_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_k_1704_);
lean_inc(v_decl_1703_);
lean_dec(v_code_1695_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1730_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_1694_, v_decl_1703_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1710_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v___x_1708_, 1);
v___x_1710_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1694_, v_k_1704_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1721_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1721_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1721_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 1, v_a_1711_);
lean_ctor_set(v___x_1706_, 0, v_a_1709_);
v___x_1716_ = v___x_1706_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1709_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1718_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1716_);
v___x_1718_ = v___x_1713_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
else
{
lean_dec(v_a_1709_);
lean_del_object(v___x_1706_);
return v___x_1710_;
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_del_object(v___x_1706_);
lean_dec_ref(v_k_1704_);
v_a_1722_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1708_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1708_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
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
}
case 1:
{
lean_object* v_decl_1731_; lean_object* v_k_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1758_; 
v_decl_1731_ = lean_ctor_get(v_code_1695_, 0);
v_k_1732_ = lean_ctor_get(v_code_1695_, 1);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_code_1695_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1734_ = v_code_1695_;
v_isShared_1735_ = v_isSharedCheck_1758_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_k_1732_);
lean_inc(v_decl_1731_);
lean_dec(v_code_1695_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1758_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1694_, v_decl_1731_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v___x_1738_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref_known(v___x_1736_, 1);
v___x_1738_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1694_, v_k_1732_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1749_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1741_ = v___x_1738_;
v_isShared_1742_ = v_isSharedCheck_1749_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1738_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1749_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v_a_1739_);
lean_ctor_set(v___x_1734_, 0, v_a_1737_);
v___x_1744_ = v___x_1734_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1737_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v___x_1746_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1744_);
v___x_1746_ = v___x_1741_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1744_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
else
{
lean_dec(v_a_1737_);
lean_del_object(v___x_1734_);
return v___x_1738_;
}
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_del_object(v___x_1734_);
lean_dec_ref(v_k_1732_);
v_a_1750_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1736_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1736_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
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
}
case 2:
{
lean_object* v_decl_1759_; lean_object* v_k_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1786_; 
v_decl_1759_ = lean_ctor_get(v_code_1695_, 0);
v_k_1760_ = lean_ctor_get(v_code_1695_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_code_1695_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1762_ = v_code_1695_;
v_isShared_1763_ = v_isSharedCheck_1786_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_k_1760_);
lean_inc(v_decl_1759_);
lean_dec(v_code_1695_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1786_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1694_, v_decl_1759_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v___x_1766_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1694_, v_k_1760_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1777_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1769_ = v___x_1766_;
v_isShared_1770_ = v_isSharedCheck_1777_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1766_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1777_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 1, v_a_1767_);
lean_ctor_set(v___x_1762_, 0, v_a_1765_);
v___x_1772_ = v___x_1762_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1765_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1774_; 
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1772_);
v___x_1774_ = v___x_1769_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
else
{
lean_dec(v_a_1765_);
lean_del_object(v___x_1762_);
return v___x_1766_;
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_del_object(v___x_1762_);
lean_dec_ref(v_k_1760_);
v_a_1778_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1764_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1764_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
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
}
case 3:
{
lean_object* v_fvarId_1787_; lean_object* v_args_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1817_; 
v_fvarId_1787_ = lean_ctor_get(v_code_1695_, 0);
v_args_1788_ = lean_ctor_get(v_code_1695_, 1);
v_isSharedCheck_1817_ = !lean_is_exclusive(v_code_1695_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1790_ = v_code_1695_;
v_isShared_1791_ = v_isSharedCheck_1817_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_args_1788_);
lean_inc(v_fvarId_1787_);
lean_dec(v_code_1695_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1817_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; uint8_t v___x_1793_; lean_object* v___x_1794_; 
v___x_1792_ = lean_st_ref_get(v_a_1697_);
v___x_1793_ = 1;
v___x_1794_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1792_, v_fvarId_1787_, v___x_1793_);
lean_dec(v___x_1792_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_fvarId_1795_; lean_object* v___x_1796_; 
v_fvarId_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_fvarId_1795_);
lean_dec_ref_known(v___x_1794_, 1);
v___x_1796_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1694_, v_args_1788_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1807_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1807_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1807_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 1, v_a_1797_);
lean_ctor_set(v___x_1790_, 0, v_fvarId_1795_);
v___x_1802_ = v___x_1790_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_fvarId_1795_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1804_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1802_);
v___x_1804_ = v___x_1799_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec(v_fvarId_1795_);
lean_del_object(v___x_1790_);
v_a_1808_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1796_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1796_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
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
lean_object* v___x_1816_; 
lean_del_object(v___x_1790_);
lean_dec_ref(v_args_1788_);
v___x_1816_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1694_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v___x_1816_;
}
}
}
case 4:
{
lean_object* v_cases_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1870_; 
v_cases_1818_ = lean_ctor_get(v_code_1695_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v_code_1695_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1820_ = v_code_1695_;
v_isShared_1821_ = v_isSharedCheck_1870_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_cases_1818_);
lean_dec(v_code_1695_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1870_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v_typeName_1822_; lean_object* v_resultType_1823_; lean_object* v_discr_1824_; lean_object* v_alts_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1869_; 
v_typeName_1822_ = lean_ctor_get(v_cases_1818_, 0);
v_resultType_1823_ = lean_ctor_get(v_cases_1818_, 1);
v_discr_1824_ = lean_ctor_get(v_cases_1818_, 2);
v_alts_1825_ = lean_ctor_get(v_cases_1818_, 3);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_cases_1818_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1827_ = v_cases_1818_;
v_isShared_1828_ = v_isSharedCheck_1869_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_alts_1825_);
lean_inc(v_discr_1824_);
lean_inc(v_resultType_1823_);
lean_inc(v_typeName_1822_);
lean_dec(v_cases_1818_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1869_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1829_; uint8_t v___x_1830_; lean_object* v___x_1831_; 
v___x_1829_ = lean_st_ref_get(v_a_1697_);
v___x_1830_ = 1;
v___x_1831_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1829_, v_discr_1824_, v___x_1830_);
lean_dec(v___x_1829_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_fvarId_1832_; lean_object* v___x_1833_; 
v_fvarId_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_fvarId_1832_);
lean_dec_ref_known(v___x_1831_, 1);
v___x_1833_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1694_, v_resultType_1823_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; size_t v_sz_1835_; size_t v___x_1836_; lean_object* v___x_1837_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1833_, 1);
v_sz_1835_ = lean_array_size(v_alts_1825_);
v___x_1836_ = ((size_t)0ULL);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_1694_, v_sz_1835_, v___x_1836_, v_alts_1825_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1851_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1851_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1851_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 3, v_a_1838_);
lean_ctor_set(v___x_1827_, 2, v_fvarId_1832_);
lean_ctor_set(v___x_1827_, 1, v_a_1834_);
v___x_1843_ = v___x_1827_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_typeName_1822_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_a_1834_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_fvarId_1832_);
lean_ctor_set(v_reuseFailAlloc_1850_, 3, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1845_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1843_);
v___x_1845_ = v___x_1820_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1847_; 
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1845_);
v___x_1847_ = v___x_1840_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec(v_a_1834_);
lean_dec(v_fvarId_1832_);
lean_del_object(v___x_1827_);
lean_dec(v_typeName_1822_);
lean_del_object(v___x_1820_);
v_a_1852_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1837_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1837_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
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
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec(v_fvarId_1832_);
lean_del_object(v___x_1827_);
lean_dec_ref(v_alts_1825_);
lean_dec(v_typeName_1822_);
lean_del_object(v___x_1820_);
v_a_1860_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1833_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1833_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
else
{
lean_object* v___x_1868_; 
lean_del_object(v___x_1827_);
lean_dec_ref(v_alts_1825_);
lean_dec_ref(v_resultType_1823_);
lean_dec(v_typeName_1822_);
lean_del_object(v___x_1820_);
v___x_1868_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1694_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v___x_1868_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1890_; 
v_fvarId_1871_ = lean_ctor_get(v_code_1695_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_code_1695_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1873_ = v_code_1695_;
v_isShared_1874_ = v_isSharedCheck_1890_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_fvarId_1871_);
lean_dec(v_code_1695_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1890_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; uint8_t v___x_1876_; lean_object* v___x_1877_; 
v___x_1875_ = lean_st_ref_get(v_a_1697_);
v___x_1876_ = 1;
v___x_1877_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1875_, v_fvarId_1871_, v___x_1876_);
lean_dec(v___x_1875_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_fvarId_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1888_; 
v_fvarId_1878_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1880_ = v___x_1877_;
v_isShared_1881_ = v_isSharedCheck_1888_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_fvarId_1878_);
lean_dec(v___x_1877_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1888_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v_fvarId_1878_);
v___x_1883_ = v___x_1873_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_fvarId_1878_);
v___x_1883_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1885_; 
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1883_);
v___x_1885_ = v___x_1880_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
else
{
lean_object* v___x_1889_; 
lean_del_object(v___x_1873_);
v___x_1889_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1694_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v___x_1889_;
}
}
}
case 6:
{
lean_object* v_type_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1915_; 
v_type_1891_ = lean_ctor_get(v_code_1695_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_code_1695_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1893_ = v_code_1695_;
v_isShared_1894_ = v_isSharedCheck_1915_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_type_1891_);
lean_dec(v_code_1695_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1915_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; 
v___x_1895_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1694_, v_type_1891_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1906_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1898_ = v___x_1895_;
v_isShared_1899_ = v_isSharedCheck_1906_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1895_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1906_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v_a_1896_);
v___x_1901_ = v___x_1893_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1903_; 
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v___x_1901_);
v___x_1903_ = v___x_1898_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
lean_del_object(v___x_1893_);
v_a_1907_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1895_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1895_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
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
}
case 7:
{
lean_object* v_fvarId_1916_; lean_object* v_i_1917_; lean_object* v_y_1918_; lean_object* v_k_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1942_; 
v_fvarId_1916_ = lean_ctor_get(v_code_1695_, 0);
v_i_1917_ = lean_ctor_get(v_code_1695_, 1);
v_y_1918_ = lean_ctor_get(v_code_1695_, 2);
v_k_1919_ = lean_ctor_get(v_code_1695_, 3);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_code_1695_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1921_ = v_code_1695_;
v_isShared_1922_ = v_isSharedCheck_1942_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_k_1919_);
lean_inc(v_y_1918_);
lean_inc(v_i_1917_);
lean_inc(v_fvarId_1916_);
lean_dec(v_code_1695_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1942_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; uint8_t v___x_1924_; lean_object* v___x_1925_; 
v___x_1923_ = lean_st_ref_get(v_a_1697_);
v___x_1924_ = 1;
v___x_1925_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1923_, v_fvarId_1916_, v___x_1924_);
lean_dec(v___x_1923_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_fvarId_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v_fvarId_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_fvarId_1926_);
lean_dec_ref_known(v___x_1925_, 1);
v___x_1927_ = lean_st_ref_get(v_a_1697_);
v___x_1928_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1694_, v___x_1927_, v_y_1918_, v___x_1924_);
lean_dec(v___x_1927_);
v___x_1929_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1694_, v_k_1919_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1940_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1932_ = v___x_1929_;
v_isShared_1933_ = v_isSharedCheck_1940_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1929_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1940_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 3, v_a_1930_);
lean_ctor_set(v___x_1921_, 2, v___x_1928_);
lean_ctor_set(v___x_1921_, 0, v_fvarId_1926_);
v___x_1935_ = v___x_1921_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_fvarId_1926_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_i_1917_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1939_, 3, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1937_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1935_);
v___x_1937_ = v___x_1932_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
else
{
lean_dec(v___x_1928_);
lean_dec(v_fvarId_1926_);
lean_del_object(v___x_1921_);
lean_dec(v_i_1917_);
return v___x_1929_;
}
}
else
{
lean_object* v___x_1941_; 
lean_del_object(v___x_1921_);
lean_dec_ref(v_k_1919_);
lean_dec(v_y_1918_);
lean_dec(v_i_1917_);
v___x_1941_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1694_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v___x_1941_;
}
}
}
case 8:
{
lean_object* v_fvarId_1943_; lean_object* v_i_1944_; lean_object* v_y_1945_; lean_object* v_k_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1971_; 
v_fvarId_1943_ = lean_ctor_get(v_code_1695_, 0);
v_i_1944_ = lean_ctor_get(v_code_1695_, 1);
v_y_1945_ = lean_ctor_get(v_code_1695_, 2);
v_k_1946_ = lean_ctor_get(v_code_1695_, 3);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_code_1695_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1948_ = v_code_1695_;
v_isShared_1949_ = v_isSharedCheck_1971_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_k_1946_);
lean_inc(v_y_1945_);
lean_inc(v_i_1944_);
lean_inc(v_fvarId_1943_);
lean_dec(v_code_1695_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1971_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1950_; uint8_t v___x_1951_; lean_object* v___x_1952_; 
v___x_1950_ = lean_st_ref_get(v_a_1697_);
v___x_1951_ = 1;
v___x_1952_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1950_, v_fvarId_1943_, v___x_1951_);
lean_dec(v___x_1950_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_fvarId_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v_fvarId_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_fvarId_1953_);
lean_dec_ref_known(v___x_1952_, 1);
v___x_1954_ = lean_st_ref_get(v_a_1697_);
v___x_1955_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1954_, v_y_1945_, v___x_1951_);
lean_dec(v___x_1954_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_fvarId_1956_; lean_object* v___x_1957_; 
v_fvarId_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_fvarId_1956_);
lean_dec_ref_known(v___x_1955_, 1);
v___x_1957_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1694_, v_k_1946_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1968_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1960_ = v___x_1957_;
v_isShared_1961_ = v_isSharedCheck_1968_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1957_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1968_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 3, v_a_1958_);
lean_ctor_set(v___x_1948_, 2, v_fvarId_1956_);
lean_ctor_set(v___x_1948_, 0, v_fvarId_1953_);
v___x_1963_ = v___x_1948_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_fvarId_1953_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_i_1944_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v_fvarId_1956_);
lean_ctor_set(v_reuseFailAlloc_1967_, 3, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
lean_object* v___x_1965_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v___x_1963_);
v___x_1965_ = v___x_1960_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
else
{
lean_dec(v_fvarId_1956_);
lean_dec(v_fvarId_1953_);
lean_del_object(v___x_1948_);
lean_dec(v_i_1944_);
return v___x_1957_;
}
}
else
{
lean_object* v___x_1969_; 
lean_dec(v_fvarId_1953_);
lean_del_object(v___x_1948_);
lean_dec_ref(v_k_1946_);
lean_dec(v_i_1944_);
v___x_1969_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1694_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v___x_1969_;
}
}
else
{
lean_object* v___x_1970_; 
lean_del_object(v___x_1948_);
lean_dec_ref(v_k_1946_);
lean_dec(v_y_1945_);
lean_dec(v_i_1944_);
v___x_1970_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1694_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v___x_1970_;
}
}
}
case 9:
{
lean_object* v_fvarId_1972_; lean_object* v_i_1973_; lean_object* v_offset_1974_; lean_object* v_y_1975_; lean_object* v_ty_1976_; lean_object* v_k_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2012_; 
v_fvarId_1972_ = lean_ctor_get(v_code_1695_, 0);
v_i_1973_ = lean_ctor_get(v_code_1695_, 1);
v_offset_1974_ = lean_ctor_get(v_code_1695_, 2);
v_y_1975_ = lean_ctor_get(v_code_1695_, 3);
v_ty_1976_ = lean_ctor_get(v_code_1695_, 4);
v_k_1977_ = lean_ctor_get(v_code_1695_, 5);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_code_1695_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1979_ = v_code_1695_;
v_isShared_1980_ = v_isSharedCheck_2012_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_k_1977_);
lean_inc(v_ty_1976_);
lean_inc(v_y_1975_);
lean_inc(v_offset_1974_);
lean_inc(v_i_1973_);
lean_inc(v_fvarId_1972_);
lean_dec(v_code_1695_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2012_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; uint8_t v___x_1982_; lean_object* v___x_1983_; 
v___x_1981_ = lean_st_ref_get(v_a_1697_);
v___x_1982_ = 1;
v___x_1983_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1981_, v_fvarId_1972_, v___x_1982_);
lean_dec(v___x_1981_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_fvarId_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v_fvarId_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_fvarId_1984_);
lean_dec_ref_known(v___x_1983_, 1);
v___x_1985_ = lean_st_ref_get(v_a_1697_);
v___x_1986_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1985_, v_y_1975_, v___x_1982_);
lean_dec(v___x_1985_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_fvarId_1987_; lean_object* v___x_1988_; 
v_fvarId_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_fvarId_1987_);
lean_dec_ref_known(v___x_1986_, 1);
v___x_1988_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1694_, v_ty_1976_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1990_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1988_, 1);
v___x_1990_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1694_, v_k_1977_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2001_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_2001_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2001_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 5, v_a_1991_);
lean_ctor_set(v___x_1979_, 4, v_a_1989_);
lean_ctor_set(v___x_1979_, 3, v_fvarId_1987_);
lean_ctor_set(v___x_1979_, 0, v_fvarId_1984_);
v___x_1996_ = v___x_1979_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_fvarId_1984_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_i_1973_);
lean_ctor_set(v_reuseFailAlloc_2000_, 2, v_offset_1974_);
lean_ctor_set(v_reuseFailAlloc_2000_, 3, v_fvarId_1987_);
lean_ctor_set(v_reuseFailAlloc_2000_, 4, v_a_1989_);
lean_ctor_set(v_reuseFailAlloc_2000_, 5, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1998_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_1996_);
v___x_1998_ = v___x_1993_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
else
{
lean_dec(v_a_1989_);
lean_dec(v_fvarId_1987_);
lean_dec(v_fvarId_1984_);
lean_del_object(v___x_1979_);
lean_dec(v_offset_1974_);
lean_dec(v_i_1973_);
return v___x_1990_;
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
lean_dec(v_fvarId_1987_);
lean_dec(v_fvarId_1984_);
lean_del_object(v___x_1979_);
lean_dec_ref(v_k_1977_);
lean_dec(v_offset_1974_);
lean_dec(v_i_1973_);
v_a_2002_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1988_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1988_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
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
lean_object* v___x_2010_; 
lean_dec(v_fvarId_1984_);
lean_del_object(v___x_1979_);
lean_dec_ref(v_k_1977_);
lean_dec_ref(v_ty_1976_);
lean_dec(v_offset_1974_);
lean_dec(v_i_1973_);
v___x_2010_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1694_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v___x_2010_;
}
}
else
{
lean_object* v___x_2011_; 
lean_del_object(v___x_1979_);
lean_dec_ref(v_k_1977_);
lean_dec_ref(v_ty_1976_);
lean_dec(v_y_1975_);
lean_dec(v_offset_1974_);
lean_dec(v_i_1973_);
v___x_2011_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1694_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v___x_2011_;
}
}
}
case 10:
{
lean_object* v_fvarId_2013_; lean_object* v_cidx_2014_; lean_object* v_k_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2036_; 
v_fvarId_2013_ = lean_ctor_get(v_code_1695_, 0);
v_cidx_2014_ = lean_ctor_get(v_code_1695_, 1);
v_k_2015_ = lean_ctor_get(v_code_1695_, 2);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_code_1695_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2017_ = v_code_1695_;
v_isShared_2018_ = v_isSharedCheck_2036_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_k_2015_);
lean_inc(v_cidx_2014_);
lean_inc(v_fvarId_2013_);
lean_dec(v_code_1695_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2036_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; uint8_t v___x_2020_; lean_object* v___x_2021_; 
v___x_2019_ = lean_st_ref_get(v_a_1697_);
v___x_2020_ = 1;
v___x_2021_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2019_, v_fvarId_2013_, v___x_2020_);
lean_dec(v___x_2019_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_fvarId_2022_; lean_object* v___x_2023_; 
v_fvarId_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_fvarId_2022_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2023_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1694_, v_k_2015_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2034_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2034_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2034_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 2, v_a_2024_);
lean_ctor_set(v___x_2017_, 0, v_fvarId_2022_);
v___x_2029_ = v___x_2017_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_fvarId_2022_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_cidx_2014_);
lean_ctor_set(v_reuseFailAlloc_2033_, 2, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2031_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2029_);
v___x_2031_ = v___x_2026_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
else
{
lean_dec(v_fvarId_2022_);
lean_del_object(v___x_2017_);
lean_dec(v_cidx_2014_);
return v___x_2023_;
}
}
else
{
lean_object* v___x_2035_; 
lean_del_object(v___x_2017_);
lean_dec_ref(v_k_2015_);
lean_dec(v_cidx_2014_);
v___x_2035_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1694_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v___x_2035_;
}
}
}
case 11:
{
lean_object* v_fvarId_2037_; lean_object* v_n_2038_; uint8_t v_check_2039_; uint8_t v_persistent_2040_; lean_object* v_k_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2062_; 
v_fvarId_2037_ = lean_ctor_get(v_code_1695_, 0);
v_n_2038_ = lean_ctor_get(v_code_1695_, 1);
v_check_2039_ = lean_ctor_get_uint8(v_code_1695_, sizeof(void*)*3);
v_persistent_2040_ = lean_ctor_get_uint8(v_code_1695_, sizeof(void*)*3 + 1);
v_k_2041_ = lean_ctor_get(v_code_1695_, 2);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_code_1695_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2043_ = v_code_1695_;
v_isShared_2044_ = v_isSharedCheck_2062_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_k_2041_);
lean_inc(v_n_2038_);
lean_inc(v_fvarId_2037_);
lean_dec(v_code_1695_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2062_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; uint8_t v___x_2046_; lean_object* v___x_2047_; 
v___x_2045_ = lean_st_ref_get(v_a_1697_);
v___x_2046_ = 1;
v___x_2047_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2045_, v_fvarId_2037_, v___x_2046_);
lean_dec(v___x_2045_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_fvarId_2048_; lean_object* v___x_2049_; 
v_fvarId_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_fvarId_2048_);
lean_dec_ref_known(v___x_2047_, 1);
v___x_2049_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1694_, v_k_2041_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2060_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2060_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2060_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 2, v_a_2050_);
lean_ctor_set(v___x_2043_, 0, v_fvarId_2048_);
v___x_2055_ = v___x_2043_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_fvarId_2048_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_n_2038_);
lean_ctor_set(v_reuseFailAlloc_2059_, 2, v_a_2050_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, sizeof(void*)*3, v_check_2039_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, sizeof(void*)*3 + 1, v_persistent_2040_);
v___x_2055_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2057_; 
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2055_);
v___x_2057_ = v___x_2052_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
else
{
lean_dec(v_fvarId_2048_);
lean_del_object(v___x_2043_);
lean_dec(v_n_2038_);
return v___x_2049_;
}
}
else
{
lean_object* v___x_2061_; 
lean_del_object(v___x_2043_);
lean_dec_ref(v_k_2041_);
lean_dec(v_n_2038_);
v___x_2061_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1694_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v___x_2061_;
}
}
}
case 12:
{
lean_object* v_fvarId_2063_; lean_object* v_n_2064_; uint8_t v_check_2065_; uint8_t v_persistent_2066_; lean_object* v_objs_x3f_2067_; lean_object* v_k_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2089_; 
v_fvarId_2063_ = lean_ctor_get(v_code_1695_, 0);
v_n_2064_ = lean_ctor_get(v_code_1695_, 1);
v_check_2065_ = lean_ctor_get_uint8(v_code_1695_, sizeof(void*)*4);
v_persistent_2066_ = lean_ctor_get_uint8(v_code_1695_, sizeof(void*)*4 + 1);
v_objs_x3f_2067_ = lean_ctor_get(v_code_1695_, 2);
v_k_2068_ = lean_ctor_get(v_code_1695_, 3);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_code_1695_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2070_ = v_code_1695_;
v_isShared_2071_ = v_isSharedCheck_2089_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_k_2068_);
lean_inc(v_objs_x3f_2067_);
lean_inc(v_n_2064_);
lean_inc(v_fvarId_2063_);
lean_dec(v_code_1695_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2089_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; uint8_t v___x_2073_; lean_object* v___x_2074_; 
v___x_2072_ = lean_st_ref_get(v_a_1697_);
v___x_2073_ = 1;
v___x_2074_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2072_, v_fvarId_2063_, v___x_2073_);
lean_dec(v___x_2072_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_fvarId_2075_; lean_object* v___x_2076_; 
v_fvarId_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_fvarId_2075_);
lean_dec_ref_known(v___x_2074_, 1);
v___x_2076_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1694_, v_k_2068_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2087_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2079_ = v___x_2076_;
v_isShared_2080_ = v_isSharedCheck_2087_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2076_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2087_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 3, v_a_2077_);
lean_ctor_set(v___x_2070_, 0, v_fvarId_2075_);
v___x_2082_ = v___x_2070_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_fvarId_2075_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_n_2064_);
lean_ctor_set(v_reuseFailAlloc_2086_, 2, v_objs_x3f_2067_);
lean_ctor_set(v_reuseFailAlloc_2086_, 3, v_a_2077_);
lean_ctor_set_uint8(v_reuseFailAlloc_2086_, sizeof(void*)*4, v_check_2065_);
lean_ctor_set_uint8(v_reuseFailAlloc_2086_, sizeof(void*)*4 + 1, v_persistent_2066_);
v___x_2082_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2084_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 0, v___x_2082_);
v___x_2084_ = v___x_2079_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2082_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
else
{
lean_dec(v_fvarId_2075_);
lean_del_object(v___x_2070_);
lean_dec(v_objs_x3f_2067_);
lean_dec(v_n_2064_);
return v___x_2076_;
}
}
else
{
lean_object* v___x_2088_; 
lean_del_object(v___x_2070_);
lean_dec_ref(v_k_2068_);
lean_dec(v_objs_x3f_2067_);
lean_dec(v_n_2064_);
v___x_2088_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1694_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v___x_2088_;
}
}
}
default: 
{
lean_object* v_fvarId_2090_; lean_object* v_k_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2112_; 
v_fvarId_2090_ = lean_ctor_get(v_code_1695_, 0);
v_k_2091_ = lean_ctor_get(v_code_1695_, 1);
v_isSharedCheck_2112_ = !lean_is_exclusive(v_code_1695_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2093_ = v_code_1695_;
v_isShared_2094_ = v_isSharedCheck_2112_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_k_2091_);
lean_inc(v_fvarId_2090_);
lean_dec(v_code_1695_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2112_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2095_; uint8_t v___x_2096_; lean_object* v___x_2097_; 
v___x_2095_ = lean_st_ref_get(v_a_1697_);
v___x_2096_ = 1;
v___x_2097_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2095_, v_fvarId_2090_, v___x_2096_);
lean_dec(v___x_2095_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_fvarId_2098_; lean_object* v___x_2099_; 
v_fvarId_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_fvarId_2098_);
lean_dec_ref_known(v___x_2097_, 1);
v___x_2099_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1694_, v_k_2091_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2110_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2102_ = v___x_2099_;
v_isShared_2103_ = v_isSharedCheck_2110_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2099_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2110_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 1, v_a_2100_);
lean_ctor_set(v___x_2093_, 0, v_fvarId_2098_);
v___x_2105_ = v___x_2093_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_fvarId_2098_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
lean_object* v___x_2107_; 
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2105_);
v___x_2107_ = v___x_2102_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_dec(v_fvarId_2098_);
lean_del_object(v___x_2093_);
return v___x_2099_;
}
}
else
{
lean_object* v___x_2111_; 
lean_del_object(v___x_2093_);
lean_dec_ref(v_k_2091_);
v___x_2111_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1694_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v___x_2111_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(uint8_t v_pu_2113_, lean_object* v_decl_2114_, uint8_t v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v_fvarId_2122_; lean_object* v_binderName_2123_; lean_object* v_params_2124_; lean_object* v_type_2125_; lean_object* v_value_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2204_; 
v_fvarId_2122_ = lean_ctor_get(v_decl_2114_, 0);
v_binderName_2123_ = lean_ctor_get(v_decl_2114_, 1);
v_params_2124_ = lean_ctor_get(v_decl_2114_, 2);
v_type_2125_ = lean_ctor_get(v_decl_2114_, 3);
v_value_2126_ = lean_ctor_get(v_decl_2114_, 4);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_decl_2114_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2128_ = v_decl_2114_;
v_isShared_2129_ = v_isSharedCheck_2204_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_value_2126_);
lean_inc(v_type_2125_);
lean_inc(v_params_2124_);
lean_inc(v_binderName_2123_);
lean_inc(v_fvarId_2122_);
lean_dec(v_decl_2114_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2204_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; 
v___x_2130_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2113_, v_type_2125_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_2123_, v_a_2115_, v_a_2118_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; size_t v_sz_2134_; size_t v___x_2135_; lean_object* v___x_2136_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v_sz_2134_ = lean_array_size(v_params_2124_);
v___x_2135_ = ((size_t)0ULL);
v___x_2136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2113_, v_sz_2134_, v___x_2135_, v_params_2124_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v___x_2138_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2113_, v_value_2126_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2140_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
v___x_2140_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_2122_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2163_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2143_ = v___x_2140_;
v_isShared_2144_ = v_isSharedCheck_2163_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2140_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2163_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2145_; lean_object* v_lctx_2146_; lean_object* v_nextIdx_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2162_; 
v___x_2145_ = lean_st_ref_take(v_a_2118_);
v_lctx_2146_ = lean_ctor_get(v___x_2145_, 0);
v_nextIdx_2147_ = lean_ctor_get(v___x_2145_, 1);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2149_ = v___x_2145_;
v_isShared_2150_ = v_isSharedCheck_2162_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_nextIdx_2147_);
lean_inc(v_lctx_2146_);
lean_dec(v___x_2145_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2162_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 4, v_a_2139_);
lean_ctor_set(v___x_2128_, 3, v_a_2131_);
lean_ctor_set(v___x_2128_, 2, v_a_2137_);
lean_ctor_set(v___x_2128_, 1, v_a_2133_);
lean_ctor_set(v___x_2128_, 0, v_a_2141_);
v___x_2152_ = v___x_2128_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2141_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_a_2133_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v_a_2137_);
lean_ctor_set(v_reuseFailAlloc_2161_, 3, v_a_2131_);
lean_ctor_set(v_reuseFailAlloc_2161_, 4, v_a_2139_);
v___x_2152_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2153_; lean_object* v___x_2155_; 
lean_inc_ref(v___x_2152_);
v___x_2153_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2113_, v_lctx_2146_, v___x_2152_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v___x_2153_);
v___x_2155_ = v___x_2149_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2153_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_nextIdx_2147_);
v___x_2155_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2156_ = lean_st_ref_put(v_a_2118_, v___x_2155_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 0, v___x_2152_);
v___x_2158_ = v___x_2143_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2152_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v_a_2139_);
lean_dec(v_a_2137_);
lean_dec(v_a_2133_);
lean_dec(v_a_2131_);
lean_del_object(v___x_2128_);
v_a_2164_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2140_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2140_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec(v_a_2137_);
lean_dec(v_a_2133_);
lean_dec(v_a_2131_);
lean_del_object(v___x_2128_);
lean_dec(v_fvarId_2122_);
v_a_2172_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2138_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2138_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec(v_a_2133_);
lean_dec(v_a_2131_);
lean_del_object(v___x_2128_);
lean_dec_ref(v_value_2126_);
lean_dec(v_fvarId_2122_);
v_a_2180_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2136_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2136_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec(v_a_2131_);
lean_del_object(v___x_2128_);
lean_dec_ref(v_value_2126_);
lean_dec_ref(v_params_2124_);
lean_dec(v_fvarId_2122_);
v_a_2188_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2132_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2132_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
else
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
lean_del_object(v___x_2128_);
lean_dec_ref(v_value_2126_);
lean_dec_ref(v_params_2124_);
lean_dec(v_binderName_2123_);
lean_dec(v_fvarId_2122_);
v_a_2196_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2130_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2130_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(lean_object* v_pu_2205_, lean_object* v_decl_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_){
_start:
{
uint8_t v_pu_boxed_2214_; uint8_t v_a_boxed_2215_; lean_object* v_res_2216_; 
v_pu_boxed_2214_ = lean_unbox(v_pu_2205_);
v_a_boxed_2215_ = lean_unbox(v_a_2207_);
v_res_2216_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_boxed_2214_, v_decl_2206_, v_a_boxed_2215_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
lean_dec(v_a_2210_);
lean_dec_ref(v_a_2209_);
lean_dec(v_a_2208_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2___boxed(lean_object* v_pu_2217_, lean_object* v_sz_2218_, lean_object* v_i_2219_, lean_object* v_bs_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
uint8_t v_pu_boxed_2228_; size_t v_sz_boxed_2229_; size_t v_i_boxed_2230_; uint8_t v___y_26952__boxed_2231_; lean_object* v_res_2232_; 
v_pu_boxed_2228_ = lean_unbox(v_pu_2217_);
v_sz_boxed_2229_ = lean_unbox_usize(v_sz_2218_);
lean_dec(v_sz_2218_);
v_i_boxed_2230_ = lean_unbox_usize(v_i_2219_);
lean_dec(v_i_2219_);
v___y_26952__boxed_2231_ = lean_unbox(v___y_2221_);
v_res_2232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_boxed_2228_, v_sz_boxed_2229_, v_i_boxed_2230_, v_bs_2220_, v___y_26952__boxed_2231_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(lean_object* v_pu_2233_, lean_object* v_code_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_){
_start:
{
uint8_t v_pu_boxed_2242_; uint8_t v_a_boxed_2243_; lean_object* v_res_2244_; 
v_pu_boxed_2242_ = lean_unbox(v_pu_2233_);
v_a_boxed_2243_ = lean_unbox(v_a_2235_);
v_res_2244_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_boxed_2242_, v_code_2234_, v_a_boxed_2243_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
lean_dec(v_a_2238_);
lean_dec_ref(v_a_2237_);
lean_dec(v_a_2236_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(uint8_t v_pu_2245_, lean_object* v_msg_2246_, uint8_t v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v_toApplicative_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2320_; 
v___x_2254_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
v___x_2255_ = l_StateRefT_x27_instMonad___redArg(v___x_2254_);
v_toApplicative_2256_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2320_ == 0)
{
lean_object* v_unused_2321_; 
v_unused_2321_ = lean_ctor_get(v___x_2255_, 1);
lean_dec(v_unused_2321_);
v___x_2258_ = v___x_2255_;
v_isShared_2259_ = v_isSharedCheck_2320_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_toApplicative_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2320_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v_toFunctor_2260_; lean_object* v_toSeq_2261_; lean_object* v_toSeqLeft_2262_; lean_object* v_toSeqRight_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2318_; 
v_toFunctor_2260_ = lean_ctor_get(v_toApplicative_2256_, 0);
v_toSeq_2261_ = lean_ctor_get(v_toApplicative_2256_, 2);
v_toSeqLeft_2262_ = lean_ctor_get(v_toApplicative_2256_, 3);
v_toSeqRight_2263_ = lean_ctor_get(v_toApplicative_2256_, 4);
v_isSharedCheck_2318_ = !lean_is_exclusive(v_toApplicative_2256_);
if (v_isSharedCheck_2318_ == 0)
{
lean_object* v_unused_2319_; 
v_unused_2319_ = lean_ctor_get(v_toApplicative_2256_, 1);
lean_dec(v_unused_2319_);
v___x_2265_ = v_toApplicative_2256_;
v_isShared_2266_ = v_isSharedCheck_2318_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_toSeqRight_2263_);
lean_inc(v_toSeqLeft_2262_);
lean_inc(v_toSeq_2261_);
lean_inc(v_toFunctor_2260_);
lean_dec(v_toApplicative_2256_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2318_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___f_2267_; lean_object* v___f_2268_; lean_object* v___f_2269_; lean_object* v___f_2270_; lean_object* v___x_2271_; lean_object* v___f_2272_; lean_object* v___f_2273_; lean_object* v___f_2274_; lean_object* v___x_2276_; 
v___f_2267_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
v___f_2268_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_2260_);
v___f_2269_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2269_, 0, v_toFunctor_2260_);
v___f_2270_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2270_, 0, v_toFunctor_2260_);
v___x_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___f_2269_);
lean_ctor_set(v___x_2271_, 1, v___f_2270_);
v___f_2272_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2272_, 0, v_toSeqRight_2263_);
v___f_2273_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2273_, 0, v_toSeqLeft_2262_);
v___f_2274_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2274_, 0, v_toSeq_2261_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 4, v___f_2272_);
lean_ctor_set(v___x_2265_, 3, v___f_2273_);
lean_ctor_set(v___x_2265_, 2, v___f_2274_);
lean_ctor_set(v___x_2265_, 1, v___f_2267_);
lean_ctor_set(v___x_2265_, 0, v___x_2271_);
v___x_2276_ = v___x_2265_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v___f_2267_);
lean_ctor_set(v_reuseFailAlloc_2317_, 2, v___f_2274_);
lean_ctor_set(v_reuseFailAlloc_2317_, 3, v___f_2273_);
lean_ctor_set(v_reuseFailAlloc_2317_, 4, v___f_2272_);
v___x_2276_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2278_; 
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 1, v___f_2268_);
lean_ctor_set(v___x_2258_, 0, v___x_2276_);
v___x_2278_ = v___x_2258_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v___f_2268_);
v___x_2278_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v___x_2279_; lean_object* v_toApplicative_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2314_; 
v___x_2279_ = l_StateRefT_x27_instMonad___redArg(v___x_2278_);
v_toApplicative_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2314_ == 0)
{
lean_object* v_unused_2315_; 
v_unused_2315_ = lean_ctor_get(v___x_2279_, 1);
lean_dec(v_unused_2315_);
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2314_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_toApplicative_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2314_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v_toFunctor_2284_; lean_object* v_toSeq_2285_; lean_object* v_toSeqLeft_2286_; lean_object* v_toSeqRight_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2312_; 
v_toFunctor_2284_ = lean_ctor_get(v_toApplicative_2280_, 0);
v_toSeq_2285_ = lean_ctor_get(v_toApplicative_2280_, 2);
v_toSeqLeft_2286_ = lean_ctor_get(v_toApplicative_2280_, 3);
v_toSeqRight_2287_ = lean_ctor_get(v_toApplicative_2280_, 4);
v_isSharedCheck_2312_ = !lean_is_exclusive(v_toApplicative_2280_);
if (v_isSharedCheck_2312_ == 0)
{
lean_object* v_unused_2313_; 
v_unused_2313_ = lean_ctor_get(v_toApplicative_2280_, 1);
lean_dec(v_unused_2313_);
v___x_2289_ = v_toApplicative_2280_;
v_isShared_2290_ = v_isSharedCheck_2312_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_toSeqRight_2287_);
lean_inc(v_toSeqLeft_2286_);
lean_inc(v_toSeq_2285_);
lean_inc(v_toFunctor_2284_);
lean_dec(v_toApplicative_2280_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2312_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___f_2291_; lean_object* v___f_2292_; lean_object* v___f_2293_; lean_object* v___f_2294_; lean_object* v___x_2295_; lean_object* v___f_2296_; lean_object* v___f_2297_; lean_object* v___f_2298_; lean_object* v___x_2300_; 
v___f_2291_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
v___f_2292_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(v_toFunctor_2284_);
v___f_2293_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2293_, 0, v_toFunctor_2284_);
v___f_2294_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2294_, 0, v_toFunctor_2284_);
v___x_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___f_2293_);
lean_ctor_set(v___x_2295_, 1, v___f_2294_);
v___f_2296_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2296_, 0, v_toSeqRight_2287_);
v___f_2297_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2297_, 0, v_toSeqLeft_2286_);
v___f_2298_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2298_, 0, v_toSeq_2285_);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 4, v___f_2296_);
lean_ctor_set(v___x_2289_, 3, v___f_2297_);
lean_ctor_set(v___x_2289_, 2, v___f_2298_);
lean_ctor_set(v___x_2289_, 1, v___f_2291_);
lean_ctor_set(v___x_2289_, 0, v___x_2295_);
v___x_2300_ = v___x_2289_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2295_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v___f_2291_);
lean_ctor_set(v_reuseFailAlloc_2311_, 2, v___f_2298_);
lean_ctor_set(v_reuseFailAlloc_2311_, 3, v___f_2297_);
lean_ctor_set(v_reuseFailAlloc_2311_, 4, v___f_2296_);
v___x_2300_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2302_; 
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 1, v___f_2292_);
lean_ctor_set(v___x_2282_, 0, v___x_2300_);
v___x_2302_ = v___x_2282_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v___f_2292_);
v___x_2302_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___f_2306_; lean_object* v___x_10948__overap_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2303_ = l_StateRefT_x27_instMonad___redArg(v___x_2302_);
v___x_2304_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v_pu_2245_);
v___x_2305_ = l_instInhabitedOfMonad___redArg(v___x_2303_, v___x_2304_);
v___f_2306_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2306_, 0, v___x_2305_);
v___x_10948__overap_2307_ = lean_panic_fn_borrowed(v___f_2306_, v_msg_2246_);
lean_dec_ref(v___f_2306_);
v___x_2308_ = lean_box(v___y_2247_);
lean_inc(v___y_2252_);
lean_inc_ref(v___y_2251_);
lean_inc(v___y_2250_);
lean_inc_ref(v___y_2249_);
lean_inc(v___y_2248_);
v___x_2309_ = lean_apply_7(v___x_10948__overap_2307_, v___x_2308_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, lean_box(0));
return v___x_2309_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___boxed(lean_object* v_pu_2322_, lean_object* v_msg_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
uint8_t v_pu_boxed_2331_; uint8_t v___y_10979__boxed_2332_; lean_object* v_res_2333_; 
v_pu_boxed_2331_ = lean_unbox(v_pu_2322_);
v___y_10979__boxed_2332_ = lean_unbox(v___y_2324_);
v_res_2333_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_boxed_2331_, v_msg_2323_, v___y_10979__boxed_2332_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
return v_res_2333_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2335_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2336_ = lean_unsigned_to_nat(41u);
v___x_2337_ = lean_unsigned_to_nat(217u);
v___x_2338_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2339_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2340_ = l_mkPanicMessageWithDecl(v___x_2339_, v___x_2338_, v___x_2337_, v___x_2336_, v___x_2335_);
return v___x_2340_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2(void){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2341_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2342_ = lean_unsigned_to_nat(31u);
v___x_2343_ = lean_unsigned_to_nat(222u);
v___x_2344_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2345_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2346_ = l_mkPanicMessageWithDecl(v___x_2345_, v___x_2344_, v___x_2343_, v___x_2342_, v___x_2341_);
return v___x_2346_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2347_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2348_ = lean_unsigned_to_nat(41u);
v___x_2349_ = lean_unsigned_to_nat(221u);
v___x_2350_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2351_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2352_ = l_mkPanicMessageWithDecl(v___x_2351_, v___x_2350_, v___x_2349_, v___x_2348_, v___x_2347_);
return v___x_2352_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4(void){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2353_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2354_ = lean_unsigned_to_nat(31u);
v___x_2355_ = lean_unsigned_to_nat(226u);
v___x_2356_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2357_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2358_ = l_mkPanicMessageWithDecl(v___x_2357_, v___x_2356_, v___x_2355_, v___x_2354_, v___x_2353_);
return v___x_2358_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5(void){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2359_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2360_ = lean_unsigned_to_nat(41u);
v___x_2361_ = lean_unsigned_to_nat(225u);
v___x_2362_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2363_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2364_ = l_mkPanicMessageWithDecl(v___x_2363_, v___x_2362_, v___x_2361_, v___x_2360_, v___x_2359_);
return v___x_2364_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2365_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2366_ = lean_unsigned_to_nat(41u);
v___x_2367_ = lean_unsigned_to_nat(230u);
v___x_2368_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2369_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2370_ = l_mkPanicMessageWithDecl(v___x_2369_, v___x_2368_, v___x_2367_, v___x_2366_, v___x_2365_);
return v___x_2370_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7(void){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2371_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2372_ = lean_unsigned_to_nat(41u);
v___x_2373_ = lean_unsigned_to_nat(233u);
v___x_2374_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2375_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2376_ = l_mkPanicMessageWithDecl(v___x_2375_, v___x_2374_, v___x_2373_, v___x_2372_, v___x_2371_);
return v___x_2376_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2377_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2378_ = lean_unsigned_to_nat(41u);
v___x_2379_ = lean_unsigned_to_nat(236u);
v___x_2380_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2381_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2382_ = l_mkPanicMessageWithDecl(v___x_2381_, v___x_2380_, v___x_2379_, v___x_2378_, v___x_2377_);
return v___x_2382_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9(void){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2383_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2384_ = lean_unsigned_to_nat(41u);
v___x_2385_ = lean_unsigned_to_nat(239u);
v___x_2386_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2387_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2388_ = l_mkPanicMessageWithDecl(v___x_2387_, v___x_2386_, v___x_2385_, v___x_2384_, v___x_2383_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t v_pu_2389_, lean_object* v_decl_2390_, uint8_t v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_){
_start:
{
switch(lean_obj_tag(v_decl_2390_))
{
case 0:
{
lean_object* v_decl_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2422_; 
v_decl_2398_ = lean_ctor_get(v_decl_2390_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v_decl_2390_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2400_ = v_decl_2390_;
v_isShared_2401_ = v_isSharedCheck_2422_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_decl_2398_);
lean_dec(v_decl_2390_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2422_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; 
v___x_2402_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_2389_, v_decl_2398_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2413_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2405_ = v___x_2402_;
v_isShared_2406_ = v_isSharedCheck_2413_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2402_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2413_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 0, v_a_2403_);
v___x_2408_ = v___x_2400_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2403_);
v___x_2408_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2410_; 
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v___x_2408_);
v___x_2410_ = v___x_2405_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_del_object(v___x_2400_);
v_a_2414_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2402_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2402_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2447_; 
v_decl_2423_ = lean_ctor_get(v_decl_2390_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v_decl_2390_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2425_ = v_decl_2390_;
v_isShared_2426_ = v_isSharedCheck_2447_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_decl_2423_);
lean_dec(v_decl_2390_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2447_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2427_; 
v___x_2427_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2389_, v_decl_2423_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2438_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2430_ = v___x_2427_;
v_isShared_2431_ = v_isSharedCheck_2438_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2427_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2438_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v_a_2428_);
v___x_2433_ = v___x_2425_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
lean_object* v___x_2435_; 
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 0, v___x_2433_);
v___x_2435_ = v___x_2430_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2433_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
lean_del_object(v___x_2425_);
v_a_2439_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2427_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2427_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
}
case 2:
{
lean_object* v_decl_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2472_; 
v_decl_2448_ = lean_ctor_get(v_decl_2390_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v_decl_2390_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2450_ = v_decl_2390_;
v_isShared_2451_ = v_isSharedCheck_2472_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_decl_2448_);
lean_dec(v_decl_2390_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2472_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2452_; 
v___x_2452_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2389_, v_decl_2448_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2463_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2463_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2463_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v_a_2453_);
v___x_2458_ = v___x_2450_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
lean_object* v___x_2460_; 
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2458_);
v___x_2460_ = v___x_2455_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2458_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_del_object(v___x_2450_);
v_a_2464_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2452_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2452_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_2473_; lean_object* v_i_2474_; lean_object* v_y_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2497_; 
v_fvarId_2473_ = lean_ctor_get(v_decl_2390_, 0);
v_i_2474_ = lean_ctor_get(v_decl_2390_, 1);
v_y_2475_ = lean_ctor_get(v_decl_2390_, 2);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_decl_2390_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2477_ = v_decl_2390_;
v_isShared_2478_ = v_isSharedCheck_2497_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_y_2475_);
lean_inc(v_i_2474_);
lean_inc(v_fvarId_2473_);
lean_dec(v_decl_2390_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2497_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2479_; uint8_t v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = lean_st_ref_get(v_a_2392_);
v___x_2480_ = 1;
v___x_2481_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2479_, v_fvarId_2473_, v___x_2480_);
lean_dec(v___x_2479_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_fvarId_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2494_; 
v_fvarId_2482_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2484_ = v___x_2481_;
v_isShared_2485_ = v_isSharedCheck_2494_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_fvarId_2482_);
lean_dec(v___x_2481_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2494_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2489_; 
v___x_2486_ = lean_st_ref_get(v_a_2392_);
v___x_2487_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2389_, v___x_2486_, v_y_2475_, v___x_2480_);
lean_dec(v___x_2486_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 2, v___x_2487_);
lean_ctor_set(v___x_2477_, 0, v_fvarId_2482_);
v___x_2489_ = v___x_2477_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_fvarId_2482_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_i_2474_);
lean_ctor_set(v_reuseFailAlloc_2493_, 2, v___x_2487_);
v___x_2489_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
lean_object* v___x_2491_; 
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 0, v___x_2489_);
v___x_2491_ = v___x_2484_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
else
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
lean_dec(v___x_2481_);
lean_del_object(v___x_2477_);
lean_dec(v_y_2475_);
lean_dec(v_i_2474_);
v___x_2495_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1);
v___x_2496_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2389_, v___x_2495_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
return v___x_2496_;
}
}
}
case 4:
{
lean_object* v_fvarId_2498_; lean_object* v_i_2499_; lean_object* v_y_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2525_; 
v_fvarId_2498_ = lean_ctor_get(v_decl_2390_, 0);
v_i_2499_ = lean_ctor_get(v_decl_2390_, 1);
v_y_2500_ = lean_ctor_get(v_decl_2390_, 2);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_decl_2390_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2502_ = v_decl_2390_;
v_isShared_2503_ = v_isSharedCheck_2525_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_y_2500_);
lean_inc(v_i_2499_);
lean_inc(v_fvarId_2498_);
lean_dec(v_decl_2390_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2525_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2504_; uint8_t v___x_2505_; lean_object* v___x_2506_; 
v___x_2504_ = lean_st_ref_get(v_a_2392_);
v___x_2505_ = 1;
v___x_2506_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2504_, v_fvarId_2498_, v___x_2505_);
lean_dec(v___x_2504_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_fvarId_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v_fvarId_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_fvarId_2507_);
lean_dec_ref_known(v___x_2506_, 1);
v___x_2508_ = lean_st_ref_get(v_a_2392_);
v___x_2509_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2508_, v_y_2500_, v___x_2505_);
lean_dec(v___x_2508_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_fvarId_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2520_; 
v_fvarId_2510_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2512_ = v___x_2509_;
v_isShared_2513_ = v_isSharedCheck_2520_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_fvarId_2510_);
lean_dec(v___x_2509_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2520_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 2, v_fvarId_2510_);
lean_ctor_set(v___x_2502_, 0, v_fvarId_2507_);
v___x_2515_ = v___x_2502_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_fvarId_2507_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v_i_2499_);
lean_ctor_set(v_reuseFailAlloc_2519_, 2, v_fvarId_2510_);
v___x_2515_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
lean_object* v___x_2517_; 
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v___x_2515_);
v___x_2517_ = v___x_2512_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
else
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
lean_dec(v___x_2509_);
lean_dec(v_fvarId_2507_);
lean_del_object(v___x_2502_);
lean_dec(v_i_2499_);
v___x_2521_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2);
v___x_2522_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2389_, v___x_2521_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
return v___x_2522_;
}
}
else
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
lean_dec(v___x_2506_);
lean_del_object(v___x_2502_);
lean_dec(v_y_2500_);
lean_dec(v_i_2499_);
v___x_2523_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3);
v___x_2524_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2389_, v___x_2523_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
return v___x_2524_;
}
}
}
case 5:
{
lean_object* v_fvarId_2526_; lean_object* v_i_2527_; lean_object* v_offset_2528_; lean_object* v_y_2529_; lean_object* v_ty_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2557_; 
v_fvarId_2526_ = lean_ctor_get(v_decl_2390_, 0);
v_i_2527_ = lean_ctor_get(v_decl_2390_, 1);
v_offset_2528_ = lean_ctor_get(v_decl_2390_, 2);
v_y_2529_ = lean_ctor_get(v_decl_2390_, 3);
v_ty_2530_ = lean_ctor_get(v_decl_2390_, 4);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_decl_2390_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2532_ = v_decl_2390_;
v_isShared_2533_ = v_isSharedCheck_2557_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_ty_2530_);
lean_inc(v_y_2529_);
lean_inc(v_offset_2528_);
lean_inc(v_i_2527_);
lean_inc(v_fvarId_2526_);
lean_dec(v_decl_2390_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2557_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2534_; uint8_t v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = lean_st_ref_get(v_a_2392_);
v___x_2535_ = 1;
v___x_2536_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2534_, v_fvarId_2526_, v___x_2535_);
lean_dec(v___x_2534_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_fvarId_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v_fvarId_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_fvarId_2537_);
lean_dec_ref_known(v___x_2536_, 1);
v___x_2538_ = lean_st_ref_get(v_a_2392_);
v___x_2539_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2538_, v_y_2529_, v___x_2535_);
lean_dec(v___x_2538_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_fvarId_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2552_; 
v_fvarId_2540_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2542_ = v___x_2539_;
v_isShared_2543_ = v_isSharedCheck_2552_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_fvarId_2540_);
lean_dec(v___x_2539_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2552_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2547_; 
v___x_2544_ = lean_st_ref_get(v_a_2392_);
v___x_2545_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2389_, v___x_2544_, v___x_2535_, v_ty_2530_);
lean_dec(v___x_2544_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 4, v___x_2545_);
lean_ctor_set(v___x_2532_, 3, v_fvarId_2540_);
lean_ctor_set(v___x_2532_, 0, v_fvarId_2537_);
v___x_2547_ = v___x_2532_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_fvarId_2537_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v_i_2527_);
lean_ctor_set(v_reuseFailAlloc_2551_, 2, v_offset_2528_);
lean_ctor_set(v_reuseFailAlloc_2551_, 3, v_fvarId_2540_);
lean_ctor_set(v_reuseFailAlloc_2551_, 4, v___x_2545_);
v___x_2547_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2549_; 
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 0, v___x_2547_);
v___x_2549_ = v___x_2542_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2547_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
lean_dec(v___x_2539_);
lean_dec(v_fvarId_2537_);
lean_del_object(v___x_2532_);
lean_dec_ref(v_ty_2530_);
lean_dec(v_offset_2528_);
lean_dec(v_i_2527_);
v___x_2553_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4);
v___x_2554_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2389_, v___x_2553_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
return v___x_2554_;
}
}
else
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
lean_dec(v___x_2536_);
lean_del_object(v___x_2532_);
lean_dec_ref(v_ty_2530_);
lean_dec(v_y_2529_);
lean_dec(v_offset_2528_);
lean_dec(v_i_2527_);
v___x_2555_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5);
v___x_2556_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2389_, v___x_2555_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
return v___x_2556_;
}
}
}
case 6:
{
lean_object* v_fvarId_2558_; lean_object* v_cidx_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2579_; 
v_fvarId_2558_ = lean_ctor_get(v_decl_2390_, 0);
v_cidx_2559_ = lean_ctor_get(v_decl_2390_, 1);
v_isSharedCheck_2579_ = !lean_is_exclusive(v_decl_2390_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2561_ = v_decl_2390_;
v_isShared_2562_ = v_isSharedCheck_2579_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_cidx_2559_);
lean_inc(v_fvarId_2558_);
lean_dec(v_decl_2390_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2579_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2563_; uint8_t v___x_2564_; lean_object* v___x_2565_; 
v___x_2563_ = lean_st_ref_get(v_a_2392_);
v___x_2564_ = 1;
v___x_2565_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2563_, v_fvarId_2558_, v___x_2564_);
lean_dec(v___x_2563_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_fvarId_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2576_; 
v_fvarId_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2576_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_fvarId_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2576_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v_fvarId_2566_);
v___x_2571_ = v___x_2561_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_fvarId_2566_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_cidx_2559_);
v___x_2571_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2573_; 
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2571_);
v___x_2573_ = v___x_2568_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2571_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
else
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
lean_dec(v___x_2565_);
lean_del_object(v___x_2561_);
lean_dec(v_cidx_2559_);
v___x_2577_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6);
v___x_2578_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2389_, v___x_2577_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
return v___x_2578_;
}
}
}
case 7:
{
lean_object* v_fvarId_2580_; lean_object* v_n_2581_; uint8_t v_check_2582_; uint8_t v_persistent_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2603_; 
v_fvarId_2580_ = lean_ctor_get(v_decl_2390_, 0);
v_n_2581_ = lean_ctor_get(v_decl_2390_, 1);
v_check_2582_ = lean_ctor_get_uint8(v_decl_2390_, sizeof(void*)*2);
v_persistent_2583_ = lean_ctor_get_uint8(v_decl_2390_, sizeof(void*)*2 + 1);
v_isSharedCheck_2603_ = !lean_is_exclusive(v_decl_2390_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2585_ = v_decl_2390_;
v_isShared_2586_ = v_isSharedCheck_2603_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_n_2581_);
lean_inc(v_fvarId_2580_);
lean_dec(v_decl_2390_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2603_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; uint8_t v___x_2588_; lean_object* v___x_2589_; 
v___x_2587_ = lean_st_ref_get(v_a_2392_);
v___x_2588_ = 1;
v___x_2589_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2587_, v_fvarId_2580_, v___x_2588_);
lean_dec(v___x_2587_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_fvarId_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2600_; 
v_fvarId_2590_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2592_ = v___x_2589_;
v_isShared_2593_ = v_isSharedCheck_2600_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_fvarId_2590_);
lean_dec(v___x_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2600_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v_fvarId_2590_);
v___x_2595_ = v___x_2585_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_fvarId_2590_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v_n_2581_);
lean_ctor_set_uint8(v_reuseFailAlloc_2599_, sizeof(void*)*2, v_check_2582_);
lean_ctor_set_uint8(v_reuseFailAlloc_2599_, sizeof(void*)*2 + 1, v_persistent_2583_);
v___x_2595_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2597_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 0, v___x_2595_);
v___x_2597_ = v___x_2592_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
lean_dec(v___x_2589_);
lean_del_object(v___x_2585_);
lean_dec(v_n_2581_);
v___x_2601_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7);
v___x_2602_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2389_, v___x_2601_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
return v___x_2602_;
}
}
}
case 8:
{
lean_object* v_fvarId_2604_; lean_object* v_n_2605_; uint8_t v_check_2606_; uint8_t v_persistent_2607_; lean_object* v_objs_x3f_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2628_; 
v_fvarId_2604_ = lean_ctor_get(v_decl_2390_, 0);
v_n_2605_ = lean_ctor_get(v_decl_2390_, 1);
v_check_2606_ = lean_ctor_get_uint8(v_decl_2390_, sizeof(void*)*3);
v_persistent_2607_ = lean_ctor_get_uint8(v_decl_2390_, sizeof(void*)*3 + 1);
v_objs_x3f_2608_ = lean_ctor_get(v_decl_2390_, 2);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_decl_2390_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2610_ = v_decl_2390_;
v_isShared_2611_ = v_isSharedCheck_2628_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_objs_x3f_2608_);
lean_inc(v_n_2605_);
lean_inc(v_fvarId_2604_);
lean_dec(v_decl_2390_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2628_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; uint8_t v___x_2613_; lean_object* v___x_2614_; 
v___x_2612_ = lean_st_ref_get(v_a_2392_);
v___x_2613_ = 1;
v___x_2614_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2612_, v_fvarId_2604_, v___x_2613_);
lean_dec(v___x_2612_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_fvarId_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2625_; 
v_fvarId_2615_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2617_ = v___x_2614_;
v_isShared_2618_ = v_isSharedCheck_2625_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_fvarId_2615_);
lean_dec(v___x_2614_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2625_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v_fvarId_2615_);
v___x_2620_ = v___x_2610_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(8, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_fvarId_2615_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_n_2605_);
lean_ctor_set(v_reuseFailAlloc_2624_, 2, v_objs_x3f_2608_);
lean_ctor_set_uint8(v_reuseFailAlloc_2624_, sizeof(void*)*3, v_check_2606_);
lean_ctor_set_uint8(v_reuseFailAlloc_2624_, sizeof(void*)*3 + 1, v_persistent_2607_);
v___x_2620_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
lean_object* v___x_2622_; 
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v___x_2620_);
v___x_2622_ = v___x_2617_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
else
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_dec(v___x_2614_);
lean_del_object(v___x_2610_);
lean_dec(v_objs_x3f_2608_);
lean_dec(v_n_2605_);
v___x_2626_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8);
v___x_2627_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2389_, v___x_2626_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
return v___x_2627_;
}
}
}
default: 
{
lean_object* v_fvarId_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2649_; 
v_fvarId_2629_ = lean_ctor_get(v_decl_2390_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_decl_2390_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2631_ = v_decl_2390_;
v_isShared_2632_ = v_isSharedCheck_2649_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_fvarId_2629_);
lean_dec(v_decl_2390_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2649_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2633_; uint8_t v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = lean_st_ref_get(v_a_2392_);
v___x_2634_ = 1;
v___x_2635_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2633_, v_fvarId_2629_, v___x_2634_);
lean_dec(v___x_2633_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_fvarId_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2646_; 
v_fvarId_2636_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2638_ = v___x_2635_;
v_isShared_2639_ = v_isSharedCheck_2646_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_fvarId_2636_);
lean_dec(v___x_2635_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2646_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v_fvarId_2636_);
v___x_2641_ = v___x_2631_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_fvarId_2636_);
v___x_2641_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
lean_object* v___x_2643_; 
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v___x_2641_);
v___x_2643_ = v___x_2638_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2641_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
lean_dec(v___x_2635_);
lean_del_object(v___x_2631_);
v___x_2647_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9);
v___x_2648_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2389_, v___x_2647_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
return v___x_2648_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(lean_object* v_pu_2650_, lean_object* v_decl_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
uint8_t v_pu_boxed_2659_; uint8_t v_a_boxed_2660_; lean_object* v_res_2661_; 
v_pu_boxed_2659_ = lean_unbox(v_pu_2650_);
v_a_boxed_2660_ = lean_unbox(v_a_2652_);
v_res_2661_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v_pu_boxed_2659_, v_decl_2651_, v_a_boxed_2660_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t v_pu_2662_, lean_object* v_code_2663_, lean_object* v_s_2664_, uint8_t v_uniqueIdents_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = lean_st_mk_ref(v_s_2664_);
v___x_2672_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2662_, v_code_2663_, v_uniqueIdents_2665_, v___x_2671_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2681_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2675_ = v___x_2672_;
v_isShared_2676_ = v_isSharedCheck_2681_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2672_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2681_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2677_; lean_object* v___x_2679_; 
v___x_2677_ = lean_st_ref_get(v___x_2671_);
lean_dec(v___x_2671_);
lean_dec(v___x_2677_);
if (v_isShared_2676_ == 0)
{
v___x_2679_ = v___x_2675_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2673_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
else
{
lean_dec(v___x_2671_);
return v___x_2672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize___boxed(lean_object* v_pu_2682_, lean_object* v_code_2683_, lean_object* v_s_2684_, lean_object* v_uniqueIdents_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_){
_start:
{
uint8_t v_pu_boxed_2691_; uint8_t v_uniqueIdents_boxed_2692_; lean_object* v_res_2693_; 
v_pu_boxed_2691_ = lean_unbox(v_pu_2682_);
v_uniqueIdents_boxed_2692_ = lean_unbox(v_uniqueIdents_2685_);
v_res_2693_ = l_Lean_Compiler_LCNF_Code_internalize(v_pu_boxed_2691_, v_code_2683_, v_s_2684_, v_uniqueIdents_boxed_2692_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(lean_object* v_f_2694_, lean_object* v_v_2695_, uint8_t v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
if (lean_obj_tag(v_v_2695_) == 0)
{
lean_object* v_code_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2728_; 
v_code_2703_ = lean_ctor_get(v_v_2695_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_v_2695_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2705_ = v_v_2695_;
v_isShared_2706_ = v_isSharedCheck_2728_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_code_2703_);
lean_dec(v_v_2695_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2728_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = lean_box(v___y_2696_);
lean_inc(v___y_2701_);
lean_inc_ref(v___y_2700_);
lean_inc(v___y_2699_);
lean_inc_ref(v___y_2698_);
lean_inc(v___y_2697_);
v___x_2708_ = lean_apply_8(v_f_2694_, v_code_2703_, v___x_2707_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, lean_box(0));
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2719_; 
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2711_ = v___x_2708_;
v_isShared_2712_ = v_isSharedCheck_2719_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2708_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2719_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 0, v_a_2709_);
v___x_2714_ = v___x_2705_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
lean_object* v___x_2716_; 
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v___x_2714_);
v___x_2716_ = v___x_2711_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_del_object(v___x_2705_);
v_a_2720_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2708_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2708_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
else
{
lean_object* v___x_2729_; 
lean_dec_ref(v_f_2694_);
v___x_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2729_, 0, v_v_2695_);
return v___x_2729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg___boxed(lean_object* v_f_2730_, lean_object* v_v_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
uint8_t v___y_1412__boxed_2739_; lean_object* v_res_2740_; 
v___y_1412__boxed_2739_ = lean_unbox(v___y_2732_);
v_res_2740_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2730_, v_v_2731_, v___y_1412__boxed_2739_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(uint8_t v_pu_2741_, lean_object* v_f_2742_, lean_object* v_v_2743_, uint8_t v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2742_, v_v_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___boxed(lean_object* v_pu_2752_, lean_object* v_f_2753_, lean_object* v_v_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
uint8_t v_pu_boxed_2762_; uint8_t v___y_1488__boxed_2763_; lean_object* v_res_2764_; 
v_pu_boxed_2762_ = lean_unbox(v_pu_2752_);
v___y_1488__boxed_2763_ = lean_unbox(v___y_2755_);
v_res_2764_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(v_pu_boxed_2762_, v_f_2753_, v_v_2754_, v___y_1488__boxed_2763_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(uint8_t v_pu_2765_, lean_object* v_decl_2766_, uint8_t v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v_toSignature_2774_; lean_object* v_value_2775_; uint8_t v_recursive_2776_; lean_object* v_inlineAttr_x3f_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2837_; 
v_toSignature_2774_ = lean_ctor_get(v_decl_2766_, 0);
v_value_2775_ = lean_ctor_get(v_decl_2766_, 1);
v_recursive_2776_ = lean_ctor_get_uint8(v_decl_2766_, sizeof(void*)*3);
v_inlineAttr_x3f_2777_ = lean_ctor_get(v_decl_2766_, 2);
v_isSharedCheck_2837_ = !lean_is_exclusive(v_decl_2766_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2779_ = v_decl_2766_;
v_isShared_2780_ = v_isSharedCheck_2837_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_inlineAttr_x3f_2777_);
lean_inc(v_value_2775_);
lean_inc(v_toSignature_2774_);
lean_dec(v_decl_2766_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2837_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v_name_2781_; lean_object* v_levelParams_2782_; lean_object* v_type_2783_; lean_object* v_params_2784_; uint8_t v_safe_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2836_; 
v_name_2781_ = lean_ctor_get(v_toSignature_2774_, 0);
v_levelParams_2782_ = lean_ctor_get(v_toSignature_2774_, 1);
v_type_2783_ = lean_ctor_get(v_toSignature_2774_, 2);
v_params_2784_ = lean_ctor_get(v_toSignature_2774_, 3);
v_safe_2785_ = lean_ctor_get_uint8(v_toSignature_2774_, sizeof(void*)*4);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_toSignature_2774_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2787_ = v_toSignature_2774_;
v_isShared_2788_ = v_isSharedCheck_2836_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_params_2784_);
lean_inc(v_type_2783_);
lean_inc(v_levelParams_2782_);
lean_inc(v_name_2781_);
lean_dec(v_toSignature_2774_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2836_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2789_; 
v___x_2789_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2765_, v_type_2783_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; size_t v_sz_2791_; size_t v___x_2792_; lean_object* v___x_2793_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2789_, 1);
v_sz_2791_ = lean_array_size(v_params_2784_);
v___x_2792_ = ((size_t)0ULL);
v___x_2793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2765_, v_sz_2791_, v___x_2792_, v_params_2784_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___x_2793_, 1);
v___x_2795_ = lean_box(v_pu_2765_);
v___x_2796_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed), 9, 1);
lean_closure_set(v___x_2796_, 0, v___x_2795_);
v___x_2797_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v___x_2796_, v_value_2775_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2811_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2800_ = v___x_2797_;
v_isShared_2801_ = v_isSharedCheck_2811_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2797_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2811_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 3, v_a_2794_);
lean_ctor_set(v___x_2787_, 2, v_a_2790_);
v___x_2803_ = v___x_2787_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_name_2781_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v_levelParams_2782_);
lean_ctor_set(v_reuseFailAlloc_2810_, 2, v_a_2790_);
lean_ctor_set(v_reuseFailAlloc_2810_, 3, v_a_2794_);
lean_ctor_set_uint8(v_reuseFailAlloc_2810_, sizeof(void*)*4, v_safe_2785_);
v___x_2803_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
lean_object* v___x_2805_; 
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 1, v_a_2798_);
lean_ctor_set(v___x_2779_, 0, v___x_2803_);
v___x_2805_ = v___x_2779_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2803_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v_a_2798_);
lean_ctor_set(v_reuseFailAlloc_2809_, 2, v_inlineAttr_x3f_2777_);
lean_ctor_set_uint8(v_reuseFailAlloc_2809_, sizeof(void*)*3, v_recursive_2776_);
v___x_2805_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
lean_object* v___x_2807_; 
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 0, v___x_2805_);
v___x_2807_ = v___x_2800_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2805_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec(v_a_2794_);
lean_dec(v_a_2790_);
lean_del_object(v___x_2787_);
lean_dec(v_levelParams_2782_);
lean_dec(v_name_2781_);
lean_del_object(v___x_2779_);
lean_dec(v_inlineAttr_x3f_2777_);
v_a_2812_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2797_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2797_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec(v_a_2790_);
lean_del_object(v___x_2787_);
lean_dec(v_levelParams_2782_);
lean_dec(v_name_2781_);
lean_del_object(v___x_2779_);
lean_dec(v_inlineAttr_x3f_2777_);
lean_dec_ref(v_value_2775_);
v_a_2820_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2793_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2793_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_del_object(v___x_2787_);
lean_dec_ref(v_params_2784_);
lean_dec(v_levelParams_2782_);
lean_dec(v_name_2781_);
lean_del_object(v___x_2779_);
lean_dec(v_inlineAttr_x3f_2777_);
lean_dec_ref(v_value_2775_);
v_a_2828_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2789_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2789_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go___boxed(lean_object* v_pu_2838_, lean_object* v_decl_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_){
_start:
{
uint8_t v_pu_boxed_2847_; uint8_t v_a_boxed_2848_; lean_object* v_res_2849_; 
v_pu_boxed_2847_ = lean_unbox(v_pu_2838_);
v_a_boxed_2848_ = lean_unbox(v_a_2840_);
v_res_2849_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_boxed_2847_, v_decl_2839_, v_a_boxed_2848_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
lean_dec(v_a_2845_);
lean_dec_ref(v_a_2844_);
lean_dec(v_a_2843_);
lean_dec_ref(v_a_2842_);
lean_dec(v_a_2841_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t v_pu_2850_, lean_object* v_decl_2851_, lean_object* v_s_2852_, uint8_t v_uniqueIdents_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = lean_st_mk_ref(v_s_2852_);
v___x_2860_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_2850_, v_decl_2851_, v_uniqueIdents_2853_, v___x_2859_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2869_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2863_ = v___x_2860_;
v_isShared_2864_ = v_isSharedCheck_2869_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2860_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2869_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2865_; lean_object* v___x_2867_; 
v___x_2865_ = lean_st_ref_get(v___x_2859_);
lean_dec(v___x_2859_);
lean_dec(v___x_2865_);
if (v_isShared_2864_ == 0)
{
v___x_2867_ = v___x_2863_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2861_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
else
{
lean_dec(v___x_2859_);
return v___x_2860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize___boxed(lean_object* v_pu_2870_, lean_object* v_decl_2871_, lean_object* v_s_2872_, lean_object* v_uniqueIdents_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_){
_start:
{
uint8_t v_pu_boxed_2879_; uint8_t v_uniqueIdents_boxed_2880_; lean_object* v_res_2881_; 
v_pu_boxed_2879_ = lean_unbox(v_pu_2870_);
v_uniqueIdents_boxed_2880_ = lean_unbox(v_uniqueIdents_2873_);
v_res_2881_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_boxed_2879_, v_decl_2871_, v_s_2872_, v_uniqueIdents_boxed_2880_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
lean_dec(v_a_2877_);
lean_dec_ref(v_a_2876_);
lean_dec(v_a_2875_);
lean_dec_ref(v_a_2874_);
return v_res_2881_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2882_ = lean_box(0);
v___x_2883_ = lean_unsigned_to_nat(16u);
v___x_2884_ = lean_mk_array(v___x_2883_, v___x_2882_);
return v___x_2884_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2885_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0);
v___x_2886_ = lean_unsigned_to_nat(0u);
v___x_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
lean_ctor_set(v___x_2887_, 1, v___x_2885_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(uint8_t v_pu_2888_, size_t v_sz_2889_, size_t v_i_2890_, lean_object* v_bs_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
uint8_t v___x_2897_; 
v___x_2897_ = lean_usize_dec_lt(v_i_2890_, v_sz_2889_);
if (v___x_2897_ == 0)
{
lean_object* v___x_2898_; 
v___x_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2898_, 0, v_bs_2891_);
return v___x_2898_;
}
else
{
lean_object* v___x_2899_; lean_object* v_lctx_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2928_; 
v___x_2899_ = lean_st_ref_take(v___y_2893_);
v_lctx_2900_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2928_ == 0)
{
lean_object* v_unused_2929_; 
v_unused_2929_ = lean_ctor_get(v___x_2899_, 1);
lean_dec(v_unused_2929_);
v___x_2902_ = v___x_2899_;
v_isShared_2903_ = v_isSharedCheck_2928_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_lctx_2900_);
lean_dec(v___x_2899_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2928_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2904_; lean_object* v___x_2906_; 
v___x_2904_ = lean_unsigned_to_nat(1u);
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 1, v___x_2904_);
v___x_2906_ = v___x_2902_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_lctx_2900_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v___x_2904_);
v___x_2906_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2907_; lean_object* v_v_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; lean_object* v___x_2912_; 
v___x_2907_ = lean_st_ref_put(v___y_2893_, v___x_2906_);
v_v_2908_ = lean_array_uget_borrowed(v_bs_2891_, v_i_2890_);
v___x_2909_ = lean_unsigned_to_nat(0u);
v___x_2910_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_2911_ = 0;
lean_inc(v_v_2908_);
v___x_2912_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_2888_, v_v_2908_, v___x_2910_, v___x_2911_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; lean_object* v_bs_x27_2914_; size_t v___x_2915_; size_t v___x_2916_; lean_object* v___x_2917_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref_known(v___x_2912_, 1);
v_bs_x27_2914_ = lean_array_uset(v_bs_2891_, v_i_2890_, v___x_2909_);
v___x_2915_ = ((size_t)1ULL);
v___x_2916_ = lean_usize_add(v_i_2890_, v___x_2915_);
v___x_2917_ = lean_array_uset(v_bs_x27_2914_, v_i_2890_, v_a_2913_);
v_i_2890_ = v___x_2916_;
v_bs_2891_ = v___x_2917_;
goto _start;
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_dec_ref(v_bs_2891_);
v_a_2919_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2912_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2912_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___boxed(lean_object* v_pu_2930_, lean_object* v_sz_2931_, lean_object* v_i_2932_, lean_object* v_bs_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
uint8_t v_pu_boxed_2939_; size_t v_sz_boxed_2940_; size_t v_i_boxed_2941_; lean_object* v_res_2942_; 
v_pu_boxed_2939_ = lean_unbox(v_pu_2930_);
v_sz_boxed_2940_ = lean_unbox_usize(v_sz_2931_);
lean_dec(v_sz_2931_);
v_i_boxed_2941_ = lean_unbox_usize(v_i_2932_);
lean_dec(v_i_2932_);
v_res_2942_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_boxed_2939_, v_sz_boxed_2940_, v_i_boxed_2941_, v_bs_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
return v_res_2942_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__0(void){
_start:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2943_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_2944_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2943_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
lean_ctor_set(v___x_2944_, 2, v___x_2943_);
lean_ctor_set(v___x_2944_, 3, v___x_2943_);
lean_ctor_set(v___x_2944_, 4, v___x_2943_);
lean_ctor_set(v___x_2944_, 5, v___x_2943_);
return v___x_2944_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__1(void){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2945_ = lean_unsigned_to_nat(1u);
v___x_2946_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__0, &l_Lean_Compiler_LCNF_cleanup___closed__0_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__0);
v___x_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
lean_ctor_set(v___x_2947_, 1, v___x_2945_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup(uint8_t v_pu_2948_, lean_object* v_decl_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; size_t v_sz_2958_; size_t v___x_2959_; lean_object* v___x_2960_; 
v___x_2955_ = lean_st_ref_take(v_a_2951_);
lean_dec(v___x_2955_);
v___x_2956_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
v___x_2957_ = lean_st_ref_put(v_a_2951_, v___x_2956_);
v_sz_2958_ = lean_array_size(v_decl_2949_);
v___x_2959_ = ((size_t)0ULL);
v___x_2960_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_2948_, v_sz_2958_, v___x_2959_, v_decl_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup___boxed(lean_object* v_pu_2961_, lean_object* v_decl_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_){
_start:
{
uint8_t v_pu_boxed_2968_; lean_object* v_res_2969_; 
v_pu_boxed_2968_ = lean_unbox(v_pu_2961_);
v_res_2969_ = l_Lean_Compiler_LCNF_cleanup(v_pu_boxed_2968_, v_decl_2962_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_);
lean_dec(v_a_2966_);
lean_dec_ref(v_a_2965_);
lean_dec(v_a_2964_);
lean_dec_ref(v_a_2963_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(lean_object* v_a_2970_, lean_object* v_ngen_2971_, lean_object* v_a_x3f_2972_){
_start:
{
lean_object* v___x_2974_; lean_object* v_env_2975_; lean_object* v_nextMacroScope_2976_; lean_object* v_auxDeclNGen_2977_; lean_object* v_traceState_2978_; lean_object* v_cache_2979_; lean_object* v_messages_2980_; lean_object* v_infoState_2981_; lean_object* v_snapshotTasks_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2992_; 
v___x_2974_ = lean_st_ref_take(v_a_2970_);
v_env_2975_ = lean_ctor_get(v___x_2974_, 0);
v_nextMacroScope_2976_ = lean_ctor_get(v___x_2974_, 1);
v_auxDeclNGen_2977_ = lean_ctor_get(v___x_2974_, 3);
v_traceState_2978_ = lean_ctor_get(v___x_2974_, 4);
v_cache_2979_ = lean_ctor_get(v___x_2974_, 5);
v_messages_2980_ = lean_ctor_get(v___x_2974_, 6);
v_infoState_2981_ = lean_ctor_get(v___x_2974_, 7);
v_snapshotTasks_2982_ = lean_ctor_get(v___x_2974_, 8);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2992_ == 0)
{
lean_object* v_unused_2993_; 
v_unused_2993_ = lean_ctor_get(v___x_2974_, 2);
lean_dec(v_unused_2993_);
v___x_2984_ = v___x_2974_;
v_isShared_2985_ = v_isSharedCheck_2992_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_snapshotTasks_2982_);
lean_inc(v_infoState_2981_);
lean_inc(v_messages_2980_);
lean_inc(v_cache_2979_);
lean_inc(v_traceState_2978_);
lean_inc(v_auxDeclNGen_2977_);
lean_inc(v_nextMacroScope_2976_);
lean_inc(v_env_2975_);
lean_dec(v___x_2974_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2992_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 2, v_ngen_2971_);
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_env_2975_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_nextMacroScope_2976_);
lean_ctor_set(v_reuseFailAlloc_2991_, 2, v_ngen_2971_);
lean_ctor_set(v_reuseFailAlloc_2991_, 3, v_auxDeclNGen_2977_);
lean_ctor_set(v_reuseFailAlloc_2991_, 4, v_traceState_2978_);
lean_ctor_set(v_reuseFailAlloc_2991_, 5, v_cache_2979_);
lean_ctor_set(v_reuseFailAlloc_2991_, 6, v_messages_2980_);
lean_ctor_set(v_reuseFailAlloc_2991_, 7, v_infoState_2981_);
lean_ctor_set(v_reuseFailAlloc_2991_, 8, v_snapshotTasks_2982_);
v___x_2987_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2988_ = lean_st_ref_put(v_a_2970_, v___x_2987_);
v___x_2989_ = lean_box(0);
v___x_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
return v___x_2990_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0___boxed(lean_object* v_a_2994_, lean_object* v_ngen_2995_, lean_object* v_a_x3f_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_2994_, v_ngen_2995_, v_a_x3f_2996_);
lean_dec(v_a_x3f_2996_);
lean_dec(v_a_2994_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(uint8_t v_pu_3005_, lean_object* v_decl_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_){
_start:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v_env_3012_; lean_object* v_nextMacroScope_3013_; lean_object* v_auxDeclNGen_3014_; lean_object* v_traceState_3015_; lean_object* v_cache_3016_; lean_object* v_messages_3017_; lean_object* v_infoState_3018_; lean_object* v_snapshotTasks_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3065_; 
v___x_3010_ = lean_st_ref_get(v_a_3008_);
v___x_3011_ = lean_st_ref_take(v_a_3008_);
v_env_3012_ = lean_ctor_get(v___x_3011_, 0);
v_nextMacroScope_3013_ = lean_ctor_get(v___x_3011_, 1);
v_auxDeclNGen_3014_ = lean_ctor_get(v___x_3011_, 3);
v_traceState_3015_ = lean_ctor_get(v___x_3011_, 4);
v_cache_3016_ = lean_ctor_get(v___x_3011_, 5);
v_messages_3017_ = lean_ctor_get(v___x_3011_, 6);
v_infoState_3018_ = lean_ctor_get(v___x_3011_, 7);
v_snapshotTasks_3019_ = lean_ctor_get(v___x_3011_, 8);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3065_ == 0)
{
lean_object* v_unused_3066_; 
v_unused_3066_ = lean_ctor_get(v___x_3011_, 2);
lean_dec(v_unused_3066_);
v___x_3021_ = v___x_3011_;
v_isShared_3022_ = v_isSharedCheck_3065_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_snapshotTasks_3019_);
lean_inc(v_infoState_3018_);
lean_inc(v_messages_3017_);
lean_inc(v_cache_3016_);
lean_inc(v_traceState_3015_);
lean_inc(v_auxDeclNGen_3014_);
lean_inc(v_nextMacroScope_3013_);
lean_inc(v_env_3012_);
lean_dec(v___x_3011_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3065_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3023_ = ((lean_object*)(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2));
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 2, v___x_3023_);
v___x_3025_ = v___x_3021_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_env_3012_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v_nextMacroScope_3013_);
lean_ctor_set(v_reuseFailAlloc_3064_, 2, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3064_, 3, v_auxDeclNGen_3014_);
lean_ctor_set(v_reuseFailAlloc_3064_, 4, v_traceState_3015_);
lean_ctor_set(v_reuseFailAlloc_3064_, 5, v_cache_3016_);
lean_ctor_set(v_reuseFailAlloc_3064_, 6, v_messages_3017_);
lean_ctor_set(v_reuseFailAlloc_3064_, 7, v_infoState_3018_);
lean_ctor_set(v_reuseFailAlloc_3064_, 8, v_snapshotTasks_3019_);
v___x_3025_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3026_; lean_object* v_ngen_3027_; lean_object* v___x_3028_; uint8_t v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; uint8_t v___x_3034_; lean_object* v_r_3035_; 
v___x_3026_ = lean_st_ref_put(v_a_3008_, v___x_3025_);
v_ngen_3027_ = lean_ctor_get(v___x_3010_, 2);
lean_inc_ref(v_ngen_3027_);
lean_dec(v___x_3010_);
v___x_3028_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_3029_ = 0;
v___x_3030_ = lean_box(v_pu_3005_);
v___x_3031_ = lean_box(v___x_3029_);
v___x_3032_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_internalize___boxed), 9, 4);
lean_closure_set(v___x_3032_, 0, v___x_3030_);
lean_closure_set(v___x_3032_, 1, v_decl_3006_);
lean_closure_set(v___x_3032_, 2, v___x_3028_);
lean_closure_set(v___x_3032_, 3, v___x_3031_);
v___x_3033_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
v___x_3034_ = 0;
v_r_3035_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v___x_3032_, v___x_3033_, v___x_3034_, v_a_3007_, v_a_3008_);
if (lean_obj_tag(v_r_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3052_; 
v_a_3036_ = lean_ctor_get(v_r_3035_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v_r_3035_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3038_ = v_r_3035_;
v_isShared_3039_ = v_isSharedCheck_3052_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v_r_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3052_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
lean_inc(v_a_3036_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set_tag(v___x_3038_, 1);
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
lean_object* v___x_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
v___x_3042_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3008_, v_ngen_3027_, v___x_3041_);
lean_dec_ref(v___x_3041_);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3049_ == 0)
{
lean_object* v_unused_3050_; 
v_unused_3050_ = lean_ctor_get(v___x_3042_, 0);
lean_dec(v_unused_3050_);
v___x_3044_ = v___x_3042_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_dec(v___x_3042_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 0, v_a_3036_);
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3036_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
v_a_3053_ = lean_ctor_get(v_r_3035_, 0);
lean_inc(v_a_3053_);
lean_dec_ref_known(v_r_3035_, 1);
v___x_3054_ = lean_box(0);
v___x_3055_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3008_, v_ngen_3027_, v___x_3054_);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3062_ == 0)
{
lean_object* v_unused_3063_; 
v_unused_3063_ = lean_ctor_get(v___x_3055_, 0);
lean_dec(v_unused_3063_);
v___x_3057_ = v___x_3055_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_dec(v___x_3055_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
lean_ctor_set_tag(v___x_3057_, 1);
lean_ctor_set(v___x_3057_, 0, v_a_3053_);
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3053_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___boxed(lean_object* v_pu_3067_, lean_object* v_decl_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_){
_start:
{
uint8_t v_pu_boxed_3072_; lean_object* v_res_3073_; 
v_pu_boxed_3072_ = lean_unbox(v_pu_3067_);
v_res_3073_ = l_Lean_Compiler_LCNF_normalizeFVarIds(v_pu_boxed_3072_, v_decl_3068_, v_a_3069_, v_a_3070_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
return v_res_3073_;
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
