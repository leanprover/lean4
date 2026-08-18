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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Compiler_LCNF_instDecidableEqPurity(uint8_t, uint8_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_anyExpr;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_cleanup___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_cleanup___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_cleanup___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_cleanup___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_cleanup___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_cleanup___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_cleanup___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_cleanup___closed__3;
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
static lean_once_cell_t l_Lean_Compiler_LCNF_normalizeFVarIds___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___closed__3;
static lean_once_cell_t l_Lean_Compiler_LCNF_normalizeFVarIds___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___closed__4;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(lean_object* v_m_275_, lean_object* v_query_276_, lean_object* v_x_277_, lean_object* v_x_278_, lean_object* v_x_279_){
_start:
{
lean_object* v_zero_280_; uint8_t v_isZero_281_; 
v_zero_280_ = lean_unsigned_to_nat(0u);
v_isZero_281_ = lean_nat_dec_eq(v_x_278_, v_zero_280_);
if (v_isZero_281_ == 1)
{
lean_dec(v_x_279_);
lean_dec(v_x_278_);
if (lean_obj_tag(v_x_277_) == 0)
{
lean_object* v___x_282_; 
v___x_282_ = lean_box(2);
return v___x_282_;
}
else
{
lean_object* v_val_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
v_val_283_ = lean_ctor_get(v_x_277_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v_x_277_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v_x_277_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_val_283_);
lean_dec(v_x_277_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_val_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
else
{
lean_object* v_keyArray_291_; lean_object* v_valueArray_292_; lean_object* v___x_293_; uint8_t v_isSome_294_; 
v_keyArray_291_ = lean_ctor_get(v_m_275_, 1);
v_valueArray_292_ = lean_ctor_get(v_m_275_, 2);
v___x_293_ = lean_array_fget_borrowed(v_keyArray_291_, v_x_279_);
v_isSome_294_ = lean_noption_is_some(v___x_293_);
if (v_isSome_294_ == 0)
{
lean_dec(v_x_278_);
if (lean_obj_tag(v_x_277_) == 0)
{
lean_object* v___x_295_; 
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v_x_279_);
return v___x_295_;
}
else
{
lean_object* v_val_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_dec(v_x_279_);
v_val_296_ = lean_ctor_get(v_x_277_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v_x_277_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v_x_277_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_val_296_);
lean_dec(v_x_277_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_val_296_);
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
else
{
lean_object* v_one_304_; lean_object* v_n_305_; lean_object* v___y_307_; 
v_one_304_ = lean_unsigned_to_nat(1u);
v_n_305_ = lean_nat_sub(v_x_278_, v_one_304_);
lean_dec(v_x_278_);
if (v_isSome_294_ == 0)
{
goto v___jp_313_;
}
else
{
lean_object* v___x_315_; uint8_t v_isSome_316_; 
v___x_315_ = lean_array_fget_borrowed(v_valueArray_292_, v_x_279_);
v_isSome_316_ = lean_noption_is_some(v___x_315_);
if (v_isSome_316_ == 0)
{
goto v___jp_313_;
}
else
{
lean_object* v_val_317_; uint8_t v___x_318_; 
lean_inc(v___x_293_);
v_val_317_ = lean_noption_get(v___x_293_);
v___x_318_ = l_Lean_instBEqFVarId_beq(v_val_317_, v_query_276_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
lean_dec(v_val_317_);
v___x_319_ = lean_array_get_size(v_keyArray_291_);
v___x_320_ = lean_nat_add(v_x_279_, v_one_304_);
lean_dec(v_x_279_);
v___x_321_ = lean_nat_dec_lt(v___x_320_, v___x_319_);
if (v___x_321_ == 0)
{
lean_dec(v___x_320_);
v_x_278_ = v_n_305_;
v_x_279_ = v_zero_280_;
goto _start;
}
else
{
v_x_278_ = v_n_305_;
v_x_279_ = v___x_320_;
goto _start;
}
}
else
{
lean_object* v_val_324_; lean_object* v___x_325_; 
lean_dec(v_n_305_);
lean_dec(v_x_277_);
lean_inc(v___x_315_);
v_val_324_ = lean_noption_get(v___x_315_);
v___x_325_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_325_, 0, v_x_279_);
lean_ctor_set(v___x_325_, 1, v_val_317_);
lean_ctor_set(v___x_325_, 2, v_val_324_);
return v___x_325_;
}
}
}
v___jp_306_:
{
lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_308_ = lean_array_get_size(v_keyArray_291_);
v___x_309_ = lean_nat_add(v_x_279_, v_one_304_);
lean_dec(v_x_279_);
v___x_310_ = lean_nat_dec_lt(v___x_309_, v___x_308_);
if (v___x_310_ == 0)
{
lean_dec(v___x_309_);
v_x_277_ = v___y_307_;
v_x_278_ = v_n_305_;
v_x_279_ = v_zero_280_;
goto _start;
}
else
{
v_x_277_ = v___y_307_;
v_x_278_ = v_n_305_;
v_x_279_ = v___x_309_;
goto _start;
}
}
v___jp_313_:
{
if (lean_obj_tag(v_x_277_) == 0)
{
lean_object* v___x_314_; 
lean_inc(v_x_279_);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v_x_279_);
v___y_307_ = v___x_314_;
goto v___jp_306_;
}
else
{
v___y_307_ = v_x_277_;
goto v___jp_306_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg___boxed(lean_object* v_m_326_, lean_object* v_query_327_, lean_object* v_x_328_, lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_m_326_, v_query_327_, v_x_328_, v_x_329_, v_x_330_);
lean_dec(v_query_327_);
lean_dec_ref(v_m_326_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(lean_object* v_m_332_, lean_object* v_query_333_){
_start:
{
lean_object* v_keyArray_334_; lean_object* v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v_fold_339_; uint64_t v___x_340_; uint64_t v___x_341_; uint64_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v___x_345_; size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_keyArray_334_ = lean_ctor_get(v_m_332_, 1);
v___x_335_ = lean_array_get_size(v_keyArray_334_);
v___x_336_ = l_Lean_instHashableFVarId_hash(v_query_333_);
v___x_337_ = 32ULL;
v___x_338_ = lean_uint64_shift_right(v___x_336_, v___x_337_);
v_fold_339_ = lean_uint64_xor(v___x_336_, v___x_338_);
v___x_340_ = 16ULL;
v___x_341_ = lean_uint64_shift_right(v_fold_339_, v___x_340_);
v___x_342_ = lean_uint64_xor(v_fold_339_, v___x_341_);
v___x_343_ = lean_uint64_to_usize(v___x_342_);
v___x_344_ = lean_usize_of_nat(v___x_335_);
v___x_345_ = ((size_t)1ULL);
v___x_346_ = lean_usize_sub(v___x_344_, v___x_345_);
v___x_347_ = lean_usize_land(v___x_343_, v___x_346_);
v___x_348_ = lean_usize_to_nat(v___x_347_);
v___x_349_ = lean_box(0);
v___x_350_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_m_332_, v_query_333_, v___x_349_, v___x_335_, v___x_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg___boxed(lean_object* v_m_351_, lean_object* v_query_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v_m_351_, v_query_352_);
lean_dec(v_query_352_);
lean_dec_ref(v_m_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4_spec__5___redArg(lean_object* v_b_354_, lean_object* v_acc_355_, lean_object* v_i_356_){
_start:
{
lean_object* v___y_358_; lean_object* v_keyArray_366_; lean_object* v_valueArray_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v_keyArray_366_ = lean_ctor_get(v_b_354_, 1);
v_valueArray_367_ = lean_ctor_get(v_b_354_, 2);
v___x_368_ = lean_array_get_size(v_keyArray_366_);
v___x_369_ = lean_nat_dec_lt(v_i_356_, v___x_368_);
if (v___x_369_ == 0)
{
lean_dec(v_i_356_);
return v_acc_355_;
}
else
{
lean_object* v___x_370_; uint8_t v_isSome_371_; 
v___x_370_ = lean_array_fget_borrowed(v_keyArray_366_, v_i_356_);
v_isSome_371_ = lean_noption_is_some(v___x_370_);
if (v_isSome_371_ == 0)
{
goto v___jp_362_;
}
else
{
lean_object* v___x_372_; uint8_t v_isSome_373_; 
v___x_372_ = lean_array_fget_borrowed(v_valueArray_367_, v_i_356_);
v_isSome_373_ = lean_noption_is_some(v___x_372_);
if (v_isSome_373_ == 0)
{
goto v___jp_362_;
}
else
{
lean_object* v_val_374_; lean_object* v_val_375_; lean_object* v_i_377_; lean_object* v___x_382_; 
lean_inc(v___x_370_);
v_val_374_ = lean_noption_get(v___x_370_);
lean_inc(v___x_372_);
v_val_375_ = lean_noption_get(v___x_372_);
v___x_382_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v_acc_355_, v_val_374_);
switch(lean_obj_tag(v___x_382_))
{
case 0:
{
lean_object* v_index_383_; lean_object* v_size_384_; lean_object* v___x_385_; 
v_index_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_index_383_);
lean_dec_ref_known(v___x_382_, 3);
v_size_384_ = lean_ctor_get(v_acc_355_, 0);
lean_inc(v_size_384_);
v___x_385_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_355_, v_size_384_, v_index_383_, v_val_374_, v_val_375_);
lean_dec(v_index_383_);
v___y_358_ = v___x_385_;
goto v___jp_357_;
}
case 1:
{
lean_object* v_index_386_; 
v_index_386_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_index_386_);
lean_dec_ref_known(v___x_382_, 1);
v_i_377_ = v_index_386_;
goto v___jp_376_;
}
default: 
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_unsigned_to_nat(0u);
v___x_388_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_355_, v___x_387_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_index_389_; 
v_index_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_index_389_);
lean_dec_ref_known(v___x_388_, 1);
v_i_377_ = v_index_389_;
goto v___jp_376_;
}
else
{
lean_dec(v_val_375_);
lean_dec(v_val_374_);
v___y_358_ = v_acc_355_;
goto v___jp_357_;
}
}
}
v___jp_376_:
{
lean_object* v_size_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_size_378_ = lean_ctor_get(v_acc_355_, 0);
v___x_379_ = lean_unsigned_to_nat(1u);
v___x_380_ = lean_nat_add(v_size_378_, v___x_379_);
v___x_381_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_355_, v___x_380_, v_i_377_, v_val_374_, v_val_375_);
lean_dec(v_i_377_);
v___y_358_ = v___x_381_;
goto v___jp_357_;
}
}
}
}
v___jp_357_:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_unsigned_to_nat(1u);
v___x_360_ = lean_nat_add(v_i_356_, v___x_359_);
lean_dec(v_i_356_);
v_acc_355_ = v___y_358_;
v_i_356_ = v___x_360_;
goto _start;
}
v___jp_362_:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_unsigned_to_nat(1u);
v___x_364_ = lean_nat_add(v_i_356_, v___x_363_);
lean_dec(v_i_356_);
v_i_356_ = v___x_364_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_390_, lean_object* v_acc_391_, lean_object* v_i_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4_spec__5___redArg(v_b_390_, v_acc_391_, v_i_392_);
lean_dec_ref(v_b_390_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4___redArg(lean_object* v_init_394_, lean_object* v_b_395_){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_unsigned_to_nat(0u);
v___x_397_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4_spec__5___redArg(v_b_395_, v_init_394_, v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4___redArg___boxed(lean_object* v_init_398_, lean_object* v_b_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4___redArg(v_init_398_, v_b_399_);
lean_dec_ref(v_b_399_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___redArg(lean_object* v_m_401_){
_start:
{
lean_object* v_keyArray_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v_cellCount_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v_target_409_; lean_object* v___x_410_; 
v_keyArray_402_ = lean_ctor_get(v_m_401_, 1);
v___x_403_ = lean_array_get_size(v_keyArray_402_);
v___x_404_ = lean_unsigned_to_nat(2u);
v_cellCount_405_ = lean_nat_mul(v___x_403_, v___x_404_);
v___x_406_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_405_);
v___x_407_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_405_);
v___x_408_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_405_);
v_target_409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_409_, 0, v___x_406_);
lean_ctor_set(v_target_409_, 1, v___x_407_);
lean_ctor_set(v_target_409_, 2, v___x_408_);
v___x_410_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4___redArg(v_target_409_, v_m_401_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___redArg___boxed(lean_object* v_m_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___redArg(v_m_411_);
lean_dec_ref(v_m_411_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; lean_object* v_ngen_416_; lean_object* v_namePrefix_417_; lean_object* v_idx_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_447_; 
v___x_415_ = lean_st_ref_get(v___y_413_);
v_ngen_416_ = lean_ctor_get(v___x_415_, 2);
lean_inc_ref(v_ngen_416_);
lean_dec(v___x_415_);
v_namePrefix_417_ = lean_ctor_get(v_ngen_416_, 0);
v_idx_418_ = lean_ctor_get(v_ngen_416_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v_ngen_416_);
if (v_isSharedCheck_447_ == 0)
{
v___x_420_ = v_ngen_416_;
v_isShared_421_ = v_isSharedCheck_447_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_idx_418_);
lean_inc(v_namePrefix_417_);
lean_dec(v_ngen_416_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_447_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v_env_423_; lean_object* v_nextMacroScope_424_; lean_object* v_auxDeclNGen_425_; lean_object* v_traceState_426_; lean_object* v_cache_427_; lean_object* v_messages_428_; lean_object* v_infoState_429_; lean_object* v_snapshotTasks_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_445_; 
v___x_422_ = lean_st_ref_take(v___y_413_);
v_env_423_ = lean_ctor_get(v___x_422_, 0);
v_nextMacroScope_424_ = lean_ctor_get(v___x_422_, 1);
v_auxDeclNGen_425_ = lean_ctor_get(v___x_422_, 3);
v_traceState_426_ = lean_ctor_get(v___x_422_, 4);
v_cache_427_ = lean_ctor_get(v___x_422_, 5);
v_messages_428_ = lean_ctor_get(v___x_422_, 6);
v_infoState_429_ = lean_ctor_get(v___x_422_, 7);
v_snapshotTasks_430_ = lean_ctor_get(v___x_422_, 8);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v___x_422_, 2);
lean_dec(v_unused_446_);
v___x_432_ = v___x_422_;
v_isShared_433_ = v_isSharedCheck_445_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_snapshotTasks_430_);
lean_inc(v_infoState_429_);
lean_inc(v_messages_428_);
lean_inc(v_cache_427_);
lean_inc(v_traceState_426_);
lean_inc(v_auxDeclNGen_425_);
lean_inc(v_nextMacroScope_424_);
lean_inc(v_env_423_);
lean_dec(v___x_422_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_445_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v_r_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_438_; 
lean_inc(v_idx_418_);
lean_inc(v_namePrefix_417_);
v_r_434_ = l_Lean_Name_num___override(v_namePrefix_417_, v_idx_418_);
v___x_435_ = lean_unsigned_to_nat(1u);
v___x_436_ = lean_nat_add(v_idx_418_, v___x_435_);
lean_dec(v_idx_418_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 1, v___x_436_);
v___x_438_ = v___x_420_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_namePrefix_417_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_436_);
v___x_438_ = v_reuseFailAlloc_444_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_440_; 
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 2, v___x_438_);
v___x_440_ = v___x_432_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_env_423_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_nextMacroScope_424_);
lean_ctor_set(v_reuseFailAlloc_443_, 2, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_443_, 3, v_auxDeclNGen_425_);
lean_ctor_set(v_reuseFailAlloc_443_, 4, v_traceState_426_);
lean_ctor_set(v_reuseFailAlloc_443_, 5, v_cache_427_);
lean_ctor_set(v_reuseFailAlloc_443_, 6, v_messages_428_);
lean_ctor_set(v_reuseFailAlloc_443_, 7, v_infoState_429_);
lean_ctor_set(v_reuseFailAlloc_443_, 8, v_snapshotTasks_430_);
v___x_440_ = v_reuseFailAlloc_443_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_st_ref_put(v___y_413_, v___x_440_);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v_r_434_);
return v___x_442_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg___boxed(lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_448_);
lean_dec(v___y_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(uint8_t v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___x_458_; lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
v___x_458_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_456_);
v_a_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0___boxed(lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
uint8_t v___y_4264__boxed_474_; lean_object* v_res_475_; 
v___y_4264__boxed_474_ = lean_unbox(v___y_467_);
v_res_475_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(v___y_4264__boxed_474_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(lean_object* v_fvarId_476_, uint8_t v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_561_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_561_ == 0)
{
v___x_487_ = v___x_484_;
v_isShared_488_ = v_isSharedCheck_561_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_561_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v___y_491_; lean_object* v___x_496_; lean_object* v___y_498_; lean_object* v_i_499_; lean_object* v___y_505_; lean_object* v___y_515_; lean_object* v_i_516_; lean_object* v___x_531_; 
v___x_489_ = lean_st_ref_take(v_a_478_);
lean_inc(v_a_485_);
v___x_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_496_, 0, v_a_485_);
v___x_531_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v___x_489_, v_fvarId_476_);
switch(lean_obj_tag(v___x_531_))
{
case 0:
{
lean_object* v_index_532_; lean_object* v_size_533_; lean_object* v___x_534_; 
v_index_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_index_532_);
lean_dec_ref_known(v___x_531_, 3);
v_size_533_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_size_533_);
v___x_534_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_489_, v_size_533_, v_index_532_, v_fvarId_476_, v___x_496_);
lean_dec(v_index_532_);
v___y_491_ = v___x_534_;
goto v___jp_490_;
}
case 1:
{
lean_object* v_index_535_; lean_object* v_size_536_; lean_object* v_keyArray_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_index_535_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_index_535_);
lean_dec_ref_known(v___x_531_, 1);
v_size_536_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_size_536_);
v_keyArray_537_ = lean_ctor_get(v___x_489_, 1);
lean_inc_ref(v_keyArray_537_);
v___x_538_ = lean_unsigned_to_nat(1u);
v___x_539_ = lean_nat_add(v_size_536_, v___x_538_);
lean_dec(v_size_536_);
v___x_540_ = lean_array_get_size(v_keyArray_537_);
lean_dec_ref(v_keyArray_537_);
v___x_541_ = lean_nat_dec_lt(v___x_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_dec(v___x_539_);
lean_dec(v_index_535_);
goto v___jp_521_;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_542_ = lean_unsigned_to_nat(4u);
v___x_543_ = lean_nat_mul(v___x_539_, v___x_542_);
v___x_544_ = lean_unsigned_to_nat(3u);
v___x_545_ = lean_nat_mul(v___x_540_, v___x_544_);
v___x_546_ = lean_nat_dec_le(v___x_543_, v___x_545_);
lean_dec(v___x_545_);
lean_dec(v___x_543_);
if (v___x_546_ == 0)
{
lean_dec(v___x_539_);
lean_dec(v_index_535_);
goto v___jp_521_;
}
else
{
lean_object* v___x_547_; 
v___x_547_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_489_, v___x_539_, v_index_535_, v_fvarId_476_, v___x_496_);
lean_dec(v_index_535_);
v___y_491_ = v___x_547_;
goto v___jp_490_;
}
}
}
default: 
{
lean_object* v_size_548_; lean_object* v_keyArray_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v_size_548_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_size_548_);
v_keyArray_549_ = lean_ctor_get(v___x_489_, 1);
lean_inc_ref(v_keyArray_549_);
v___x_550_ = lean_unsigned_to_nat(1u);
v___x_551_ = lean_nat_add(v_size_548_, v___x_550_);
lean_dec(v_size_548_);
v___x_552_ = lean_array_get_size(v_keyArray_549_);
lean_dec_ref(v_keyArray_549_);
v___x_553_ = lean_nat_dec_lt(v___x_551_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
lean_dec(v___x_551_);
v___x_554_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___redArg(v___x_489_);
lean_dec(v___x_489_);
v___y_505_ = v___x_554_;
goto v___jp_504_;
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_555_ = lean_unsigned_to_nat(4u);
v___x_556_ = lean_nat_mul(v___x_551_, v___x_555_);
lean_dec(v___x_551_);
v___x_557_ = lean_unsigned_to_nat(3u);
v___x_558_ = lean_nat_mul(v___x_552_, v___x_557_);
v___x_559_ = lean_nat_dec_le(v___x_556_, v___x_558_);
lean_dec(v___x_558_);
lean_dec(v___x_556_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
v___x_560_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___redArg(v___x_489_);
lean_dec(v___x_489_);
v___y_505_ = v___x_560_;
goto v___jp_504_;
}
else
{
v___y_505_ = v___x_489_;
goto v___jp_504_;
}
}
}
}
v___jp_490_:
{
lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_492_ = lean_st_ref_put(v_a_478_, v___y_491_);
if (v_isShared_488_ == 0)
{
v___x_494_ = v___x_487_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_485_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
v___jp_497_:
{
lean_object* v_size_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_size_500_ = lean_ctor_get(v___y_498_, 0);
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_add(v_size_500_, v___x_501_);
v___x_503_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_498_, v___x_502_, v_i_499_, v_fvarId_476_, v___x_496_);
lean_dec(v_i_499_);
v___y_491_ = v___x_503_;
goto v___jp_490_;
}
v___jp_504_:
{
lean_object* v___x_506_; 
v___x_506_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v___y_505_, v_fvarId_476_);
switch(lean_obj_tag(v___x_506_))
{
case 0:
{
lean_object* v_index_507_; lean_object* v_size_508_; lean_object* v___x_509_; 
v_index_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_index_507_);
lean_dec_ref_known(v___x_506_, 3);
v_size_508_ = lean_ctor_get(v___y_505_, 0);
lean_inc(v_size_508_);
v___x_509_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_505_, v_size_508_, v_index_507_, v_fvarId_476_, v___x_496_);
lean_dec(v_index_507_);
v___y_491_ = v___x_509_;
goto v___jp_490_;
}
case 1:
{
lean_object* v_index_510_; 
v_index_510_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_index_510_);
lean_dec_ref_known(v___x_506_, 1);
v___y_498_ = v___y_505_;
v_i_499_ = v_index_510_;
goto v___jp_497_;
}
default: 
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_505_, v___x_511_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_index_513_; 
v_index_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_index_513_);
lean_dec_ref_known(v___x_512_, 1);
v___y_498_ = v___y_505_;
v_i_499_ = v_index_513_;
goto v___jp_497_;
}
else
{
lean_dec_ref_known(v___x_496_, 1);
lean_dec(v_fvarId_476_);
v___y_491_ = v___y_505_;
goto v___jp_490_;
}
}
}
}
v___jp_514_:
{
lean_object* v_size_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_size_517_ = lean_ctor_get(v___y_515_, 0);
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_nat_add(v_size_517_, v___x_518_);
v___x_520_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_515_, v___x_519_, v_i_516_, v_fvarId_476_, v___x_496_);
lean_dec(v_i_516_);
v___y_491_ = v___x_520_;
goto v___jp_490_;
}
v___jp_521_:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___redArg(v___x_489_);
lean_dec(v___x_489_);
v___x_523_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v___x_522_, v_fvarId_476_);
switch(lean_obj_tag(v___x_523_))
{
case 0:
{
lean_object* v_index_524_; lean_object* v_size_525_; lean_object* v___x_526_; 
v_index_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_index_524_);
lean_dec_ref_known(v___x_523_, 3);
v_size_525_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_size_525_);
v___x_526_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_522_, v_size_525_, v_index_524_, v_fvarId_476_, v___x_496_);
lean_dec(v_index_524_);
v___y_491_ = v___x_526_;
goto v___jp_490_;
}
case 1:
{
lean_object* v_index_527_; 
v_index_527_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_index_527_);
lean_dec_ref_known(v___x_523_, 1);
v___y_515_ = v___x_522_;
v_i_516_ = v_index_527_;
goto v___jp_514_;
}
default: 
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_522_, v___x_528_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_index_530_; 
v_index_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_index_530_);
lean_dec_ref_known(v___x_529_, 1);
v___y_515_ = v___x_522_;
v_i_516_ = v_index_530_;
goto v___jp_514_;
}
else
{
lean_dec_ref_known(v___x_496_, 1);
lean_dec(v_fvarId_476_);
v___y_491_ = v___x_522_;
goto v___jp_490_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_476_);
return v___x_484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg___boxed(lean_object* v_fvarId_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
uint8_t v_a_boxed_570_; lean_object* v_res_571_; 
v_a_boxed_570_ = lean_unbox(v_a_563_);
v_res_571_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_562_, v_a_boxed_570_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec(v_a_564_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(uint8_t v_pu_572_, lean_object* v_fvarId_573_, uint8_t v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___boxed(lean_object* v_pu_582_, lean_object* v_fvarId_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
uint8_t v_pu_boxed_591_; uint8_t v_a_boxed_592_; lean_object* v_res_593_; 
v_pu_boxed_591_ = lean_unbox(v_pu_582_);
v_a_boxed_592_ = lean_unbox(v_a_584_);
v_res_593_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(v_pu_boxed_591_, v_fvarId_583_, v_a_boxed_592_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
lean_dec(v_a_585_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(uint8_t v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_599_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___boxed(lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
uint8_t v___y_4447__boxed_609_; lean_object* v_res_610_; 
v___y_4447__boxed_609_ = lean_unbox(v___y_602_);
v_res_610_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(v___y_4447__boxed_609_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1(lean_object* v_00_u03b2_611_, lean_object* v_m_612_, lean_object* v_query_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v_m_612_, v_query_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___boxed(lean_object* v_00_u03b2_615_, lean_object* v_m_616_, lean_object* v_query_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1(v_00_u03b2_615_, v_m_616_, v_query_617_);
lean_dec(v_query_617_);
lean_dec_ref(v_m_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2(lean_object* v_00_u03b2_619_, lean_object* v_m_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___redArg(v_m_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___boxed(lean_object* v_00_u03b2_622_, lean_object* v_m_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2(v_00_u03b2_622_, v_m_623_);
lean_dec_ref(v_m_623_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(lean_object* v_00_u03b2_625_, lean_object* v_m_626_, lean_object* v_query_627_, lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_m_626_, v_query_627_, v_x_628_, v_x_629_, v_x_630_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___boxed(lean_object* v_00_u03b2_633_, lean_object* v_m_634_, lean_object* v_query_635_, lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(v_00_u03b2_633_, v_m_634_, v_query_635_, v_x_636_, v_x_637_, v_x_638_, v_x_639_);
lean_dec(v_query_635_);
lean_dec_ref(v_m_634_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4(lean_object* v_00_u03b2_641_, lean_object* v_init_642_, lean_object* v_b_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4___redArg(v_init_642_, v_b_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4___boxed(lean_object* v_00_u03b2_645_, lean_object* v_init_646_, lean_object* v_b_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4(v_00_u03b2_645_, v_init_646_, v_b_647_);
lean_dec_ref(v_b_647_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_649_, lean_object* v_b_650_, lean_object* v_acc_651_, lean_object* v_i_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4_spec__5___redArg(v_b_650_, v_acc_651_, v_i_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_654_, lean_object* v_b_655_, lean_object* v_acc_656_, lean_object* v_i_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2_spec__4_spec__5(v_00_u03b2_654_, v_b_655_, v_acc_656_, v_i_657_);
lean_dec_ref(v_b_655_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(lean_object* v_m_659_, lean_object* v_query_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v_m_659_, v_query_660_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_index_662_; lean_object* v_key_663_; lean_object* v_value_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
v_index_662_ = lean_ctor_get(v___x_661_, 0);
v_key_663_ = lean_ctor_get(v___x_661_, 1);
v_value_664_ = lean_ctor_get(v___x_661_, 2);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_661_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_value_664_);
lean_inc(v_key_663_);
lean_inc(v_index_662_);
lean_dec(v___x_661_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_index_662_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_key_663_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v_value_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
else
{
lean_object* v___x_672_; 
lean_dec(v___x_661_);
v___x_672_ = lean_box(1);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg___boxed(lean_object* v_m_673_, lean_object* v_query_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_m_673_, v_query_674_);
lean_dec(v_query_674_);
lean_dec_ref(v_m_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(lean_object* v_m_676_, lean_object* v_a_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_m_676_, v_a_677_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_value_679_; lean_object* v___x_680_; 
v_value_679_ = lean_ctor_get(v___x_678_, 2);
lean_inc(v_value_679_);
lean_dec_ref_known(v___x_678_, 3);
v___x_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_680_, 0, v_value_679_);
return v___x_680_;
}
else
{
lean_object* v___x_681_; 
v___x_681_ = lean_box(0);
return v___x_681_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg___boxed(lean_object* v_m_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v_m_682_, v_a_683_);
lean_dec(v_a_683_);
lean_dec_ref(v_m_682_);
return v_res_684_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_instMonadEIO(lean_box(0));
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(lean_object* v_msg_690_, uint8_t v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v_toApplicative_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_764_; 
v___x_698_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
v___x_699_ = l_StateRefT_x27_instMonad___redArg(v___x_698_);
v_toApplicative_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; 
v_unused_765_ = lean_ctor_get(v___x_699_, 1);
lean_dec(v_unused_765_);
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_764_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_toApplicative_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_764_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_toFunctor_704_; lean_object* v_toSeq_705_; lean_object* v_toSeqLeft_706_; lean_object* v_toSeqRight_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_762_; 
v_toFunctor_704_ = lean_ctor_get(v_toApplicative_700_, 0);
v_toSeq_705_ = lean_ctor_get(v_toApplicative_700_, 2);
v_toSeqLeft_706_ = lean_ctor_get(v_toApplicative_700_, 3);
v_toSeqRight_707_ = lean_ctor_get(v_toApplicative_700_, 4);
v_isSharedCheck_762_ = !lean_is_exclusive(v_toApplicative_700_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v_toApplicative_700_, 1);
lean_dec(v_unused_763_);
v___x_709_ = v_toApplicative_700_;
v_isShared_710_ = v_isSharedCheck_762_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_toSeqRight_707_);
lean_inc(v_toSeqLeft_706_);
lean_inc(v_toSeq_705_);
lean_inc(v_toFunctor_704_);
lean_dec(v_toApplicative_700_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_762_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___f_711_; lean_object* v___f_712_; lean_object* v___f_713_; lean_object* v___f_714_; lean_object* v___x_715_; lean_object* v___f_716_; lean_object* v___f_717_; lean_object* v___f_718_; lean_object* v___x_720_; 
v___f_711_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
v___f_712_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_704_);
v___f_713_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_713_, 0, v_toFunctor_704_);
v___f_714_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_714_, 0, v_toFunctor_704_);
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v___f_713_);
lean_ctor_set(v___x_715_, 1, v___f_714_);
v___f_716_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_716_, 0, v_toSeqRight_707_);
v___f_717_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_717_, 0, v_toSeqLeft_706_);
v___f_718_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_718_, 0, v_toSeq_705_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 4, v___f_716_);
lean_ctor_set(v___x_709_, 3, v___f_717_);
lean_ctor_set(v___x_709_, 2, v___f_718_);
lean_ctor_set(v___x_709_, 1, v___f_711_);
lean_ctor_set(v___x_709_, 0, v___x_715_);
v___x_720_ = v___x_709_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v___f_711_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v___f_718_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v___f_717_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v___f_716_);
v___x_720_ = v_reuseFailAlloc_761_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_722_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v___f_712_);
lean_ctor_set(v___x_702_, 0, v___x_720_);
v___x_722_ = v___x_702_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___f_712_);
v___x_722_ = v_reuseFailAlloc_760_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_723_; lean_object* v_toApplicative_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_758_; 
v___x_723_ = l_StateRefT_x27_instMonad___redArg(v___x_722_);
v_toApplicative_724_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; 
v_unused_759_ = lean_ctor_get(v___x_723_, 1);
lean_dec(v_unused_759_);
v___x_726_ = v___x_723_;
v_isShared_727_ = v_isSharedCheck_758_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_toApplicative_724_);
lean_dec(v___x_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_758_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v_toFunctor_728_; lean_object* v_toSeq_729_; lean_object* v_toSeqLeft_730_; lean_object* v_toSeqRight_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_756_; 
v_toFunctor_728_ = lean_ctor_get(v_toApplicative_724_, 0);
v_toSeq_729_ = lean_ctor_get(v_toApplicative_724_, 2);
v_toSeqLeft_730_ = lean_ctor_get(v_toApplicative_724_, 3);
v_toSeqRight_731_ = lean_ctor_get(v_toApplicative_724_, 4);
v_isSharedCheck_756_ = !lean_is_exclusive(v_toApplicative_724_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; 
v_unused_757_ = lean_ctor_get(v_toApplicative_724_, 1);
lean_dec(v_unused_757_);
v___x_733_ = v_toApplicative_724_;
v_isShared_734_ = v_isSharedCheck_756_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_toSeqRight_731_);
lean_inc(v_toSeqLeft_730_);
lean_inc(v_toSeq_729_);
lean_inc(v_toFunctor_728_);
lean_dec(v_toApplicative_724_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_756_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___f_735_; lean_object* v___f_736_; lean_object* v___f_737_; lean_object* v___f_738_; lean_object* v___x_739_; lean_object* v___f_740_; lean_object* v___f_741_; lean_object* v___f_742_; lean_object* v___x_744_; 
v___f_735_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
v___f_736_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(v_toFunctor_728_);
v___f_737_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_737_, 0, v_toFunctor_728_);
v___f_738_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_738_, 0, v_toFunctor_728_);
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v___f_737_);
lean_ctor_set(v___x_739_, 1, v___f_738_);
v___f_740_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_740_, 0, v_toSeqRight_731_);
v___f_741_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_741_, 0, v_toSeqLeft_730_);
v___f_742_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_742_, 0, v_toSeq_729_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 4, v___f_740_);
lean_ctor_set(v___x_733_, 3, v___f_741_);
lean_ctor_set(v___x_733_, 2, v___f_742_);
lean_ctor_set(v___x_733_, 1, v___f_735_);
lean_ctor_set(v___x_733_, 0, v___x_739_);
v___x_744_ = v___x_733_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___f_735_);
lean_ctor_set(v_reuseFailAlloc_755_, 2, v___f_742_);
lean_ctor_set(v_reuseFailAlloc_755_, 3, v___f_741_);
lean_ctor_set(v_reuseFailAlloc_755_, 4, v___f_740_);
v___x_744_ = v_reuseFailAlloc_755_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_746_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v___f_736_);
lean_ctor_set(v___x_726_, 0, v___x_744_);
v___x_746_ = v___x_726_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v___f_736_);
v___x_746_ = v_reuseFailAlloc_754_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___f_750_; lean_object* v___x_8133__overap_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_747_ = l_StateRefT_x27_instMonad___redArg(v___x_746_);
v___x_748_ = l_Lean_instInhabitedExpr;
v___x_749_ = l_instInhabitedOfMonad___redArg(v___x_747_, v___x_748_);
v___f_750_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_750_, 0, v___x_749_);
v___x_8133__overap_751_ = lean_panic_fn_borrowed(v___f_750_, v_msg_690_);
lean_dec_ref(v___f_750_);
v___x_752_ = lean_box(v___y_691_);
lean_inc(v___y_696_);
lean_inc_ref(v___y_695_);
lean_inc(v___y_694_);
lean_inc_ref(v___y_693_);
lean_inc(v___y_692_);
v___x_753_ = lean_apply_7(v___x_8133__overap_751_, v___x_752_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, lean_box(0));
return v___x_753_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___boxed(lean_object* v_msg_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
uint8_t v___y_8247__boxed_774_; lean_object* v_res_775_; 
v___y_8247__boxed_774_ = lean_unbox(v___y_767_);
v_res_775_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v_msg_766_, v___y_8247__boxed_774_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
return v_res_775_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_779_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_780_ = lean_unsigned_to_nat(20u);
v___x_781_ = lean_unsigned_to_nat(88u);
v___x_782_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__1));
v___x_783_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_784_ = l_mkPanicMessageWithDecl(v___x_783_, v___x_782_, v___x_781_, v___x_780_, v___x_779_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(uint8_t v_pu_785_, lean_object* v_e_786_, uint8_t v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
uint8_t v___x_794_; 
v___x_794_ = l_Lean_Expr_hasFVar(v_e_786_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; 
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v_e_786_);
return v___x_795_;
}
else
{
switch(lean_obj_tag(v_e_786_))
{
case 1:
{
lean_object* v_fvarId_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_fvarId_796_ = lean_ctor_get(v_e_786_, 0);
v___x_797_ = lean_st_ref_get(v_a_788_);
v___x_798_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v___x_797_, v_fvarId_796_);
lean_dec(v___x_797_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v___x_799_; 
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v_e_786_);
return v___x_799_;
}
else
{
lean_object* v_val_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_845_; 
lean_dec_ref_known(v_e_786_, 1);
v_val_800_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_845_ == 0)
{
v___x_802_ = v___x_798_;
v_isShared_803_ = v_isSharedCheck_845_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_val_800_);
lean_dec(v___x_798_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_845_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
switch(lean_obj_tag(v_val_800_))
{
case 0:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_804_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_803_ == 0)
{
lean_ctor_set_tag(v___x_802_, 0);
lean_ctor_set(v___x_802_, 0, v___x_804_);
v___x_806_ = v___x_802_;
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
case 1:
{
lean_object* v_fvarId_808_; lean_object* v___x_809_; 
lean_del_object(v___x_802_);
v_fvarId_808_ = lean_ctor_get(v_val_800_, 0);
lean_inc(v_fvarId_808_);
lean_dec_ref_known(v_val_800_, 1);
v___x_809_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_785_, v_fvarId_808_, v_a_790_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_828_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_828_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_828_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_828_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
if (lean_obj_tag(v_a_810_) == 0)
{
lean_dec(v_fvarId_808_);
goto v___jp_814_;
}
else
{
lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_826_; 
v_isSharedCheck_826_ = !lean_is_exclusive(v_a_810_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v_a_810_, 0);
lean_dec(v_unused_827_);
v___x_820_ = v_a_810_;
v_isShared_821_ = v_isSharedCheck_826_;
goto v_resetjp_819_;
}
else
{
lean_dec(v_a_810_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_826_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
if (v___x_794_ == 0)
{
lean_del_object(v___x_820_);
lean_dec(v_fvarId_808_);
goto v___jp_814_;
}
else
{
lean_object* v___x_822_; lean_object* v___x_824_; 
lean_del_object(v___x_812_);
v___x_822_ = l_Lean_Expr_fvar___override(v_fvarId_808_);
if (v_isShared_821_ == 0)
{
lean_ctor_set_tag(v___x_820_, 0);
lean_ctor_set(v___x_820_, 0, v___x_822_);
v___x_824_ = v___x_820_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
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
v___jp_814_:
{
lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_815_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_815_);
v___x_817_ = v___x_812_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec(v_fvarId_808_);
v_a_829_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_809_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_809_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
default: 
{
lean_object* v_expr_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_del_object(v___x_802_);
v_expr_837_ = lean_ctor_get(v_val_800_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v_val_800_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v_val_800_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_expr_837_);
lean_dec(v_val_800_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
lean_ctor_set_tag(v___x_839_, 0);
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_expr_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_846_; lean_object* v_arg_847_; lean_object* v___x_848_; 
v_fn_846_ = lean_ctor_get(v_e_786_, 0);
v_arg_847_ = lean_ctor_get(v_e_786_, 1);
lean_inc_ref(v_fn_846_);
v___x_848_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_785_, v_fn_846_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_850_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
lean_inc_ref(v_arg_847_);
v___x_850_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_785_, v_arg_847_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_870_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_870_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_870_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_870_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___y_856_; uint8_t v___y_862_; size_t v___x_864_; size_t v___x_865_; uint8_t v___x_866_; 
v___x_864_ = lean_ptr_addr(v_fn_846_);
v___x_865_ = lean_ptr_addr(v_a_849_);
v___x_866_ = lean_usize_dec_eq(v___x_864_, v___x_865_);
if (v___x_866_ == 0)
{
v___y_862_ = v___x_866_;
goto v___jp_861_;
}
else
{
size_t v___x_867_; size_t v___x_868_; uint8_t v___x_869_; 
v___x_867_ = lean_ptr_addr(v_arg_847_);
v___x_868_ = lean_ptr_addr(v_a_851_);
v___x_869_ = lean_usize_dec_eq(v___x_867_, v___x_868_);
v___y_862_ = v___x_869_;
goto v___jp_861_;
}
v___jp_855_:
{
lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_857_ = l_Lean_Expr_headBeta(v___y_856_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_857_);
v___x_859_ = v___x_853_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
v___jp_861_:
{
if (v___y_862_ == 0)
{
lean_object* v___x_863_; 
lean_dec_ref_known(v_e_786_, 2);
v___x_863_ = l_Lean_Expr_app___override(v_a_849_, v_a_851_);
v___y_856_ = v___x_863_;
goto v___jp_855_;
}
else
{
lean_dec(v_a_851_);
lean_dec(v_a_849_);
v___y_856_ = v_e_786_;
goto v___jp_855_;
}
}
}
}
else
{
lean_dec(v_a_849_);
lean_dec_ref_known(v_e_786_, 2);
return v___x_850_;
}
}
else
{
lean_dec_ref_known(v_e_786_, 2);
return v___x_848_;
}
}
case 6:
{
lean_object* v_binderName_871_; lean_object* v_binderType_872_; lean_object* v_body_873_; uint8_t v_binderInfo_874_; lean_object* v___x_875_; 
v_binderName_871_ = lean_ctor_get(v_e_786_, 0);
v_binderType_872_ = lean_ctor_get(v_e_786_, 1);
v_body_873_ = lean_ctor_get(v_e_786_, 2);
v_binderInfo_874_ = lean_ctor_get_uint8(v_e_786_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_872_);
v___x_875_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_785_, v_binderType_872_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_877_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v___x_875_, 1);
lean_inc_ref(v_body_873_);
v___x_877_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_785_, v_body_873_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_902_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_902_ == 0)
{
v___x_880_ = v___x_877_;
v_isShared_881_ = v_isSharedCheck_902_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_877_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_902_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
uint8_t v___y_883_; size_t v___x_896_; size_t v___x_897_; uint8_t v___x_898_; 
v___x_896_ = lean_ptr_addr(v_binderType_872_);
v___x_897_ = lean_ptr_addr(v_a_876_);
v___x_898_ = lean_usize_dec_eq(v___x_896_, v___x_897_);
if (v___x_898_ == 0)
{
v___y_883_ = v___x_898_;
goto v___jp_882_;
}
else
{
size_t v___x_899_; size_t v___x_900_; uint8_t v___x_901_; 
v___x_899_ = lean_ptr_addr(v_body_873_);
v___x_900_ = lean_ptr_addr(v_a_878_);
v___x_901_ = lean_usize_dec_eq(v___x_899_, v___x_900_);
v___y_883_ = v___x_901_;
goto v___jp_882_;
}
v___jp_882_:
{
if (v___y_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_886_; 
lean_inc(v_binderName_871_);
lean_dec_ref_known(v_e_786_, 3);
v___x_884_ = l_Lean_Expr_lam___override(v_binderName_871_, v_a_876_, v_a_878_, v_binderInfo_874_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_884_);
v___x_886_ = v___x_880_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
else
{
uint8_t v___x_888_; 
v___x_888_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_874_, v_binderInfo_874_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; lean_object* v___x_891_; 
lean_inc(v_binderName_871_);
lean_dec_ref_known(v_e_786_, 3);
v___x_889_ = l_Lean_Expr_lam___override(v_binderName_871_, v_a_876_, v_a_878_, v_binderInfo_874_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_889_);
v___x_891_ = v___x_880_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
else
{
lean_object* v___x_894_; 
lean_dec(v_a_878_);
lean_dec(v_a_876_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v_e_786_);
v___x_894_ = v___x_880_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_e_786_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
}
else
{
lean_dec(v_a_876_);
lean_dec_ref_known(v_e_786_, 3);
return v___x_877_;
}
}
else
{
lean_dec_ref_known(v_e_786_, 3);
return v___x_875_;
}
}
case 7:
{
lean_object* v_binderName_903_; lean_object* v_binderType_904_; lean_object* v_body_905_; uint8_t v_binderInfo_906_; lean_object* v___x_907_; 
v_binderName_903_ = lean_ctor_get(v_e_786_, 0);
v_binderType_904_ = lean_ctor_get(v_e_786_, 1);
v_body_905_ = lean_ctor_get(v_e_786_, 2);
v_binderInfo_906_ = lean_ctor_get_uint8(v_e_786_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_904_);
v___x_907_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_785_, v_binderType_904_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_909_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v___x_907_, 1);
lean_inc_ref(v_body_905_);
v___x_909_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_785_, v_body_905_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_934_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_934_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_934_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_934_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
uint8_t v___y_915_; size_t v___x_928_; size_t v___x_929_; uint8_t v___x_930_; 
v___x_928_ = lean_ptr_addr(v_binderType_904_);
v___x_929_ = lean_ptr_addr(v_a_908_);
v___x_930_ = lean_usize_dec_eq(v___x_928_, v___x_929_);
if (v___x_930_ == 0)
{
v___y_915_ = v___x_930_;
goto v___jp_914_;
}
else
{
size_t v___x_931_; size_t v___x_932_; uint8_t v___x_933_; 
v___x_931_ = lean_ptr_addr(v_body_905_);
v___x_932_ = lean_ptr_addr(v_a_910_);
v___x_933_ = lean_usize_dec_eq(v___x_931_, v___x_932_);
v___y_915_ = v___x_933_;
goto v___jp_914_;
}
v___jp_914_:
{
if (v___y_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_918_; 
lean_inc(v_binderName_903_);
lean_dec_ref_known(v_e_786_, 3);
v___x_916_ = l_Lean_Expr_forallE___override(v_binderName_903_, v_a_908_, v_a_910_, v_binderInfo_906_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_916_);
v___x_918_ = v___x_912_;
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
uint8_t v___x_920_; 
v___x_920_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_906_, v_binderInfo_906_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_923_; 
lean_inc(v_binderName_903_);
lean_dec_ref_known(v_e_786_, 3);
v___x_921_ = l_Lean_Expr_forallE___override(v_binderName_903_, v_a_908_, v_a_910_, v_binderInfo_906_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_921_);
v___x_923_ = v___x_912_;
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
lean_object* v___x_926_; 
lean_dec(v_a_910_);
lean_dec(v_a_908_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v_e_786_);
v___x_926_ = v___x_912_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_e_786_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
}
else
{
lean_dec(v_a_908_);
lean_dec_ref_known(v_e_786_, 3);
return v___x_909_;
}
}
else
{
lean_dec_ref_known(v_e_786_, 3);
return v___x_907_;
}
}
case 8:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec_ref_known(v_e_786_, 4);
v___x_935_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3, &l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3);
v___x_936_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v___x_935_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
return v___x_936_;
}
case 10:
{
lean_object* v_data_937_; lean_object* v_expr_938_; lean_object* v___x_939_; 
v_data_937_ = lean_ctor_get(v_e_786_, 0);
v_expr_938_ = lean_ctor_get(v_e_786_, 1);
lean_inc_ref(v_expr_938_);
v___x_939_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_785_, v_expr_938_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_954_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_954_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_954_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_954_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
size_t v___x_944_; size_t v___x_945_; uint8_t v___x_946_; 
v___x_944_ = lean_ptr_addr(v_expr_938_);
v___x_945_ = lean_ptr_addr(v_a_940_);
v___x_946_ = lean_usize_dec_eq(v___x_944_, v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_949_; 
lean_inc(v_data_937_);
lean_dec_ref_known(v_e_786_, 2);
v___x_947_ = l_Lean_Expr_mdata___override(v_data_937_, v_a_940_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_947_);
v___x_949_ = v___x_942_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
else
{
lean_object* v___x_952_; 
lean_dec(v_a_940_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v_e_786_);
v___x_952_ = v___x_942_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_e_786_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_786_, 2);
return v___x_939_;
}
}
case 11:
{
lean_object* v_typeName_955_; lean_object* v_idx_956_; lean_object* v_struct_957_; lean_object* v___x_958_; 
v_typeName_955_ = lean_ctor_get(v_e_786_, 0);
v_idx_956_ = lean_ctor_get(v_e_786_, 1);
v_struct_957_ = lean_ctor_get(v_e_786_, 2);
lean_inc_ref(v_struct_957_);
v___x_958_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_785_, v_struct_957_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_973_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_973_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_973_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_973_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
size_t v___x_963_; size_t v___x_964_; uint8_t v___x_965_; 
v___x_963_ = lean_ptr_addr(v_struct_957_);
v___x_964_ = lean_ptr_addr(v_a_959_);
v___x_965_ = lean_usize_dec_eq(v___x_963_, v___x_964_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_968_; 
lean_inc(v_idx_956_);
lean_inc(v_typeName_955_);
lean_dec_ref_known(v_e_786_, 3);
v___x_966_ = l_Lean_Expr_proj___override(v_typeName_955_, v_idx_956_, v_a_959_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_966_);
v___x_968_ = v___x_961_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
else
{
lean_object* v___x_971_; 
lean_dec(v_a_959_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v_e_786_);
v___x_971_ = v___x_961_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_e_786_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_786_, 3);
return v___x_958_;
}
}
default: 
{
lean_object* v___x_974_; 
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v_e_786_);
return v___x_974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(uint8_t v_pu_975_, lean_object* v_e_976_, uint8_t v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
if (lean_obj_tag(v_e_976_) == 5)
{
lean_object* v_fn_984_; lean_object* v_arg_985_; lean_object* v___x_986_; 
v_fn_984_ = lean_ctor_get(v_e_976_, 0);
v_arg_985_ = lean_ctor_get(v_e_976_, 1);
lean_inc_ref(v_fn_984_);
v___x_986_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_975_, v_fn_984_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_988_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 1);
lean_inc_ref(v_arg_985_);
v___x_988_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_975_, v_arg_985_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1008_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_1008_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1008_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
uint8_t v___y_994_; size_t v___x_1002_; size_t v___x_1003_; uint8_t v___x_1004_; 
v___x_1002_ = lean_ptr_addr(v_fn_984_);
v___x_1003_ = lean_ptr_addr(v_a_987_);
v___x_1004_ = lean_usize_dec_eq(v___x_1002_, v___x_1003_);
if (v___x_1004_ == 0)
{
v___y_994_ = v___x_1004_;
goto v___jp_993_;
}
else
{
size_t v___x_1005_; size_t v___x_1006_; uint8_t v___x_1007_; 
v___x_1005_ = lean_ptr_addr(v_arg_985_);
v___x_1006_ = lean_ptr_addr(v_a_989_);
v___x_1007_ = lean_usize_dec_eq(v___x_1005_, v___x_1006_);
v___y_994_ = v___x_1007_;
goto v___jp_993_;
}
v___jp_993_:
{
if (v___y_994_ == 0)
{
lean_object* v___x_995_; lean_object* v___x_997_; 
lean_dec_ref_known(v_e_976_, 2);
v___x_995_ = l_Lean_Expr_app___override(v_a_987_, v_a_989_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v___x_995_);
v___x_997_ = v___x_991_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
else
{
lean_object* v___x_1000_; 
lean_dec(v_a_989_);
lean_dec(v_a_987_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v_e_976_);
v___x_1000_ = v___x_991_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_e_976_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
else
{
lean_dec(v_a_987_);
lean_dec_ref_known(v_e_976_, 2);
return v___x_988_;
}
}
else
{
lean_dec_ref_known(v_e_976_, 2);
return v___x_986_;
}
}
else
{
lean_object* v___x_1009_; 
v___x_1009_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_975_, v_e_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
return v___x_1009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp___boxed(lean_object* v_pu_1010_, lean_object* v_e_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
uint8_t v_pu_boxed_1019_; uint8_t v_a_boxed_1020_; lean_object* v_res_1021_; 
v_pu_boxed_1019_ = lean_unbox(v_pu_1010_);
v_a_boxed_1020_ = lean_unbox(v_a_1012_);
v_res_1021_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_boxed_1019_, v_e_1011_, v_a_boxed_1020_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___boxed(lean_object* v_pu_1022_, lean_object* v_e_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
uint8_t v_pu_boxed_1031_; uint8_t v_a_boxed_1032_; lean_object* v_res_1033_; 
v_pu_boxed_1031_ = lean_unbox(v_pu_1022_);
v_a_boxed_1032_ = lean_unbox(v_a_1024_);
v_res_1033_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_boxed_1031_, v_e_1023_, v_a_boxed_1032_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(lean_object* v_00_u03b2_1034_, lean_object* v_m_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v_m_1035_, v_a_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___boxed(lean_object* v_00_u03b2_1038_, lean_object* v_m_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(v_00_u03b2_1038_, v_m_1039_, v_a_1040_);
lean_dec(v_a_1040_);
lean_dec_ref(v_m_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(lean_object* v_00_u03b2_1042_, lean_object* v_m_1043_, lean_object* v_query_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_m_1043_, v_query_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1046_, lean_object* v_m_1047_, lean_object* v_query_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(v_00_u03b2_1046_, v_m_1047_, v_query_1048_);
lean_dec(v_query_1048_);
lean_dec_ref(v_m_1047_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(uint8_t v_pu_1050_, lean_object* v_e_1051_, uint8_t v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
uint8_t v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = 1;
v___x_1060_ = l_Lean_Compiler_LCNF_instDecidableEqPurity(v_pu_1050_, v___x_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
v___x_1061_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_1050_, v_e_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
return v___x_1061_;
}
else
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v_e_1051_);
return v___x_1062_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___boxed(lean_object* v_pu_1063_, lean_object* v_e_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
uint8_t v_pu_boxed_1072_; uint8_t v_a_boxed_1073_; lean_object* v_res_1074_; 
v_pu_boxed_1072_ = lean_unbox(v_pu_1063_);
v_a_boxed_1073_ = lean_unbox(v_a_1065_);
v_res_1074_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_boxed_1072_, v_e_1064_, v_a_boxed_1073_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t v_pu_1075_, lean_object* v_p_1076_, uint8_t v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v_fvarId_1084_; lean_object* v_binderName_1085_; lean_object* v_type_1086_; uint8_t v_borrow_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1135_; 
v_fvarId_1084_ = lean_ctor_get(v_p_1076_, 0);
v_binderName_1085_ = lean_ctor_get(v_p_1076_, 1);
v_type_1086_ = lean_ctor_get(v_p_1076_, 2);
v_borrow_1087_ = lean_ctor_get_uint8(v_p_1076_, sizeof(void*)*3);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_p_1076_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1089_ = v_p_1076_;
v_isShared_1090_ = v_isSharedCheck_1135_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_type_1086_);
lean_inc(v_binderName_1085_);
lean_inc(v_fvarId_1084_);
lean_dec(v_p_1076_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1135_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v_a_1092_; lean_object* v___x_1093_; 
v___x_1091_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_1085_, v_a_1077_, v_a_1080_);
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref(v___x_1091_);
v___x_1093_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1075_, v_type_1086_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1095_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1093_, 1);
v___x_1095_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_1084_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1118_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1098_ = v___x_1095_;
v_isShared_1099_ = v_isSharedCheck_1118_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1095_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1118_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; lean_object* v_lctx_1101_; lean_object* v_nextIdx_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1117_; 
v___x_1100_ = lean_st_ref_take(v_a_1080_);
v_lctx_1101_ = lean_ctor_get(v___x_1100_, 0);
v_nextIdx_1102_ = lean_ctor_get(v___x_1100_, 1);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1104_ = v___x_1100_;
v_isShared_1105_ = v_isSharedCheck_1117_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_nextIdx_1102_);
lean_inc(v_lctx_1101_);
lean_dec(v___x_1100_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1117_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 2, v_a_1094_);
lean_ctor_set(v___x_1089_, 1, v_a_1092_);
lean_ctor_set(v___x_1089_, 0, v_a_1096_);
v___x_1107_ = v___x_1089_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1096_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_a_1092_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v_a_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1116_, sizeof(void*)*3, v_borrow_1087_);
v___x_1107_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
lean_inc_ref(v___x_1107_);
v___x_1108_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_1075_, v_lctx_1101_, v___x_1107_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1108_);
v___x_1110_ = v___x_1104_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_nextIdx_1102_);
v___x_1110_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1111_ = lean_st_ref_put(v_a_1080_, v___x_1110_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 0, v___x_1107_);
v___x_1113_ = v___x_1098_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1107_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v_a_1094_);
lean_dec(v_a_1092_);
lean_del_object(v___x_1089_);
v_a_1119_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1095_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1095_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec(v_a_1092_);
lean_del_object(v___x_1089_);
lean_dec(v_fvarId_1084_);
v_a_1127_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1093_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1093_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(lean_object* v_pu_1136_, lean_object* v_p_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
uint8_t v_pu_boxed_1145_; uint8_t v_a_boxed_1146_; lean_object* v_res_1147_; 
v_pu_boxed_1145_ = lean_unbox(v_pu_1136_);
v_a_boxed_1146_ = lean_unbox(v_a_1138_);
v_res_1147_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_boxed_1145_, v_p_1137_, v_a_boxed_1146_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg(uint8_t v_pu_1148_, lean_object* v_arg_1149_, uint8_t v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
switch(lean_obj_tag(v_arg_1149_))
{
case 0:
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v_arg_1149_);
return v___x_1157_;
}
case 1:
{
lean_object* v_fvarId_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v_fvarId_1158_ = lean_ctor_get(v_arg_1149_, 0);
v___x_1159_ = lean_st_ref_get(v_a_1151_);
v___x_1160_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v___x_1159_, v_fvarId_1158_);
lean_dec(v___x_1159_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v_arg_1149_);
return v___x_1161_;
}
else
{
lean_object* v_val_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1192_; 
lean_dec_ref_known(v_arg_1149_, 1);
v_val_1162_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1164_ = v___x_1160_;
v_isShared_1165_ = v_isSharedCheck_1192_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_val_1162_);
lean_dec(v___x_1160_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1192_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
switch(lean_obj_tag(v_val_1162_))
{
case 0:
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = lean_box(0);
if (v_isShared_1165_ == 0)
{
lean_ctor_set_tag(v___x_1164_, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1166_);
v___x_1168_ = v___x_1164_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
case 1:
{
lean_object* v_fvarId_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1180_; 
v_fvarId_1170_ = lean_ctor_get(v_val_1162_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_val_1162_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1172_ = v_val_1162_;
v_isShared_1173_ = v_isSharedCheck_1180_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_fvarId_1170_);
lean_dec(v_val_1162_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1180_;
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
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_fvarId_1170_);
v___x_1175_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1177_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set_tag(v___x_1164_, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1175_);
v___x_1177_ = v___x_1164_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
default: 
{
lean_object* v_expr_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1191_; 
v_expr_1181_ = lean_ctor_get(v_val_1162_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_val_1162_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1183_ = v_val_1162_;
v_isShared_1184_ = v_isSharedCheck_1191_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_expr_1181_);
lean_dec(v_val_1162_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1191_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_expr_1181_);
v___x_1186_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1188_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set_tag(v___x_1164_, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1186_);
v___x_1188_ = v___x_1164_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
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
lean_object* v_expr_1193_; lean_object* v___x_1194_; 
v_expr_1193_ = lean_ctor_get(v_arg_1149_, 0);
lean_inc_ref(v_expr_1193_);
v___x_1194_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1148_, v_expr_1193_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1203_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1197_ = v___x_1194_;
v_isShared_1198_ = v_isSharedCheck_1203_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1203_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1199_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1148_, v_arg_1149_, v_a_1195_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1199_);
v___x_1201_ = v___x_1197_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec_ref_known(v_arg_1149_, 1);
v_a_1204_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1194_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1194_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg___boxed(lean_object* v_pu_1212_, lean_object* v_arg_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
uint8_t v_pu_boxed_1221_; uint8_t v_a_boxed_1222_; lean_object* v_res_1223_; 
v_pu_boxed_1221_ = lean_unbox(v_pu_1212_);
v_a_boxed_1222_ = lean_unbox(v_a_1214_);
v_res_1223_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_boxed_1221_, v_arg_1213_, v_a_boxed_1222_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(uint8_t v_pu_1224_, size_t v_sz_1225_, size_t v_i_1226_, lean_object* v_bs_1227_, uint8_t v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
uint8_t v___x_1235_; 
v___x_1235_ = lean_usize_dec_lt(v_i_1226_, v_sz_1225_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; 
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v_bs_1227_);
return v___x_1236_;
}
else
{
lean_object* v_v_1237_; lean_object* v___x_1238_; 
v_v_1237_ = lean_array_uget_borrowed(v_bs_1227_, v_i_1226_);
lean_inc(v_v_1237_);
v___x_1238_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_1224_, v_v_1237_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1240_; lean_object* v_bs_x27_1241_; size_t v___x_1242_; size_t v___x_1243_; lean_object* v___x_1244_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref_known(v___x_1238_, 1);
v___x_1240_ = lean_unsigned_to_nat(0u);
v_bs_x27_1241_ = lean_array_uset(v_bs_1227_, v_i_1226_, v___x_1240_);
v___x_1242_ = ((size_t)1ULL);
v___x_1243_ = lean_usize_add(v_i_1226_, v___x_1242_);
v___x_1244_ = lean_array_uset(v_bs_x27_1241_, v_i_1226_, v_a_1239_);
v_i_1226_ = v___x_1243_;
v_bs_1227_ = v___x_1244_;
goto _start;
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec_ref(v_bs_1227_);
v_a_1246_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1238_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1238_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0___boxed(lean_object* v_pu_1254_, lean_object* v_sz_1255_, lean_object* v_i_1256_, lean_object* v_bs_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
uint8_t v_pu_boxed_1265_; size_t v_sz_boxed_1266_; size_t v_i_boxed_1267_; uint8_t v___y_341__boxed_1268_; lean_object* v_res_1269_; 
v_pu_boxed_1265_ = lean_unbox(v_pu_1254_);
v_sz_boxed_1266_ = lean_unbox_usize(v_sz_1255_);
lean_dec(v_sz_1255_);
v_i_boxed_1267_ = lean_unbox_usize(v_i_1256_);
lean_dec(v_i_1256_);
v___y_341__boxed_1268_ = lean_unbox(v___y_1258_);
v_res_1269_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_boxed_1265_, v_sz_boxed_1266_, v_i_boxed_1267_, v_bs_1257_, v___y_341__boxed_1268_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs(uint8_t v_pu_1270_, lean_object* v_args_1271_, uint8_t v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
size_t v_sz_1279_; size_t v___x_1280_; lean_object* v___x_1281_; 
v_sz_1279_ = lean_array_size(v_args_1271_);
v___x_1280_ = ((size_t)0ULL);
v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_1270_, v_sz_1279_, v___x_1280_, v_args_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs___boxed(lean_object* v_pu_1282_, lean_object* v_args_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
uint8_t v_pu_boxed_1291_; uint8_t v_a_boxed_1292_; lean_object* v_res_1293_; 
v_pu_boxed_1291_ = lean_unbox(v_pu_1282_);
v_a_boxed_1292_ = lean_unbox(v_a_1284_);
v_res_1293_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_boxed_1291_, v_args_1283_, v_a_boxed_1292_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(uint8_t v_pu_1294_, lean_object* v_e_1295_, uint8_t v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_fvarId_1304_; lean_object* v___y_1305_; lean_object* v_args_1321_; uint8_t v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; 
switch(lean_obj_tag(v_e_1295_))
{
case 2:
{
lean_object* v_struct_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; lean_object* v___x_1349_; 
v_struct_1346_ = lean_ctor_get(v_e_1295_, 2);
v___x_1347_ = lean_st_ref_get(v_a_1297_);
v___x_1348_ = 1;
lean_inc(v_struct_1346_);
v___x_1349_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1347_, v_struct_1346_, v___x_1348_);
lean_dec(v___x_1347_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_fvarId_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1358_; 
v_fvarId_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1358_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_fvarId_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1358_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1354_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1294_, v_e_1295_, v_fvarId_1350_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1354_);
v___x_1356_ = v___x_1352_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec_ref_known(v_e_1295_, 3);
v___x_1359_ = lean_box(1);
v___x_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
return v___x_1360_;
}
}
case 3:
{
lean_object* v_args_1361_; lean_object* v___x_1362_; 
v_args_1361_ = lean_ctor_get(v_e_1295_, 2);
lean_inc_ref(v_args_1361_);
v___x_1362_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1294_, v_args_1361_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1371_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1365_ = v___x_1362_;
v_isShared_1366_ = v_isSharedCheck_1371_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1362_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1371_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1369_; 
v___x_1367_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1294_, v_e_1295_, v_a_1363_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1367_);
v___x_1369_ = v___x_1365_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec_ref_known(v_e_1295_, 3);
v_a_1372_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1362_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1362_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
case 4:
{
lean_object* v_fvarId_1380_; lean_object* v_args_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; lean_object* v___x_1384_; 
v_fvarId_1380_ = lean_ctor_get(v_e_1295_, 0);
v_args_1381_ = lean_ctor_get(v_e_1295_, 1);
v___x_1382_ = lean_st_ref_get(v_a_1297_);
v___x_1383_ = 1;
lean_inc(v_fvarId_1380_);
v___x_1384_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1382_, v_fvarId_1380_, v___x_1383_);
lean_dec(v___x_1382_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_fvarId_1385_; lean_object* v___x_1386_; 
v_fvarId_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_fvarId_1385_);
lean_dec_ref_known(v___x_1384_, 1);
lean_inc_ref(v_args_1381_);
v___x_1386_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1294_, v_args_1381_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1395_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1395_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1395_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_1294_, v_e_1295_, v_fvarId_1385_, v_a_1387_);
lean_dec_ref_known(v_e_1295_, 2);
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
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_dec(v_fvarId_1385_);
lean_dec_ref_known(v_e_1295_, 2);
v_a_1396_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1386_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1386_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
else
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_dec_ref_known(v_e_1295_, 2);
v___x_1404_ = lean_box(1);
v___x_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
return v___x_1405_;
}
}
case 5:
{
lean_object* v_args_1406_; lean_object* v___x_1407_; 
v_args_1406_ = lean_ctor_get(v_e_1295_, 1);
lean_inc_ref(v_args_1406_);
v___x_1407_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1294_, v_args_1406_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1416_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1416_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1416_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1294_, v_e_1295_, v_a_1408_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v___x_1412_);
v___x_1414_ = v___x_1410_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec_ref_known(v_e_1295_, 2);
v_a_1417_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1407_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1407_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
case 6:
{
lean_object* v_var_1425_; 
v_var_1425_ = lean_ctor_get(v_e_1295_, 1);
lean_inc(v_var_1425_);
v_fvarId_1304_ = v_var_1425_;
v___y_1305_ = v_a_1297_;
goto v___jp_1303_;
}
case 7:
{
lean_object* v_var_1426_; 
v_var_1426_ = lean_ctor_get(v_e_1295_, 1);
lean_inc(v_var_1426_);
v_fvarId_1304_ = v_var_1426_;
v___y_1305_ = v_a_1297_;
goto v___jp_1303_;
}
case 8:
{
lean_object* v_var_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; lean_object* v___x_1430_; 
v_var_1427_ = lean_ctor_get(v_e_1295_, 2);
v___x_1428_ = lean_st_ref_get(v_a_1297_);
v___x_1429_ = 1;
lean_inc(v_var_1427_);
v___x_1430_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1428_, v_var_1427_, v___x_1429_);
lean_dec(v___x_1428_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_fvarId_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1439_; 
v_fvarId_1431_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1433_ = v___x_1430_;
v_isShared_1434_ = v_isSharedCheck_1439_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_fvarId_1431_);
lean_dec(v___x_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1439_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1435_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1294_, v_e_1295_, v_fvarId_1431_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 0, v___x_1435_);
v___x_1437_ = v___x_1433_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
lean_dec_ref_known(v_e_1295_, 3);
v___x_1440_ = lean_box(1);
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
return v___x_1441_;
}
}
case 9:
{
lean_object* v_args_1442_; 
v_args_1442_ = lean_ctor_get(v_e_1295_, 1);
lean_inc_ref(v_args_1442_);
v_args_1321_ = v_args_1442_;
v___y_1322_ = v_a_1296_;
v___y_1323_ = v_a_1297_;
v___y_1324_ = v_a_1298_;
v___y_1325_ = v_a_1299_;
v___y_1326_ = v_a_1300_;
v___y_1327_ = v_a_1301_;
goto v___jp_1320_;
}
case 10:
{
lean_object* v_args_1443_; 
v_args_1443_ = lean_ctor_get(v_e_1295_, 1);
lean_inc_ref(v_args_1443_);
v_args_1321_ = v_args_1443_;
v___y_1322_ = v_a_1296_;
v___y_1323_ = v_a_1297_;
v___y_1324_ = v_a_1298_;
v___y_1325_ = v_a_1299_;
v___y_1326_ = v_a_1300_;
v___y_1327_ = v_a_1301_;
goto v___jp_1320_;
}
case 11:
{
lean_object* v_n_1444_; lean_object* v_var_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; lean_object* v___x_1448_; 
v_n_1444_ = lean_ctor_get(v_e_1295_, 0);
lean_inc(v_n_1444_);
v_var_1445_ = lean_ctor_get(v_e_1295_, 1);
v___x_1446_ = lean_st_ref_get(v_a_1297_);
v___x_1447_ = 1;
lean_inc(v_var_1445_);
v___x_1448_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1446_, v_var_1445_, v___x_1447_);
lean_dec(v___x_1446_);
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
v___x_1453_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_1294_, v_e_1295_, v_n_1444_, v_fvarId_1449_);
lean_dec_ref_known(v_e_1295_, 2);
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
lean_dec_ref_known(v_e_1295_, 2);
lean_dec(v_n_1444_);
v___x_1458_ = lean_box(1);
v___x_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
return v___x_1459_;
}
}
case 12:
{
lean_object* v_var_1460_; lean_object* v_i_1461_; uint8_t v_updateHeader_1462_; lean_object* v_args_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; lean_object* v___x_1466_; 
v_var_1460_ = lean_ctor_get(v_e_1295_, 0);
v_i_1461_ = lean_ctor_get(v_e_1295_, 1);
lean_inc_ref(v_i_1461_);
v_updateHeader_1462_ = lean_ctor_get_uint8(v_e_1295_, sizeof(void*)*3);
v_args_1463_ = lean_ctor_get(v_e_1295_, 2);
v___x_1464_ = lean_st_ref_get(v_a_1297_);
v___x_1465_ = 1;
lean_inc(v_var_1460_);
v___x_1466_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1464_, v_var_1460_, v___x_1465_);
lean_dec(v___x_1464_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_fvarId_1467_; lean_object* v___x_1468_; 
v_fvarId_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_fvarId_1467_);
lean_dec_ref_known(v___x_1466_, 1);
lean_inc_ref(v_args_1463_);
v___x_1468_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1294_, v_args_1463_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1477_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1471_ = v___x_1468_;
v_isShared_1472_ = v_isSharedCheck_1477_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1468_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1477_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1473_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_1294_, v_e_1295_, v_fvarId_1467_, v_i_1461_, v_updateHeader_1462_, v_a_1469_);
if (v_isShared_1472_ == 0)
{
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
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec(v_fvarId_1467_);
lean_dec_ref(v_i_1461_);
lean_dec_ref_known(v_e_1295_, 3);
v_a_1478_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1468_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1468_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_dec_ref(v_i_1461_);
lean_dec_ref_known(v_e_1295_, 3);
v___x_1486_ = lean_box(1);
v___x_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
return v___x_1487_;
}
}
case 13:
{
lean_object* v_ty_1488_; lean_object* v_fvarId_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; lean_object* v___x_1492_; 
v_ty_1488_ = lean_ctor_get(v_e_1295_, 0);
lean_inc_ref(v_ty_1488_);
v_fvarId_1489_ = lean_ctor_get(v_e_1295_, 1);
v___x_1490_ = lean_st_ref_get(v_a_1297_);
v___x_1491_ = 1;
lean_inc(v_fvarId_1489_);
v___x_1492_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1490_, v_fvarId_1489_, v___x_1491_);
lean_dec(v___x_1490_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_fvarId_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1501_; 
v_fvarId_1493_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1495_ = v___x_1492_;
v_isShared_1496_ = v_isSharedCheck_1501_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_fvarId_1493_);
lean_dec(v___x_1492_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1501_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1497_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_1294_, v_e_1295_, v_ty_1488_, v_fvarId_1493_);
lean_dec_ref_known(v_e_1295_, 2);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v___x_1497_);
v___x_1499_ = v___x_1495_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
else
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_dec_ref(v_ty_1488_);
lean_dec_ref_known(v_e_1295_, 2);
v___x_1502_ = lean_box(1);
v___x_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
return v___x_1503_;
}
}
case 14:
{
lean_object* v_fvarId_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; lean_object* v___x_1507_; 
v_fvarId_1504_ = lean_ctor_get(v_e_1295_, 0);
v___x_1505_ = lean_st_ref_get(v_a_1297_);
v___x_1506_ = 1;
lean_inc(v_fvarId_1504_);
v___x_1507_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1505_, v_fvarId_1504_, v___x_1506_);
lean_dec(v___x_1505_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_fvarId_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1516_; 
v_fvarId_1508_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1510_ = v___x_1507_;
v_isShared_1511_ = v_isSharedCheck_1516_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_fvarId_1508_);
lean_dec(v___x_1507_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1516_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1512_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_1294_, v_e_1295_, v_fvarId_1508_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v___x_1512_);
v___x_1514_ = v___x_1510_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
else
{
lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1524_; 
v_isSharedCheck_1524_ = !lean_is_exclusive(v_e_1295_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; 
v_unused_1525_ = lean_ctor_get(v_e_1295_, 0);
lean_dec(v_unused_1525_);
v___x_1518_ = v_e_1295_;
v_isShared_1519_ = v_isSharedCheck_1524_;
goto v_resetjp_1517_;
}
else
{
lean_dec(v_e_1295_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1524_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1520_ = lean_box(1);
if (v_isShared_1519_ == 0)
{
lean_ctor_set_tag(v___x_1518_, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1520_);
v___x_1522_ = v___x_1518_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
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
case 15:
{
lean_object* v_fvarId_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; 
v_fvarId_1526_ = lean_ctor_get(v_e_1295_, 0);
v___x_1527_ = lean_st_ref_get(v_a_1297_);
v___x_1528_ = 1;
lean_inc(v_fvarId_1526_);
v___x_1529_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1527_, v_fvarId_1526_, v___x_1528_);
lean_dec(v___x_1527_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_fvarId_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1538_; 
v_fvarId_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1538_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_fvarId_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1538_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1534_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_1294_, v_e_1295_, v_fvarId_1530_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v___x_1534_);
v___x_1536_ = v___x_1532_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
else
{
lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1546_; 
v_isSharedCheck_1546_ = !lean_is_exclusive(v_e_1295_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v_e_1295_, 0);
lean_dec(v_unused_1547_);
v___x_1540_ = v_e_1295_;
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
else
{
lean_dec(v_e_1295_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1542_ = lean_box(1);
if (v_isShared_1541_ == 0)
{
lean_ctor_set_tag(v___x_1540_, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1542_);
v___x_1544_ = v___x_1540_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
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
default: 
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v_e_1295_);
return v___x_1548_;
}
}
v___jp_1303_:
{
lean_object* v___x_1306_; uint8_t v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_st_ref_get(v___y_1305_);
v___x_1307_ = 1;
v___x_1308_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1306_, v_fvarId_1304_, v___x_1307_);
lean_dec(v___x_1306_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_fvarId_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1317_; 
v_fvarId_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1317_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_fvarId_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1317_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1313_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1294_, v_e_1295_, v_fvarId_1309_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v___x_1313_);
v___x_1315_ = v___x_1311_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_dec(v_e_1295_);
v___x_1318_ = lean_box(1);
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
return v___x_1319_;
}
}
v___jp_1320_:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1294_, v_args_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
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
v___x_1333_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1294_, v_e_1295_, v_a_1329_);
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
lean_dec(v_e_1295_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue___boxed(lean_object* v_pu_1549_, lean_object* v_e_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
uint8_t v_pu_boxed_1558_; uint8_t v_a_boxed_1559_; lean_object* v_res_1560_; 
v_pu_boxed_1558_ = lean_unbox(v_pu_1549_);
v_a_boxed_1559_ = lean_unbox(v_a_1551_);
v_res_1560_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_boxed_1558_, v_e_1550_, v_a_boxed_1559_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec_ref(v_a_1553_);
lean_dec(v_a_1552_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(uint8_t v_pu_1561_, lean_object* v_decl_1562_, uint8_t v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v_fvarId_1570_; lean_object* v_binderName_1571_; lean_object* v_type_1572_; lean_object* v_value_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1631_; 
v_fvarId_1570_ = lean_ctor_get(v_decl_1562_, 0);
v_binderName_1571_ = lean_ctor_get(v_decl_1562_, 1);
v_type_1572_ = lean_ctor_get(v_decl_1562_, 2);
v_value_1573_ = lean_ctor_get(v_decl_1562_, 3);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_decl_1562_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1575_ = v_decl_1562_;
v_isShared_1576_ = v_isSharedCheck_1631_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_value_1573_);
lean_inc(v_type_1572_);
lean_inc(v_binderName_1571_);
lean_inc(v_fvarId_1570_);
lean_dec(v_decl_1562_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1631_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; lean_object* v_a_1578_; lean_object* v___x_1579_; 
v___x_1577_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_1571_, v_a_1563_, v_a_1566_);
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref(v___x_1577_);
v___x_1579_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1561_, v_type_1572_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v___x_1581_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_1561_, v_value_1573_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1583_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_1570_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1606_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1606_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1606_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v_lctx_1589_; lean_object* v_nextIdx_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1605_; 
v___x_1588_ = lean_st_ref_take(v_a_1566_);
v_lctx_1589_ = lean_ctor_get(v___x_1588_, 0);
v_nextIdx_1590_ = lean_ctor_get(v___x_1588_, 1);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1592_ = v___x_1588_;
v_isShared_1593_ = v_isSharedCheck_1605_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_nextIdx_1590_);
lean_inc(v_lctx_1589_);
lean_dec(v___x_1588_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1605_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 3, v_a_1582_);
lean_ctor_set(v___x_1575_, 2, v_a_1580_);
lean_ctor_set(v___x_1575_, 1, v_a_1578_);
lean_ctor_set(v___x_1575_, 0, v_a_1584_);
v___x_1595_ = v___x_1575_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1584_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_a_1578_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_a_1580_);
lean_ctor_set(v_reuseFailAlloc_1604_, 3, v_a_1582_);
v___x_1595_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1596_; lean_object* v___x_1598_; 
lean_inc_ref(v___x_1595_);
v___x_1596_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_1561_, v_lctx_1589_, v___x_1595_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1596_);
v___x_1598_ = v___x_1592_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_nextIdx_1590_);
v___x_1598_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; lean_object* v___x_1601_; 
v___x_1599_ = lean_st_ref_put(v_a_1566_, v___x_1598_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1595_);
v___x_1601_ = v___x_1586_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1595_);
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
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec(v_a_1582_);
lean_dec(v_a_1580_);
lean_dec(v_a_1578_);
lean_del_object(v___x_1575_);
v_a_1607_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1583_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1583_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec(v_a_1580_);
lean_dec(v_a_1578_);
lean_del_object(v___x_1575_);
lean_dec(v_fvarId_1570_);
v_a_1615_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1581_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1581_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec(v_a_1578_);
lean_del_object(v___x_1575_);
lean_dec(v_value_1573_);
lean_dec(v_fvarId_1570_);
v_a_1623_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1579_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1579_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(lean_object* v_pu_1632_, lean_object* v_decl_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
uint8_t v_pu_boxed_1641_; uint8_t v_a_boxed_1642_; lean_object* v_res_1643_; 
v_pu_boxed_1641_ = lean_unbox(v_pu_1632_);
v_a_boxed_1642_ = lean_unbox(v_a_1634_);
v_res_1643_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_boxed_1641_, v_decl_1633_, v_a_boxed_1642_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
lean_dec(v_a_1637_);
lean_dec_ref(v_a_1636_);
lean_dec(v_a_1635_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(uint8_t v_pu_1644_, size_t v_sz_1645_, size_t v_i_1646_, lean_object* v_bs_1647_, uint8_t v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
uint8_t v___x_1655_; 
v___x_1655_ = lean_usize_dec_lt(v_i_1646_, v_sz_1645_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1656_, 0, v_bs_1647_);
return v___x_1656_;
}
else
{
lean_object* v_v_1657_; lean_object* v___x_1658_; 
v_v_1657_ = lean_array_uget_borrowed(v_bs_1647_, v_i_1646_);
lean_inc(v_v_1657_);
v___x_1658_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_1644_, v_v_1657_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1660_; lean_object* v_bs_x27_1661_; size_t v___x_1662_; size_t v___x_1663_; lean_object* v___x_1664_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1658_, 1);
v___x_1660_ = lean_unsigned_to_nat(0u);
v_bs_x27_1661_ = lean_array_uset(v_bs_1647_, v_i_1646_, v___x_1660_);
v___x_1662_ = ((size_t)1ULL);
v___x_1663_ = lean_usize_add(v_i_1646_, v___x_1662_);
v___x_1664_ = lean_array_uset(v_bs_x27_1661_, v_i_1646_, v_a_1659_);
v_i_1646_ = v___x_1663_;
v_bs_1647_ = v___x_1664_;
goto _start;
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
lean_dec_ref(v_bs_1647_);
v_a_1666_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1658_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1658_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0___boxed(lean_object* v_pu_1674_, lean_object* v_sz_1675_, lean_object* v_i_1676_, lean_object* v_bs_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
uint8_t v_pu_boxed_1685_; size_t v_sz_boxed_1686_; size_t v_i_boxed_1687_; uint8_t v___y_26868__boxed_1688_; lean_object* v_res_1689_; 
v_pu_boxed_1685_ = lean_unbox(v_pu_1674_);
v_sz_boxed_1686_ = lean_unbox_usize(v_sz_1675_);
lean_dec(v_sz_1675_);
v_i_boxed_1687_ = lean_unbox_usize(v_i_1676_);
lean_dec(v_i_1676_);
v___y_26868__boxed_1688_ = lean_unbox(v___y_1678_);
v_res_1689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_boxed_1685_, v_sz_boxed_1686_, v_i_boxed_1687_, v_bs_1677_, v___y_26868__boxed_1688_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(uint8_t v_pu_1690_, size_t v_sz_1691_, size_t v_i_1692_, lean_object* v_bs_1693_, uint8_t v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
uint8_t v___x_1701_; 
v___x_1701_ = lean_usize_dec_lt(v_i_1692_, v_sz_1691_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; 
v___x_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1702_, 0, v_bs_1693_);
return v___x_1702_;
}
else
{
lean_object* v_v_1703_; lean_object* v___x_1704_; lean_object* v_bs_x27_1705_; lean_object* v_a_1707_; 
v_v_1703_ = lean_array_uget(v_bs_1693_, v_i_1692_);
v___x_1704_ = lean_unsigned_to_nat(0u);
v_bs_x27_1705_ = lean_array_uset(v_bs_1693_, v_i_1692_, v___x_1704_);
switch(lean_obj_tag(v_v_1703_))
{
case 0:
{
lean_object* v_ctorName_1712_; lean_object* v_params_1713_; lean_object* v_code_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1735_; 
v_ctorName_1712_ = lean_ctor_get(v_v_1703_, 0);
v_params_1713_ = lean_ctor_get(v_v_1703_, 1);
v_code_1714_ = lean_ctor_get(v_v_1703_, 2);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_v_1703_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1716_ = v_v_1703_;
v_isShared_1717_ = v_isSharedCheck_1735_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_code_1714_);
lean_inc(v_params_1713_);
lean_inc(v_ctorName_1712_);
lean_dec(v_v_1703_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1735_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
size_t v_sz_1718_; size_t v___x_1719_; lean_object* v___x_1720_; 
v_sz_1718_ = lean_array_size(v_params_1713_);
v___x_1719_ = ((size_t)0ULL);
v___x_1720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_1690_, v_sz_1718_, v___x_1719_, v_params_1713_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1722_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v___x_1720_, 1);
v___x_1722_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1690_, v_code_1714_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1725_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 2, v_a_1723_);
lean_ctor_set(v___x_1716_, 1, v_a_1721_);
v___x_1725_ = v___x_1716_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_ctorName_1712_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_a_1721_);
lean_ctor_set(v_reuseFailAlloc_1726_, 2, v_a_1723_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
v_a_1707_ = v___x_1725_;
goto v___jp_1706_;
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec(v_a_1721_);
lean_del_object(v___x_1716_);
lean_dec(v_ctorName_1712_);
lean_dec_ref(v_bs_x27_1705_);
v_a_1727_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1722_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1722_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
else
{
lean_del_object(v___x_1716_);
lean_dec_ref(v_code_1714_);
lean_dec(v_ctorName_1712_);
lean_dec_ref(v_bs_x27_1705_);
return v___x_1720_;
}
}
}
case 1:
{
lean_object* v_info_1736_; lean_object* v_code_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1754_; 
v_info_1736_ = lean_ctor_get(v_v_1703_, 0);
v_code_1737_ = lean_ctor_get(v_v_1703_, 1);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_v_1703_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1739_ = v_v_1703_;
v_isShared_1740_ = v_isSharedCheck_1754_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_code_1737_);
lean_inc(v_info_1736_);
lean_dec(v_v_1703_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1754_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1690_, v_code_1737_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1744_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref_known(v___x_1741_, 1);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 1, v_a_1742_);
v___x_1744_ = v___x_1739_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_info_1736_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_a_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
v_a_1707_ = v___x_1744_;
goto v___jp_1706_;
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_del_object(v___x_1739_);
lean_dec_ref(v_info_1736_);
lean_dec_ref(v_bs_x27_1705_);
v_a_1746_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1741_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1741_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
default: 
{
lean_object* v_code_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1772_; 
v_code_1755_ = lean_ctor_get(v_v_1703_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v_v_1703_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1757_ = v_v_1703_;
v_isShared_1758_ = v_isSharedCheck_1772_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_code_1755_);
lean_dec(v_v_1703_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1772_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1690_, v_code_1755_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1762_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref_known(v___x_1759_, 1);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v_a_1760_);
v___x_1762_ = v___x_1757_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
v_a_1707_ = v___x_1762_;
goto v___jp_1706_;
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_del_object(v___x_1757_);
lean_dec_ref(v_bs_x27_1705_);
v_a_1764_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1759_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1759_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
}
v___jp_1706_:
{
size_t v___x_1708_; size_t v___x_1709_; lean_object* v___x_1710_; 
v___x_1708_ = ((size_t)1ULL);
v___x_1709_ = lean_usize_add(v_i_1692_, v___x_1708_);
v___x_1710_ = lean_array_uset(v_bs_x27_1705_, v_i_1692_, v_a_1707_);
v_i_1692_ = v___x_1709_;
v_bs_1693_ = v___x_1710_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t v_pu_1773_, lean_object* v_code_1774_, uint8_t v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
switch(lean_obj_tag(v_code_1774_))
{
case 0:
{
lean_object* v_decl_1782_; lean_object* v_k_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1809_; 
v_decl_1782_ = lean_ctor_get(v_code_1774_, 0);
v_k_1783_ = lean_ctor_get(v_code_1774_, 1);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_code_1774_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1785_ = v_code_1774_;
v_isShared_1786_ = v_isSharedCheck_1809_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_k_1783_);
lean_inc(v_decl_1782_);
lean_dec(v_code_1774_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1809_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_1773_, v_decl_1782_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1789_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1787_, 1);
v___x_1789_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1773_, v_k_1783_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1800_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1800_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1800_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 1, v_a_1790_);
lean_ctor_set(v___x_1785_, 0, v_a_1788_);
v___x_1795_ = v___x_1785_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1788_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1797_; 
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v___x_1795_);
v___x_1797_ = v___x_1792_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
else
{
lean_dec(v_a_1788_);
lean_del_object(v___x_1785_);
return v___x_1789_;
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_del_object(v___x_1785_);
lean_dec_ref(v_k_1783_);
v_a_1801_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1787_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1787_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_1810_; lean_object* v_k_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1837_; 
v_decl_1810_ = lean_ctor_get(v_code_1774_, 0);
v_k_1811_ = lean_ctor_get(v_code_1774_, 1);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_code_1774_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1813_ = v_code_1774_;
v_isShared_1814_ = v_isSharedCheck_1837_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_k_1811_);
lean_inc(v_decl_1810_);
lean_dec(v_code_1774_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1837_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1773_, v_decl_1810_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1817_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_a_1816_);
lean_dec_ref_known(v___x_1815_, 1);
v___x_1817_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1773_, v_k_1811_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1828_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1828_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1828_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 1, v_a_1818_);
lean_ctor_set(v___x_1813_, 0, v_a_1816_);
v___x_1823_ = v___x_1813_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1816_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1825_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1823_);
v___x_1825_ = v___x_1820_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
else
{
lean_dec(v_a_1816_);
lean_del_object(v___x_1813_);
return v___x_1817_;
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_del_object(v___x_1813_);
lean_dec_ref(v_k_1811_);
v_a_1829_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1815_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1815_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
}
case 2:
{
lean_object* v_decl_1838_; lean_object* v_k_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1865_; 
v_decl_1838_ = lean_ctor_get(v_code_1774_, 0);
v_k_1839_ = lean_ctor_get(v_code_1774_, 1);
v_isSharedCheck_1865_ = !lean_is_exclusive(v_code_1774_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1841_ = v_code_1774_;
v_isShared_1842_ = v_isSharedCheck_1865_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_k_1839_);
lean_inc(v_decl_1838_);
lean_dec(v_code_1774_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1865_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1773_, v_decl_1838_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1845_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v___x_1843_, 1);
v___x_1845_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1773_, v_k_1839_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1856_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1856_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1856_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 1, v_a_1846_);
lean_ctor_set(v___x_1841_, 0, v_a_1844_);
v___x_1851_ = v___x_1841_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1844_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1853_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v___x_1851_);
v___x_1853_ = v___x_1848_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
else
{
lean_dec(v_a_1844_);
lean_del_object(v___x_1841_);
return v___x_1845_;
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_del_object(v___x_1841_);
lean_dec_ref(v_k_1839_);
v_a_1857_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1843_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1843_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_1866_; lean_object* v_args_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1896_; 
v_fvarId_1866_ = lean_ctor_get(v_code_1774_, 0);
v_args_1867_ = lean_ctor_get(v_code_1774_, 1);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_code_1774_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1869_ = v_code_1774_;
v_isShared_1870_ = v_isSharedCheck_1896_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_args_1867_);
lean_inc(v_fvarId_1866_);
lean_dec(v_code_1774_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1896_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; uint8_t v___x_1872_; lean_object* v___x_1873_; 
v___x_1871_ = lean_st_ref_get(v_a_1776_);
v___x_1872_ = 1;
v___x_1873_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1871_, v_fvarId_1866_, v___x_1872_);
lean_dec(v___x_1871_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_fvarId_1874_; lean_object* v___x_1875_; 
v_fvarId_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_fvarId_1874_);
lean_dec_ref_known(v___x_1873_, 1);
v___x_1875_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1773_, v_args_1867_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1886_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1878_ = v___x_1875_;
v_isShared_1879_ = v_isSharedCheck_1886_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1875_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1886_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 1, v_a_1876_);
lean_ctor_set(v___x_1869_, 0, v_fvarId_1874_);
v___x_1881_ = v___x_1869_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_fvarId_1874_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1883_; 
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1881_);
v___x_1883_ = v___x_1878_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
lean_dec(v_fvarId_1874_);
lean_del_object(v___x_1869_);
v_a_1887_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___x_1875_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1875_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
else
{
lean_object* v___x_1895_; 
lean_del_object(v___x_1869_);
lean_dec_ref(v_args_1867_);
v___x_1895_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1773_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
return v___x_1895_;
}
}
}
case 4:
{
lean_object* v_cases_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1949_; 
v_cases_1897_ = lean_ctor_get(v_code_1774_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_code_1774_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1899_ = v_code_1774_;
v_isShared_1900_ = v_isSharedCheck_1949_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_cases_1897_);
lean_dec(v_code_1774_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1949_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v_typeName_1901_; lean_object* v_resultType_1902_; lean_object* v_discr_1903_; lean_object* v_alts_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1948_; 
v_typeName_1901_ = lean_ctor_get(v_cases_1897_, 0);
v_resultType_1902_ = lean_ctor_get(v_cases_1897_, 1);
v_discr_1903_ = lean_ctor_get(v_cases_1897_, 2);
v_alts_1904_ = lean_ctor_get(v_cases_1897_, 3);
v_isSharedCheck_1948_ = !lean_is_exclusive(v_cases_1897_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1906_ = v_cases_1897_;
v_isShared_1907_ = v_isSharedCheck_1948_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_alts_1904_);
lean_inc(v_discr_1903_);
lean_inc(v_resultType_1902_);
lean_inc(v_typeName_1901_);
lean_dec(v_cases_1897_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1948_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; uint8_t v___x_1909_; lean_object* v___x_1910_; 
v___x_1908_ = lean_st_ref_get(v_a_1776_);
v___x_1909_ = 1;
v___x_1910_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1908_, v_discr_1903_, v___x_1909_);
lean_dec(v___x_1908_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_fvarId_1911_; lean_object* v___x_1912_; 
v_fvarId_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_fvarId_1911_);
lean_dec_ref_known(v___x_1910_, 1);
v___x_1912_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1773_, v_resultType_1902_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; size_t v_sz_1914_; size_t v___x_1915_; lean_object* v___x_1916_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v___x_1912_, 1);
v_sz_1914_ = lean_array_size(v_alts_1904_);
v___x_1915_ = ((size_t)0ULL);
v___x_1916_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_1773_, v_sz_1914_, v___x_1915_, v_alts_1904_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1930_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1930_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1930_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 3, v_a_1917_);
lean_ctor_set(v___x_1906_, 2, v_fvarId_1911_);
lean_ctor_set(v___x_1906_, 1, v_a_1913_);
v___x_1922_ = v___x_1906_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_typeName_1901_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_a_1913_);
lean_ctor_set(v_reuseFailAlloc_1929_, 2, v_fvarId_1911_);
lean_ctor_set(v_reuseFailAlloc_1929_, 3, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1924_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1922_);
v___x_1924_ = v___x_1899_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1926_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1924_);
v___x_1926_ = v___x_1919_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec(v_a_1913_);
lean_dec(v_fvarId_1911_);
lean_del_object(v___x_1906_);
lean_dec(v_typeName_1901_);
lean_del_object(v___x_1899_);
v_a_1931_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1916_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1916_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
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
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec(v_fvarId_1911_);
lean_del_object(v___x_1906_);
lean_dec_ref(v_alts_1904_);
lean_dec(v_typeName_1901_);
lean_del_object(v___x_1899_);
v_a_1939_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1912_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1912_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
else
{
lean_object* v___x_1947_; 
lean_del_object(v___x_1906_);
lean_dec_ref(v_alts_1904_);
lean_dec_ref(v_resultType_1902_);
lean_dec(v_typeName_1901_);
lean_del_object(v___x_1899_);
v___x_1947_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1773_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
return v___x_1947_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1969_; 
v_fvarId_1950_ = lean_ctor_get(v_code_1774_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_code_1774_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1952_ = v_code_1774_;
v_isShared_1953_ = v_isSharedCheck_1969_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_fvarId_1950_);
lean_dec(v_code_1774_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1969_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; uint8_t v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = lean_st_ref_get(v_a_1776_);
v___x_1955_ = 1;
v___x_1956_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1954_, v_fvarId_1950_, v___x_1955_);
lean_dec(v___x_1954_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_fvarId_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1967_; 
v_fvarId_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_1967_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_fvarId_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1967_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v_fvarId_1957_);
v___x_1962_ = v___x_1952_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_fvarId_1957_);
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
lean_object* v___x_1968_; 
lean_del_object(v___x_1952_);
v___x_1968_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1773_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
return v___x_1968_;
}
}
}
case 6:
{
lean_object* v_type_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1994_; 
v_type_1970_ = lean_ctor_get(v_code_1774_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_code_1774_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1972_ = v_code_1774_;
v_isShared_1973_ = v_isSharedCheck_1994_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_type_1970_);
lean_dec(v_code_1774_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1994_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; 
v___x_1974_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1773_, v_type_1970_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1985_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_1985_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1985_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v_a_1975_);
v___x_1980_ = v___x_1972_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1982_; 
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1980_);
v___x_1982_ = v___x_1977_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_del_object(v___x_1972_);
v_a_1986_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1974_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1974_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_1995_; lean_object* v_i_1996_; lean_object* v_y_1997_; lean_object* v_k_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2021_; 
v_fvarId_1995_ = lean_ctor_get(v_code_1774_, 0);
v_i_1996_ = lean_ctor_get(v_code_1774_, 1);
v_y_1997_ = lean_ctor_get(v_code_1774_, 2);
v_k_1998_ = lean_ctor_get(v_code_1774_, 3);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_code_1774_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2000_ = v_code_1774_;
v_isShared_2001_ = v_isSharedCheck_2021_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_k_1998_);
lean_inc(v_y_1997_);
lean_inc(v_i_1996_);
lean_inc(v_fvarId_1995_);
lean_dec(v_code_1774_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2021_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; uint8_t v___x_2003_; lean_object* v___x_2004_; 
v___x_2002_ = lean_st_ref_get(v_a_1776_);
v___x_2003_ = 1;
v___x_2004_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2002_, v_fvarId_1995_, v___x_2003_);
lean_dec(v___x_2002_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_fvarId_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v_fvarId_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_fvarId_2005_);
lean_dec_ref_known(v___x_2004_, 1);
v___x_2006_ = lean_st_ref_get(v_a_1776_);
v___x_2007_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1773_, v___x_2006_, v_y_1997_, v___x_2003_);
lean_dec(v___x_2006_);
v___x_2008_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1773_, v_k_1998_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2019_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2011_ = v___x_2008_;
v_isShared_2012_ = v_isSharedCheck_2019_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2008_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2019_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 3, v_a_2009_);
lean_ctor_set(v___x_2000_, 2, v___x_2007_);
lean_ctor_set(v___x_2000_, 0, v_fvarId_2005_);
v___x_2014_ = v___x_2000_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_fvarId_2005_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_i_1996_);
lean_ctor_set(v_reuseFailAlloc_2018_, 2, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2018_, 3, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2016_; 
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_2014_);
v___x_2016_ = v___x_2011_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2014_);
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
lean_dec(v___x_2007_);
lean_dec(v_fvarId_2005_);
lean_del_object(v___x_2000_);
lean_dec(v_i_1996_);
return v___x_2008_;
}
}
else
{
lean_object* v___x_2020_; 
lean_del_object(v___x_2000_);
lean_dec_ref(v_k_1998_);
lean_dec(v_y_1997_);
lean_dec(v_i_1996_);
v___x_2020_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1773_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
return v___x_2020_;
}
}
}
case 8:
{
lean_object* v_fvarId_2022_; lean_object* v_i_2023_; lean_object* v_y_2024_; lean_object* v_k_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2050_; 
v_fvarId_2022_ = lean_ctor_get(v_code_1774_, 0);
v_i_2023_ = lean_ctor_get(v_code_1774_, 1);
v_y_2024_ = lean_ctor_get(v_code_1774_, 2);
v_k_2025_ = lean_ctor_get(v_code_1774_, 3);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_code_1774_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2027_ = v_code_1774_;
v_isShared_2028_ = v_isSharedCheck_2050_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_k_2025_);
lean_inc(v_y_2024_);
lean_inc(v_i_2023_);
lean_inc(v_fvarId_2022_);
lean_dec(v_code_1774_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2050_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2029_; uint8_t v___x_2030_; lean_object* v___x_2031_; 
v___x_2029_ = lean_st_ref_get(v_a_1776_);
v___x_2030_ = 1;
v___x_2031_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2029_, v_fvarId_2022_, v___x_2030_);
lean_dec(v___x_2029_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_fvarId_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v_fvarId_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_fvarId_2032_);
lean_dec_ref_known(v___x_2031_, 1);
v___x_2033_ = lean_st_ref_get(v_a_1776_);
v___x_2034_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2033_, v_y_2024_, v___x_2030_);
lean_dec(v___x_2033_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_fvarId_2035_; lean_object* v___x_2036_; 
v_fvarId_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_fvarId_2035_);
lean_dec_ref_known(v___x_2034_, 1);
v___x_2036_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1773_, v_k_2025_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2047_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2047_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2047_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 3, v_a_2037_);
lean_ctor_set(v___x_2027_, 2, v_fvarId_2035_);
lean_ctor_set(v___x_2027_, 0, v_fvarId_2032_);
v___x_2042_ = v___x_2027_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_fvarId_2032_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_i_2023_);
lean_ctor_set(v_reuseFailAlloc_2046_, 2, v_fvarId_2035_);
lean_ctor_set(v_reuseFailAlloc_2046_, 3, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2044_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2042_);
v___x_2044_ = v___x_2039_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
else
{
lean_dec(v_fvarId_2035_);
lean_dec(v_fvarId_2032_);
lean_del_object(v___x_2027_);
lean_dec(v_i_2023_);
return v___x_2036_;
}
}
else
{
lean_object* v___x_2048_; 
lean_dec(v_fvarId_2032_);
lean_del_object(v___x_2027_);
lean_dec_ref(v_k_2025_);
lean_dec(v_i_2023_);
v___x_2048_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1773_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
return v___x_2048_;
}
}
else
{
lean_object* v___x_2049_; 
lean_del_object(v___x_2027_);
lean_dec_ref(v_k_2025_);
lean_dec(v_y_2024_);
lean_dec(v_i_2023_);
v___x_2049_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1773_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
return v___x_2049_;
}
}
}
case 9:
{
lean_object* v_fvarId_2051_; lean_object* v_i_2052_; lean_object* v_offset_2053_; lean_object* v_y_2054_; lean_object* v_ty_2055_; lean_object* v_k_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2091_; 
v_fvarId_2051_ = lean_ctor_get(v_code_1774_, 0);
v_i_2052_ = lean_ctor_get(v_code_1774_, 1);
v_offset_2053_ = lean_ctor_get(v_code_1774_, 2);
v_y_2054_ = lean_ctor_get(v_code_1774_, 3);
v_ty_2055_ = lean_ctor_get(v_code_1774_, 4);
v_k_2056_ = lean_ctor_get(v_code_1774_, 5);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_code_1774_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2058_ = v_code_1774_;
v_isShared_2059_ = v_isSharedCheck_2091_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_k_2056_);
lean_inc(v_ty_2055_);
lean_inc(v_y_2054_);
lean_inc(v_offset_2053_);
lean_inc(v_i_2052_);
lean_inc(v_fvarId_2051_);
lean_dec(v_code_1774_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2091_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; uint8_t v___x_2061_; lean_object* v___x_2062_; 
v___x_2060_ = lean_st_ref_get(v_a_1776_);
v___x_2061_ = 1;
v___x_2062_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2060_, v_fvarId_2051_, v___x_2061_);
lean_dec(v___x_2060_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_fvarId_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v_fvarId_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_fvarId_2063_);
lean_dec_ref_known(v___x_2062_, 1);
v___x_2064_ = lean_st_ref_get(v_a_1776_);
v___x_2065_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2064_, v_y_2054_, v___x_2061_);
lean_dec(v___x_2064_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_fvarId_2066_; lean_object* v___x_2067_; 
v_fvarId_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_fvarId_2066_);
lean_dec_ref_known(v___x_2065_, 1);
v___x_2067_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1773_, v_ty_2055_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2069_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref_known(v___x_2067_, 1);
v___x_2069_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1773_, v_k_2056_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2080_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2072_ = v___x_2069_;
v_isShared_2073_ = v_isSharedCheck_2080_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2080_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 5, v_a_2070_);
lean_ctor_set(v___x_2058_, 4, v_a_2068_);
lean_ctor_set(v___x_2058_, 3, v_fvarId_2066_);
lean_ctor_set(v___x_2058_, 0, v_fvarId_2063_);
v___x_2075_ = v___x_2058_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_fvarId_2063_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_i_2052_);
lean_ctor_set(v_reuseFailAlloc_2079_, 2, v_offset_2053_);
lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_fvarId_2066_);
lean_ctor_set(v_reuseFailAlloc_2079_, 4, v_a_2068_);
lean_ctor_set(v_reuseFailAlloc_2079_, 5, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2077_; 
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v___x_2075_);
v___x_2077_ = v___x_2072_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
else
{
lean_dec(v_a_2068_);
lean_dec(v_fvarId_2066_);
lean_dec(v_fvarId_2063_);
lean_del_object(v___x_2058_);
lean_dec(v_offset_2053_);
lean_dec(v_i_2052_);
return v___x_2069_;
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec(v_fvarId_2066_);
lean_dec(v_fvarId_2063_);
lean_del_object(v___x_2058_);
lean_dec_ref(v_k_2056_);
lean_dec(v_offset_2053_);
lean_dec(v_i_2052_);
v_a_2081_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2067_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2067_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v___x_2089_; 
lean_dec(v_fvarId_2063_);
lean_del_object(v___x_2058_);
lean_dec_ref(v_k_2056_);
lean_dec_ref(v_ty_2055_);
lean_dec(v_offset_2053_);
lean_dec(v_i_2052_);
v___x_2089_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1773_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
return v___x_2089_;
}
}
else
{
lean_object* v___x_2090_; 
lean_del_object(v___x_2058_);
lean_dec_ref(v_k_2056_);
lean_dec_ref(v_ty_2055_);
lean_dec(v_y_2054_);
lean_dec(v_offset_2053_);
lean_dec(v_i_2052_);
v___x_2090_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1773_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
return v___x_2090_;
}
}
}
case 10:
{
lean_object* v_fvarId_2092_; lean_object* v_cidx_2093_; lean_object* v_k_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2115_; 
v_fvarId_2092_ = lean_ctor_get(v_code_1774_, 0);
v_cidx_2093_ = lean_ctor_get(v_code_1774_, 1);
v_k_2094_ = lean_ctor_get(v_code_1774_, 2);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_code_1774_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2096_ = v_code_1774_;
v_isShared_2097_ = v_isSharedCheck_2115_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_k_2094_);
lean_inc(v_cidx_2093_);
lean_inc(v_fvarId_2092_);
lean_dec(v_code_1774_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2115_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; uint8_t v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = lean_st_ref_get(v_a_1776_);
v___x_2099_ = 1;
v___x_2100_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2098_, v_fvarId_2092_, v___x_2099_);
lean_dec(v___x_2098_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_fvarId_2101_; lean_object* v___x_2102_; 
v_fvarId_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_fvarId_2101_);
lean_dec_ref_known(v___x_2100_, 1);
v___x_2102_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1773_, v_k_2094_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
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
lean_ctor_set(v___x_2096_, 2, v_a_2103_);
lean_ctor_set(v___x_2096_, 0, v_fvarId_2101_);
v___x_2108_ = v___x_2096_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_fvarId_2101_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_cidx_2093_);
lean_ctor_set(v_reuseFailAlloc_2112_, 2, v_a_2103_);
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
lean_dec(v_cidx_2093_);
return v___x_2102_;
}
}
else
{
lean_object* v___x_2114_; 
lean_del_object(v___x_2096_);
lean_dec_ref(v_k_2094_);
lean_dec(v_cidx_2093_);
v___x_2114_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1773_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
return v___x_2114_;
}
}
}
case 11:
{
lean_object* v_fvarId_2116_; lean_object* v_n_2117_; uint8_t v_check_2118_; uint8_t v_persistent_2119_; lean_object* v_k_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2141_; 
v_fvarId_2116_ = lean_ctor_get(v_code_1774_, 0);
v_n_2117_ = lean_ctor_get(v_code_1774_, 1);
v_check_2118_ = lean_ctor_get_uint8(v_code_1774_, sizeof(void*)*3);
v_persistent_2119_ = lean_ctor_get_uint8(v_code_1774_, sizeof(void*)*3 + 1);
v_k_2120_ = lean_ctor_get(v_code_1774_, 2);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_code_1774_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2122_ = v_code_1774_;
v_isShared_2123_ = v_isSharedCheck_2141_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_k_2120_);
lean_inc(v_n_2117_);
lean_inc(v_fvarId_2116_);
lean_dec(v_code_1774_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2141_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; uint8_t v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = lean_st_ref_get(v_a_1776_);
v___x_2125_ = 1;
v___x_2126_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2124_, v_fvarId_2116_, v___x_2125_);
lean_dec(v___x_2124_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_fvarId_2127_; lean_object* v___x_2128_; 
v_fvarId_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_fvarId_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v___x_2128_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1773_, v_k_2120_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2139_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2131_ = v___x_2128_;
v_isShared_2132_ = v_isSharedCheck_2139_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2128_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2139_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 2, v_a_2129_);
lean_ctor_set(v___x_2122_, 0, v_fvarId_2127_);
v___x_2134_ = v___x_2122_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_fvarId_2127_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_n_2117_);
lean_ctor_set(v_reuseFailAlloc_2138_, 2, v_a_2129_);
lean_ctor_set_uint8(v_reuseFailAlloc_2138_, sizeof(void*)*3, v_check_2118_);
lean_ctor_set_uint8(v_reuseFailAlloc_2138_, sizeof(void*)*3 + 1, v_persistent_2119_);
v___x_2134_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2136_; 
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v___x_2134_);
v___x_2136_ = v___x_2131_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
else
{
lean_dec(v_fvarId_2127_);
lean_del_object(v___x_2122_);
lean_dec(v_n_2117_);
return v___x_2128_;
}
}
else
{
lean_object* v___x_2140_; 
lean_del_object(v___x_2122_);
lean_dec_ref(v_k_2120_);
lean_dec(v_n_2117_);
v___x_2140_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1773_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
return v___x_2140_;
}
}
}
case 12:
{
lean_object* v_fvarId_2142_; lean_object* v_n_2143_; uint8_t v_check_2144_; uint8_t v_persistent_2145_; lean_object* v_objs_x3f_2146_; lean_object* v_k_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2168_; 
v_fvarId_2142_ = lean_ctor_get(v_code_1774_, 0);
v_n_2143_ = lean_ctor_get(v_code_1774_, 1);
v_check_2144_ = lean_ctor_get_uint8(v_code_1774_, sizeof(void*)*4);
v_persistent_2145_ = lean_ctor_get_uint8(v_code_1774_, sizeof(void*)*4 + 1);
v_objs_x3f_2146_ = lean_ctor_get(v_code_1774_, 2);
v_k_2147_ = lean_ctor_get(v_code_1774_, 3);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_code_1774_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2149_ = v_code_1774_;
v_isShared_2150_ = v_isSharedCheck_2168_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_k_2147_);
lean_inc(v_objs_x3f_2146_);
lean_inc(v_n_2143_);
lean_inc(v_fvarId_2142_);
lean_dec(v_code_1774_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2168_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2151_; uint8_t v___x_2152_; lean_object* v___x_2153_; 
v___x_2151_ = lean_st_ref_get(v_a_1776_);
v___x_2152_ = 1;
v___x_2153_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2151_, v_fvarId_2142_, v___x_2152_);
lean_dec(v___x_2151_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_fvarId_2154_; lean_object* v___x_2155_; 
v_fvarId_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_fvarId_2154_);
lean_dec_ref_known(v___x_2153_, 1);
v___x_2155_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1773_, v_k_2147_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2166_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2158_ = v___x_2155_;
v_isShared_2159_ = v_isSharedCheck_2166_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2155_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2166_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 3, v_a_2156_);
lean_ctor_set(v___x_2149_, 0, v_fvarId_2154_);
v___x_2161_ = v___x_2149_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_fvarId_2154_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_n_2143_);
lean_ctor_set(v_reuseFailAlloc_2165_, 2, v_objs_x3f_2146_);
lean_ctor_set(v_reuseFailAlloc_2165_, 3, v_a_2156_);
lean_ctor_set_uint8(v_reuseFailAlloc_2165_, sizeof(void*)*4, v_check_2144_);
lean_ctor_set_uint8(v_reuseFailAlloc_2165_, sizeof(void*)*4 + 1, v_persistent_2145_);
v___x_2161_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
lean_object* v___x_2163_; 
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2161_);
v___x_2163_ = v___x_2158_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
else
{
lean_dec(v_fvarId_2154_);
lean_del_object(v___x_2149_);
lean_dec(v_objs_x3f_2146_);
lean_dec(v_n_2143_);
return v___x_2155_;
}
}
else
{
lean_object* v___x_2167_; 
lean_del_object(v___x_2149_);
lean_dec_ref(v_k_2147_);
lean_dec(v_objs_x3f_2146_);
lean_dec(v_n_2143_);
v___x_2167_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1773_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
return v___x_2167_;
}
}
}
default: 
{
lean_object* v_fvarId_2169_; lean_object* v_k_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2191_; 
v_fvarId_2169_ = lean_ctor_get(v_code_1774_, 0);
v_k_2170_ = lean_ctor_get(v_code_1774_, 1);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_code_1774_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2172_ = v_code_1774_;
v_isShared_2173_ = v_isSharedCheck_2191_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_k_2170_);
lean_inc(v_fvarId_2169_);
lean_dec(v_code_1774_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2191_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2174_; uint8_t v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = lean_st_ref_get(v_a_1776_);
v___x_2175_ = 1;
v___x_2176_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2174_, v_fvarId_2169_, v___x_2175_);
lean_dec(v___x_2174_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_fvarId_2177_; lean_object* v___x_2178_; 
v_fvarId_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_fvarId_2177_);
lean_dec_ref_known(v___x_2176_, 1);
v___x_2178_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1773_, v_k_2170_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2189_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2189_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2189_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 1, v_a_2179_);
lean_ctor_set(v___x_2172_, 0, v_fvarId_2177_);
v___x_2184_ = v___x_2172_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_fvarId_2177_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2186_; 
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2184_);
v___x_2186_ = v___x_2181_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
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
lean_dec(v_fvarId_2177_);
lean_del_object(v___x_2172_);
return v___x_2178_;
}
}
else
{
lean_object* v___x_2190_; 
lean_del_object(v___x_2172_);
lean_dec_ref(v_k_2170_);
v___x_2190_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1773_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
return v___x_2190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(uint8_t v_pu_2192_, lean_object* v_decl_2193_, uint8_t v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v_fvarId_2201_; lean_object* v_binderName_2202_; lean_object* v_params_2203_; lean_object* v_type_2204_; lean_object* v_value_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2283_; 
v_fvarId_2201_ = lean_ctor_get(v_decl_2193_, 0);
v_binderName_2202_ = lean_ctor_get(v_decl_2193_, 1);
v_params_2203_ = lean_ctor_get(v_decl_2193_, 2);
v_type_2204_ = lean_ctor_get(v_decl_2193_, 3);
v_value_2205_ = lean_ctor_get(v_decl_2193_, 4);
v_isSharedCheck_2283_ = !lean_is_exclusive(v_decl_2193_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2207_ = v_decl_2193_;
v_isShared_2208_ = v_isSharedCheck_2283_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_value_2205_);
lean_inc(v_type_2204_);
lean_inc(v_params_2203_);
lean_inc(v_binderName_2202_);
lean_inc(v_fvarId_2201_);
lean_dec(v_decl_2193_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2283_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; 
v___x_2209_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2192_, v_type_2204_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2211_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref_known(v___x_2209_, 1);
v___x_2211_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_2202_, v_a_2194_, v_a_2197_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; size_t v_sz_2213_; size_t v___x_2214_; lean_object* v___x_2215_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_a_2212_);
lean_dec_ref_known(v___x_2211_, 1);
v_sz_2213_ = lean_array_size(v_params_2203_);
v___x_2214_ = ((size_t)0ULL);
v___x_2215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2192_, v_sz_2213_, v___x_2214_, v_params_2203_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2217_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
v___x_2217_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2192_, v_value_2205_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2219_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
v___x_2219_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_2201_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2242_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2222_ = v___x_2219_;
v_isShared_2223_ = v_isSharedCheck_2242_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2219_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2242_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v_lctx_2225_; lean_object* v_nextIdx_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2241_; 
v___x_2224_ = lean_st_ref_take(v_a_2197_);
v_lctx_2225_ = lean_ctor_get(v___x_2224_, 0);
v_nextIdx_2226_ = lean_ctor_get(v___x_2224_, 1);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2228_ = v___x_2224_;
v_isShared_2229_ = v_isSharedCheck_2241_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_nextIdx_2226_);
lean_inc(v_lctx_2225_);
lean_dec(v___x_2224_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2241_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 4, v_a_2218_);
lean_ctor_set(v___x_2207_, 3, v_a_2210_);
lean_ctor_set(v___x_2207_, 2, v_a_2216_);
lean_ctor_set(v___x_2207_, 1, v_a_2212_);
lean_ctor_set(v___x_2207_, 0, v_a_2220_);
v___x_2231_ = v___x_2207_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2220_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_a_2212_);
lean_ctor_set(v_reuseFailAlloc_2240_, 2, v_a_2216_);
lean_ctor_set(v_reuseFailAlloc_2240_, 3, v_a_2210_);
lean_ctor_set(v_reuseFailAlloc_2240_, 4, v_a_2218_);
v___x_2231_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2232_; lean_object* v___x_2234_; 
lean_inc_ref(v___x_2231_);
v___x_2232_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2192_, v_lctx_2225_, v___x_2231_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v___x_2232_);
v___x_2234_ = v___x_2228_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v_nextIdx_2226_);
v___x_2234_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
lean_object* v___x_2235_; lean_object* v___x_2237_; 
v___x_2235_ = lean_st_ref_put(v_a_2197_, v___x_2234_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v___x_2231_);
v___x_2237_ = v___x_2222_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2231_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec(v_a_2218_);
lean_dec(v_a_2216_);
lean_dec(v_a_2212_);
lean_dec(v_a_2210_);
lean_del_object(v___x_2207_);
v_a_2243_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2219_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2219_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec(v_a_2216_);
lean_dec(v_a_2212_);
lean_dec(v_a_2210_);
lean_del_object(v___x_2207_);
lean_dec(v_fvarId_2201_);
v_a_2251_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2217_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2217_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v_a_2212_);
lean_dec(v_a_2210_);
lean_del_object(v___x_2207_);
lean_dec_ref(v_value_2205_);
lean_dec(v_fvarId_2201_);
v_a_2259_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2215_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2215_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec(v_a_2210_);
lean_del_object(v___x_2207_);
lean_dec_ref(v_value_2205_);
lean_dec_ref(v_params_2203_);
lean_dec(v_fvarId_2201_);
v_a_2267_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2211_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2211_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
lean_del_object(v___x_2207_);
lean_dec_ref(v_value_2205_);
lean_dec_ref(v_params_2203_);
lean_dec(v_binderName_2202_);
lean_dec(v_fvarId_2201_);
v_a_2275_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2209_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2209_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(lean_object* v_pu_2284_, lean_object* v_decl_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_){
_start:
{
uint8_t v_pu_boxed_2293_; uint8_t v_a_boxed_2294_; lean_object* v_res_2295_; 
v_pu_boxed_2293_ = lean_unbox(v_pu_2284_);
v_a_boxed_2294_ = lean_unbox(v_a_2286_);
v_res_2295_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_boxed_2293_, v_decl_2285_, v_a_boxed_2294_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
lean_dec(v_a_2287_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2___boxed(lean_object* v_pu_2296_, lean_object* v_sz_2297_, lean_object* v_i_2298_, lean_object* v_bs_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
uint8_t v_pu_boxed_2307_; size_t v_sz_boxed_2308_; size_t v_i_boxed_2309_; uint8_t v___y_26956__boxed_2310_; lean_object* v_res_2311_; 
v_pu_boxed_2307_ = lean_unbox(v_pu_2296_);
v_sz_boxed_2308_ = lean_unbox_usize(v_sz_2297_);
lean_dec(v_sz_2297_);
v_i_boxed_2309_ = lean_unbox_usize(v_i_2298_);
lean_dec(v_i_2298_);
v___y_26956__boxed_2310_ = lean_unbox(v___y_2300_);
v_res_2311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_boxed_2307_, v_sz_boxed_2308_, v_i_boxed_2309_, v_bs_2299_, v___y_26956__boxed_2310_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(lean_object* v_pu_2312_, lean_object* v_code_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_){
_start:
{
uint8_t v_pu_boxed_2321_; uint8_t v_a_boxed_2322_; lean_object* v_res_2323_; 
v_pu_boxed_2321_ = lean_unbox(v_pu_2312_);
v_a_boxed_2322_ = lean_unbox(v_a_2314_);
v_res_2323_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_boxed_2321_, v_code_2313_, v_a_boxed_2322_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
lean_dec(v_a_2319_);
lean_dec_ref(v_a_2318_);
lean_dec(v_a_2317_);
lean_dec_ref(v_a_2316_);
lean_dec(v_a_2315_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(uint8_t v_pu_2324_, lean_object* v_msg_2325_, uint8_t v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v_toApplicative_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2399_; 
v___x_2333_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
v___x_2334_ = l_StateRefT_x27_instMonad___redArg(v___x_2333_);
v_toApplicative_2335_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2399_ == 0)
{
lean_object* v_unused_2400_; 
v_unused_2400_ = lean_ctor_get(v___x_2334_, 1);
lean_dec(v_unused_2400_);
v___x_2337_ = v___x_2334_;
v_isShared_2338_ = v_isSharedCheck_2399_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_toApplicative_2335_);
lean_dec(v___x_2334_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2399_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v_toFunctor_2339_; lean_object* v_toSeq_2340_; lean_object* v_toSeqLeft_2341_; lean_object* v_toSeqRight_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2397_; 
v_toFunctor_2339_ = lean_ctor_get(v_toApplicative_2335_, 0);
v_toSeq_2340_ = lean_ctor_get(v_toApplicative_2335_, 2);
v_toSeqLeft_2341_ = lean_ctor_get(v_toApplicative_2335_, 3);
v_toSeqRight_2342_ = lean_ctor_get(v_toApplicative_2335_, 4);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_toApplicative_2335_);
if (v_isSharedCheck_2397_ == 0)
{
lean_object* v_unused_2398_; 
v_unused_2398_ = lean_ctor_get(v_toApplicative_2335_, 1);
lean_dec(v_unused_2398_);
v___x_2344_ = v_toApplicative_2335_;
v_isShared_2345_ = v_isSharedCheck_2397_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_toSeqRight_2342_);
lean_inc(v_toSeqLeft_2341_);
lean_inc(v_toSeq_2340_);
lean_inc(v_toFunctor_2339_);
lean_dec(v_toApplicative_2335_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2397_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___f_2346_; lean_object* v___f_2347_; lean_object* v___f_2348_; lean_object* v___f_2349_; lean_object* v___x_2350_; lean_object* v___f_2351_; lean_object* v___f_2352_; lean_object* v___f_2353_; lean_object* v___x_2355_; 
v___f_2346_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
v___f_2347_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_2339_);
v___f_2348_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2348_, 0, v_toFunctor_2339_);
v___f_2349_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2349_, 0, v_toFunctor_2339_);
v___x_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___f_2348_);
lean_ctor_set(v___x_2350_, 1, v___f_2349_);
v___f_2351_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2351_, 0, v_toSeqRight_2342_);
v___f_2352_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2352_, 0, v_toSeqLeft_2341_);
v___f_2353_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2353_, 0, v_toSeq_2340_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 4, v___f_2351_);
lean_ctor_set(v___x_2344_, 3, v___f_2352_);
lean_ctor_set(v___x_2344_, 2, v___f_2353_);
lean_ctor_set(v___x_2344_, 1, v___f_2346_);
lean_ctor_set(v___x_2344_, 0, v___x_2350_);
v___x_2355_ = v___x_2344_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v___f_2346_);
lean_ctor_set(v_reuseFailAlloc_2396_, 2, v___f_2353_);
lean_ctor_set(v_reuseFailAlloc_2396_, 3, v___f_2352_);
lean_ctor_set(v_reuseFailAlloc_2396_, 4, v___f_2351_);
v___x_2355_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2357_; 
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 1, v___f_2347_);
lean_ctor_set(v___x_2337_, 0, v___x_2355_);
v___x_2357_ = v___x_2337_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2355_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v___f_2347_);
v___x_2357_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2358_; lean_object* v_toApplicative_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2393_; 
v___x_2358_ = l_StateRefT_x27_instMonad___redArg(v___x_2357_);
v_toApplicative_2359_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2393_ == 0)
{
lean_object* v_unused_2394_; 
v_unused_2394_ = lean_ctor_get(v___x_2358_, 1);
lean_dec(v_unused_2394_);
v___x_2361_ = v___x_2358_;
v_isShared_2362_ = v_isSharedCheck_2393_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_toApplicative_2359_);
lean_dec(v___x_2358_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2393_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v_toFunctor_2363_; lean_object* v_toSeq_2364_; lean_object* v_toSeqLeft_2365_; lean_object* v_toSeqRight_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2391_; 
v_toFunctor_2363_ = lean_ctor_get(v_toApplicative_2359_, 0);
v_toSeq_2364_ = lean_ctor_get(v_toApplicative_2359_, 2);
v_toSeqLeft_2365_ = lean_ctor_get(v_toApplicative_2359_, 3);
v_toSeqRight_2366_ = lean_ctor_get(v_toApplicative_2359_, 4);
v_isSharedCheck_2391_ = !lean_is_exclusive(v_toApplicative_2359_);
if (v_isSharedCheck_2391_ == 0)
{
lean_object* v_unused_2392_; 
v_unused_2392_ = lean_ctor_get(v_toApplicative_2359_, 1);
lean_dec(v_unused_2392_);
v___x_2368_ = v_toApplicative_2359_;
v_isShared_2369_ = v_isSharedCheck_2391_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_toSeqRight_2366_);
lean_inc(v_toSeqLeft_2365_);
lean_inc(v_toSeq_2364_);
lean_inc(v_toFunctor_2363_);
lean_dec(v_toApplicative_2359_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2391_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___f_2370_; lean_object* v___f_2371_; lean_object* v___f_2372_; lean_object* v___f_2373_; lean_object* v___x_2374_; lean_object* v___f_2375_; lean_object* v___f_2376_; lean_object* v___f_2377_; lean_object* v___x_2379_; 
v___f_2370_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
v___f_2371_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(v_toFunctor_2363_);
v___f_2372_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2372_, 0, v_toFunctor_2363_);
v___f_2373_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2373_, 0, v_toFunctor_2363_);
v___x_2374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___f_2372_);
lean_ctor_set(v___x_2374_, 1, v___f_2373_);
v___f_2375_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2375_, 0, v_toSeqRight_2366_);
v___f_2376_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2376_, 0, v_toSeqLeft_2365_);
v___f_2377_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2377_, 0, v_toSeq_2364_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 4, v___f_2375_);
lean_ctor_set(v___x_2368_, 3, v___f_2376_);
lean_ctor_set(v___x_2368_, 2, v___f_2377_);
lean_ctor_set(v___x_2368_, 1, v___f_2370_);
lean_ctor_set(v___x_2368_, 0, v___x_2374_);
v___x_2379_ = v___x_2368_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v___f_2370_);
lean_ctor_set(v_reuseFailAlloc_2390_, 2, v___f_2377_);
lean_ctor_set(v_reuseFailAlloc_2390_, 3, v___f_2376_);
lean_ctor_set(v_reuseFailAlloc_2390_, 4, v___f_2375_);
v___x_2379_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2381_; 
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 1, v___f_2371_);
lean_ctor_set(v___x_2361_, 0, v___x_2379_);
v___x_2381_ = v___x_2361_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2379_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v___f_2371_);
v___x_2381_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___f_2385_; lean_object* v___x_11427__overap_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2382_ = l_StateRefT_x27_instMonad___redArg(v___x_2381_);
v___x_2383_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v_pu_2324_);
v___x_2384_ = l_instInhabitedOfMonad___redArg(v___x_2382_, v___x_2383_);
v___f_2385_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2385_, 0, v___x_2384_);
v___x_11427__overap_2386_ = lean_panic_fn_borrowed(v___f_2385_, v_msg_2325_);
lean_dec_ref(v___f_2385_);
v___x_2387_ = lean_box(v___y_2326_);
lean_inc(v___y_2331_);
lean_inc_ref(v___y_2330_);
lean_inc(v___y_2329_);
lean_inc_ref(v___y_2328_);
lean_inc(v___y_2327_);
v___x_2388_ = lean_apply_7(v___x_11427__overap_2386_, v___x_2387_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, lean_box(0));
return v___x_2388_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___boxed(lean_object* v_pu_2401_, lean_object* v_msg_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
uint8_t v_pu_boxed_2410_; uint8_t v___y_11458__boxed_2411_; lean_object* v_res_2412_; 
v_pu_boxed_2410_ = lean_unbox(v_pu_2401_);
v___y_11458__boxed_2411_ = lean_unbox(v___y_2403_);
v_res_2412_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_boxed_2410_, v_msg_2402_, v___y_11458__boxed_2411_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
return v_res_2412_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1(void){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2414_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2415_ = lean_unsigned_to_nat(41u);
v___x_2416_ = lean_unsigned_to_nat(217u);
v___x_2417_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2418_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2419_ = l_mkPanicMessageWithDecl(v___x_2418_, v___x_2417_, v___x_2416_, v___x_2415_, v___x_2414_);
return v___x_2419_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2(void){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2420_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2421_ = lean_unsigned_to_nat(31u);
v___x_2422_ = lean_unsigned_to_nat(222u);
v___x_2423_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2424_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2425_ = l_mkPanicMessageWithDecl(v___x_2424_, v___x_2423_, v___x_2422_, v___x_2421_, v___x_2420_);
return v___x_2425_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3(void){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2426_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2427_ = lean_unsigned_to_nat(41u);
v___x_2428_ = lean_unsigned_to_nat(221u);
v___x_2429_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2430_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2431_ = l_mkPanicMessageWithDecl(v___x_2430_, v___x_2429_, v___x_2428_, v___x_2427_, v___x_2426_);
return v___x_2431_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4(void){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2432_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2433_ = lean_unsigned_to_nat(31u);
v___x_2434_ = lean_unsigned_to_nat(226u);
v___x_2435_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2436_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2437_ = l_mkPanicMessageWithDecl(v___x_2436_, v___x_2435_, v___x_2434_, v___x_2433_, v___x_2432_);
return v___x_2437_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5(void){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2438_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2439_ = lean_unsigned_to_nat(41u);
v___x_2440_ = lean_unsigned_to_nat(225u);
v___x_2441_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2442_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2443_ = l_mkPanicMessageWithDecl(v___x_2442_, v___x_2441_, v___x_2440_, v___x_2439_, v___x_2438_);
return v___x_2443_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2444_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2445_ = lean_unsigned_to_nat(41u);
v___x_2446_ = lean_unsigned_to_nat(230u);
v___x_2447_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2448_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2449_ = l_mkPanicMessageWithDecl(v___x_2448_, v___x_2447_, v___x_2446_, v___x_2445_, v___x_2444_);
return v___x_2449_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7(void){
_start:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2450_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2451_ = lean_unsigned_to_nat(41u);
v___x_2452_ = lean_unsigned_to_nat(233u);
v___x_2453_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2454_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2455_ = l_mkPanicMessageWithDecl(v___x_2454_, v___x_2453_, v___x_2452_, v___x_2451_, v___x_2450_);
return v___x_2455_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2456_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2457_ = lean_unsigned_to_nat(41u);
v___x_2458_ = lean_unsigned_to_nat(236u);
v___x_2459_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2460_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2461_ = l_mkPanicMessageWithDecl(v___x_2460_, v___x_2459_, v___x_2458_, v___x_2457_, v___x_2456_);
return v___x_2461_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9(void){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2462_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2463_ = lean_unsigned_to_nat(41u);
v___x_2464_ = lean_unsigned_to_nat(239u);
v___x_2465_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2466_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2467_ = l_mkPanicMessageWithDecl(v___x_2466_, v___x_2465_, v___x_2464_, v___x_2463_, v___x_2462_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t v_pu_2468_, lean_object* v_decl_2469_, uint8_t v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
switch(lean_obj_tag(v_decl_2469_))
{
case 0:
{
lean_object* v_decl_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2501_; 
v_decl_2477_ = lean_ctor_get(v_decl_2469_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v_decl_2469_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2479_ = v_decl_2469_;
v_isShared_2480_ = v_isSharedCheck_2501_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_decl_2477_);
lean_dec(v_decl_2469_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2501_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_2468_, v_decl_2477_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
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
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 0);
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
case 1:
{
lean_object* v_decl_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2526_; 
v_decl_2502_ = lean_ctor_get(v_decl_2469_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v_decl_2469_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2504_ = v_decl_2469_;
v_isShared_2505_ = v_isSharedCheck_2526_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_decl_2502_);
lean_dec(v_decl_2469_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2526_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; 
v___x_2506_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2468_, v_decl_2502_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2517_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2509_ = v___x_2506_;
v_isShared_2510_ = v_isSharedCheck_2517_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2506_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2517_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 0, v_a_2507_);
v___x_2512_ = v___x_2504_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2507_);
v___x_2512_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
lean_object* v___x_2514_; 
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 0, v___x_2512_);
v___x_2514_ = v___x_2509_;
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
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_del_object(v___x_2504_);
v_a_2518_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2506_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2506_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
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
}
case 2:
{
lean_object* v_decl_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2551_; 
v_decl_2527_ = lean_ctor_get(v_decl_2469_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_decl_2469_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2529_ = v_decl_2469_;
v_isShared_2530_ = v_isSharedCheck_2551_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_decl_2527_);
lean_dec(v_decl_2469_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2551_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2468_, v_decl_2527_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2542_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2542_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2542_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 0, v_a_2532_);
v___x_2537_ = v___x_2529_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2539_; 
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v___x_2537_);
v___x_2539_ = v___x_2534_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_del_object(v___x_2529_);
v_a_2543_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2531_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2531_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
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
}
case 3:
{
lean_object* v_fvarId_2552_; lean_object* v_i_2553_; lean_object* v_y_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2576_; 
v_fvarId_2552_ = lean_ctor_get(v_decl_2469_, 0);
v_i_2553_ = lean_ctor_get(v_decl_2469_, 1);
v_y_2554_ = lean_ctor_get(v_decl_2469_, 2);
v_isSharedCheck_2576_ = !lean_is_exclusive(v_decl_2469_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2556_ = v_decl_2469_;
v_isShared_2557_ = v_isSharedCheck_2576_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_y_2554_);
lean_inc(v_i_2553_);
lean_inc(v_fvarId_2552_);
lean_dec(v_decl_2469_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2576_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2558_; uint8_t v___x_2559_; lean_object* v___x_2560_; 
v___x_2558_ = lean_st_ref_get(v_a_2471_);
v___x_2559_ = 1;
v___x_2560_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2558_, v_fvarId_2552_, v___x_2559_);
lean_dec(v___x_2558_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_fvarId_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2573_; 
v_fvarId_2561_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2563_ = v___x_2560_;
v_isShared_2564_ = v_isSharedCheck_2573_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_fvarId_2561_);
lean_dec(v___x_2560_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2573_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2568_; 
v___x_2565_ = lean_st_ref_get(v_a_2471_);
v___x_2566_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2468_, v___x_2565_, v_y_2554_, v___x_2559_);
lean_dec(v___x_2565_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 2, v___x_2566_);
lean_ctor_set(v___x_2556_, 0, v_fvarId_2561_);
v___x_2568_ = v___x_2556_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_fvarId_2561_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v_i_2553_);
lean_ctor_set(v_reuseFailAlloc_2572_, 2, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
lean_object* v___x_2570_; 
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 0, v___x_2568_);
v___x_2570_ = v___x_2563_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2568_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
else
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
lean_dec(v___x_2560_);
lean_del_object(v___x_2556_);
lean_dec(v_y_2554_);
lean_dec(v_i_2553_);
v___x_2574_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1);
v___x_2575_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2468_, v___x_2574_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
return v___x_2575_;
}
}
}
case 4:
{
lean_object* v_fvarId_2577_; lean_object* v_i_2578_; lean_object* v_y_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2604_; 
v_fvarId_2577_ = lean_ctor_get(v_decl_2469_, 0);
v_i_2578_ = lean_ctor_get(v_decl_2469_, 1);
v_y_2579_ = lean_ctor_get(v_decl_2469_, 2);
v_isSharedCheck_2604_ = !lean_is_exclusive(v_decl_2469_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2581_ = v_decl_2469_;
v_isShared_2582_ = v_isSharedCheck_2604_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_y_2579_);
lean_inc(v_i_2578_);
lean_inc(v_fvarId_2577_);
lean_dec(v_decl_2469_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2604_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; uint8_t v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = lean_st_ref_get(v_a_2471_);
v___x_2584_ = 1;
v___x_2585_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2583_, v_fvarId_2577_, v___x_2584_);
lean_dec(v___x_2583_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_fvarId_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v_fvarId_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_fvarId_2586_);
lean_dec_ref_known(v___x_2585_, 1);
v___x_2587_ = lean_st_ref_get(v_a_2471_);
v___x_2588_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2587_, v_y_2579_, v___x_2584_);
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
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 2, v_fvarId_2589_);
lean_ctor_set(v___x_2581_, 0, v_fvarId_2586_);
v___x_2594_ = v___x_2581_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_fvarId_2586_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_i_2578_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_fvarId_2589_);
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
lean_dec(v_fvarId_2586_);
lean_del_object(v___x_2581_);
lean_dec(v_i_2578_);
v___x_2600_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2);
v___x_2601_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2468_, v___x_2600_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
return v___x_2601_;
}
}
else
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
lean_dec(v___x_2585_);
lean_del_object(v___x_2581_);
lean_dec(v_y_2579_);
lean_dec(v_i_2578_);
v___x_2602_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3);
v___x_2603_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2468_, v___x_2602_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
return v___x_2603_;
}
}
}
case 5:
{
lean_object* v_fvarId_2605_; lean_object* v_i_2606_; lean_object* v_offset_2607_; lean_object* v_y_2608_; lean_object* v_ty_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2636_; 
v_fvarId_2605_ = lean_ctor_get(v_decl_2469_, 0);
v_i_2606_ = lean_ctor_get(v_decl_2469_, 1);
v_offset_2607_ = lean_ctor_get(v_decl_2469_, 2);
v_y_2608_ = lean_ctor_get(v_decl_2469_, 3);
v_ty_2609_ = lean_ctor_get(v_decl_2469_, 4);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_decl_2469_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2611_ = v_decl_2469_;
v_isShared_2612_ = v_isSharedCheck_2636_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_ty_2609_);
lean_inc(v_y_2608_);
lean_inc(v_offset_2607_);
lean_inc(v_i_2606_);
lean_inc(v_fvarId_2605_);
lean_dec(v_decl_2469_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2636_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2613_; uint8_t v___x_2614_; lean_object* v___x_2615_; 
v___x_2613_ = lean_st_ref_get(v_a_2471_);
v___x_2614_ = 1;
v___x_2615_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2613_, v_fvarId_2605_, v___x_2614_);
lean_dec(v___x_2613_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_fvarId_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v_fvarId_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_fvarId_2616_);
lean_dec_ref_known(v___x_2615_, 1);
v___x_2617_ = lean_st_ref_get(v_a_2471_);
v___x_2618_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2617_, v_y_2608_, v___x_2614_);
lean_dec(v___x_2617_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_fvarId_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2631_; 
v_fvarId_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2631_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_fvarId_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2631_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2623_ = lean_st_ref_get(v_a_2471_);
v___x_2624_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2468_, v___x_2623_, v___x_2614_, v_ty_2609_);
lean_dec(v___x_2623_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 4, v___x_2624_);
lean_ctor_set(v___x_2611_, 3, v_fvarId_2619_);
lean_ctor_set(v___x_2611_, 0, v_fvarId_2616_);
v___x_2626_ = v___x_2611_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_fvarId_2616_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_i_2606_);
lean_ctor_set(v_reuseFailAlloc_2630_, 2, v_offset_2607_);
lean_ctor_set(v_reuseFailAlloc_2630_, 3, v_fvarId_2619_);
lean_ctor_set(v_reuseFailAlloc_2630_, 4, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
lean_object* v___x_2628_; 
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2626_);
v___x_2628_ = v___x_2621_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
else
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
lean_dec(v___x_2618_);
lean_dec(v_fvarId_2616_);
lean_del_object(v___x_2611_);
lean_dec_ref(v_ty_2609_);
lean_dec(v_offset_2607_);
lean_dec(v_i_2606_);
v___x_2632_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4);
v___x_2633_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2468_, v___x_2632_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
return v___x_2633_;
}
}
else
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_dec(v___x_2615_);
lean_del_object(v___x_2611_);
lean_dec_ref(v_ty_2609_);
lean_dec(v_y_2608_);
lean_dec(v_offset_2607_);
lean_dec(v_i_2606_);
v___x_2634_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5);
v___x_2635_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2468_, v___x_2634_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
return v___x_2635_;
}
}
}
case 6:
{
lean_object* v_fvarId_2637_; lean_object* v_cidx_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2658_; 
v_fvarId_2637_ = lean_ctor_get(v_decl_2469_, 0);
v_cidx_2638_ = lean_ctor_get(v_decl_2469_, 1);
v_isSharedCheck_2658_ = !lean_is_exclusive(v_decl_2469_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2640_ = v_decl_2469_;
v_isShared_2641_ = v_isSharedCheck_2658_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_cidx_2638_);
lean_inc(v_fvarId_2637_);
lean_dec(v_decl_2469_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2658_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; uint8_t v___x_2643_; lean_object* v___x_2644_; 
v___x_2642_ = lean_st_ref_get(v_a_2471_);
v___x_2643_ = 1;
v___x_2644_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2642_, v_fvarId_2637_, v___x_2643_);
lean_dec(v___x_2642_);
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
v_reuseFailAlloc_2654_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_fvarId_2645_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v_cidx_2638_);
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
lean_dec(v_cidx_2638_);
v___x_2656_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6);
v___x_2657_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2468_, v___x_2656_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
return v___x_2657_;
}
}
}
case 7:
{
lean_object* v_fvarId_2659_; lean_object* v_n_2660_; uint8_t v_check_2661_; uint8_t v_persistent_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2682_; 
v_fvarId_2659_ = lean_ctor_get(v_decl_2469_, 0);
v_n_2660_ = lean_ctor_get(v_decl_2469_, 1);
v_check_2661_ = lean_ctor_get_uint8(v_decl_2469_, sizeof(void*)*2);
v_persistent_2662_ = lean_ctor_get_uint8(v_decl_2469_, sizeof(void*)*2 + 1);
v_isSharedCheck_2682_ = !lean_is_exclusive(v_decl_2469_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2664_ = v_decl_2469_;
v_isShared_2665_ = v_isSharedCheck_2682_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_n_2660_);
lean_inc(v_fvarId_2659_);
lean_dec(v_decl_2469_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2682_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2666_; uint8_t v___x_2667_; lean_object* v___x_2668_; 
v___x_2666_ = lean_st_ref_get(v_a_2471_);
v___x_2667_ = 1;
v___x_2668_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2666_, v_fvarId_2659_, v___x_2667_);
lean_dec(v___x_2666_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_fvarId_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2679_; 
v_fvarId_2669_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2671_ = v___x_2668_;
v_isShared_2672_ = v_isSharedCheck_2679_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_fvarId_2669_);
lean_dec(v___x_2668_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2679_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v_fvarId_2669_);
v___x_2674_ = v___x_2664_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_fvarId_2669_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v_n_2660_);
lean_ctor_set_uint8(v_reuseFailAlloc_2678_, sizeof(void*)*2, v_check_2661_);
lean_ctor_set_uint8(v_reuseFailAlloc_2678_, sizeof(void*)*2 + 1, v_persistent_2662_);
v___x_2674_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2676_; 
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 0, v___x_2674_);
v___x_2676_ = v___x_2671_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2681_; 
lean_dec(v___x_2668_);
lean_del_object(v___x_2664_);
lean_dec(v_n_2660_);
v___x_2680_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7);
v___x_2681_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2468_, v___x_2680_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
return v___x_2681_;
}
}
}
case 8:
{
lean_object* v_fvarId_2683_; lean_object* v_n_2684_; uint8_t v_check_2685_; uint8_t v_persistent_2686_; lean_object* v_objs_x3f_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2707_; 
v_fvarId_2683_ = lean_ctor_get(v_decl_2469_, 0);
v_n_2684_ = lean_ctor_get(v_decl_2469_, 1);
v_check_2685_ = lean_ctor_get_uint8(v_decl_2469_, sizeof(void*)*3);
v_persistent_2686_ = lean_ctor_get_uint8(v_decl_2469_, sizeof(void*)*3 + 1);
v_objs_x3f_2687_ = lean_ctor_get(v_decl_2469_, 2);
v_isSharedCheck_2707_ = !lean_is_exclusive(v_decl_2469_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2689_ = v_decl_2469_;
v_isShared_2690_ = v_isSharedCheck_2707_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_objs_x3f_2687_);
lean_inc(v_n_2684_);
lean_inc(v_fvarId_2683_);
lean_dec(v_decl_2469_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2707_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2691_; uint8_t v___x_2692_; lean_object* v___x_2693_; 
v___x_2691_ = lean_st_ref_get(v_a_2471_);
v___x_2692_ = 1;
v___x_2693_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2691_, v_fvarId_2683_, v___x_2692_);
lean_dec(v___x_2691_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_fvarId_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2704_; 
v_fvarId_2694_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2696_ = v___x_2693_;
v_isShared_2697_ = v_isSharedCheck_2704_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_fvarId_2694_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2704_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 0, v_fvarId_2694_);
v___x_2699_ = v___x_2689_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(8, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_fvarId_2694_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v_n_2684_);
lean_ctor_set(v_reuseFailAlloc_2703_, 2, v_objs_x3f_2687_);
lean_ctor_set_uint8(v_reuseFailAlloc_2703_, sizeof(void*)*3, v_check_2685_);
lean_ctor_set_uint8(v_reuseFailAlloc_2703_, sizeof(void*)*3 + 1, v_persistent_2686_);
v___x_2699_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2701_; 
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v___x_2699_);
v___x_2701_ = v___x_2696_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
else
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
lean_dec(v___x_2693_);
lean_del_object(v___x_2689_);
lean_dec(v_objs_x3f_2687_);
lean_dec(v_n_2684_);
v___x_2705_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8);
v___x_2706_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2468_, v___x_2705_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
return v___x_2706_;
}
}
}
default: 
{
lean_object* v_fvarId_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2728_; 
v_fvarId_2708_ = lean_ctor_get(v_decl_2469_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_decl_2469_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2710_ = v_decl_2469_;
v_isShared_2711_ = v_isSharedCheck_2728_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_fvarId_2708_);
lean_dec(v_decl_2469_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2728_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2712_; uint8_t v___x_2713_; lean_object* v___x_2714_; 
v___x_2712_ = lean_st_ref_get(v_a_2471_);
v___x_2713_ = 1;
v___x_2714_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2712_, v_fvarId_2708_, v___x_2713_);
lean_dec(v___x_2712_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_fvarId_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2725_; 
v_fvarId_2715_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2717_ = v___x_2714_;
v_isShared_2718_ = v_isSharedCheck_2725_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_fvarId_2715_);
lean_dec(v___x_2714_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2725_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v_fvarId_2715_);
v___x_2720_ = v___x_2710_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_fvarId_2715_);
v___x_2720_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
lean_object* v___x_2722_; 
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 0, v___x_2720_);
v___x_2722_ = v___x_2717_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
else
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
lean_dec(v___x_2714_);
lean_del_object(v___x_2710_);
v___x_2726_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9);
v___x_2727_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2468_, v___x_2726_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
return v___x_2727_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(lean_object* v_pu_2729_, lean_object* v_decl_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
uint8_t v_pu_boxed_2738_; uint8_t v_a_boxed_2739_; lean_object* v_res_2740_; 
v_pu_boxed_2738_ = lean_unbox(v_pu_2729_);
v_a_boxed_2739_ = lean_unbox(v_a_2731_);
v_res_2740_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v_pu_boxed_2738_, v_decl_2730_, v_a_boxed_2739_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
lean_dec(v_a_2732_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t v_pu_2741_, lean_object* v_code_2742_, lean_object* v_s_2743_, uint8_t v_uniqueIdents_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = lean_st_mk_ref(v_s_2743_);
v___x_2751_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2741_, v_code_2742_, v_uniqueIdents_2744_, v___x_2750_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2760_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2760_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2760_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2756_ = lean_st_ref_get(v___x_2750_);
lean_dec(v___x_2750_);
lean_dec(v___x_2756_);
if (v_isShared_2755_ == 0)
{
v___x_2758_ = v___x_2754_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2752_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
else
{
lean_dec(v___x_2750_);
return v___x_2751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize___boxed(lean_object* v_pu_2761_, lean_object* v_code_2762_, lean_object* v_s_2763_, lean_object* v_uniqueIdents_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_){
_start:
{
uint8_t v_pu_boxed_2770_; uint8_t v_uniqueIdents_boxed_2771_; lean_object* v_res_2772_; 
v_pu_boxed_2770_ = lean_unbox(v_pu_2761_);
v_uniqueIdents_boxed_2771_ = lean_unbox(v_uniqueIdents_2764_);
v_res_2772_ = l_Lean_Compiler_LCNF_Code_internalize(v_pu_boxed_2770_, v_code_2762_, v_s_2763_, v_uniqueIdents_boxed_2771_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_);
lean_dec(v_a_2768_);
lean_dec_ref(v_a_2767_);
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2765_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(lean_object* v_f_2773_, lean_object* v_v_2774_, uint8_t v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
if (lean_obj_tag(v_v_2774_) == 0)
{
lean_object* v_code_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2807_; 
v_code_2782_ = lean_ctor_get(v_v_2774_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_v_2774_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2784_ = v_v_2774_;
v_isShared_2785_ = v_isSharedCheck_2807_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_code_2782_);
lean_dec(v_v_2774_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2807_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = lean_box(v___y_2775_);
lean_inc(v___y_2780_);
lean_inc_ref(v___y_2779_);
lean_inc(v___y_2778_);
lean_inc_ref(v___y_2777_);
lean_inc(v___y_2776_);
v___x_2787_ = lean_apply_8(v_f_2773_, v_code_2782_, v___x_2786_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, lean_box(0));
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2798_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2790_ = v___x_2787_;
v_isShared_2791_ = v_isSharedCheck_2798_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2787_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2798_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v_a_2788_);
v___x_2793_ = v___x_2784_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2795_; 
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v___x_2793_);
v___x_2795_ = v___x_2790_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2793_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_del_object(v___x_2784_);
v_a_2799_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2787_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2787_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
}
else
{
lean_object* v___x_2808_; 
lean_dec_ref(v_f_2773_);
v___x_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2808_, 0, v_v_2774_);
return v___x_2808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg___boxed(lean_object* v_f_2809_, lean_object* v_v_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
uint8_t v___y_1412__boxed_2818_; lean_object* v_res_2819_; 
v___y_1412__boxed_2818_ = lean_unbox(v___y_2811_);
v_res_2819_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2809_, v_v_2810_, v___y_1412__boxed_2818_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(uint8_t v_pu_2820_, lean_object* v_f_2821_, lean_object* v_v_2822_, uint8_t v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v___x_2830_; 
v___x_2830_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2821_, v_v_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___boxed(lean_object* v_pu_2831_, lean_object* v_f_2832_, lean_object* v_v_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
uint8_t v_pu_boxed_2841_; uint8_t v___y_1488__boxed_2842_; lean_object* v_res_2843_; 
v_pu_boxed_2841_ = lean_unbox(v_pu_2831_);
v___y_1488__boxed_2842_ = lean_unbox(v___y_2834_);
v_res_2843_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(v_pu_boxed_2841_, v_f_2832_, v_v_2833_, v___y_1488__boxed_2842_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(uint8_t v_pu_2844_, lean_object* v_decl_2845_, uint8_t v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v_toSignature_2853_; lean_object* v_value_2854_; uint8_t v_recursive_2855_; lean_object* v_inlineAttr_x3f_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2916_; 
v_toSignature_2853_ = lean_ctor_get(v_decl_2845_, 0);
v_value_2854_ = lean_ctor_get(v_decl_2845_, 1);
v_recursive_2855_ = lean_ctor_get_uint8(v_decl_2845_, sizeof(void*)*3);
v_inlineAttr_x3f_2856_ = lean_ctor_get(v_decl_2845_, 2);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_decl_2845_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2858_ = v_decl_2845_;
v_isShared_2859_ = v_isSharedCheck_2916_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_inlineAttr_x3f_2856_);
lean_inc(v_value_2854_);
lean_inc(v_toSignature_2853_);
lean_dec(v_decl_2845_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2916_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v_name_2860_; lean_object* v_levelParams_2861_; lean_object* v_type_2862_; lean_object* v_params_2863_; uint8_t v_safe_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2915_; 
v_name_2860_ = lean_ctor_get(v_toSignature_2853_, 0);
v_levelParams_2861_ = lean_ctor_get(v_toSignature_2853_, 1);
v_type_2862_ = lean_ctor_get(v_toSignature_2853_, 2);
v_params_2863_ = lean_ctor_get(v_toSignature_2853_, 3);
v_safe_2864_ = lean_ctor_get_uint8(v_toSignature_2853_, sizeof(void*)*4);
v_isSharedCheck_2915_ = !lean_is_exclusive(v_toSignature_2853_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2866_ = v_toSignature_2853_;
v_isShared_2867_ = v_isSharedCheck_2915_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_params_2863_);
lean_inc(v_type_2862_);
lean_inc(v_levelParams_2861_);
lean_inc(v_name_2860_);
lean_dec(v_toSignature_2853_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2915_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2868_; 
v___x_2868_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2844_, v_type_2862_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; size_t v_sz_2870_; size_t v___x_2871_; lean_object* v___x_2872_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref_known(v___x_2868_, 1);
v_sz_2870_ = lean_array_size(v_params_2863_);
v___x_2871_ = ((size_t)0ULL);
v___x_2872_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2844_, v_sz_2870_, v___x_2871_, v_params_2863_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___x_2872_, 1);
v___x_2874_ = lean_box(v_pu_2844_);
v___x_2875_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed), 9, 1);
lean_closure_set(v___x_2875_, 0, v___x_2874_);
v___x_2876_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v___x_2875_, v_value_2854_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2890_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2879_ = v___x_2876_;
v_isShared_2880_ = v_isSharedCheck_2890_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2876_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2890_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 3, v_a_2873_);
lean_ctor_set(v___x_2866_, 2, v_a_2869_);
v___x_2882_ = v___x_2866_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_name_2860_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v_levelParams_2861_);
lean_ctor_set(v_reuseFailAlloc_2889_, 2, v_a_2869_);
lean_ctor_set(v_reuseFailAlloc_2889_, 3, v_a_2873_);
lean_ctor_set_uint8(v_reuseFailAlloc_2889_, sizeof(void*)*4, v_safe_2864_);
v___x_2882_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2884_; 
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 1, v_a_2877_);
lean_ctor_set(v___x_2858_, 0, v___x_2882_);
v___x_2884_ = v___x_2858_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2882_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v_a_2877_);
lean_ctor_set(v_reuseFailAlloc_2888_, 2, v_inlineAttr_x3f_2856_);
lean_ctor_set_uint8(v_reuseFailAlloc_2888_, sizeof(void*)*3, v_recursive_2855_);
v___x_2884_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
lean_object* v___x_2886_; 
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 0, v___x_2884_);
v___x_2886_ = v___x_2879_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2884_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
lean_dec(v_a_2873_);
lean_dec(v_a_2869_);
lean_del_object(v___x_2866_);
lean_dec(v_levelParams_2861_);
lean_dec(v_name_2860_);
lean_del_object(v___x_2858_);
lean_dec(v_inlineAttr_x3f_2856_);
v_a_2891_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2876_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2876_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec(v_a_2869_);
lean_del_object(v___x_2866_);
lean_dec(v_levelParams_2861_);
lean_dec(v_name_2860_);
lean_del_object(v___x_2858_);
lean_dec(v_inlineAttr_x3f_2856_);
lean_dec_ref(v_value_2854_);
v_a_2899_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2872_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2872_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
lean_del_object(v___x_2866_);
lean_dec_ref(v_params_2863_);
lean_dec(v_levelParams_2861_);
lean_dec(v_name_2860_);
lean_del_object(v___x_2858_);
lean_dec(v_inlineAttr_x3f_2856_);
lean_dec_ref(v_value_2854_);
v_a_2907_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2868_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2868_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go___boxed(lean_object* v_pu_2917_, lean_object* v_decl_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_){
_start:
{
uint8_t v_pu_boxed_2926_; uint8_t v_a_boxed_2927_; lean_object* v_res_2928_; 
v_pu_boxed_2926_ = lean_unbox(v_pu_2917_);
v_a_boxed_2927_ = lean_unbox(v_a_2919_);
v_res_2928_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_boxed_2926_, v_decl_2918_, v_a_boxed_2927_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_);
lean_dec(v_a_2924_);
lean_dec_ref(v_a_2923_);
lean_dec(v_a_2922_);
lean_dec_ref(v_a_2921_);
lean_dec(v_a_2920_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t v_pu_2929_, lean_object* v_decl_2930_, lean_object* v_s_2931_, uint8_t v_uniqueIdents_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = lean_st_mk_ref(v_s_2931_);
v___x_2939_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_2929_, v_decl_2930_, v_uniqueIdents_2932_, v___x_2938_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2948_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2942_ = v___x_2939_;
v_isShared_2943_ = v_isSharedCheck_2948_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2939_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2948_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; lean_object* v___x_2946_; 
v___x_2944_ = lean_st_ref_get(v___x_2938_);
lean_dec(v___x_2938_);
lean_dec(v___x_2944_);
if (v_isShared_2943_ == 0)
{
v___x_2946_ = v___x_2942_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2940_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
else
{
lean_dec(v___x_2938_);
return v___x_2939_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize___boxed(lean_object* v_pu_2949_, lean_object* v_decl_2950_, lean_object* v_s_2951_, lean_object* v_uniqueIdents_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_){
_start:
{
uint8_t v_pu_boxed_2958_; uint8_t v_uniqueIdents_boxed_2959_; lean_object* v_res_2960_; 
v_pu_boxed_2958_ = lean_unbox(v_pu_2949_);
v_uniqueIdents_boxed_2959_ = lean_unbox(v_uniqueIdents_2952_);
v_res_2960_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_boxed_2958_, v_decl_2950_, v_s_2951_, v_uniqueIdents_boxed_2959_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
return v_res_2960_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0(void){
_start:
{
lean_object* v_cellCount_2961_; lean_object* v___x_2962_; 
v_cellCount_2961_ = lean_unsigned_to_nat(16u);
v___x_2962_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2961_);
return v___x_2962_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1(void){
_start:
{
lean_object* v_cellCount_2963_; lean_object* v___x_2964_; 
v_cellCount_2963_ = lean_unsigned_to_nat(16u);
v___x_2964_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2963_);
return v___x_2964_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2965_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_2966_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0);
v___x_2967_ = lean_unsigned_to_nat(0u);
v___x_2968_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
lean_ctor_set(v___x_2968_, 1, v___x_2966_);
lean_ctor_set(v___x_2968_, 2, v___x_2965_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(uint8_t v_pu_2969_, size_t v_sz_2970_, size_t v_i_2971_, lean_object* v_bs_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
uint8_t v___x_2978_; 
v___x_2978_ = lean_usize_dec_lt(v_i_2971_, v_sz_2970_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; 
v___x_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2979_, 0, v_bs_2972_);
return v___x_2979_;
}
else
{
lean_object* v___x_2980_; lean_object* v_lctx_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_3009_; 
v___x_2980_ = lean_st_ref_take(v___y_2974_);
v_lctx_2981_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3009_ == 0)
{
lean_object* v_unused_3010_; 
v_unused_3010_ = lean_ctor_get(v___x_2980_, 1);
lean_dec(v_unused_3010_);
v___x_2983_ = v___x_2980_;
v_isShared_2984_ = v_isSharedCheck_3009_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_lctx_2981_);
lean_dec(v___x_2980_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_3009_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2985_; lean_object* v___x_2987_; 
v___x_2985_ = lean_unsigned_to_nat(1u);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 1, v___x_2985_);
v___x_2987_ = v___x_2983_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_lctx_2981_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v___x_2985_);
v___x_2987_ = v_reuseFailAlloc_3008_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; lean_object* v_v_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; uint8_t v___x_2992_; lean_object* v___x_2993_; 
v___x_2988_ = lean_st_ref_put(v___y_2974_, v___x_2987_);
v_v_2989_ = lean_array_uget_borrowed(v_bs_2972_, v_i_2971_);
v___x_2990_ = lean_unsigned_to_nat(0u);
v___x_2991_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__2);
v___x_2992_ = 0;
lean_inc(v_v_2989_);
v___x_2993_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_2969_, v_v_2989_, v___x_2991_, v___x_2992_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v_bs_x27_2995_; size_t v___x_2996_; size_t v___x_2997_; lean_object* v___x_2998_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
v_bs_x27_2995_ = lean_array_uset(v_bs_2972_, v_i_2971_, v___x_2990_);
v___x_2996_ = ((size_t)1ULL);
v___x_2997_ = lean_usize_add(v_i_2971_, v___x_2996_);
v___x_2998_ = lean_array_uset(v_bs_x27_2995_, v_i_2971_, v_a_2994_);
v_i_2971_ = v___x_2997_;
v_bs_2972_ = v___x_2998_;
goto _start;
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
lean_dec_ref(v_bs_2972_);
v_a_3000_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2993_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2993_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___boxed(lean_object* v_pu_3011_, lean_object* v_sz_3012_, lean_object* v_i_3013_, lean_object* v_bs_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
uint8_t v_pu_boxed_3020_; size_t v_sz_boxed_3021_; size_t v_i_boxed_3022_; lean_object* v_res_3023_; 
v_pu_boxed_3020_ = lean_unbox(v_pu_3011_);
v_sz_boxed_3021_ = lean_unbox_usize(v_sz_3012_);
lean_dec(v_sz_3012_);
v_i_boxed_3022_ = lean_unbox_usize(v_i_3013_);
lean_dec(v_i_3013_);
v_res_3023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_boxed_3020_, v_sz_boxed_3021_, v_i_boxed_3022_, v_bs_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
return v_res_3023_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__0(void){
_start:
{
lean_object* v_cellCount_3024_; lean_object* v___x_3025_; 
v_cellCount_3024_ = lean_unsigned_to_nat(16u);
v___x_3025_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3024_);
return v___x_3025_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__1(void){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3026_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__0, &l_Lean_Compiler_LCNF_cleanup___closed__0_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__0);
v___x_3027_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0);
v___x_3028_ = lean_unsigned_to_nat(0u);
v___x_3029_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
lean_ctor_set(v___x_3029_, 1, v___x_3027_);
lean_ctor_set(v___x_3029_, 2, v___x_3026_);
return v___x_3029_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__2(void){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3030_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
v___x_3031_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
lean_ctor_set(v___x_3031_, 2, v___x_3030_);
lean_ctor_set(v___x_3031_, 3, v___x_3030_);
lean_ctor_set(v___x_3031_, 4, v___x_3030_);
lean_ctor_set(v___x_3031_, 5, v___x_3030_);
return v___x_3031_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__3(void){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3032_ = lean_unsigned_to_nat(1u);
v___x_3033_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__2, &l_Lean_Compiler_LCNF_cleanup___closed__2_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__2);
v___x_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
lean_ctor_set(v___x_3034_, 1, v___x_3032_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup(uint8_t v_pu_3035_, lean_object* v_decl_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; size_t v_sz_3045_; size_t v___x_3046_; lean_object* v___x_3047_; 
v___x_3042_ = lean_st_ref_take(v_a_3038_);
lean_dec(v___x_3042_);
v___x_3043_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__3, &l_Lean_Compiler_LCNF_cleanup___closed__3_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__3);
v___x_3044_ = lean_st_ref_put(v_a_3038_, v___x_3043_);
v_sz_3045_ = lean_array_size(v_decl_3036_);
v___x_3046_ = ((size_t)0ULL);
v___x_3047_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_3035_, v_sz_3045_, v___x_3046_, v_decl_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup___boxed(lean_object* v_pu_3048_, lean_object* v_decl_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_){
_start:
{
uint8_t v_pu_boxed_3055_; lean_object* v_res_3056_; 
v_pu_boxed_3055_ = lean_unbox(v_pu_3048_);
v_res_3056_ = l_Lean_Compiler_LCNF_cleanup(v_pu_boxed_3055_, v_decl_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_);
lean_dec(v_a_3053_);
lean_dec_ref(v_a_3052_);
lean_dec(v_a_3051_);
lean_dec_ref(v_a_3050_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(lean_object* v_a_3057_, lean_object* v_ngen_3058_, lean_object* v_a_x3f_3059_){
_start:
{
lean_object* v___x_3061_; lean_object* v_env_3062_; lean_object* v_nextMacroScope_3063_; lean_object* v_auxDeclNGen_3064_; lean_object* v_traceState_3065_; lean_object* v_cache_3066_; lean_object* v_messages_3067_; lean_object* v_infoState_3068_; lean_object* v_snapshotTasks_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3079_; 
v___x_3061_ = lean_st_ref_take(v_a_3057_);
v_env_3062_ = lean_ctor_get(v___x_3061_, 0);
v_nextMacroScope_3063_ = lean_ctor_get(v___x_3061_, 1);
v_auxDeclNGen_3064_ = lean_ctor_get(v___x_3061_, 3);
v_traceState_3065_ = lean_ctor_get(v___x_3061_, 4);
v_cache_3066_ = lean_ctor_get(v___x_3061_, 5);
v_messages_3067_ = lean_ctor_get(v___x_3061_, 6);
v_infoState_3068_ = lean_ctor_get(v___x_3061_, 7);
v_snapshotTasks_3069_ = lean_ctor_get(v___x_3061_, 8);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3079_ == 0)
{
lean_object* v_unused_3080_; 
v_unused_3080_ = lean_ctor_get(v___x_3061_, 2);
lean_dec(v_unused_3080_);
v___x_3071_ = v___x_3061_;
v_isShared_3072_ = v_isSharedCheck_3079_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_snapshotTasks_3069_);
lean_inc(v_infoState_3068_);
lean_inc(v_messages_3067_);
lean_inc(v_cache_3066_);
lean_inc(v_traceState_3065_);
lean_inc(v_auxDeclNGen_3064_);
lean_inc(v_nextMacroScope_3063_);
lean_inc(v_env_3062_);
lean_dec(v___x_3061_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3079_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 2, v_ngen_3058_);
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_env_3062_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v_nextMacroScope_3063_);
lean_ctor_set(v_reuseFailAlloc_3078_, 2, v_ngen_3058_);
lean_ctor_set(v_reuseFailAlloc_3078_, 3, v_auxDeclNGen_3064_);
lean_ctor_set(v_reuseFailAlloc_3078_, 4, v_traceState_3065_);
lean_ctor_set(v_reuseFailAlloc_3078_, 5, v_cache_3066_);
lean_ctor_set(v_reuseFailAlloc_3078_, 6, v_messages_3067_);
lean_ctor_set(v_reuseFailAlloc_3078_, 7, v_infoState_3068_);
lean_ctor_set(v_reuseFailAlloc_3078_, 8, v_snapshotTasks_3069_);
v___x_3074_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = lean_st_ref_put(v_a_3057_, v___x_3074_);
v___x_3076_ = lean_box(0);
v___x_3077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3076_);
return v___x_3077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0___boxed(lean_object* v_a_3081_, lean_object* v_ngen_3082_, lean_object* v_a_x3f_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3081_, v_ngen_3082_, v_a_x3f_3083_);
lean_dec(v_a_x3f_3083_);
lean_dec(v_a_3081_);
return v_res_3085_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normalizeFVarIds___closed__3(void){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__2);
v___x_3093_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
lean_ctor_set(v___x_3093_, 2, v___x_3092_);
lean_ctor_set(v___x_3093_, 3, v___x_3092_);
lean_ctor_set(v___x_3093_, 4, v___x_3092_);
lean_ctor_set(v___x_3093_, 5, v___x_3092_);
return v___x_3093_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normalizeFVarIds___closed__4(void){
_start:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3094_ = lean_unsigned_to_nat(1u);
v___x_3095_ = lean_obj_once(&l_Lean_Compiler_LCNF_normalizeFVarIds___closed__3, &l_Lean_Compiler_LCNF_normalizeFVarIds___closed__3_once, _init_l_Lean_Compiler_LCNF_normalizeFVarIds___closed__3);
v___x_3096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
lean_ctor_set(v___x_3096_, 1, v___x_3094_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(uint8_t v_pu_3097_, lean_object* v_decl_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v_env_3104_; lean_object* v_nextMacroScope_3105_; lean_object* v_auxDeclNGen_3106_; lean_object* v_traceState_3107_; lean_object* v_cache_3108_; lean_object* v_messages_3109_; lean_object* v_infoState_3110_; lean_object* v_snapshotTasks_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3157_; 
v___x_3102_ = lean_st_ref_get(v_a_3100_);
v___x_3103_ = lean_st_ref_take(v_a_3100_);
v_env_3104_ = lean_ctor_get(v___x_3103_, 0);
v_nextMacroScope_3105_ = lean_ctor_get(v___x_3103_, 1);
v_auxDeclNGen_3106_ = lean_ctor_get(v___x_3103_, 3);
v_traceState_3107_ = lean_ctor_get(v___x_3103_, 4);
v_cache_3108_ = lean_ctor_get(v___x_3103_, 5);
v_messages_3109_ = lean_ctor_get(v___x_3103_, 6);
v_infoState_3110_ = lean_ctor_get(v___x_3103_, 7);
v_snapshotTasks_3111_ = lean_ctor_get(v___x_3103_, 8);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3157_ == 0)
{
lean_object* v_unused_3158_; 
v_unused_3158_ = lean_ctor_get(v___x_3103_, 2);
lean_dec(v_unused_3158_);
v___x_3113_ = v___x_3103_;
v_isShared_3114_ = v_isSharedCheck_3157_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_snapshotTasks_3111_);
lean_inc(v_infoState_3110_);
lean_inc(v_messages_3109_);
lean_inc(v_cache_3108_);
lean_inc(v_traceState_3107_);
lean_inc(v_auxDeclNGen_3106_);
lean_inc(v_nextMacroScope_3105_);
lean_inc(v_env_3104_);
lean_dec(v___x_3103_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3157_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3115_; lean_object* v___x_3117_; 
v___x_3115_ = ((lean_object*)(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2));
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 2, v___x_3115_);
v___x_3117_ = v___x_3113_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_env_3104_);
lean_ctor_set(v_reuseFailAlloc_3156_, 1, v_nextMacroScope_3105_);
lean_ctor_set(v_reuseFailAlloc_3156_, 2, v___x_3115_);
lean_ctor_set(v_reuseFailAlloc_3156_, 3, v_auxDeclNGen_3106_);
lean_ctor_set(v_reuseFailAlloc_3156_, 4, v_traceState_3107_);
lean_ctor_set(v_reuseFailAlloc_3156_, 5, v_cache_3108_);
lean_ctor_set(v_reuseFailAlloc_3156_, 6, v_messages_3109_);
lean_ctor_set(v_reuseFailAlloc_3156_, 7, v_infoState_3110_);
lean_ctor_set(v_reuseFailAlloc_3156_, 8, v_snapshotTasks_3111_);
v___x_3117_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
lean_object* v___x_3118_; lean_object* v_ngen_3119_; lean_object* v___x_3120_; uint8_t v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; uint8_t v___x_3126_; lean_object* v_r_3127_; 
v___x_3118_ = lean_st_ref_put(v_a_3100_, v___x_3117_);
v_ngen_3119_ = lean_ctor_get(v___x_3102_, 2);
lean_inc_ref(v_ngen_3119_);
lean_dec(v___x_3102_);
v___x_3120_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__2);
v___x_3121_ = 0;
v___x_3122_ = lean_box(v_pu_3097_);
v___x_3123_ = lean_box(v___x_3121_);
v___x_3124_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_internalize___boxed), 9, 4);
lean_closure_set(v___x_3124_, 0, v___x_3122_);
lean_closure_set(v___x_3124_, 1, v_decl_3098_);
lean_closure_set(v___x_3124_, 2, v___x_3120_);
lean_closure_set(v___x_3124_, 3, v___x_3123_);
v___x_3125_ = lean_obj_once(&l_Lean_Compiler_LCNF_normalizeFVarIds___closed__4, &l_Lean_Compiler_LCNF_normalizeFVarIds___closed__4_once, _init_l_Lean_Compiler_LCNF_normalizeFVarIds___closed__4);
v___x_3126_ = 0;
v_r_3127_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v___x_3124_, v___x_3125_, v___x_3126_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v_r_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3144_; 
v_a_3128_ = lean_ctor_get(v_r_3127_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v_r_3127_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3130_ = v_r_3127_;
v_isShared_3131_ = v_isSharedCheck_3144_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v_r_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3144_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
lean_inc(v_a_3128_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set_tag(v___x_3130_, 1);
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3128_);
v___x_3133_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v___x_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
v___x_3134_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3100_, v_ngen_3119_, v___x_3133_);
lean_dec_ref(v___x_3133_);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3141_ == 0)
{
lean_object* v_unused_3142_; 
v_unused_3142_ = lean_ctor_get(v___x_3134_, 0);
lean_dec(v_unused_3142_);
v___x_3136_ = v___x_3134_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_dec(v___x_3134_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 0, v_a_3128_);
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3128_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
v_a_3145_ = lean_ctor_get(v_r_3127_, 0);
lean_inc(v_a_3145_);
lean_dec_ref_known(v_r_3127_, 1);
v___x_3146_ = lean_box(0);
v___x_3147_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3100_, v_ngen_3119_, v___x_3146_);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3154_ == 0)
{
lean_object* v_unused_3155_; 
v_unused_3155_ = lean_ctor_get(v___x_3147_, 0);
lean_dec(v_unused_3155_);
v___x_3149_ = v___x_3147_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_dec(v___x_3147_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
lean_ctor_set_tag(v___x_3149_, 1);
lean_ctor_set(v___x_3149_, 0, v_a_3145_);
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3145_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___boxed(lean_object* v_pu_3159_, lean_object* v_decl_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_){
_start:
{
uint8_t v_pu_boxed_3164_; lean_object* v_res_3165_; 
v_pu_boxed_3164_ = lean_unbox(v_pu_3159_);
v_res_3165_ = l_Lean_Compiler_LCNF_normalizeFVarIds(v_pu_boxed_3164_, v_decl_3160_, v_a_3161_, v_a_3162_);
lean_dec(v_a_3162_);
lean_dec_ref(v_a_3161_);
return v_res_3165_;
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
