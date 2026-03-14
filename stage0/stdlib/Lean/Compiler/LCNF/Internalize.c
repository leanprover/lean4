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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run(uint8_t v_pu_40_, lean_object* v_00_u03b1_41_, lean_object* v_x_42_, lean_object* v_state_43_, uint8_t v_ctx_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_st_mk_ref(v_state_43_);
v___x_51_ = lean_box(v_ctx_44_);
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
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___redArg(lean_object* v_x_84_, lean_object* v_state_85_, uint8_t v_ctx_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = lean_st_mk_ref(v_state_85_);
v___x_93_ = lean_box(v_ctx_86_);
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
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27(uint8_t v_pu_114_, lean_object* v_00_u03b1_115_, lean_object* v_x_116_, lean_object* v_state_117_, uint8_t v_ctx_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lean_st_mk_ref(v_state_117_);
v___x_125_ = lean_box(v_ctx_118_);
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
lean_dec_ref(v_binderName_149_);
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
v___x_164_ = lean_st_ref_set(v_a_151_, v___x_163_);
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
v___x_180_ = lean_st_ref_set(v_a_151_, v___x_179_);
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
uint8_t v_a_2512__boxed_189_; lean_object* v_res_190_; 
v_a_2512__boxed_189_ = lean_unbox(v_a_186_);
v_res_190_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_185_, v_a_2512__boxed_189_, v_a_187_);
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
uint8_t v_pu_boxed_210_; uint8_t v_a_2578__boxed_211_; lean_object* v_res_212_; 
v_pu_boxed_210_ = lean_unbox(v_pu_201_);
v_a_2578__boxed_211_ = lean_unbox(v_a_203_);
v_res_212_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName(v_pu_boxed_210_, v_binderName_202_, v_a_2578__boxed_211_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
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
lean_object* v___f_261_; lean_object* v___x_262_; lean_object* v_get_263_; lean_object* v_set_264_; lean_object* v_modifyGet_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_277_; 
v___f_261_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0));
v___x_262_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11, &l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11_once, _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11);
v_get_263_ = lean_ctor_get(v___x_262_, 0);
v_set_264_ = lean_ctor_get(v___x_262_, 1);
v_modifyGet_265_ = lean_ctor_get(v___x_262_, 2);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_277_ == 0)
{
v___x_267_ = v___x_262_;
v_isShared_268_ = v_isSharedCheck_277_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_modifyGet_265_);
lean_inc(v_set_264_);
lean_inc(v_get_263_);
lean_dec(v___x_262_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_277_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___f_269_; lean_object* v___f_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v___f_269_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_269_, 0, v_set_264_);
lean_closure_set(v___f_269_, 1, v___f_261_);
v___f_270_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_270_, 0, v_modifyGet_265_);
lean_closure_set(v___f_270_, 1, v___f_261_);
v___x_271_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_271_, 0, lean_box(0));
lean_closure_set(v___x_271_, 1, v_get_263_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 2, v___f_270_);
lean_ctor_set(v___x_267_, 1, v___f_269_);
lean_ctor_set(v___x_267_, 0, v___x_271_);
v___x_273_ = v___x_267_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v___f_269_);
lean_ctor_set(v_reuseFailAlloc_276_, 2, v___f_270_);
v___x_273_ = v_reuseFailAlloc_276_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = l_instMonadStateOfMonadStateOf___redArg(v___x_273_);
v___x_275_ = lean_alloc_closure((void*)(l_modify), 4, 3);
lean_closure_set(v___x_275_, 0, lean_box(0));
lean_closure_set(v___x_275_, 1, lean_box(0));
lean_closure_set(v___x_275_, 2, v___x_274_);
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___boxed(lean_object* v_pu_278_){
_start:
{
uint8_t v_pu_boxed_279_; lean_object* v_res_280_; 
v_pu_boxed_279_ = lean_unbox(v_pu_278_);
v_res_280_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM(v_pu_boxed_279_);
return v_res_280_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(lean_object* v_a_281_, lean_object* v_x_282_){
_start:
{
if (lean_obj_tag(v_x_282_) == 0)
{
uint8_t v___x_283_; 
v___x_283_ = 0;
return v___x_283_;
}
else
{
lean_object* v_key_284_; lean_object* v_tail_285_; uint8_t v___x_286_; 
v_key_284_ = lean_ctor_get(v_x_282_, 0);
v_tail_285_ = lean_ctor_get(v_x_282_, 2);
v___x_286_ = l_Lean_instBEqFVarId_beq(v_key_284_, v_a_281_);
if (v___x_286_ == 0)
{
v_x_282_ = v_tail_285_;
goto _start;
}
else
{
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg___boxed(lean_object* v_a_288_, lean_object* v_x_289_){
_start:
{
uint8_t v_res_290_; lean_object* v_r_291_; 
v_res_290_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_a_288_, v_x_289_);
lean_dec(v_x_289_);
lean_dec(v_a_288_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(lean_object* v_a_292_, lean_object* v_b_293_, lean_object* v_x_294_){
_start:
{
if (lean_obj_tag(v_x_294_) == 0)
{
lean_dec(v_b_293_);
lean_dec(v_a_292_);
return v_x_294_;
}
else
{
lean_object* v_key_295_; lean_object* v_value_296_; lean_object* v_tail_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_309_; 
v_key_295_ = lean_ctor_get(v_x_294_, 0);
v_value_296_ = lean_ctor_get(v_x_294_, 1);
v_tail_297_ = lean_ctor_get(v_x_294_, 2);
v_isSharedCheck_309_ = !lean_is_exclusive(v_x_294_);
if (v_isSharedCheck_309_ == 0)
{
v___x_299_ = v_x_294_;
v_isShared_300_ = v_isSharedCheck_309_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_tail_297_);
lean_inc(v_value_296_);
lean_inc(v_key_295_);
lean_dec(v_x_294_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_309_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
uint8_t v___x_301_; 
v___x_301_ = l_Lean_instBEqFVarId_beq(v_key_295_, v_a_292_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_302_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(v_a_292_, v_b_293_, v_tail_297_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 2, v___x_302_);
v___x_304_ = v___x_299_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_key_295_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_value_296_);
lean_ctor_set(v_reuseFailAlloc_305_, 2, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
else
{
lean_object* v___x_307_; 
lean_dec(v_value_296_);
lean_dec(v_key_295_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v_b_293_);
lean_ctor_set(v___x_299_, 0, v_a_292_);
v___x_307_ = v___x_299_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_292_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_b_293_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v_tail_297_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_310_, lean_object* v_x_311_){
_start:
{
if (lean_obj_tag(v_x_311_) == 0)
{
return v_x_310_;
}
else
{
lean_object* v_key_312_; lean_object* v_value_313_; lean_object* v_tail_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_337_; 
v_key_312_ = lean_ctor_get(v_x_311_, 0);
v_value_313_ = lean_ctor_get(v_x_311_, 1);
v_tail_314_ = lean_ctor_get(v_x_311_, 2);
v_isSharedCheck_337_ = !lean_is_exclusive(v_x_311_);
if (v_isSharedCheck_337_ == 0)
{
v___x_316_ = v_x_311_;
v_isShared_317_ = v_isSharedCheck_337_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_tail_314_);
lean_inc(v_value_313_);
lean_inc(v_key_312_);
lean_dec(v_x_311_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_337_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; uint64_t v___x_319_; uint64_t v___x_320_; uint64_t v___x_321_; uint64_t v_fold_322_; uint64_t v___x_323_; uint64_t v___x_324_; uint64_t v___x_325_; size_t v___x_326_; size_t v___x_327_; size_t v___x_328_; size_t v___x_329_; size_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_318_ = lean_array_get_size(v_x_310_);
v___x_319_ = l_Lean_instHashableFVarId_hash(v_key_312_);
v___x_320_ = 32ULL;
v___x_321_ = lean_uint64_shift_right(v___x_319_, v___x_320_);
v_fold_322_ = lean_uint64_xor(v___x_319_, v___x_321_);
v___x_323_ = 16ULL;
v___x_324_ = lean_uint64_shift_right(v_fold_322_, v___x_323_);
v___x_325_ = lean_uint64_xor(v_fold_322_, v___x_324_);
v___x_326_ = lean_uint64_to_usize(v___x_325_);
v___x_327_ = lean_usize_of_nat(v___x_318_);
v___x_328_ = ((size_t)1ULL);
v___x_329_ = lean_usize_sub(v___x_327_, v___x_328_);
v___x_330_ = lean_usize_land(v___x_326_, v___x_329_);
v___x_331_ = lean_array_uget_borrowed(v_x_310_, v___x_330_);
lean_inc(v___x_331_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 2, v___x_331_);
v___x_333_ = v___x_316_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_key_312_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_value_313_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v___x_331_);
v___x_333_ = v_reuseFailAlloc_336_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; 
v___x_334_ = lean_array_uset(v_x_310_, v___x_330_, v___x_333_);
v_x_310_ = v___x_334_;
v_x_311_ = v_tail_314_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(lean_object* v_i_338_, lean_object* v_source_339_, lean_object* v_target_340_){
_start:
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = lean_array_get_size(v_source_339_);
v___x_342_ = lean_nat_dec_lt(v_i_338_, v___x_341_);
if (v___x_342_ == 0)
{
lean_dec_ref(v_source_339_);
lean_dec(v_i_338_);
return v_target_340_;
}
else
{
lean_object* v_es_343_; lean_object* v___x_344_; lean_object* v_source_345_; lean_object* v_target_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_es_343_ = lean_array_fget(v_source_339_, v_i_338_);
v___x_344_ = lean_box(0);
v_source_345_ = lean_array_fset(v_source_339_, v_i_338_, v___x_344_);
v_target_346_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(v_target_340_, v_es_343_);
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = lean_nat_add(v_i_338_, v___x_347_);
lean_dec(v_i_338_);
v_i_338_ = v___x_348_;
v_source_339_ = v_source_345_;
v_target_340_ = v_target_346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(lean_object* v_data_350_){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v_nbuckets_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_351_ = lean_array_get_size(v_data_350_);
v___x_352_ = lean_unsigned_to_nat(2u);
v_nbuckets_353_ = lean_nat_mul(v___x_351_, v___x_352_);
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = lean_box(0);
v___x_356_ = lean_mk_array(v_nbuckets_353_, v___x_355_);
v___x_357_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(v___x_354_, v_data_350_, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(lean_object* v_m_358_, lean_object* v_a_359_, lean_object* v_b_360_){
_start:
{
lean_object* v_size_361_; lean_object* v_buckets_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_405_; 
v_size_361_ = lean_ctor_get(v_m_358_, 0);
v_buckets_362_ = lean_ctor_get(v_m_358_, 1);
v_isSharedCheck_405_ = !lean_is_exclusive(v_m_358_);
if (v_isSharedCheck_405_ == 0)
{
v___x_364_ = v_m_358_;
v_isShared_365_ = v_isSharedCheck_405_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_buckets_362_);
lean_inc(v_size_361_);
lean_dec(v_m_358_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_405_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; uint64_t v___x_367_; uint64_t v___x_368_; uint64_t v___x_369_; uint64_t v_fold_370_; uint64_t v___x_371_; uint64_t v___x_372_; uint64_t v___x_373_; size_t v___x_374_; size_t v___x_375_; size_t v___x_376_; size_t v___x_377_; size_t v___x_378_; lean_object* v_bkt_379_; uint8_t v___x_380_; 
v___x_366_ = lean_array_get_size(v_buckets_362_);
v___x_367_ = l_Lean_instHashableFVarId_hash(v_a_359_);
v___x_368_ = 32ULL;
v___x_369_ = lean_uint64_shift_right(v___x_367_, v___x_368_);
v_fold_370_ = lean_uint64_xor(v___x_367_, v___x_369_);
v___x_371_ = 16ULL;
v___x_372_ = lean_uint64_shift_right(v_fold_370_, v___x_371_);
v___x_373_ = lean_uint64_xor(v_fold_370_, v___x_372_);
v___x_374_ = lean_uint64_to_usize(v___x_373_);
v___x_375_ = lean_usize_of_nat(v___x_366_);
v___x_376_ = ((size_t)1ULL);
v___x_377_ = lean_usize_sub(v___x_375_, v___x_376_);
v___x_378_ = lean_usize_land(v___x_374_, v___x_377_);
v_bkt_379_ = lean_array_uget_borrowed(v_buckets_362_, v___x_378_);
v___x_380_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_a_359_, v_bkt_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v_size_x27_382_; lean_object* v___x_383_; lean_object* v_buckets_x27_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_381_ = lean_unsigned_to_nat(1u);
v_size_x27_382_ = lean_nat_add(v_size_361_, v___x_381_);
lean_dec(v_size_361_);
lean_inc(v_bkt_379_);
v___x_383_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_383_, 0, v_a_359_);
lean_ctor_set(v___x_383_, 1, v_b_360_);
lean_ctor_set(v___x_383_, 2, v_bkt_379_);
v_buckets_x27_384_ = lean_array_uset(v_buckets_362_, v___x_378_, v___x_383_);
v___x_385_ = lean_unsigned_to_nat(4u);
v___x_386_ = lean_nat_mul(v_size_x27_382_, v___x_385_);
v___x_387_ = lean_unsigned_to_nat(3u);
v___x_388_ = lean_nat_div(v___x_386_, v___x_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_array_get_size(v_buckets_x27_384_);
v___x_390_ = lean_nat_dec_le(v___x_388_, v___x_389_);
lean_dec(v___x_388_);
if (v___x_390_ == 0)
{
lean_object* v_val_391_; lean_object* v___x_393_; 
v_val_391_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(v_buckets_x27_384_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 1, v_val_391_);
lean_ctor_set(v___x_364_, 0, v_size_x27_382_);
v___x_393_ = v___x_364_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_size_x27_382_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_val_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
else
{
lean_object* v___x_396_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 1, v_buckets_x27_384_);
lean_ctor_set(v___x_364_, 0, v_size_x27_382_);
v___x_396_ = v___x_364_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_size_x27_382_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_buckets_x27_384_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
else
{
lean_object* v___x_398_; lean_object* v_buckets_x27_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
lean_inc(v_bkt_379_);
v___x_398_ = lean_box(0);
v_buckets_x27_399_ = lean_array_uset(v_buckets_362_, v___x_378_, v___x_398_);
v___x_400_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(v_a_359_, v_b_360_, v_bkt_379_);
v___x_401_ = lean_array_uset(v_buckets_x27_399_, v___x_378_, v___x_400_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 1, v___x_401_);
v___x_403_ = v___x_364_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_size_361_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(lean_object* v___y_406_){
_start:
{
lean_object* v___x_408_; lean_object* v_ngen_409_; lean_object* v_namePrefix_410_; lean_object* v_idx_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_440_; 
v___x_408_ = lean_st_ref_get(v___y_406_);
v_ngen_409_ = lean_ctor_get(v___x_408_, 2);
lean_inc_ref(v_ngen_409_);
lean_dec(v___x_408_);
v_namePrefix_410_ = lean_ctor_get(v_ngen_409_, 0);
v_idx_411_ = lean_ctor_get(v_ngen_409_, 1);
v_isSharedCheck_440_ = !lean_is_exclusive(v_ngen_409_);
if (v_isSharedCheck_440_ == 0)
{
v___x_413_ = v_ngen_409_;
v_isShared_414_ = v_isSharedCheck_440_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_idx_411_);
lean_inc(v_namePrefix_410_);
lean_dec(v_ngen_409_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_440_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v_env_416_; lean_object* v_nextMacroScope_417_; lean_object* v_auxDeclNGen_418_; lean_object* v_traceState_419_; lean_object* v_cache_420_; lean_object* v_messages_421_; lean_object* v_infoState_422_; lean_object* v_snapshotTasks_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_438_; 
v___x_415_ = lean_st_ref_take(v___y_406_);
v_env_416_ = lean_ctor_get(v___x_415_, 0);
v_nextMacroScope_417_ = lean_ctor_get(v___x_415_, 1);
v_auxDeclNGen_418_ = lean_ctor_get(v___x_415_, 3);
v_traceState_419_ = lean_ctor_get(v___x_415_, 4);
v_cache_420_ = lean_ctor_get(v___x_415_, 5);
v_messages_421_ = lean_ctor_get(v___x_415_, 6);
v_infoState_422_ = lean_ctor_get(v___x_415_, 7);
v_snapshotTasks_423_ = lean_ctor_get(v___x_415_, 8);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; 
v_unused_439_ = lean_ctor_get(v___x_415_, 2);
lean_dec(v_unused_439_);
v___x_425_ = v___x_415_;
v_isShared_426_ = v_isSharedCheck_438_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_snapshotTasks_423_);
lean_inc(v_infoState_422_);
lean_inc(v_messages_421_);
lean_inc(v_cache_420_);
lean_inc(v_traceState_419_);
lean_inc(v_auxDeclNGen_418_);
lean_inc(v_nextMacroScope_417_);
lean_inc(v_env_416_);
lean_dec(v___x_415_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_438_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v_r_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
lean_inc(v_idx_411_);
lean_inc(v_namePrefix_410_);
v_r_427_ = l_Lean_Name_num___override(v_namePrefix_410_, v_idx_411_);
v___x_428_ = lean_unsigned_to_nat(1u);
v___x_429_ = lean_nat_add(v_idx_411_, v___x_428_);
lean_dec(v_idx_411_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v___x_429_);
v___x_431_ = v___x_413_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_namePrefix_410_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_429_);
v___x_431_ = v_reuseFailAlloc_437_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_433_; 
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 2, v___x_431_);
v___x_433_ = v___x_425_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_env_416_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_nextMacroScope_417_);
lean_ctor_set(v_reuseFailAlloc_436_, 2, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_436_, 3, v_auxDeclNGen_418_);
lean_ctor_set(v_reuseFailAlloc_436_, 4, v_traceState_419_);
lean_ctor_set(v_reuseFailAlloc_436_, 5, v_cache_420_);
lean_ctor_set(v_reuseFailAlloc_436_, 6, v_messages_421_);
lean_ctor_set(v_reuseFailAlloc_436_, 7, v_infoState_422_);
lean_ctor_set(v_reuseFailAlloc_436_, 8, v_snapshotTasks_423_);
v___x_433_ = v_reuseFailAlloc_436_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_st_ref_set(v___y_406_, v___x_433_);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v_r_427_);
return v___x_435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg___boxed(lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_441_);
lean_dec(v___y_441_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(uint8_t v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v___x_451_; lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
v___x_451_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_449_);
v_a_452_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_451_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_451_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0___boxed(lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
uint8_t v___y_3162__boxed_467_; lean_object* v_res_468_; 
v___y_3162__boxed_467_ = lean_unbox(v___y_460_);
v_res_468_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(v___y_3162__boxed_467_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(lean_object* v_fvarId_469_, uint8_t v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_489_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_489_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_489_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_489_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_482_ = lean_st_ref_take(v_a_471_);
lean_inc(v_a_478_);
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v_a_478_);
v___x_484_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v___x_482_, v_fvarId_469_, v___x_483_);
v___x_485_ = lean_st_ref_set(v_a_471_, v___x_484_);
if (v_isShared_481_ == 0)
{
v___x_487_ = v___x_480_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_478_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
else
{
lean_dec(v_fvarId_469_);
return v___x_477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg___boxed(lean_object* v_fvarId_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
uint8_t v_a_3202__boxed_498_; lean_object* v_res_499_; 
v_a_3202__boxed_498_ = lean_unbox(v_a_491_);
v_res_499_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_490_, v_a_3202__boxed_498_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(uint8_t v_pu_500_, lean_object* v_fvarId_501_, uint8_t v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___boxed(lean_object* v_pu_510_, lean_object* v_fvarId_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
uint8_t v_pu_boxed_519_; uint8_t v_a_3250__boxed_520_; lean_object* v_res_521_; 
v_pu_boxed_519_ = lean_unbox(v_pu_510_);
v_a_3250__boxed_520_ = lean_unbox(v_a_512_);
v_res_521_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(v_pu_boxed_519_, v_fvarId_511_, v_a_3250__boxed_520_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(uint8_t v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_527_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___boxed(lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
uint8_t v___y_3273__boxed_537_; lean_object* v_res_538_; 
v___y_3273__boxed_537_ = lean_unbox(v___y_530_);
v_res_538_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(v___y_3273__boxed_537_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1(lean_object* v_00_u03b2_539_, lean_object* v_m_540_, lean_object* v_a_541_, lean_object* v_b_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v_m_540_, v_a_541_, v_b_542_);
return v___x_543_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(lean_object* v_00_u03b2_544_, lean_object* v_a_545_, lean_object* v_x_546_){
_start:
{
uint8_t v___x_547_; 
v___x_547_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_a_545_, v_x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___boxed(lean_object* v_00_u03b2_548_, lean_object* v_a_549_, lean_object* v_x_550_){
_start:
{
uint8_t v_res_551_; lean_object* v_r_552_; 
v_res_551_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(v_00_u03b2_548_, v_a_549_, v_x_550_);
lean_dec(v_x_550_);
lean_dec(v_a_549_);
v_r_552_ = lean_box(v_res_551_);
return v_r_552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3(lean_object* v_00_u03b2_553_, lean_object* v_data_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(v_data_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4(lean_object* v_00_u03b2_556_, lean_object* v_a_557_, lean_object* v_b_558_, lean_object* v_x_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(v_a_557_, v_b_558_, v_x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_561_, lean_object* v_i_562_, lean_object* v_source_563_, lean_object* v_target_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(v_i_562_, v_source_563_, v_target_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_566_, lean_object* v_x_567_, lean_object* v_x_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(v_x_567_, v_x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(lean_object* v_a_570_, lean_object* v_x_571_){
_start:
{
if (lean_obj_tag(v_x_571_) == 0)
{
lean_object* v___x_572_; 
v___x_572_ = lean_box(0);
return v___x_572_;
}
else
{
lean_object* v_key_573_; lean_object* v_value_574_; lean_object* v_tail_575_; uint8_t v___x_576_; 
v_key_573_ = lean_ctor_get(v_x_571_, 0);
v_value_574_ = lean_ctor_get(v_x_571_, 1);
v_tail_575_ = lean_ctor_get(v_x_571_, 2);
v___x_576_ = l_Lean_instBEqFVarId_beq(v_key_573_, v_a_570_);
if (v___x_576_ == 0)
{
v_x_571_ = v_tail_575_;
goto _start;
}
else
{
lean_object* v___x_578_; 
lean_inc(v_value_574_);
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v_value_574_);
return v___x_578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_579_, lean_object* v_x_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_579_, v_x_580_);
lean_dec(v_x_580_);
lean_dec(v_a_579_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(lean_object* v_m_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_buckets_584_; lean_object* v___x_585_; uint64_t v___x_586_; uint64_t v___x_587_; uint64_t v___x_588_; uint64_t v_fold_589_; uint64_t v___x_590_; uint64_t v___x_591_; uint64_t v___x_592_; size_t v___x_593_; size_t v___x_594_; size_t v___x_595_; size_t v___x_596_; size_t v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_buckets_584_ = lean_ctor_get(v_m_582_, 1);
v___x_585_ = lean_array_get_size(v_buckets_584_);
v___x_586_ = l_Lean_instHashableFVarId_hash(v_a_583_);
v___x_587_ = 32ULL;
v___x_588_ = lean_uint64_shift_right(v___x_586_, v___x_587_);
v_fold_589_ = lean_uint64_xor(v___x_586_, v___x_588_);
v___x_590_ = 16ULL;
v___x_591_ = lean_uint64_shift_right(v_fold_589_, v___x_590_);
v___x_592_ = lean_uint64_xor(v_fold_589_, v___x_591_);
v___x_593_ = lean_uint64_to_usize(v___x_592_);
v___x_594_ = lean_usize_of_nat(v___x_585_);
v___x_595_ = ((size_t)1ULL);
v___x_596_ = lean_usize_sub(v___x_594_, v___x_595_);
v___x_597_ = lean_usize_land(v___x_593_, v___x_596_);
v___x_598_ = lean_array_uget_borrowed(v_buckets_584_, v___x_597_);
v___x_599_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_583_, v___x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg___boxed(lean_object* v_m_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v_m_600_, v_a_601_);
lean_dec(v_a_601_);
lean_dec_ref(v_m_600_);
return v_res_602_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(lean_object* v_msg_608_, uint8_t v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v_toApplicative_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_682_; 
v___x_616_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
v___x_617_ = l_ReaderT_instMonad___redArg(v___x_616_);
v_toApplicative_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_682_ == 0)
{
lean_object* v_unused_683_; 
v_unused_683_ = lean_ctor_get(v___x_617_, 1);
lean_dec(v_unused_683_);
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_682_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_toApplicative_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_682_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v_toFunctor_622_; lean_object* v_toSeq_623_; lean_object* v_toSeqLeft_624_; lean_object* v_toSeqRight_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_680_; 
v_toFunctor_622_ = lean_ctor_get(v_toApplicative_618_, 0);
v_toSeq_623_ = lean_ctor_get(v_toApplicative_618_, 2);
v_toSeqLeft_624_ = lean_ctor_get(v_toApplicative_618_, 3);
v_toSeqRight_625_ = lean_ctor_get(v_toApplicative_618_, 4);
v_isSharedCheck_680_ = !lean_is_exclusive(v_toApplicative_618_);
if (v_isSharedCheck_680_ == 0)
{
lean_object* v_unused_681_; 
v_unused_681_ = lean_ctor_get(v_toApplicative_618_, 1);
lean_dec(v_unused_681_);
v___x_627_ = v_toApplicative_618_;
v_isShared_628_ = v_isSharedCheck_680_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_toSeqRight_625_);
lean_inc(v_toSeqLeft_624_);
lean_inc(v_toSeq_623_);
lean_inc(v_toFunctor_622_);
lean_dec(v_toApplicative_618_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_680_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___f_629_; lean_object* v___f_630_; lean_object* v___f_631_; lean_object* v___f_632_; lean_object* v___x_633_; lean_object* v___f_634_; lean_object* v___f_635_; lean_object* v___f_636_; lean_object* v___x_638_; 
v___f_629_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
v___f_630_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_622_);
v___f_631_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_631_, 0, v_toFunctor_622_);
v___f_632_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_632_, 0, v_toFunctor_622_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v___f_631_);
lean_ctor_set(v___x_633_, 1, v___f_632_);
v___f_634_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_634_, 0, v_toSeqRight_625_);
v___f_635_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_635_, 0, v_toSeqLeft_624_);
v___f_636_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_636_, 0, v_toSeq_623_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 4, v___f_634_);
lean_ctor_set(v___x_627_, 3, v___f_635_);
lean_ctor_set(v___x_627_, 2, v___f_636_);
lean_ctor_set(v___x_627_, 1, v___f_629_);
lean_ctor_set(v___x_627_, 0, v___x_633_);
v___x_638_ = v___x_627_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v___f_629_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v___f_636_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v___f_635_);
lean_ctor_set(v_reuseFailAlloc_679_, 4, v___f_634_);
v___x_638_ = v_reuseFailAlloc_679_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_640_; 
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 1, v___f_630_);
lean_ctor_set(v___x_620_, 0, v___x_638_);
v___x_640_ = v___x_620_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v___f_630_);
v___x_640_ = v_reuseFailAlloc_678_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; lean_object* v_toApplicative_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_676_; 
v___x_641_ = l_ReaderT_instMonad___redArg(v___x_640_);
v_toApplicative_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; 
v_unused_677_ = lean_ctor_get(v___x_641_, 1);
lean_dec(v_unused_677_);
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_676_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_toApplicative_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_676_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v_toFunctor_646_; lean_object* v_toSeq_647_; lean_object* v_toSeqLeft_648_; lean_object* v_toSeqRight_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_674_; 
v_toFunctor_646_ = lean_ctor_get(v_toApplicative_642_, 0);
v_toSeq_647_ = lean_ctor_get(v_toApplicative_642_, 2);
v_toSeqLeft_648_ = lean_ctor_get(v_toApplicative_642_, 3);
v_toSeqRight_649_ = lean_ctor_get(v_toApplicative_642_, 4);
v_isSharedCheck_674_ = !lean_is_exclusive(v_toApplicative_642_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; 
v_unused_675_ = lean_ctor_get(v_toApplicative_642_, 1);
lean_dec(v_unused_675_);
v___x_651_ = v_toApplicative_642_;
v_isShared_652_ = v_isSharedCheck_674_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_toSeqRight_649_);
lean_inc(v_toSeqLeft_648_);
lean_inc(v_toSeq_647_);
lean_inc(v_toFunctor_646_);
lean_dec(v_toApplicative_642_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_674_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___f_653_; lean_object* v___f_654_; lean_object* v___f_655_; lean_object* v___f_656_; lean_object* v___x_657_; lean_object* v___f_658_; lean_object* v___f_659_; lean_object* v___f_660_; lean_object* v___x_662_; 
v___f_653_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
v___f_654_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(v_toFunctor_646_);
v___f_655_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_655_, 0, v_toFunctor_646_);
v___f_656_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_656_, 0, v_toFunctor_646_);
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v___f_655_);
lean_ctor_set(v___x_657_, 1, v___f_656_);
v___f_658_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_658_, 0, v_toSeqRight_649_);
v___f_659_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_659_, 0, v_toSeqLeft_648_);
v___f_660_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_660_, 0, v_toSeq_647_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 4, v___f_658_);
lean_ctor_set(v___x_651_, 3, v___f_659_);
lean_ctor_set(v___x_651_, 2, v___f_660_);
lean_ctor_set(v___x_651_, 1, v___f_653_);
lean_ctor_set(v___x_651_, 0, v___x_657_);
v___x_662_ = v___x_651_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v___f_653_);
lean_ctor_set(v_reuseFailAlloc_673_, 2, v___f_660_);
lean_ctor_set(v_reuseFailAlloc_673_, 3, v___f_659_);
lean_ctor_set(v_reuseFailAlloc_673_, 4, v___f_658_);
v___x_662_ = v_reuseFailAlloc_673_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_664_; 
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 1, v___f_654_);
lean_ctor_set(v___x_644_, 0, v___x_662_);
v___x_664_ = v___x_644_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v___f_654_);
v___x_664_ = v_reuseFailAlloc_672_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___f_668_; lean_object* v___x_8577__overap_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_665_ = l_ReaderT_instMonad___redArg(v___x_664_);
v___x_666_ = l_Lean_instInhabitedExpr;
v___x_667_ = l_instInhabitedOfMonad___redArg(v___x_665_, v___x_666_);
v___f_668_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_668_, 0, v___x_667_);
v___x_8577__overap_669_ = lean_panic_fn(v___f_668_, v_msg_608_);
v___x_670_ = lean_box(v___y_609_);
v___x_671_ = lean_apply_7(v___x_8577__overap_669_, v___x_670_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, lean_box(0));
return v___x_671_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___boxed(lean_object* v_msg_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
uint8_t v___y_8698__boxed_692_; lean_object* v_res_693_; 
v___y_8698__boxed_692_ = lean_unbox(v___y_685_);
v_res_693_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v_msg_684_, v___y_8698__boxed_692_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
return v_res_693_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_697_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_698_ = lean_unsigned_to_nat(20u);
v___x_699_ = lean_unsigned_to_nat(88u);
v___x_700_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__1));
v___x_701_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_702_ = l_mkPanicMessageWithDecl(v___x_701_, v___x_700_, v___x_699_, v___x_698_, v___x_697_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(uint8_t v_pu_703_, lean_object* v_e_704_, uint8_t v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
uint8_t v___x_712_; 
v___x_712_ = l_Lean_Expr_hasFVar(v_e_704_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v_e_704_);
return v___x_713_;
}
else
{
switch(lean_obj_tag(v_e_704_))
{
case 1:
{
lean_object* v_fvarId_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_a_707_);
v_fvarId_714_ = lean_ctor_get(v_e_704_, 0);
v___x_715_ = lean_st_ref_get(v_a_706_);
lean_dec(v_a_706_);
v___x_716_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v___x_715_, v_fvarId_714_);
lean_dec(v___x_715_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v___x_717_; 
lean_dec(v_a_708_);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v_e_704_);
return v___x_717_;
}
else
{
lean_object* v_val_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_763_; 
lean_dec_ref(v_e_704_);
v_val_718_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_763_ == 0)
{
v___x_720_ = v___x_716_;
v_isShared_721_ = v_isSharedCheck_763_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_val_718_);
lean_dec(v___x_716_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_763_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
switch(lean_obj_tag(v_val_718_))
{
case 0:
{
lean_object* v___x_722_; lean_object* v___x_724_; 
lean_dec(v_a_708_);
v___x_722_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_721_ == 0)
{
lean_ctor_set_tag(v___x_720_, 0);
lean_ctor_set(v___x_720_, 0, v___x_722_);
v___x_724_ = v___x_720_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
case 1:
{
lean_object* v_fvarId_726_; lean_object* v___x_727_; 
lean_del_object(v___x_720_);
v_fvarId_726_ = lean_ctor_get(v_val_718_, 0);
lean_inc(v_fvarId_726_);
lean_dec_ref(v_val_718_);
v___x_727_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_703_, v_fvarId_726_, v_a_708_);
lean_dec(v_a_708_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_746_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_746_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_746_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_746_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
if (lean_obj_tag(v_a_728_) == 0)
{
lean_dec(v_fvarId_726_);
goto v___jp_732_;
}
else
{
lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_744_; 
v_isSharedCheck_744_ = !lean_is_exclusive(v_a_728_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v_a_728_, 0);
lean_dec(v_unused_745_);
v___x_738_ = v_a_728_;
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
else
{
lean_dec(v_a_728_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
if (v___x_712_ == 0)
{
lean_del_object(v___x_738_);
lean_dec(v_fvarId_726_);
goto v___jp_732_;
}
else
{
lean_object* v___x_740_; lean_object* v___x_742_; 
lean_del_object(v___x_730_);
v___x_740_ = l_Lean_Expr_fvar___override(v_fvarId_726_);
if (v_isShared_739_ == 0)
{
lean_ctor_set_tag(v___x_738_, 0);
lean_ctor_set(v___x_738_, 0, v___x_740_);
v___x_742_ = v___x_738_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
v___jp_732_:
{
lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_733_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_733_);
v___x_735_ = v___x_730_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v_fvarId_726_);
v_a_747_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_727_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_727_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
default: 
{
lean_object* v_expr_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_del_object(v___x_720_);
lean_dec(v_a_708_);
v_expr_755_ = lean_ctor_get(v_val_718_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v_val_718_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v_val_718_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_expr_755_);
lean_dec(v_val_718_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set_tag(v___x_757_, 0);
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_expr_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_764_; lean_object* v_arg_765_; lean_object* v___x_766_; 
v_fn_764_ = lean_ctor_get(v_e_704_, 0);
v_arg_765_ = lean_ctor_get(v_e_704_, 1);
lean_inc(v_a_710_);
lean_inc_ref(v_a_709_);
lean_inc(v_a_708_);
lean_inc_ref(v_a_707_);
lean_inc(v_a_706_);
lean_inc_ref(v_fn_764_);
v___x_766_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_703_, v_fn_764_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref(v___x_766_);
lean_inc_ref(v_arg_765_);
v___x_768_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_703_, v_arg_765_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_788_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_788_ == 0)
{
v___x_771_ = v___x_768_;
v_isShared_772_ = v_isSharedCheck_788_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_768_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_788_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___y_774_; uint8_t v___y_780_; size_t v___x_782_; size_t v___x_783_; uint8_t v___x_784_; 
v___x_782_ = lean_ptr_addr(v_fn_764_);
v___x_783_ = lean_ptr_addr(v_a_767_);
v___x_784_ = lean_usize_dec_eq(v___x_782_, v___x_783_);
if (v___x_784_ == 0)
{
v___y_780_ = v___x_784_;
goto v___jp_779_;
}
else
{
size_t v___x_785_; size_t v___x_786_; uint8_t v___x_787_; 
v___x_785_ = lean_ptr_addr(v_arg_765_);
v___x_786_ = lean_ptr_addr(v_a_769_);
v___x_787_ = lean_usize_dec_eq(v___x_785_, v___x_786_);
v___y_780_ = v___x_787_;
goto v___jp_779_;
}
v___jp_773_:
{
lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_775_ = l_Lean_Expr_headBeta(v___y_774_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_775_);
v___x_777_ = v___x_771_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
v___jp_779_:
{
if (v___y_780_ == 0)
{
lean_object* v___x_781_; 
lean_dec_ref(v_e_704_);
v___x_781_ = l_Lean_Expr_app___override(v_a_767_, v_a_769_);
v___y_774_ = v___x_781_;
goto v___jp_773_;
}
else
{
lean_dec(v_a_769_);
lean_dec(v_a_767_);
v___y_774_ = v_e_704_;
goto v___jp_773_;
}
}
}
}
else
{
lean_dec(v_a_767_);
lean_dec_ref(v_e_704_);
return v___x_768_;
}
}
else
{
lean_dec_ref(v_e_704_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
return v___x_766_;
}
}
case 6:
{
lean_object* v_binderName_789_; lean_object* v_binderType_790_; lean_object* v_body_791_; uint8_t v_binderInfo_792_; lean_object* v___x_793_; 
v_binderName_789_ = lean_ctor_get(v_e_704_, 0);
v_binderType_790_ = lean_ctor_get(v_e_704_, 1);
v_body_791_ = lean_ctor_get(v_e_704_, 2);
v_binderInfo_792_ = lean_ctor_get_uint8(v_e_704_, sizeof(void*)*3 + 8);
lean_inc(v_a_710_);
lean_inc_ref(v_a_709_);
lean_inc(v_a_708_);
lean_inc_ref(v_a_707_);
lean_inc(v_a_706_);
lean_inc_ref(v_binderType_790_);
v___x_793_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_703_, v_binderType_790_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_795_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
lean_dec_ref(v___x_793_);
lean_inc_ref(v_body_791_);
v___x_795_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_703_, v_body_791_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_820_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_820_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_820_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_820_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
uint8_t v___y_801_; size_t v___x_814_; size_t v___x_815_; uint8_t v___x_816_; 
v___x_814_ = lean_ptr_addr(v_binderType_790_);
v___x_815_ = lean_ptr_addr(v_a_794_);
v___x_816_ = lean_usize_dec_eq(v___x_814_, v___x_815_);
if (v___x_816_ == 0)
{
v___y_801_ = v___x_816_;
goto v___jp_800_;
}
else
{
size_t v___x_817_; size_t v___x_818_; uint8_t v___x_819_; 
v___x_817_ = lean_ptr_addr(v_body_791_);
v___x_818_ = lean_ptr_addr(v_a_796_);
v___x_819_ = lean_usize_dec_eq(v___x_817_, v___x_818_);
v___y_801_ = v___x_819_;
goto v___jp_800_;
}
v___jp_800_:
{
if (v___y_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_804_; 
lean_inc(v_binderName_789_);
lean_dec_ref(v_e_704_);
v___x_802_ = l_Lean_Expr_lam___override(v_binderName_789_, v_a_794_, v_a_796_, v_binderInfo_792_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_802_);
v___x_804_ = v___x_798_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
else
{
uint8_t v___x_806_; 
v___x_806_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_792_, v_binderInfo_792_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_809_; 
lean_inc(v_binderName_789_);
lean_dec_ref(v_e_704_);
v___x_807_ = l_Lean_Expr_lam___override(v_binderName_789_, v_a_794_, v_a_796_, v_binderInfo_792_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_807_);
v___x_809_ = v___x_798_;
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
lean_object* v___x_812_; 
lean_dec(v_a_796_);
lean_dec(v_a_794_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v_e_704_);
v___x_812_ = v___x_798_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_e_704_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
}
else
{
lean_dec(v_a_794_);
lean_dec_ref(v_e_704_);
return v___x_795_;
}
}
else
{
lean_dec_ref(v_e_704_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
return v___x_793_;
}
}
case 7:
{
lean_object* v_binderName_821_; lean_object* v_binderType_822_; lean_object* v_body_823_; uint8_t v_binderInfo_824_; lean_object* v___x_825_; 
v_binderName_821_ = lean_ctor_get(v_e_704_, 0);
v_binderType_822_ = lean_ctor_get(v_e_704_, 1);
v_body_823_ = lean_ctor_get(v_e_704_, 2);
v_binderInfo_824_ = lean_ctor_get_uint8(v_e_704_, sizeof(void*)*3 + 8);
lean_inc(v_a_710_);
lean_inc_ref(v_a_709_);
lean_inc(v_a_708_);
lean_inc_ref(v_a_707_);
lean_inc(v_a_706_);
lean_inc_ref(v_binderType_822_);
v___x_825_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_703_, v_binderType_822_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_827_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref(v___x_825_);
lean_inc_ref(v_body_823_);
v___x_827_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_703_, v_body_823_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_852_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_852_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_852_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_852_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
uint8_t v___y_833_; size_t v___x_846_; size_t v___x_847_; uint8_t v___x_848_; 
v___x_846_ = lean_ptr_addr(v_binderType_822_);
v___x_847_ = lean_ptr_addr(v_a_826_);
v___x_848_ = lean_usize_dec_eq(v___x_846_, v___x_847_);
if (v___x_848_ == 0)
{
v___y_833_ = v___x_848_;
goto v___jp_832_;
}
else
{
size_t v___x_849_; size_t v___x_850_; uint8_t v___x_851_; 
v___x_849_ = lean_ptr_addr(v_body_823_);
v___x_850_ = lean_ptr_addr(v_a_828_);
v___x_851_ = lean_usize_dec_eq(v___x_849_, v___x_850_);
v___y_833_ = v___x_851_;
goto v___jp_832_;
}
v___jp_832_:
{
if (v___y_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_836_; 
lean_inc(v_binderName_821_);
lean_dec_ref(v_e_704_);
v___x_834_ = l_Lean_Expr_forallE___override(v_binderName_821_, v_a_826_, v_a_828_, v_binderInfo_824_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_834_);
v___x_836_ = v___x_830_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
else
{
uint8_t v___x_838_; 
v___x_838_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_824_, v_binderInfo_824_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; lean_object* v___x_841_; 
lean_inc(v_binderName_821_);
lean_dec_ref(v_e_704_);
v___x_839_ = l_Lean_Expr_forallE___override(v_binderName_821_, v_a_826_, v_a_828_, v_binderInfo_824_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_839_);
v___x_841_ = v___x_830_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
else
{
lean_object* v___x_844_; 
lean_dec(v_a_828_);
lean_dec(v_a_826_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v_e_704_);
v___x_844_ = v___x_830_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_e_704_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
}
else
{
lean_dec(v_a_826_);
lean_dec_ref(v_e_704_);
return v___x_827_;
}
}
else
{
lean_dec_ref(v_e_704_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
return v___x_825_;
}
}
case 8:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec_ref(v_e_704_);
v___x_853_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3, &l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3);
v___x_854_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v___x_853_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
return v___x_854_;
}
case 10:
{
lean_object* v_data_855_; lean_object* v_expr_856_; lean_object* v___x_857_; 
v_data_855_ = lean_ctor_get(v_e_704_, 0);
v_expr_856_ = lean_ctor_get(v_e_704_, 1);
lean_inc_ref(v_expr_856_);
v___x_857_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_703_, v_expr_856_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_872_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_872_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_872_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_872_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
size_t v___x_862_; size_t v___x_863_; uint8_t v___x_864_; 
v___x_862_ = lean_ptr_addr(v_expr_856_);
v___x_863_ = lean_ptr_addr(v_a_858_);
v___x_864_ = lean_usize_dec_eq(v___x_862_, v___x_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; lean_object* v___x_867_; 
lean_inc(v_data_855_);
lean_dec_ref(v_e_704_);
v___x_865_ = l_Lean_Expr_mdata___override(v_data_855_, v_a_858_);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_865_);
v___x_867_ = v___x_860_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
else
{
lean_object* v___x_870_; 
lean_dec(v_a_858_);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v_e_704_);
v___x_870_ = v___x_860_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_e_704_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
else
{
lean_dec_ref(v_e_704_);
return v___x_857_;
}
}
case 11:
{
lean_object* v_typeName_873_; lean_object* v_idx_874_; lean_object* v_struct_875_; lean_object* v___x_876_; 
v_typeName_873_ = lean_ctor_get(v_e_704_, 0);
v_idx_874_ = lean_ctor_get(v_e_704_, 1);
v_struct_875_ = lean_ctor_get(v_e_704_, 2);
lean_inc_ref(v_struct_875_);
v___x_876_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_703_, v_struct_875_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_891_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_891_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_891_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_891_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
size_t v___x_881_; size_t v___x_882_; uint8_t v___x_883_; 
v___x_881_ = lean_ptr_addr(v_struct_875_);
v___x_882_ = lean_ptr_addr(v_a_877_);
v___x_883_ = lean_usize_dec_eq(v___x_881_, v___x_882_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_886_; 
lean_inc(v_idx_874_);
lean_inc(v_typeName_873_);
lean_dec_ref(v_e_704_);
v___x_884_ = l_Lean_Expr_proj___override(v_typeName_873_, v_idx_874_, v_a_877_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_884_);
v___x_886_ = v___x_879_;
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
lean_object* v___x_889_; 
lean_dec(v_a_877_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v_e_704_);
v___x_889_ = v___x_879_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_e_704_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_dec_ref(v_e_704_);
return v___x_876_;
}
}
default: 
{
lean_object* v___x_892_; 
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v_e_704_);
return v___x_892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(uint8_t v_pu_893_, lean_object* v_e_894_, uint8_t v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
if (lean_obj_tag(v_e_894_) == 5)
{
lean_object* v_fn_902_; lean_object* v_arg_903_; lean_object* v___x_904_; 
v_fn_902_ = lean_ctor_get(v_e_894_, 0);
v_arg_903_ = lean_ctor_get(v_e_894_, 1);
lean_inc(v_a_900_);
lean_inc_ref(v_a_899_);
lean_inc(v_a_898_);
lean_inc_ref(v_a_897_);
lean_inc(v_a_896_);
lean_inc_ref(v_fn_902_);
v___x_904_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_893_, v_fn_902_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_906_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref(v___x_904_);
lean_inc_ref(v_arg_903_);
v___x_906_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_893_, v_arg_903_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_926_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_926_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_926_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_926_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
uint8_t v___y_912_; size_t v___x_920_; size_t v___x_921_; uint8_t v___x_922_; 
v___x_920_ = lean_ptr_addr(v_fn_902_);
v___x_921_ = lean_ptr_addr(v_a_905_);
v___x_922_ = lean_usize_dec_eq(v___x_920_, v___x_921_);
if (v___x_922_ == 0)
{
v___y_912_ = v___x_922_;
goto v___jp_911_;
}
else
{
size_t v___x_923_; size_t v___x_924_; uint8_t v___x_925_; 
v___x_923_ = lean_ptr_addr(v_arg_903_);
v___x_924_ = lean_ptr_addr(v_a_907_);
v___x_925_ = lean_usize_dec_eq(v___x_923_, v___x_924_);
v___y_912_ = v___x_925_;
goto v___jp_911_;
}
v___jp_911_:
{
if (v___y_912_ == 0)
{
lean_object* v___x_913_; lean_object* v___x_915_; 
lean_dec_ref(v_e_894_);
v___x_913_ = l_Lean_Expr_app___override(v_a_905_, v_a_907_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_913_);
v___x_915_ = v___x_909_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
else
{
lean_object* v___x_918_; 
lean_dec(v_a_907_);
lean_dec(v_a_905_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v_e_894_);
v___x_918_ = v___x_909_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_e_894_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
else
{
lean_dec(v_a_905_);
lean_dec_ref(v_e_894_);
return v___x_906_;
}
}
else
{
lean_dec_ref(v_e_894_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
return v___x_904_;
}
}
else
{
lean_object* v___x_927_; 
v___x_927_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_893_, v_e_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp___boxed(lean_object* v_pu_928_, lean_object* v_e_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
uint8_t v_pu_boxed_937_; uint8_t v_a_8847__boxed_938_; lean_object* v_res_939_; 
v_pu_boxed_937_ = lean_unbox(v_pu_928_);
v_a_8847__boxed_938_ = lean_unbox(v_a_930_);
v_res_939_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_boxed_937_, v_e_929_, v_a_8847__boxed_938_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___boxed(lean_object* v_pu_940_, lean_object* v_e_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
uint8_t v_pu_boxed_949_; uint8_t v_a_8883__boxed_950_; lean_object* v_res_951_; 
v_pu_boxed_949_ = lean_unbox(v_pu_940_);
v_a_8883__boxed_950_ = lean_unbox(v_a_942_);
v_res_951_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_boxed_949_, v_e_941_, v_a_8883__boxed_950_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(uint8_t v_pu_968_, lean_object* v_e_969_, uint8_t v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
uint8_t v___x_977_; uint8_t v___x_978_; 
v___x_977_ = 1;
v___x_978_ = l_Lean_Compiler_LCNF_instDecidableEqPurity(v_pu_968_, v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
v___x_979_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_968_, v_e_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_979_;
}
else
{
lean_object* v___x_980_; 
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v_e_969_);
return v___x_980_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___boxed(lean_object* v_pu_981_, lean_object* v_e_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
uint8_t v_pu_boxed_990_; uint8_t v_a_220__boxed_991_; lean_object* v_res_992_; 
v_pu_boxed_990_ = lean_unbox(v_pu_981_);
v_a_220__boxed_991_ = lean_unbox(v_a_983_);
v_res_992_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_boxed_990_, v_e_982_, v_a_220__boxed_991_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t v_pu_993_, lean_object* v_p_994_, uint8_t v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_fvarId_1002_; lean_object* v_binderName_1003_; lean_object* v_type_1004_; uint8_t v_borrow_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1053_; 
v_fvarId_1002_ = lean_ctor_get(v_p_994_, 0);
v_binderName_1003_ = lean_ctor_get(v_p_994_, 1);
v_type_1004_ = lean_ctor_get(v_p_994_, 2);
v_borrow_1005_ = lean_ctor_get_uint8(v_p_994_, sizeof(void*)*3);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_p_994_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1007_ = v_p_994_;
v_isShared_1008_ = v_isSharedCheck_1053_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_type_1004_);
lean_inc(v_binderName_1003_);
lean_inc(v_fvarId_1002_);
lean_dec(v_p_994_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1053_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v_a_1010_; lean_object* v___x_1011_; 
v___x_1009_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_1003_, v_a_995_, v_a_998_);
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref(v___x_1009_);
lean_inc(v_a_1000_);
lean_inc_ref(v_a_999_);
lean_inc(v_a_998_);
lean_inc_ref(v_a_997_);
lean_inc(v_a_996_);
v___x_1011_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_993_, v_type_1004_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1013_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref(v___x_1011_);
v___x_1013_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_1002_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1036_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1036_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1036_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v_lctx_1019_; lean_object* v_nextIdx_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1035_; 
v___x_1018_ = lean_st_ref_take(v_a_998_);
v_lctx_1019_ = lean_ctor_get(v___x_1018_, 0);
v_nextIdx_1020_ = lean_ctor_get(v___x_1018_, 1);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1022_ = v___x_1018_;
v_isShared_1023_ = v_isSharedCheck_1035_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_nextIdx_1020_);
lean_inc(v_lctx_1019_);
lean_dec(v___x_1018_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1035_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 2, v_a_1012_);
lean_ctor_set(v___x_1007_, 1, v_a_1010_);
lean_ctor_set(v___x_1007_, 0, v_a_1014_);
v___x_1025_ = v___x_1007_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1014_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_a_1010_);
lean_ctor_set(v_reuseFailAlloc_1034_, 2, v_a_1012_);
lean_ctor_set_uint8(v_reuseFailAlloc_1034_, sizeof(void*)*3, v_borrow_1005_);
v___x_1025_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
lean_inc_ref(v___x_1025_);
v___x_1026_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_993_, v_lctx_1019_, v___x_1025_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1026_);
v___x_1028_ = v___x_1022_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_nextIdx_1020_);
v___x_1028_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1029_ = lean_st_ref_set(v_a_998_, v___x_1028_);
lean_dec(v_a_998_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1025_);
v___x_1031_ = v___x_1016_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1025_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec(v_a_1012_);
lean_dec(v_a_1010_);
lean_del_object(v___x_1007_);
lean_dec(v_a_998_);
v_a_1037_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1013_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1013_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec(v_a_1010_);
lean_del_object(v___x_1007_);
lean_dec(v_fvarId_1002_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
v_a_1045_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1011_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1011_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(lean_object* v_pu_1054_, lean_object* v_p_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
uint8_t v_pu_boxed_1063_; uint8_t v_a_1358__boxed_1064_; lean_object* v_res_1065_; 
v_pu_boxed_1063_ = lean_unbox(v_pu_1054_);
v_a_1358__boxed_1064_ = lean_unbox(v_a_1056_);
v_res_1065_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_boxed_1063_, v_p_1055_, v_a_1358__boxed_1064_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg(uint8_t v_pu_1066_, lean_object* v_arg_1067_, uint8_t v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
switch(lean_obj_tag(v_arg_1067_))
{
case 0:
{
lean_object* v___x_1075_; 
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v_arg_1067_);
return v___x_1075_;
}
case 1:
{
lean_object* v_fvarId_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
v_fvarId_1076_ = lean_ctor_get(v_arg_1067_, 0);
v___x_1077_ = lean_st_ref_get(v_a_1069_);
lean_dec(v_a_1069_);
v___x_1078_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v___x_1077_, v_fvarId_1076_);
lean_dec(v___x_1077_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v_arg_1067_);
return v___x_1079_;
}
else
{
lean_object* v_val_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1110_; 
lean_dec_ref(v_arg_1067_);
v_val_1080_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1082_ = v___x_1078_;
v_isShared_1083_ = v_isSharedCheck_1110_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_val_1080_);
lean_dec(v___x_1078_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1110_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
switch(lean_obj_tag(v_val_1080_))
{
case 0:
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1084_ = lean_box(0);
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1084_);
v___x_1086_ = v___x_1082_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
case 1:
{
lean_object* v_fvarId_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1098_; 
v_fvarId_1088_ = lean_ctor_get(v_val_1080_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_val_1080_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1090_ = v_val_1080_;
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_fvarId_1088_);
lean_dec(v_val_1080_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_fvarId_1088_);
v___x_1093_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1095_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1093_);
v___x_1095_ = v___x_1082_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
default: 
{
lean_object* v_expr_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1109_; 
v_expr_1099_ = lean_ctor_get(v_val_1080_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_val_1080_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1101_ = v_val_1080_;
v_isShared_1102_ = v_isSharedCheck_1109_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_expr_1099_);
lean_dec(v_val_1080_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1109_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_expr_1099_);
v___x_1104_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1106_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1104_);
v___x_1106_ = v___x_1082_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
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
lean_object* v_expr_1111_; lean_object* v___x_1112_; 
v_expr_1111_ = lean_ctor_get(v_arg_1067_, 0);
lean_inc_ref(v_expr_1111_);
v___x_1112_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1066_, v_expr_1111_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1121_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1117_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1066_, v_arg_1067_, v_a_1113_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1117_);
v___x_1119_ = v___x_1115_;
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
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec_ref(v_arg_1067_);
v_a_1122_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1112_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1112_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg___boxed(lean_object* v_pu_1130_, lean_object* v_arg_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
uint8_t v_pu_boxed_1139_; uint8_t v_a_1938__boxed_1140_; lean_object* v_res_1141_; 
v_pu_boxed_1139_ = lean_unbox(v_pu_1130_);
v_a_1938__boxed_1140_ = lean_unbox(v_a_1132_);
v_res_1141_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_boxed_1139_, v_arg_1131_, v_a_1938__boxed_1140_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(uint8_t v_pu_1142_, size_t v_sz_1143_, size_t v_i_1144_, lean_object* v_bs_1145_, uint8_t v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
uint8_t v___x_1153_; 
v___x_1153_ = lean_usize_dec_lt(v_i_1144_, v_sz_1143_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v_bs_1145_);
return v___x_1154_;
}
else
{
lean_object* v_v_1155_; lean_object* v___x_1156_; 
v_v_1155_ = lean_array_uget_borrowed(v_bs_1145_, v_i_1144_);
lean_inc(v___y_1151_);
lean_inc_ref(v___y_1150_);
lean_inc(v___y_1149_);
lean_inc_ref(v___y_1148_);
lean_inc(v___y_1147_);
lean_inc(v_v_1155_);
v___x_1156_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_1142_, v_v_1155_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1158_; lean_object* v_bs_x27_1159_; size_t v___x_1160_; size_t v___x_1161_; lean_object* v___x_1162_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref(v___x_1156_);
v___x_1158_ = lean_unsigned_to_nat(0u);
v_bs_x27_1159_ = lean_array_uset(v_bs_1145_, v_i_1144_, v___x_1158_);
v___x_1160_ = ((size_t)1ULL);
v___x_1161_ = lean_usize_add(v_i_1144_, v___x_1160_);
v___x_1162_ = lean_array_uset(v_bs_x27_1159_, v_i_1144_, v_a_1157_);
v_i_1144_ = v___x_1161_;
v_bs_1145_ = v___x_1162_;
goto _start;
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v_bs_1145_);
v_a_1164_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1156_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1156_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0___boxed(lean_object* v_pu_1172_, lean_object* v_sz_1173_, lean_object* v_i_1174_, lean_object* v_bs_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
uint8_t v_pu_boxed_1183_; size_t v_sz_boxed_1184_; size_t v_i_boxed_1185_; uint8_t v___y_368__boxed_1186_; lean_object* v_res_1187_; 
v_pu_boxed_1183_ = lean_unbox(v_pu_1172_);
v_sz_boxed_1184_ = lean_unbox_usize(v_sz_1173_);
lean_dec(v_sz_1173_);
v_i_boxed_1185_ = lean_unbox_usize(v_i_1174_);
lean_dec(v_i_1174_);
v___y_368__boxed_1186_ = lean_unbox(v___y_1176_);
v_res_1187_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_boxed_1183_, v_sz_boxed_1184_, v_i_boxed_1185_, v_bs_1175_, v___y_368__boxed_1186_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs(uint8_t v_pu_1188_, lean_object* v_args_1189_, uint8_t v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
size_t v_sz_1197_; size_t v___x_1198_; lean_object* v___x_1199_; 
v_sz_1197_ = lean_array_size(v_args_1189_);
v___x_1198_ = ((size_t)0ULL);
v___x_1199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_1188_, v_sz_1197_, v___x_1198_, v_args_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs___boxed(lean_object* v_pu_1200_, lean_object* v_args_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
uint8_t v_pu_boxed_1209_; uint8_t v_a_423__boxed_1210_; lean_object* v_res_1211_; 
v_pu_boxed_1209_ = lean_unbox(v_pu_1200_);
v_a_423__boxed_1210_ = lean_unbox(v_a_1202_);
v_res_1211_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_boxed_1209_, v_args_1201_, v_a_423__boxed_1210_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(uint8_t v_pu_1212_, lean_object* v_e_1213_, uint8_t v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_fvarId_1222_; lean_object* v___y_1223_; lean_object* v_args_1239_; uint8_t v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; 
switch(lean_obj_tag(v_e_1213_))
{
case 2:
{
lean_object* v_struct_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; 
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
v_struct_1264_ = lean_ctor_get(v_e_1213_, 2);
v___x_1265_ = lean_st_ref_get(v_a_1215_);
lean_dec(v_a_1215_);
v___x_1266_ = 1;
lean_inc(v_struct_1264_);
v___x_1267_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1265_, v_struct_1264_, v___x_1266_);
lean_dec(v___x_1265_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_fvarId_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1276_; 
v_fvarId_1268_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1270_ = v___x_1267_;
v_isShared_1271_ = v_isSharedCheck_1276_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_fvarId_1268_);
lean_dec(v___x_1267_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1276_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1272_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1212_, v_e_1213_, v_fvarId_1268_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 0, v___x_1272_);
v___x_1274_ = v___x_1270_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec_ref(v_e_1213_);
v___x_1277_ = lean_box(1);
v___x_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
return v___x_1278_;
}
}
case 3:
{
lean_object* v_args_1279_; lean_object* v___x_1280_; 
v_args_1279_ = lean_ctor_get(v_e_1213_, 2);
lean_inc_ref(v_args_1279_);
v___x_1280_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1212_, v_args_1279_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1289_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1285_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1212_, v_e_1213_, v_a_1281_);
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
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec_ref(v_e_1213_);
v_a_1290_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1280_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1280_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
case 4:
{
lean_object* v_fvarId_1298_; lean_object* v_args_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; lean_object* v___x_1302_; 
v_fvarId_1298_ = lean_ctor_get(v_e_1213_, 0);
v_args_1299_ = lean_ctor_get(v_e_1213_, 1);
v___x_1300_ = lean_st_ref_get(v_a_1215_);
v___x_1301_ = 1;
lean_inc(v_fvarId_1298_);
v___x_1302_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1300_, v_fvarId_1298_, v___x_1301_);
lean_dec(v___x_1300_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_fvarId_1303_; lean_object* v___x_1304_; 
v_fvarId_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_fvarId_1303_);
lean_dec_ref(v___x_1302_);
lean_inc_ref(v_args_1299_);
v___x_1304_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1212_, v_args_1299_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1313_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1307_ = v___x_1304_;
v_isShared_1308_ = v_isSharedCheck_1313_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1304_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1313_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1309_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_1212_, v_e_1213_, v_fvarId_1303_, v_a_1305_);
lean_dec_ref(v_e_1213_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v___x_1309_);
v___x_1311_ = v___x_1307_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_dec(v_fvarId_1303_);
lean_dec_ref(v_e_1213_);
v_a_1314_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1304_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1304_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_dec_ref(v_e_1213_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
v___x_1322_ = lean_box(1);
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
return v___x_1323_;
}
}
case 5:
{
lean_object* v_args_1324_; lean_object* v___x_1325_; 
v_args_1324_ = lean_ctor_get(v_e_1213_, 1);
lean_inc_ref(v_args_1324_);
v___x_1325_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1212_, v_args_1324_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1334_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1328_ = v___x_1325_;
v_isShared_1329_ = v_isSharedCheck_1334_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1334_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1330_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1212_, v_e_1213_, v_a_1326_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v___x_1330_);
v___x_1332_ = v___x_1328_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec_ref(v_e_1213_);
v_a_1335_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1325_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1325_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
case 6:
{
lean_object* v_var_1343_; 
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
v_var_1343_ = lean_ctor_get(v_e_1213_, 1);
lean_inc(v_var_1343_);
v_fvarId_1222_ = v_var_1343_;
v___y_1223_ = v_a_1215_;
goto v___jp_1221_;
}
case 7:
{
lean_object* v_var_1344_; 
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
v_var_1344_ = lean_ctor_get(v_e_1213_, 1);
lean_inc(v_var_1344_);
v_fvarId_1222_ = v_var_1344_;
v___y_1223_ = v_a_1215_;
goto v___jp_1221_;
}
case 8:
{
lean_object* v_var_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; lean_object* v___x_1348_; 
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
v_var_1345_ = lean_ctor_get(v_e_1213_, 2);
v___x_1346_ = lean_st_ref_get(v_a_1215_);
lean_dec(v_a_1215_);
v___x_1347_ = 1;
lean_inc(v_var_1345_);
v___x_1348_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1346_, v_var_1345_, v___x_1347_);
lean_dec(v___x_1346_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_fvarId_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1357_; 
v_fvarId_1349_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1351_ = v___x_1348_;
v_isShared_1352_ = v_isSharedCheck_1357_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_fvarId_1349_);
lean_dec(v___x_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1357_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1353_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1212_, v_e_1213_, v_fvarId_1349_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___x_1353_);
v___x_1355_ = v___x_1351_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_dec_ref(v_e_1213_);
v___x_1358_ = lean_box(1);
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
return v___x_1359_;
}
}
case 9:
{
lean_object* v_args_1360_; 
v_args_1360_ = lean_ctor_get(v_e_1213_, 1);
lean_inc_ref(v_args_1360_);
v_args_1239_ = v_args_1360_;
v___y_1240_ = v_a_1214_;
v___y_1241_ = v_a_1215_;
v___y_1242_ = v_a_1216_;
v___y_1243_ = v_a_1217_;
v___y_1244_ = v_a_1218_;
v___y_1245_ = v_a_1219_;
goto v___jp_1238_;
}
case 10:
{
lean_object* v_args_1361_; 
v_args_1361_ = lean_ctor_get(v_e_1213_, 1);
lean_inc_ref(v_args_1361_);
v_args_1239_ = v_args_1361_;
v___y_1240_ = v_a_1214_;
v___y_1241_ = v_a_1215_;
v___y_1242_ = v_a_1216_;
v___y_1243_ = v_a_1217_;
v___y_1244_ = v_a_1218_;
v___y_1245_ = v_a_1219_;
goto v___jp_1238_;
}
case 11:
{
lean_object* v_n_1362_; lean_object* v_var_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; lean_object* v___x_1366_; 
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
v_n_1362_ = lean_ctor_get(v_e_1213_, 0);
lean_inc(v_n_1362_);
v_var_1363_ = lean_ctor_get(v_e_1213_, 1);
v___x_1364_ = lean_st_ref_get(v_a_1215_);
lean_dec(v_a_1215_);
v___x_1365_ = 1;
lean_inc(v_var_1363_);
v___x_1366_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1364_, v_var_1363_, v___x_1365_);
lean_dec(v___x_1364_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_fvarId_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1375_; 
v_fvarId_1367_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1369_ = v___x_1366_;
v_isShared_1370_ = v_isSharedCheck_1375_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_fvarId_1367_);
lean_dec(v___x_1366_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1375_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1371_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_1212_, v_e_1213_, v_n_1362_, v_fvarId_1367_);
lean_dec_ref(v_e_1213_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1371_);
v___x_1373_ = v___x_1369_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec(v_n_1362_);
lean_dec_ref(v_e_1213_);
v___x_1376_ = lean_box(1);
v___x_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
return v___x_1377_;
}
}
case 12:
{
lean_object* v_var_1378_; lean_object* v_i_1379_; uint8_t v_updateHeader_1380_; lean_object* v_args_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; lean_object* v___x_1384_; 
v_var_1378_ = lean_ctor_get(v_e_1213_, 0);
v_i_1379_ = lean_ctor_get(v_e_1213_, 1);
lean_inc_ref(v_i_1379_);
v_updateHeader_1380_ = lean_ctor_get_uint8(v_e_1213_, sizeof(void*)*3);
v_args_1381_ = lean_ctor_get(v_e_1213_, 2);
v___x_1382_ = lean_st_ref_get(v_a_1215_);
v___x_1383_ = 1;
lean_inc(v_var_1378_);
v___x_1384_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1382_, v_var_1378_, v___x_1383_);
lean_dec(v___x_1382_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_fvarId_1385_; lean_object* v___x_1386_; 
v_fvarId_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_fvarId_1385_);
lean_dec_ref(v___x_1384_);
lean_inc_ref(v_args_1381_);
v___x_1386_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1212_, v_args_1381_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
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
v___x_1391_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_1212_, v_e_1213_, v_fvarId_1385_, v_i_1379_, v_updateHeader_1380_, v_a_1387_);
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
lean_dec_ref(v_i_1379_);
lean_dec_ref(v_e_1213_);
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
lean_dec_ref(v_i_1379_);
lean_dec_ref(v_e_1213_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
v___x_1404_ = lean_box(1);
v___x_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
return v___x_1405_;
}
}
case 13:
{
lean_object* v_ty_1406_; lean_object* v_fvarId_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; lean_object* v___x_1410_; 
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
v_ty_1406_ = lean_ctor_get(v_e_1213_, 0);
lean_inc_ref(v_ty_1406_);
v_fvarId_1407_ = lean_ctor_get(v_e_1213_, 1);
v___x_1408_ = lean_st_ref_get(v_a_1215_);
lean_dec(v_a_1215_);
v___x_1409_ = 1;
lean_inc(v_fvarId_1407_);
v___x_1410_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1408_, v_fvarId_1407_, v___x_1409_);
lean_dec(v___x_1408_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_fvarId_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1419_; 
v_fvarId_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1419_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_fvarId_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1419_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1415_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_1212_, v_e_1213_, v_ty_1406_, v_fvarId_1411_);
lean_dec_ref(v_e_1213_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v___x_1415_);
v___x_1417_ = v___x_1413_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
lean_dec_ref(v_ty_1406_);
lean_dec_ref(v_e_1213_);
v___x_1420_ = lean_box(1);
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
return v___x_1421_;
}
}
case 14:
{
lean_object* v_fvarId_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; lean_object* v___x_1425_; 
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
v_fvarId_1422_ = lean_ctor_get(v_e_1213_, 0);
v___x_1423_ = lean_st_ref_get(v_a_1215_);
lean_dec(v_a_1215_);
v___x_1424_ = 1;
lean_inc(v_fvarId_1422_);
v___x_1425_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1423_, v_fvarId_1422_, v___x_1424_);
lean_dec(v___x_1423_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_fvarId_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1434_; 
v_fvarId_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1434_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_fvarId_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1434_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1430_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_1212_, v_e_1213_, v_fvarId_1426_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1430_);
v___x_1432_ = v___x_1428_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
else
{
lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1442_; 
v_isSharedCheck_1442_ = !lean_is_exclusive(v_e_1213_);
if (v_isSharedCheck_1442_ == 0)
{
lean_object* v_unused_1443_; 
v_unused_1443_ = lean_ctor_get(v_e_1213_, 0);
lean_dec(v_unused_1443_);
v___x_1436_ = v_e_1213_;
v_isShared_1437_ = v_isSharedCheck_1442_;
goto v_resetjp_1435_;
}
else
{
lean_dec(v_e_1213_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1442_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1438_ = lean_box(1);
if (v_isShared_1437_ == 0)
{
lean_ctor_set_tag(v___x_1436_, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1438_);
v___x_1440_ = v___x_1436_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
case 15:
{
lean_object* v_fvarId_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; lean_object* v___x_1447_; 
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
v_fvarId_1444_ = lean_ctor_get(v_e_1213_, 0);
v___x_1445_ = lean_st_ref_get(v_a_1215_);
lean_dec(v_a_1215_);
v___x_1446_ = 1;
lean_inc(v_fvarId_1444_);
v___x_1447_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1445_, v_fvarId_1444_, v___x_1446_);
lean_dec(v___x_1445_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_fvarId_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1456_; 
v_fvarId_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1456_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_fvarId_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1456_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1454_; 
v___x_1452_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_1212_, v_e_1213_, v_fvarId_1448_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1452_);
v___x_1454_ = v___x_1450_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1452_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
else
{
lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1464_; 
v_isSharedCheck_1464_ = !lean_is_exclusive(v_e_1213_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; 
v_unused_1465_ = lean_ctor_get(v_e_1213_, 0);
lean_dec(v_unused_1465_);
v___x_1458_ = v_e_1213_;
v_isShared_1459_ = v_isSharedCheck_1464_;
goto v_resetjp_1457_;
}
else
{
lean_dec(v_e_1213_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1464_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1460_ = lean_box(1);
if (v_isShared_1459_ == 0)
{
lean_ctor_set_tag(v___x_1458_, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1460_);
v___x_1462_ = v___x_1458_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
default: 
{
lean_object* v___x_1466_; 
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v_e_1213_);
return v___x_1466_;
}
}
v___jp_1221_:
{
lean_object* v___x_1224_; uint8_t v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = lean_st_ref_get(v___y_1223_);
lean_dec(v___y_1223_);
v___x_1225_ = 1;
v___x_1226_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1224_, v_fvarId_1222_, v___x_1225_);
lean_dec(v___x_1224_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_fvarId_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1235_; 
v_fvarId_1227_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1229_ = v___x_1226_;
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_fvarId_1227_);
lean_dec(v___x_1226_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1231_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1212_, v_e_1213_, v_fvarId_1227_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1231_);
v___x_1233_ = v___x_1229_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
lean_dec(v_e_1213_);
v___x_1236_ = lean_box(1);
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
return v___x_1237_;
}
}
v___jp_1238_:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1212_, v_args_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1255_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1255_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1255_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1251_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1212_, v_e_1213_, v_a_1247_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1251_);
v___x_1253_ = v___x_1249_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec(v_e_1213_);
v_a_1256_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1246_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1246_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue___boxed(lean_object* v_pu_1467_, lean_object* v_e_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
uint8_t v_pu_boxed_1476_; uint8_t v_a_11661__boxed_1477_; lean_object* v_res_1478_; 
v_pu_boxed_1476_ = lean_unbox(v_pu_1467_);
v_a_11661__boxed_1477_ = lean_unbox(v_a_1469_);
v_res_1478_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_boxed_1476_, v_e_1468_, v_a_11661__boxed_1477_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(uint8_t v_pu_1479_, lean_object* v_decl_1480_, uint8_t v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v_fvarId_1488_; lean_object* v_binderName_1489_; lean_object* v_type_1490_; lean_object* v_value_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1549_; 
v_fvarId_1488_ = lean_ctor_get(v_decl_1480_, 0);
v_binderName_1489_ = lean_ctor_get(v_decl_1480_, 1);
v_type_1490_ = lean_ctor_get(v_decl_1480_, 2);
v_value_1491_ = lean_ctor_get(v_decl_1480_, 3);
v_isSharedCheck_1549_ = !lean_is_exclusive(v_decl_1480_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1493_ = v_decl_1480_;
v_isShared_1494_ = v_isSharedCheck_1549_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_value_1491_);
lean_inc(v_type_1490_);
lean_inc(v_binderName_1489_);
lean_inc(v_fvarId_1488_);
lean_dec(v_decl_1480_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1549_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v_a_1496_; lean_object* v___x_1497_; 
v___x_1495_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_1489_, v_a_1481_, v_a_1484_);
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1496_);
lean_dec_ref(v___x_1495_);
lean_inc(v_a_1486_);
lean_inc_ref(v_a_1485_);
lean_inc(v_a_1484_);
lean_inc_ref(v_a_1483_);
lean_inc(v_a_1482_);
v___x_1497_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1479_, v_type_1490_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1499_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref(v___x_1497_);
lean_inc(v_a_1486_);
lean_inc_ref(v_a_1485_);
lean_inc(v_a_1484_);
lean_inc_ref(v_a_1483_);
lean_inc(v_a_1482_);
v___x_1499_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_1479_, v_value_1491_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1501_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref(v___x_1499_);
v___x_1501_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_1488_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec_ref(v_a_1483_);
lean_dec(v_a_1482_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1524_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1524_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1524_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1506_; lean_object* v_lctx_1507_; lean_object* v_nextIdx_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1523_; 
v___x_1506_ = lean_st_ref_take(v_a_1484_);
v_lctx_1507_ = lean_ctor_get(v___x_1506_, 0);
v_nextIdx_1508_ = lean_ctor_get(v___x_1506_, 1);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1510_ = v___x_1506_;
v_isShared_1511_ = v_isSharedCheck_1523_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_nextIdx_1508_);
lean_inc(v_lctx_1507_);
lean_dec(v___x_1506_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1523_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 3, v_a_1500_);
lean_ctor_set(v___x_1493_, 2, v_a_1498_);
lean_ctor_set(v___x_1493_, 1, v_a_1496_);
lean_ctor_set(v___x_1493_, 0, v_a_1502_);
v___x_1513_ = v___x_1493_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1502_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_a_1496_);
lean_ctor_set(v_reuseFailAlloc_1522_, 2, v_a_1498_);
lean_ctor_set(v_reuseFailAlloc_1522_, 3, v_a_1500_);
v___x_1513_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1514_; lean_object* v___x_1516_; 
lean_inc_ref(v___x_1513_);
v___x_1514_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_1479_, v_lctx_1507_, v___x_1513_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v___x_1514_);
v___x_1516_ = v___x_1510_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_nextIdx_1508_);
v___x_1516_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1517_ = lean_st_ref_set(v_a_1484_, v___x_1516_);
lean_dec(v_a_1484_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1513_);
v___x_1519_ = v___x_1504_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1513_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec(v_a_1500_);
lean_dec(v_a_1498_);
lean_dec(v_a_1496_);
lean_del_object(v___x_1493_);
lean_dec(v_a_1484_);
v_a_1525_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1501_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1501_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec(v_a_1498_);
lean_dec(v_a_1496_);
lean_del_object(v___x_1493_);
lean_dec(v_fvarId_1488_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec(v_a_1482_);
v_a_1533_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1499_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1499_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec(v_a_1496_);
lean_del_object(v___x_1493_);
lean_dec(v_value_1491_);
lean_dec(v_fvarId_1488_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec(v_a_1482_);
v_a_1541_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1497_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1497_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(lean_object* v_pu_1550_, lean_object* v_decl_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
uint8_t v_pu_boxed_1559_; uint8_t v_a_1743__boxed_1560_; lean_object* v_res_1561_; 
v_pu_boxed_1559_ = lean_unbox(v_pu_1550_);
v_a_1743__boxed_1560_ = lean_unbox(v_a_1552_);
v_res_1561_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_boxed_1559_, v_decl_1551_, v_a_1743__boxed_1560_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(uint8_t v_pu_1562_, size_t v_sz_1563_, size_t v_i_1564_, lean_object* v_bs_1565_, uint8_t v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
uint8_t v___x_1573_; 
v___x_1573_ = lean_usize_dec_lt(v_i_1564_, v_sz_1563_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; 
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v_bs_1565_);
return v___x_1574_;
}
else
{
lean_object* v_v_1575_; lean_object* v___x_1576_; 
v_v_1575_ = lean_array_uget_borrowed(v_bs_1565_, v_i_1564_);
lean_inc(v___y_1571_);
lean_inc_ref(v___y_1570_);
lean_inc(v___y_1569_);
lean_inc_ref(v___y_1568_);
lean_inc(v___y_1567_);
lean_inc(v_v_1575_);
v___x_1576_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_1562_, v_v_1575_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1578_; lean_object* v_bs_x27_1579_; size_t v___x_1580_; size_t v___x_1581_; lean_object* v___x_1582_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref(v___x_1576_);
v___x_1578_ = lean_unsigned_to_nat(0u);
v_bs_x27_1579_ = lean_array_uset(v_bs_1565_, v_i_1564_, v___x_1578_);
v___x_1580_ = ((size_t)1ULL);
v___x_1581_ = lean_usize_add(v_i_1564_, v___x_1580_);
v___x_1582_ = lean_array_uset(v_bs_x27_1579_, v_i_1564_, v_a_1577_);
v_i_1564_ = v___x_1581_;
v_bs_1565_ = v___x_1582_;
goto _start;
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v_bs_1565_);
v_a_1584_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1576_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1576_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0___boxed(lean_object* v_pu_1592_, lean_object* v_sz_1593_, lean_object* v_i_1594_, lean_object* v_bs_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
uint8_t v_pu_boxed_1603_; size_t v_sz_boxed_1604_; size_t v_i_boxed_1605_; uint8_t v___y_27340__boxed_1606_; lean_object* v_res_1607_; 
v_pu_boxed_1603_ = lean_unbox(v_pu_1592_);
v_sz_boxed_1604_ = lean_unbox_usize(v_sz_1593_);
lean_dec(v_sz_1593_);
v_i_boxed_1605_ = lean_unbox_usize(v_i_1594_);
lean_dec(v_i_1594_);
v___y_27340__boxed_1606_ = lean_unbox(v___y_1596_);
v_res_1607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_boxed_1603_, v_sz_boxed_1604_, v_i_boxed_1605_, v_bs_1595_, v___y_27340__boxed_1606_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(uint8_t v_pu_1608_, size_t v_sz_1609_, size_t v_i_1610_, lean_object* v_bs_1611_, uint8_t v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
uint8_t v___x_1619_; 
v___x_1619_ = lean_usize_dec_lt(v_i_1610_, v_sz_1609_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; 
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
v___x_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1620_, 0, v_bs_1611_);
return v___x_1620_;
}
else
{
lean_object* v_v_1621_; lean_object* v___x_1622_; lean_object* v_bs_x27_1623_; lean_object* v_a_1625_; 
v_v_1621_ = lean_array_uget(v_bs_1611_, v_i_1610_);
v___x_1622_ = lean_unsigned_to_nat(0u);
v_bs_x27_1623_ = lean_array_uset(v_bs_1611_, v_i_1610_, v___x_1622_);
switch(lean_obj_tag(v_v_1621_))
{
case 0:
{
lean_object* v_ctorName_1630_; lean_object* v_params_1631_; lean_object* v_code_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1653_; 
v_ctorName_1630_ = lean_ctor_get(v_v_1621_, 0);
v_params_1631_ = lean_ctor_get(v_v_1621_, 1);
v_code_1632_ = lean_ctor_get(v_v_1621_, 2);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_v_1621_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1634_ = v_v_1621_;
v_isShared_1635_ = v_isSharedCheck_1653_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_code_1632_);
lean_inc(v_params_1631_);
lean_inc(v_ctorName_1630_);
lean_dec(v_v_1621_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1653_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
size_t v_sz_1636_; size_t v___x_1637_; lean_object* v___x_1638_; 
v_sz_1636_ = lean_array_size(v_params_1631_);
v___x_1637_ = ((size_t)0ULL);
lean_inc(v___y_1617_);
lean_inc_ref(v___y_1616_);
lean_inc(v___y_1615_);
lean_inc_ref(v___y_1614_);
lean_inc(v___y_1613_);
v___x_1638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_1608_, v_sz_1636_, v___x_1637_, v_params_1631_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1640_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref(v___x_1638_);
lean_inc(v___y_1617_);
lean_inc_ref(v___y_1616_);
lean_inc(v___y_1615_);
lean_inc_ref(v___y_1614_);
lean_inc(v___y_1613_);
v___x_1640_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1608_, v_code_1632_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1643_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref(v___x_1640_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 2, v_a_1641_);
lean_ctor_set(v___x_1634_, 1, v_a_1639_);
v___x_1643_ = v___x_1634_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_ctorName_1630_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_a_1639_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_a_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
v_a_1625_ = v___x_1643_;
goto v___jp_1624_;
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_dec(v_a_1639_);
lean_del_object(v___x_1634_);
lean_dec(v_ctorName_1630_);
lean_dec_ref(v_bs_x27_1623_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
v_a_1645_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1640_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1640_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
else
{
lean_del_object(v___x_1634_);
lean_dec_ref(v_code_1632_);
lean_dec(v_ctorName_1630_);
lean_dec_ref(v_bs_x27_1623_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
return v___x_1638_;
}
}
}
case 1:
{
lean_object* v_info_1654_; lean_object* v_code_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1672_; 
v_info_1654_ = lean_ctor_get(v_v_1621_, 0);
v_code_1655_ = lean_ctor_get(v_v_1621_, 1);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_v_1621_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1657_ = v_v_1621_;
v_isShared_1658_ = v_isSharedCheck_1672_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_code_1655_);
lean_inc(v_info_1654_);
lean_dec(v_v_1621_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1672_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; 
lean_inc(v___y_1617_);
lean_inc_ref(v___y_1616_);
lean_inc(v___y_1615_);
lean_inc_ref(v___y_1614_);
lean_inc(v___y_1613_);
v___x_1659_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1608_, v_code_1655_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1662_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref(v___x_1659_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 1, v_a_1660_);
v___x_1662_ = v___x_1657_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_info_1654_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_a_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
v_a_1625_ = v___x_1662_;
goto v___jp_1624_;
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_del_object(v___x_1657_);
lean_dec_ref(v_info_1654_);
lean_dec_ref(v_bs_x27_1623_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
v_a_1664_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1659_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1659_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
}
default: 
{
lean_object* v_code_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1690_; 
v_code_1673_ = lean_ctor_get(v_v_1621_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_v_1621_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1675_ = v_v_1621_;
v_isShared_1676_ = v_isSharedCheck_1690_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_code_1673_);
lean_dec(v_v_1621_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1690_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; 
lean_inc(v___y_1617_);
lean_inc_ref(v___y_1616_);
lean_inc(v___y_1615_);
lean_inc_ref(v___y_1614_);
lean_inc(v___y_1613_);
v___x_1677_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1608_, v_code_1673_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1680_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_a_1678_);
lean_dec_ref(v___x_1677_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v_a_1678_);
v___x_1680_ = v___x_1675_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
v_a_1625_ = v___x_1680_;
goto v___jp_1624_;
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_del_object(v___x_1675_);
lean_dec_ref(v_bs_x27_1623_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
v_a_1682_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1677_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1677_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
}
v___jp_1624_:
{
size_t v___x_1626_; size_t v___x_1627_; lean_object* v___x_1628_; 
v___x_1626_ = ((size_t)1ULL);
v___x_1627_ = lean_usize_add(v_i_1610_, v___x_1626_);
v___x_1628_ = lean_array_uset(v_bs_x27_1623_, v_i_1610_, v_a_1625_);
v_i_1610_ = v___x_1627_;
v_bs_1611_ = v___x_1628_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t v_pu_1691_, lean_object* v_code_1692_, uint8_t v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
switch(lean_obj_tag(v_code_1692_))
{
case 0:
{
lean_object* v_decl_1700_; lean_object* v_k_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1727_; 
v_decl_1700_ = lean_ctor_get(v_code_1692_, 0);
v_k_1701_ = lean_ctor_get(v_code_1692_, 1);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_code_1692_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1703_ = v_code_1692_;
v_isShared_1704_ = v_isSharedCheck_1727_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_k_1701_);
lean_inc(v_decl_1700_);
lean_dec(v_code_1692_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1727_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; 
lean_inc(v_a_1698_);
lean_inc_ref(v_a_1697_);
lean_inc(v_a_1696_);
lean_inc_ref(v_a_1695_);
lean_inc(v_a_1694_);
v___x_1705_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_1691_, v_decl_1700_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1707_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref(v___x_1705_);
v___x_1707_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1691_, v_k_1701_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1718_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1710_ = v___x_1707_;
v_isShared_1711_ = v_isSharedCheck_1718_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1718_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 1, v_a_1708_);
lean_ctor_set(v___x_1703_, 0, v_a_1706_);
v___x_1713_ = v___x_1703_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1706_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_object* v___x_1715_; 
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1713_);
v___x_1715_ = v___x_1710_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
else
{
lean_dec(v_a_1706_);
lean_del_object(v___x_1703_);
return v___x_1707_;
}
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_del_object(v___x_1703_);
lean_dec_ref(v_k_1701_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
v_a_1719_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1705_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1705_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_1728_; lean_object* v_k_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1755_; 
v_decl_1728_ = lean_ctor_get(v_code_1692_, 0);
v_k_1729_ = lean_ctor_get(v_code_1692_, 1);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_code_1692_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1731_ = v_code_1692_;
v_isShared_1732_ = v_isSharedCheck_1755_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_k_1729_);
lean_inc(v_decl_1728_);
lean_dec(v_code_1692_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1755_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; 
lean_inc(v_a_1698_);
lean_inc_ref(v_a_1697_);
lean_inc(v_a_1696_);
lean_inc_ref(v_a_1695_);
lean_inc(v_a_1694_);
v___x_1733_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1691_, v_decl_1728_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v___x_1735_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1734_);
lean_dec_ref(v___x_1733_);
v___x_1735_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1691_, v_k_1729_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1746_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1746_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1746_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 1, v_a_1736_);
lean_ctor_set(v___x_1731_, 0, v_a_1734_);
v___x_1741_ = v___x_1731_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1734_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1743_; 
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v___x_1741_);
v___x_1743_ = v___x_1738_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
else
{
lean_dec(v_a_1734_);
lean_del_object(v___x_1731_);
return v___x_1735_;
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_del_object(v___x_1731_);
lean_dec_ref(v_k_1729_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
v_a_1747_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1733_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1733_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
case 2:
{
lean_object* v_decl_1756_; lean_object* v_k_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1783_; 
v_decl_1756_ = lean_ctor_get(v_code_1692_, 0);
v_k_1757_ = lean_ctor_get(v_code_1692_, 1);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_code_1692_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1759_ = v_code_1692_;
v_isShared_1760_ = v_isSharedCheck_1783_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_k_1757_);
lean_inc(v_decl_1756_);
lean_dec(v_code_1692_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1783_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; 
lean_inc(v_a_1698_);
lean_inc_ref(v_a_1697_);
lean_inc(v_a_1696_);
lean_inc_ref(v_a_1695_);
lean_inc(v_a_1694_);
v___x_1761_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1691_, v_decl_1756_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref(v___x_1761_);
v___x_1763_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1691_, v_k_1757_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1774_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1766_ = v___x_1763_;
v_isShared_1767_ = v_isSharedCheck_1774_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1763_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1774_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 1, v_a_1764_);
lean_ctor_set(v___x_1759_, 0, v_a_1762_);
v___x_1769_ = v___x_1759_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1762_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1771_; 
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v___x_1769_);
v___x_1771_ = v___x_1766_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
else
{
lean_dec(v_a_1762_);
lean_del_object(v___x_1759_);
return v___x_1763_;
}
}
else
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
lean_del_object(v___x_1759_);
lean_dec_ref(v_k_1757_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
v_a_1775_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1761_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1761_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_1784_; lean_object* v_args_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1814_; 
v_fvarId_1784_ = lean_ctor_get(v_code_1692_, 0);
v_args_1785_ = lean_ctor_get(v_code_1692_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_code_1692_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1787_ = v_code_1692_;
v_isShared_1788_ = v_isSharedCheck_1814_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_args_1785_);
lean_inc(v_fvarId_1784_);
lean_dec(v_code_1692_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1814_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; uint8_t v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = lean_st_ref_get(v_a_1694_);
v___x_1790_ = 1;
v___x_1791_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1789_, v_fvarId_1784_, v___x_1790_);
lean_dec(v___x_1789_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_fvarId_1792_; lean_object* v___x_1793_; 
v_fvarId_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_fvarId_1792_);
lean_dec_ref(v___x_1791_);
v___x_1793_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1691_, v_args_1785_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1804_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1796_ = v___x_1793_;
v_isShared_1797_ = v_isSharedCheck_1804_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1793_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1804_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 1, v_a_1794_);
lean_ctor_set(v___x_1787_, 0, v_fvarId_1792_);
v___x_1799_ = v___x_1787_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_fvarId_1792_);
lean_ctor_set(v_reuseFailAlloc_1803_, 1, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
lean_object* v___x_1801_; 
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v___x_1799_);
v___x_1801_ = v___x_1796_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_dec(v_fvarId_1792_);
lean_del_object(v___x_1787_);
v_a_1805_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1793_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1793_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
else
{
lean_object* v___x_1813_; 
lean_del_object(v___x_1787_);
lean_dec_ref(v_args_1785_);
lean_dec(v_a_1694_);
v___x_1813_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1691_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
return v___x_1813_;
}
}
}
case 4:
{
lean_object* v_cases_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1867_; 
v_cases_1815_ = lean_ctor_get(v_code_1692_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_code_1692_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1817_ = v_code_1692_;
v_isShared_1818_ = v_isSharedCheck_1867_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_cases_1815_);
lean_dec(v_code_1692_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1867_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v_typeName_1819_; lean_object* v_resultType_1820_; lean_object* v_discr_1821_; lean_object* v_alts_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1866_; 
v_typeName_1819_ = lean_ctor_get(v_cases_1815_, 0);
v_resultType_1820_ = lean_ctor_get(v_cases_1815_, 1);
v_discr_1821_ = lean_ctor_get(v_cases_1815_, 2);
v_alts_1822_ = lean_ctor_get(v_cases_1815_, 3);
v_isSharedCheck_1866_ = !lean_is_exclusive(v_cases_1815_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1824_ = v_cases_1815_;
v_isShared_1825_ = v_isSharedCheck_1866_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_alts_1822_);
lean_inc(v_discr_1821_);
lean_inc(v_resultType_1820_);
lean_inc(v_typeName_1819_);
lean_dec(v_cases_1815_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1866_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; uint8_t v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = lean_st_ref_get(v_a_1694_);
v___x_1827_ = 1;
v___x_1828_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1826_, v_discr_1821_, v___x_1827_);
lean_dec(v___x_1826_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_fvarId_1829_; lean_object* v___x_1830_; 
v_fvarId_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_fvarId_1829_);
lean_dec_ref(v___x_1828_);
lean_inc(v_a_1698_);
lean_inc_ref(v_a_1697_);
lean_inc(v_a_1696_);
lean_inc_ref(v_a_1695_);
lean_inc(v_a_1694_);
v___x_1830_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1691_, v_resultType_1820_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; size_t v_sz_1832_; size_t v___x_1833_; lean_object* v___x_1834_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref(v___x_1830_);
v_sz_1832_ = lean_array_size(v_alts_1822_);
v___x_1833_ = ((size_t)0ULL);
v___x_1834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_1691_, v_sz_1832_, v___x_1833_, v_alts_1822_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1848_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1848_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1848_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 3, v_a_1835_);
lean_ctor_set(v___x_1824_, 2, v_fvarId_1829_);
lean_ctor_set(v___x_1824_, 1, v_a_1831_);
v___x_1840_ = v___x_1824_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_typeName_1819_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_a_1831_);
lean_ctor_set(v_reuseFailAlloc_1847_, 2, v_fvarId_1829_);
lean_ctor_set(v_reuseFailAlloc_1847_, 3, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1842_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1840_);
v___x_1842_ = v___x_1817_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1844_; 
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1842_);
v___x_1844_ = v___x_1837_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v_a_1831_);
lean_dec(v_fvarId_1829_);
lean_del_object(v___x_1824_);
lean_dec(v_typeName_1819_);
lean_del_object(v___x_1817_);
v_a_1849_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1834_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1834_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec(v_fvarId_1829_);
lean_del_object(v___x_1824_);
lean_dec_ref(v_alts_1822_);
lean_dec(v_typeName_1819_);
lean_del_object(v___x_1817_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
v_a_1857_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1830_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1830_);
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
else
{
lean_object* v___x_1865_; 
lean_del_object(v___x_1824_);
lean_dec_ref(v_alts_1822_);
lean_dec_ref(v_resultType_1820_);
lean_dec(v_typeName_1819_);
lean_del_object(v___x_1817_);
lean_dec(v_a_1694_);
v___x_1865_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1691_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
return v___x_1865_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1887_; 
v_fvarId_1868_ = lean_ctor_get(v_code_1692_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_code_1692_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1870_ = v_code_1692_;
v_isShared_1871_ = v_isSharedCheck_1887_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_fvarId_1868_);
lean_dec(v_code_1692_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1887_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1872_; uint8_t v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = lean_st_ref_get(v_a_1694_);
lean_dec(v_a_1694_);
v___x_1873_ = 1;
v___x_1874_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1872_, v_fvarId_1868_, v___x_1873_);
lean_dec(v___x_1872_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_fvarId_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1885_; 
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
v_fvarId_1875_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1877_ = v___x_1874_;
v_isShared_1878_ = v_isSharedCheck_1885_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_fvarId_1875_);
lean_dec(v___x_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1885_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v_fvarId_1875_);
v___x_1880_ = v___x_1870_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_fvarId_1875_);
v___x_1880_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1882_; 
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1880_);
v___x_1882_ = v___x_1877_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
else
{
lean_object* v___x_1886_; 
lean_del_object(v___x_1870_);
v___x_1886_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1691_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
return v___x_1886_;
}
}
}
case 6:
{
lean_object* v_type_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1912_; 
v_type_1888_ = lean_ctor_get(v_code_1692_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_code_1692_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1890_ = v_code_1692_;
v_isShared_1891_ = v_isSharedCheck_1912_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_type_1888_);
lean_dec(v_code_1692_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1912_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1892_; 
v___x_1892_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1691_, v_type_1888_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1903_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1903_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1903_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v_a_1893_);
v___x_1898_ = v___x_1890_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1900_; 
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v___x_1898_);
v___x_1900_ = v___x_1895_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_del_object(v___x_1890_);
v_a_1904_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1892_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1892_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_1913_; lean_object* v_i_1914_; lean_object* v_y_1915_; lean_object* v_k_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1939_; 
v_fvarId_1913_ = lean_ctor_get(v_code_1692_, 0);
v_i_1914_ = lean_ctor_get(v_code_1692_, 1);
v_y_1915_ = lean_ctor_get(v_code_1692_, 2);
v_k_1916_ = lean_ctor_get(v_code_1692_, 3);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_code_1692_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1918_ = v_code_1692_;
v_isShared_1919_ = v_isSharedCheck_1939_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_k_1916_);
lean_inc(v_y_1915_);
lean_inc(v_i_1914_);
lean_inc(v_fvarId_1913_);
lean_dec(v_code_1692_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1939_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; uint8_t v___x_1921_; lean_object* v___x_1922_; 
v___x_1920_ = lean_st_ref_get(v_a_1694_);
v___x_1921_ = 1;
v___x_1922_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1920_, v_fvarId_1913_, v___x_1921_);
lean_dec(v___x_1920_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_fvarId_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_fvarId_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_fvarId_1923_);
lean_dec_ref(v___x_1922_);
v___x_1924_ = lean_st_ref_get(v_a_1694_);
v___x_1925_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1691_, v___x_1924_, v_y_1915_, v___x_1921_);
lean_dec(v___x_1924_);
v___x_1926_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1691_, v_k_1916_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1937_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1929_ = v___x_1926_;
v_isShared_1930_ = v_isSharedCheck_1937_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1926_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1937_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 3, v_a_1927_);
lean_ctor_set(v___x_1918_, 2, v___x_1925_);
lean_ctor_set(v___x_1918_, 0, v_fvarId_1923_);
v___x_1932_ = v___x_1918_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_fvarId_1923_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_i_1914_);
lean_ctor_set(v_reuseFailAlloc_1936_, 2, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1936_, 3, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1934_; 
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 0, v___x_1932_);
v___x_1934_ = v___x_1929_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1932_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
else
{
lean_dec(v___x_1925_);
lean_dec(v_fvarId_1923_);
lean_del_object(v___x_1918_);
lean_dec(v_i_1914_);
return v___x_1926_;
}
}
else
{
lean_object* v___x_1938_; 
lean_del_object(v___x_1918_);
lean_dec_ref(v_k_1916_);
lean_dec(v_y_1915_);
lean_dec(v_i_1914_);
lean_dec(v_a_1694_);
v___x_1938_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1691_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
return v___x_1938_;
}
}
}
case 8:
{
lean_object* v_fvarId_1940_; lean_object* v_i_1941_; lean_object* v_y_1942_; lean_object* v_k_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1968_; 
v_fvarId_1940_ = lean_ctor_get(v_code_1692_, 0);
v_i_1941_ = lean_ctor_get(v_code_1692_, 1);
v_y_1942_ = lean_ctor_get(v_code_1692_, 2);
v_k_1943_ = lean_ctor_get(v_code_1692_, 3);
v_isSharedCheck_1968_ = !lean_is_exclusive(v_code_1692_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1945_ = v_code_1692_;
v_isShared_1946_ = v_isSharedCheck_1968_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_k_1943_);
lean_inc(v_y_1942_);
lean_inc(v_i_1941_);
lean_inc(v_fvarId_1940_);
lean_dec(v_code_1692_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1968_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1947_; uint8_t v___x_1948_; lean_object* v___x_1949_; 
v___x_1947_ = lean_st_ref_get(v_a_1694_);
v___x_1948_ = 1;
v___x_1949_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1947_, v_fvarId_1940_, v___x_1948_);
lean_dec(v___x_1947_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_fvarId_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v_fvarId_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_fvarId_1950_);
lean_dec_ref(v___x_1949_);
v___x_1951_ = lean_st_ref_get(v_a_1694_);
v___x_1952_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1951_, v_y_1942_, v___x_1948_);
lean_dec(v___x_1951_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_fvarId_1953_; lean_object* v___x_1954_; 
v_fvarId_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_fvarId_1953_);
lean_dec_ref(v___x_1952_);
v___x_1954_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1691_, v_k_1943_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1965_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1965_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1965_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 3, v_a_1955_);
lean_ctor_set(v___x_1945_, 2, v_fvarId_1953_);
lean_ctor_set(v___x_1945_, 0, v_fvarId_1950_);
v___x_1960_ = v___x_1945_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_fvarId_1950_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_i_1941_);
lean_ctor_set(v_reuseFailAlloc_1964_, 2, v_fvarId_1953_);
lean_ctor_set(v_reuseFailAlloc_1964_, 3, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1962_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1960_);
v___x_1962_ = v___x_1957_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
else
{
lean_dec(v_fvarId_1953_);
lean_dec(v_fvarId_1950_);
lean_del_object(v___x_1945_);
lean_dec(v_i_1941_);
return v___x_1954_;
}
}
else
{
lean_object* v___x_1966_; 
lean_dec(v_fvarId_1950_);
lean_del_object(v___x_1945_);
lean_dec_ref(v_k_1943_);
lean_dec(v_i_1941_);
lean_dec(v_a_1694_);
v___x_1966_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1691_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
return v___x_1966_;
}
}
else
{
lean_object* v___x_1967_; 
lean_del_object(v___x_1945_);
lean_dec_ref(v_k_1943_);
lean_dec(v_y_1942_);
lean_dec(v_i_1941_);
lean_dec(v_a_1694_);
v___x_1967_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1691_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
return v___x_1967_;
}
}
}
case 9:
{
lean_object* v_fvarId_1969_; lean_object* v_i_1970_; lean_object* v_offset_1971_; lean_object* v_y_1972_; lean_object* v_ty_1973_; lean_object* v_k_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_2009_; 
v_fvarId_1969_ = lean_ctor_get(v_code_1692_, 0);
v_i_1970_ = lean_ctor_get(v_code_1692_, 1);
v_offset_1971_ = lean_ctor_get(v_code_1692_, 2);
v_y_1972_ = lean_ctor_get(v_code_1692_, 3);
v_ty_1973_ = lean_ctor_get(v_code_1692_, 4);
v_k_1974_ = lean_ctor_get(v_code_1692_, 5);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_code_1692_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_1976_ = v_code_1692_;
v_isShared_1977_ = v_isSharedCheck_2009_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_k_1974_);
lean_inc(v_ty_1973_);
lean_inc(v_y_1972_);
lean_inc(v_offset_1971_);
lean_inc(v_i_1970_);
lean_inc(v_fvarId_1969_);
lean_dec(v_code_1692_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_2009_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; uint8_t v___x_1979_; lean_object* v___x_1980_; 
v___x_1978_ = lean_st_ref_get(v_a_1694_);
v___x_1979_ = 1;
v___x_1980_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1978_, v_fvarId_1969_, v___x_1979_);
lean_dec(v___x_1978_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_fvarId_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v_fvarId_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_fvarId_1981_);
lean_dec_ref(v___x_1980_);
v___x_1982_ = lean_st_ref_get(v_a_1694_);
v___x_1983_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1982_, v_y_1972_, v___x_1979_);
lean_dec(v___x_1982_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_fvarId_1984_; lean_object* v___x_1985_; 
v_fvarId_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_fvarId_1984_);
lean_dec_ref(v___x_1983_);
lean_inc(v_a_1698_);
lean_inc_ref(v_a_1697_);
lean_inc(v_a_1696_);
lean_inc_ref(v_a_1695_);
lean_inc(v_a_1694_);
v___x_1985_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1691_, v_ty_1973_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; lean_object* v___x_1987_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_a_1986_);
lean_dec_ref(v___x_1985_);
v___x_1987_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1691_, v_k_1974_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1998_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_1998_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1998_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 5, v_a_1988_);
lean_ctor_set(v___x_1976_, 4, v_a_1986_);
lean_ctor_set(v___x_1976_, 3, v_fvarId_1984_);
lean_ctor_set(v___x_1976_, 0, v_fvarId_1981_);
v___x_1993_ = v___x_1976_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_fvarId_1981_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v_i_1970_);
lean_ctor_set(v_reuseFailAlloc_1997_, 2, v_offset_1971_);
lean_ctor_set(v_reuseFailAlloc_1997_, 3, v_fvarId_1984_);
lean_ctor_set(v_reuseFailAlloc_1997_, 4, v_a_1986_);
lean_ctor_set(v_reuseFailAlloc_1997_, 5, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1995_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_1993_);
v___x_1995_ = v___x_1990_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
else
{
lean_dec(v_a_1986_);
lean_dec(v_fvarId_1984_);
lean_dec(v_fvarId_1981_);
lean_del_object(v___x_1976_);
lean_dec(v_offset_1971_);
lean_dec(v_i_1970_);
return v___x_1987_;
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec(v_fvarId_1984_);
lean_dec(v_fvarId_1981_);
lean_del_object(v___x_1976_);
lean_dec_ref(v_k_1974_);
lean_dec(v_offset_1971_);
lean_dec(v_i_1970_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
v_a_1999_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1985_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1985_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
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
lean_object* v___x_2007_; 
lean_dec(v_fvarId_1981_);
lean_del_object(v___x_1976_);
lean_dec_ref(v_k_1974_);
lean_dec_ref(v_ty_1973_);
lean_dec(v_offset_1971_);
lean_dec(v_i_1970_);
lean_dec(v_a_1694_);
v___x_2007_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1691_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
return v___x_2007_;
}
}
else
{
lean_object* v___x_2008_; 
lean_del_object(v___x_1976_);
lean_dec_ref(v_k_1974_);
lean_dec_ref(v_ty_1973_);
lean_dec(v_y_1972_);
lean_dec(v_offset_1971_);
lean_dec(v_i_1970_);
lean_dec(v_a_1694_);
v___x_2008_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1691_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
return v___x_2008_;
}
}
}
case 10:
{
lean_object* v_fvarId_2010_; lean_object* v_cidx_2011_; lean_object* v_k_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2033_; 
v_fvarId_2010_ = lean_ctor_get(v_code_1692_, 0);
v_cidx_2011_ = lean_ctor_get(v_code_1692_, 1);
v_k_2012_ = lean_ctor_get(v_code_1692_, 2);
v_isSharedCheck_2033_ = !lean_is_exclusive(v_code_1692_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2014_ = v_code_1692_;
v_isShared_2015_ = v_isSharedCheck_2033_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_k_2012_);
lean_inc(v_cidx_2011_);
lean_inc(v_fvarId_2010_);
lean_dec(v_code_1692_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2033_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; uint8_t v___x_2017_; lean_object* v___x_2018_; 
v___x_2016_ = lean_st_ref_get(v_a_1694_);
v___x_2017_ = 1;
v___x_2018_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2016_, v_fvarId_2010_, v___x_2017_);
lean_dec(v___x_2016_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_fvarId_2019_; lean_object* v___x_2020_; 
v_fvarId_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_fvarId_2019_);
lean_dec_ref(v___x_2018_);
v___x_2020_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1691_, v_k_2012_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2031_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2023_ = v___x_2020_;
v_isShared_2024_ = v_isSharedCheck_2031_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2020_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2031_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 2, v_a_2021_);
lean_ctor_set(v___x_2014_, 0, v_fvarId_2019_);
v___x_2026_ = v___x_2014_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_fvarId_2019_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v_cidx_2011_);
lean_ctor_set(v_reuseFailAlloc_2030_, 2, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2028_; 
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2026_);
v___x_2028_ = v___x_2023_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
else
{
lean_dec(v_fvarId_2019_);
lean_del_object(v___x_2014_);
lean_dec(v_cidx_2011_);
return v___x_2020_;
}
}
else
{
lean_object* v___x_2032_; 
lean_del_object(v___x_2014_);
lean_dec_ref(v_k_2012_);
lean_dec(v_cidx_2011_);
lean_dec(v_a_1694_);
v___x_2032_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1691_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
return v___x_2032_;
}
}
}
case 11:
{
lean_object* v_fvarId_2034_; lean_object* v_n_2035_; uint8_t v_check_2036_; uint8_t v_persistent_2037_; lean_object* v_k_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2059_; 
v_fvarId_2034_ = lean_ctor_get(v_code_1692_, 0);
v_n_2035_ = lean_ctor_get(v_code_1692_, 1);
v_check_2036_ = lean_ctor_get_uint8(v_code_1692_, sizeof(void*)*3);
v_persistent_2037_ = lean_ctor_get_uint8(v_code_1692_, sizeof(void*)*3 + 1);
v_k_2038_ = lean_ctor_get(v_code_1692_, 2);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_code_1692_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2040_ = v_code_1692_;
v_isShared_2041_ = v_isSharedCheck_2059_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_k_2038_);
lean_inc(v_n_2035_);
lean_inc(v_fvarId_2034_);
lean_dec(v_code_1692_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2059_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; uint8_t v___x_2043_; lean_object* v___x_2044_; 
v___x_2042_ = lean_st_ref_get(v_a_1694_);
v___x_2043_ = 1;
v___x_2044_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2042_, v_fvarId_2034_, v___x_2043_);
lean_dec(v___x_2042_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_fvarId_2045_; lean_object* v___x_2046_; 
v_fvarId_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_fvarId_2045_);
lean_dec_ref(v___x_2044_);
v___x_2046_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1691_, v_k_2038_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2057_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2057_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2057_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 2, v_a_2047_);
lean_ctor_set(v___x_2040_, 0, v_fvarId_2045_);
v___x_2052_ = v___x_2040_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_fvarId_2045_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_n_2035_);
lean_ctor_set(v_reuseFailAlloc_2056_, 2, v_a_2047_);
lean_ctor_set_uint8(v_reuseFailAlloc_2056_, sizeof(void*)*3, v_check_2036_);
lean_ctor_set_uint8(v_reuseFailAlloc_2056_, sizeof(void*)*3 + 1, v_persistent_2037_);
v___x_2052_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
lean_object* v___x_2054_; 
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2052_);
v___x_2054_ = v___x_2049_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_dec(v_fvarId_2045_);
lean_del_object(v___x_2040_);
lean_dec(v_n_2035_);
return v___x_2046_;
}
}
else
{
lean_object* v___x_2058_; 
lean_del_object(v___x_2040_);
lean_dec_ref(v_k_2038_);
lean_dec(v_n_2035_);
lean_dec(v_a_1694_);
v___x_2058_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1691_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
return v___x_2058_;
}
}
}
case 12:
{
lean_object* v_fvarId_2060_; lean_object* v_n_2061_; uint8_t v_check_2062_; uint8_t v_persistent_2063_; lean_object* v_k_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2085_; 
v_fvarId_2060_ = lean_ctor_get(v_code_1692_, 0);
v_n_2061_ = lean_ctor_get(v_code_1692_, 1);
v_check_2062_ = lean_ctor_get_uint8(v_code_1692_, sizeof(void*)*3);
v_persistent_2063_ = lean_ctor_get_uint8(v_code_1692_, sizeof(void*)*3 + 1);
v_k_2064_ = lean_ctor_get(v_code_1692_, 2);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_code_1692_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2066_ = v_code_1692_;
v_isShared_2067_ = v_isSharedCheck_2085_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_k_2064_);
lean_inc(v_n_2061_);
lean_inc(v_fvarId_2060_);
lean_dec(v_code_1692_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2085_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; uint8_t v___x_2069_; lean_object* v___x_2070_; 
v___x_2068_ = lean_st_ref_get(v_a_1694_);
v___x_2069_ = 1;
v___x_2070_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2068_, v_fvarId_2060_, v___x_2069_);
lean_dec(v___x_2068_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_fvarId_2071_; lean_object* v___x_2072_; 
v_fvarId_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_fvarId_2071_);
lean_dec_ref(v___x_2070_);
v___x_2072_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1691_, v_k_2064_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2083_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2075_ = v___x_2072_;
v_isShared_2076_ = v_isSharedCheck_2083_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2083_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 2, v_a_2073_);
lean_ctor_set(v___x_2066_, 0, v_fvarId_2071_);
v___x_2078_ = v___x_2066_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_fvarId_2071_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_n_2061_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v_a_2073_);
lean_ctor_set_uint8(v_reuseFailAlloc_2082_, sizeof(void*)*3, v_check_2062_);
lean_ctor_set_uint8(v_reuseFailAlloc_2082_, sizeof(void*)*3 + 1, v_persistent_2063_);
v___x_2078_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2080_; 
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v___x_2078_);
v___x_2080_ = v___x_2075_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_dec(v_fvarId_2071_);
lean_del_object(v___x_2066_);
lean_dec(v_n_2061_);
return v___x_2072_;
}
}
else
{
lean_object* v___x_2084_; 
lean_del_object(v___x_2066_);
lean_dec_ref(v_k_2064_);
lean_dec(v_n_2061_);
lean_dec(v_a_1694_);
v___x_2084_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1691_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
return v___x_2084_;
}
}
}
default: 
{
lean_object* v_fvarId_2086_; lean_object* v_k_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2108_; 
v_fvarId_2086_ = lean_ctor_get(v_code_1692_, 0);
v_k_2087_ = lean_ctor_get(v_code_1692_, 1);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_code_1692_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2089_ = v_code_1692_;
v_isShared_2090_ = v_isSharedCheck_2108_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_k_2087_);
lean_inc(v_fvarId_2086_);
lean_dec(v_code_1692_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2108_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; uint8_t v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = lean_st_ref_get(v_a_1694_);
v___x_2092_ = 1;
v___x_2093_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2091_, v_fvarId_2086_, v___x_2092_);
lean_dec(v___x_2091_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_fvarId_2094_; lean_object* v___x_2095_; 
v_fvarId_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_fvarId_2094_);
lean_dec_ref(v___x_2093_);
v___x_2095_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1691_, v_k_2087_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2106_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2098_ = v___x_2095_;
v_isShared_2099_ = v_isSharedCheck_2106_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2106_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 1, v_a_2096_);
lean_ctor_set(v___x_2089_, 0, v_fvarId_2094_);
v___x_2101_ = v___x_2089_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_fvarId_2094_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2103_; 
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2101_);
v___x_2103_ = v___x_2098_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
else
{
lean_dec(v_fvarId_2094_);
lean_del_object(v___x_2089_);
return v___x_2095_;
}
}
else
{
lean_object* v___x_2107_; 
lean_del_object(v___x_2089_);
lean_dec_ref(v_k_2087_);
lean_dec(v_a_1694_);
v___x_2107_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1691_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
return v___x_2107_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(uint8_t v_pu_2109_, lean_object* v_decl_2110_, uint8_t v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v_fvarId_2118_; lean_object* v_binderName_2119_; lean_object* v_params_2120_; lean_object* v_type_2121_; lean_object* v_value_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2200_; 
v_fvarId_2118_ = lean_ctor_get(v_decl_2110_, 0);
v_binderName_2119_ = lean_ctor_get(v_decl_2110_, 1);
v_params_2120_ = lean_ctor_get(v_decl_2110_, 2);
v_type_2121_ = lean_ctor_get(v_decl_2110_, 3);
v_value_2122_ = lean_ctor_get(v_decl_2110_, 4);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_decl_2110_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2124_ = v_decl_2110_;
v_isShared_2125_ = v_isSharedCheck_2200_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_value_2122_);
lean_inc(v_type_2121_);
lean_inc(v_params_2120_);
lean_inc(v_binderName_2119_);
lean_inc(v_fvarId_2118_);
lean_dec(v_decl_2110_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2200_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; 
lean_inc(v_a_2116_);
lean_inc_ref(v_a_2115_);
lean_inc(v_a_2114_);
lean_inc_ref(v_a_2113_);
lean_inc(v_a_2112_);
v___x_2126_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2109_, v_type_2121_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref(v___x_2126_);
v___x_2128_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_2119_, v_a_2111_, v_a_2114_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; size_t v_sz_2130_; size_t v___x_2131_; lean_object* v___x_2132_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref(v___x_2128_);
v_sz_2130_ = lean_array_size(v_params_2120_);
v___x_2131_ = ((size_t)0ULL);
lean_inc(v_a_2116_);
lean_inc_ref(v_a_2115_);
lean_inc(v_a_2114_);
lean_inc_ref(v_a_2113_);
lean_inc(v_a_2112_);
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2109_, v_sz_2130_, v___x_2131_, v_params_2120_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref(v___x_2132_);
lean_inc(v_a_2116_);
lean_inc_ref(v_a_2115_);
lean_inc(v_a_2114_);
lean_inc_ref(v_a_2113_);
lean_inc(v_a_2112_);
v___x_2134_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2109_, v_value_2122_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2136_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref(v___x_2134_);
v___x_2136_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_2118_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec_ref(v_a_2113_);
lean_dec(v_a_2112_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2159_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2139_ = v___x_2136_;
v_isShared_2140_ = v_isSharedCheck_2159_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2136_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2159_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; lean_object* v_lctx_2142_; lean_object* v_nextIdx_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2158_; 
v___x_2141_ = lean_st_ref_take(v_a_2114_);
v_lctx_2142_ = lean_ctor_get(v___x_2141_, 0);
v_nextIdx_2143_ = lean_ctor_get(v___x_2141_, 1);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2145_ = v___x_2141_;
v_isShared_2146_ = v_isSharedCheck_2158_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_nextIdx_2143_);
lean_inc(v_lctx_2142_);
lean_dec(v___x_2141_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2158_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 4, v_a_2135_);
lean_ctor_set(v___x_2124_, 3, v_a_2127_);
lean_ctor_set(v___x_2124_, 2, v_a_2133_);
lean_ctor_set(v___x_2124_, 1, v_a_2129_);
lean_ctor_set(v___x_2124_, 0, v_a_2137_);
v___x_2148_ = v___x_2124_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2137_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_a_2129_);
lean_ctor_set(v_reuseFailAlloc_2157_, 2, v_a_2133_);
lean_ctor_set(v_reuseFailAlloc_2157_, 3, v_a_2127_);
lean_ctor_set(v_reuseFailAlloc_2157_, 4, v_a_2135_);
v___x_2148_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2151_; 
lean_inc_ref(v___x_2148_);
v___x_2149_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2109_, v_lctx_2142_, v___x_2148_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 0, v___x_2149_);
v___x_2151_ = v___x_2145_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_nextIdx_2143_);
v___x_2151_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2152_; lean_object* v___x_2154_; 
v___x_2152_ = lean_st_ref_set(v_a_2114_, v___x_2151_);
lean_dec(v_a_2114_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2148_);
v___x_2154_ = v___x_2139_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2148_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec(v_a_2135_);
lean_dec(v_a_2133_);
lean_dec(v_a_2129_);
lean_dec(v_a_2127_);
lean_del_object(v___x_2124_);
lean_dec(v_a_2114_);
v_a_2160_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2136_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2136_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec(v_a_2133_);
lean_dec(v_a_2129_);
lean_dec(v_a_2127_);
lean_del_object(v___x_2124_);
lean_dec(v_fvarId_2118_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec(v_a_2114_);
lean_dec_ref(v_a_2113_);
lean_dec(v_a_2112_);
v_a_2168_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2134_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2134_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec(v_a_2129_);
lean_dec(v_a_2127_);
lean_del_object(v___x_2124_);
lean_dec_ref(v_value_2122_);
lean_dec(v_fvarId_2118_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec(v_a_2114_);
lean_dec_ref(v_a_2113_);
lean_dec(v_a_2112_);
v_a_2176_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2132_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2132_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v_a_2127_);
lean_del_object(v___x_2124_);
lean_dec_ref(v_value_2122_);
lean_dec_ref(v_params_2120_);
lean_dec(v_fvarId_2118_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec(v_a_2114_);
lean_dec_ref(v_a_2113_);
lean_dec(v_a_2112_);
v_a_2184_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2128_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2128_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_del_object(v___x_2124_);
lean_dec_ref(v_value_2122_);
lean_dec_ref(v_params_2120_);
lean_dec(v_binderName_2119_);
lean_dec(v_fvarId_2118_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec(v_a_2114_);
lean_dec_ref(v_a_2113_);
lean_dec(v_a_2112_);
v_a_2192_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2126_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2126_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(lean_object* v_pu_2201_, lean_object* v_decl_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_){
_start:
{
uint8_t v_pu_boxed_2210_; uint8_t v_a_27395__boxed_2211_; lean_object* v_res_2212_; 
v_pu_boxed_2210_ = lean_unbox(v_pu_2201_);
v_a_27395__boxed_2211_ = lean_unbox(v_a_2203_);
v_res_2212_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_boxed_2210_, v_decl_2202_, v_a_27395__boxed_2211_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2___boxed(lean_object* v_pu_2213_, lean_object* v_sz_2214_, lean_object* v_i_2215_, lean_object* v_bs_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
uint8_t v_pu_boxed_2224_; size_t v_sz_boxed_2225_; size_t v_i_boxed_2226_; uint8_t v___y_27434__boxed_2227_; lean_object* v_res_2228_; 
v_pu_boxed_2224_ = lean_unbox(v_pu_2213_);
v_sz_boxed_2225_ = lean_unbox_usize(v_sz_2214_);
lean_dec(v_sz_2214_);
v_i_boxed_2226_ = lean_unbox_usize(v_i_2215_);
lean_dec(v_i_2215_);
v___y_27434__boxed_2227_ = lean_unbox(v___y_2217_);
v_res_2228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_boxed_2224_, v_sz_boxed_2225_, v_i_boxed_2226_, v_bs_2216_, v___y_27434__boxed_2227_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(lean_object* v_pu_2229_, lean_object* v_code_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
uint8_t v_pu_boxed_2238_; uint8_t v_a_27475__boxed_2239_; lean_object* v_res_2240_; 
v_pu_boxed_2238_ = lean_unbox(v_pu_2229_);
v_a_27475__boxed_2239_ = lean_unbox(v_a_2231_);
v_res_2240_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_boxed_2238_, v_code_2230_, v_a_27475__boxed_2239_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(uint8_t v_pu_2241_, lean_object* v_msg_2242_, uint8_t v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v_toApplicative_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2316_; 
v___x_2250_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
v___x_2251_ = l_ReaderT_instMonad___redArg(v___x_2250_);
v_toApplicative_2252_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2316_ == 0)
{
lean_object* v_unused_2317_; 
v_unused_2317_ = lean_ctor_get(v___x_2251_, 1);
lean_dec(v_unused_2317_);
v___x_2254_ = v___x_2251_;
v_isShared_2255_ = v_isSharedCheck_2316_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_toApplicative_2252_);
lean_dec(v___x_2251_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2316_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v_toFunctor_2256_; lean_object* v_toSeq_2257_; lean_object* v_toSeqLeft_2258_; lean_object* v_toSeqRight_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2314_; 
v_toFunctor_2256_ = lean_ctor_get(v_toApplicative_2252_, 0);
v_toSeq_2257_ = lean_ctor_get(v_toApplicative_2252_, 2);
v_toSeqLeft_2258_ = lean_ctor_get(v_toApplicative_2252_, 3);
v_toSeqRight_2259_ = lean_ctor_get(v_toApplicative_2252_, 4);
v_isSharedCheck_2314_ = !lean_is_exclusive(v_toApplicative_2252_);
if (v_isSharedCheck_2314_ == 0)
{
lean_object* v_unused_2315_; 
v_unused_2315_ = lean_ctor_get(v_toApplicative_2252_, 1);
lean_dec(v_unused_2315_);
v___x_2261_ = v_toApplicative_2252_;
v_isShared_2262_ = v_isSharedCheck_2314_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_toSeqRight_2259_);
lean_inc(v_toSeqLeft_2258_);
lean_inc(v_toSeq_2257_);
lean_inc(v_toFunctor_2256_);
lean_dec(v_toApplicative_2252_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2314_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___f_2263_; lean_object* v___f_2264_; lean_object* v___f_2265_; lean_object* v___f_2266_; lean_object* v___x_2267_; lean_object* v___f_2268_; lean_object* v___f_2269_; lean_object* v___f_2270_; lean_object* v___x_2272_; 
v___f_2263_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
v___f_2264_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_2256_);
v___f_2265_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2265_, 0, v_toFunctor_2256_);
v___f_2266_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2266_, 0, v_toFunctor_2256_);
v___x_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___f_2265_);
lean_ctor_set(v___x_2267_, 1, v___f_2266_);
v___f_2268_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2268_, 0, v_toSeqRight_2259_);
v___f_2269_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2269_, 0, v_toSeqLeft_2258_);
v___f_2270_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2270_, 0, v_toSeq_2257_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v___f_2268_);
lean_ctor_set(v___x_2261_, 3, v___f_2269_);
lean_ctor_set(v___x_2261_, 2, v___f_2270_);
lean_ctor_set(v___x_2261_, 1, v___f_2263_);
lean_ctor_set(v___x_2261_, 0, v___x_2267_);
v___x_2272_ = v___x_2261_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2267_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v___f_2263_);
lean_ctor_set(v_reuseFailAlloc_2313_, 2, v___f_2270_);
lean_ctor_set(v_reuseFailAlloc_2313_, 3, v___f_2269_);
lean_ctor_set(v_reuseFailAlloc_2313_, 4, v___f_2268_);
v___x_2272_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
lean_object* v___x_2274_; 
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 1, v___f_2264_);
lean_ctor_set(v___x_2254_, 0, v___x_2272_);
v___x_2274_ = v___x_2254_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v___f_2264_);
v___x_2274_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
lean_object* v___x_2275_; lean_object* v_toApplicative_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2310_; 
v___x_2275_ = l_ReaderT_instMonad___redArg(v___x_2274_);
v_toApplicative_2276_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2310_ == 0)
{
lean_object* v_unused_2311_; 
v_unused_2311_ = lean_ctor_get(v___x_2275_, 1);
lean_dec(v_unused_2311_);
v___x_2278_ = v___x_2275_;
v_isShared_2279_ = v_isSharedCheck_2310_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_toApplicative_2276_);
lean_dec(v___x_2275_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2310_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v_toFunctor_2280_; lean_object* v_toSeq_2281_; lean_object* v_toSeqLeft_2282_; lean_object* v_toSeqRight_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2308_; 
v_toFunctor_2280_ = lean_ctor_get(v_toApplicative_2276_, 0);
v_toSeq_2281_ = lean_ctor_get(v_toApplicative_2276_, 2);
v_toSeqLeft_2282_ = lean_ctor_get(v_toApplicative_2276_, 3);
v_toSeqRight_2283_ = lean_ctor_get(v_toApplicative_2276_, 4);
v_isSharedCheck_2308_ = !lean_is_exclusive(v_toApplicative_2276_);
if (v_isSharedCheck_2308_ == 0)
{
lean_object* v_unused_2309_; 
v_unused_2309_ = lean_ctor_get(v_toApplicative_2276_, 1);
lean_dec(v_unused_2309_);
v___x_2285_ = v_toApplicative_2276_;
v_isShared_2286_ = v_isSharedCheck_2308_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_toSeqRight_2283_);
lean_inc(v_toSeqLeft_2282_);
lean_inc(v_toSeq_2281_);
lean_inc(v_toFunctor_2280_);
lean_dec(v_toApplicative_2276_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2308_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___f_2287_; lean_object* v___f_2288_; lean_object* v___f_2289_; lean_object* v___f_2290_; lean_object* v___x_2291_; lean_object* v___f_2292_; lean_object* v___f_2293_; lean_object* v___f_2294_; lean_object* v___x_2296_; 
v___f_2287_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
v___f_2288_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(v_toFunctor_2280_);
v___f_2289_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2289_, 0, v_toFunctor_2280_);
v___f_2290_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2290_, 0, v_toFunctor_2280_);
v___x_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___f_2289_);
lean_ctor_set(v___x_2291_, 1, v___f_2290_);
v___f_2292_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2292_, 0, v_toSeqRight_2283_);
v___f_2293_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2293_, 0, v_toSeqLeft_2282_);
v___f_2294_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2294_, 0, v_toSeq_2281_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 4, v___f_2292_);
lean_ctor_set(v___x_2285_, 3, v___f_2293_);
lean_ctor_set(v___x_2285_, 2, v___f_2294_);
lean_ctor_set(v___x_2285_, 1, v___f_2287_);
lean_ctor_set(v___x_2285_, 0, v___x_2291_);
v___x_2296_ = v___x_2285_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2291_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v___f_2287_);
lean_ctor_set(v_reuseFailAlloc_2307_, 2, v___f_2294_);
lean_ctor_set(v_reuseFailAlloc_2307_, 3, v___f_2293_);
lean_ctor_set(v_reuseFailAlloc_2307_, 4, v___f_2292_);
v___x_2296_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
lean_object* v___x_2298_; 
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 1, v___f_2288_);
lean_ctor_set(v___x_2278_, 0, v___x_2296_);
v___x_2298_ = v___x_2278_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2296_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v___f_2288_);
v___x_2298_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___f_2302_; lean_object* v___x_11831__overap_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2299_ = l_ReaderT_instMonad___redArg(v___x_2298_);
v___x_2300_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v_pu_2241_);
v___x_2301_ = l_instInhabitedOfMonad___redArg(v___x_2299_, v___x_2300_);
v___f_2302_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2302_, 0, v___x_2301_);
v___x_11831__overap_2303_ = lean_panic_fn(v___f_2302_, v_msg_2242_);
v___x_2304_ = lean_box(v___y_2243_);
v___x_2305_ = lean_apply_7(v___x_11831__overap_2303_, v___x_2304_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, lean_box(0));
return v___x_2305_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___boxed(lean_object* v_pu_2318_, lean_object* v_msg_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
uint8_t v_pu_boxed_2327_; uint8_t v___y_11863__boxed_2328_; lean_object* v_res_2329_; 
v_pu_boxed_2327_ = lean_unbox(v_pu_2318_);
v___y_11863__boxed_2328_ = lean_unbox(v___y_2320_);
v_res_2329_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_boxed_2327_, v_msg_2319_, v___y_11863__boxed_2328_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
return v_res_2329_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1(void){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2331_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2332_ = lean_unsigned_to_nat(41u);
v___x_2333_ = lean_unsigned_to_nat(217u);
v___x_2334_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2335_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2336_ = l_mkPanicMessageWithDecl(v___x_2335_, v___x_2334_, v___x_2333_, v___x_2332_, v___x_2331_);
return v___x_2336_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2(void){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2337_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2338_ = lean_unsigned_to_nat(31u);
v___x_2339_ = lean_unsigned_to_nat(222u);
v___x_2340_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2341_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2342_ = l_mkPanicMessageWithDecl(v___x_2341_, v___x_2340_, v___x_2339_, v___x_2338_, v___x_2337_);
return v___x_2342_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2343_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2344_ = lean_unsigned_to_nat(41u);
v___x_2345_ = lean_unsigned_to_nat(221u);
v___x_2346_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2347_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2348_ = l_mkPanicMessageWithDecl(v___x_2347_, v___x_2346_, v___x_2345_, v___x_2344_, v___x_2343_);
return v___x_2348_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4(void){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2349_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2350_ = lean_unsigned_to_nat(31u);
v___x_2351_ = lean_unsigned_to_nat(226u);
v___x_2352_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2353_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2354_ = l_mkPanicMessageWithDecl(v___x_2353_, v___x_2352_, v___x_2351_, v___x_2350_, v___x_2349_);
return v___x_2354_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5(void){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2355_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2356_ = lean_unsigned_to_nat(41u);
v___x_2357_ = lean_unsigned_to_nat(225u);
v___x_2358_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2359_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2360_ = l_mkPanicMessageWithDecl(v___x_2359_, v___x_2358_, v___x_2357_, v___x_2356_, v___x_2355_);
return v___x_2360_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6(void){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2361_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2362_ = lean_unsigned_to_nat(41u);
v___x_2363_ = lean_unsigned_to_nat(230u);
v___x_2364_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2365_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2366_ = l_mkPanicMessageWithDecl(v___x_2365_, v___x_2364_, v___x_2363_, v___x_2362_, v___x_2361_);
return v___x_2366_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7(void){
_start:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2367_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2368_ = lean_unsigned_to_nat(41u);
v___x_2369_ = lean_unsigned_to_nat(233u);
v___x_2370_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2371_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2372_ = l_mkPanicMessageWithDecl(v___x_2371_, v___x_2370_, v___x_2369_, v___x_2368_, v___x_2367_);
return v___x_2372_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2373_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2374_ = lean_unsigned_to_nat(41u);
v___x_2375_ = lean_unsigned_to_nat(236u);
v___x_2376_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2377_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2378_ = l_mkPanicMessageWithDecl(v___x_2377_, v___x_2376_, v___x_2375_, v___x_2374_, v___x_2373_);
return v___x_2378_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9(void){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2379_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2380_ = lean_unsigned_to_nat(41u);
v___x_2381_ = lean_unsigned_to_nat(239u);
v___x_2382_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2383_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2384_ = l_mkPanicMessageWithDecl(v___x_2383_, v___x_2382_, v___x_2381_, v___x_2380_, v___x_2379_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t v_pu_2385_, lean_object* v_decl_2386_, uint8_t v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_){
_start:
{
switch(lean_obj_tag(v_decl_2386_))
{
case 0:
{
lean_object* v_decl_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2418_; 
v_decl_2394_ = lean_ctor_get(v_decl_2386_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v_decl_2386_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2396_ = v_decl_2386_;
v_isShared_2397_ = v_isSharedCheck_2418_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_decl_2394_);
lean_dec(v_decl_2386_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2418_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_2385_, v_decl_2394_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2409_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2401_ = v___x_2398_;
v_isShared_2402_ = v_isSharedCheck_2409_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2398_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2409_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v_a_2399_);
v___x_2404_ = v___x_2396_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
lean_object* v___x_2406_; 
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 0, v___x_2404_);
v___x_2406_ = v___x_2401_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_del_object(v___x_2396_);
v_a_2410_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2398_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2398_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2443_; 
v_decl_2419_ = lean_ctor_get(v_decl_2386_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_decl_2386_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2421_ = v_decl_2386_;
v_isShared_2422_ = v_isSharedCheck_2443_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_decl_2419_);
lean_dec(v_decl_2386_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2443_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2385_, v_decl_2419_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2434_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2426_ = v___x_2423_;
v_isShared_2427_ = v_isSharedCheck_2434_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2434_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v_a_2424_);
v___x_2429_ = v___x_2421_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2431_; 
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2429_);
v___x_2431_ = v___x_2426_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2429_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_del_object(v___x_2421_);
v_a_2435_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2423_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2423_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
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
}
case 2:
{
lean_object* v_decl_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2468_; 
v_decl_2444_ = lean_ctor_get(v_decl_2386_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_decl_2386_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2446_ = v_decl_2386_;
v_isShared_2447_ = v_isSharedCheck_2468_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_decl_2444_);
lean_dec(v_decl_2386_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2468_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2448_; 
v___x_2448_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2385_, v_decl_2444_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2459_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2451_ = v___x_2448_;
v_isShared_2452_ = v_isSharedCheck_2459_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2448_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2459_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v_a_2449_);
v___x_2454_ = v___x_2446_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2456_; 
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 0, v___x_2454_);
v___x_2456_ = v___x_2451_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_del_object(v___x_2446_);
v_a_2460_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2448_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2448_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
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
}
case 3:
{
lean_object* v_fvarId_2469_; lean_object* v_i_2470_; lean_object* v_y_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2493_; 
v_fvarId_2469_ = lean_ctor_get(v_decl_2386_, 0);
v_i_2470_ = lean_ctor_get(v_decl_2386_, 1);
v_y_2471_ = lean_ctor_get(v_decl_2386_, 2);
v_isSharedCheck_2493_ = !lean_is_exclusive(v_decl_2386_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2473_ = v_decl_2386_;
v_isShared_2474_ = v_isSharedCheck_2493_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_y_2471_);
lean_inc(v_i_2470_);
lean_inc(v_fvarId_2469_);
lean_dec(v_decl_2386_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2493_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2475_; uint8_t v___x_2476_; lean_object* v___x_2477_; 
v___x_2475_ = lean_st_ref_get(v_a_2388_);
v___x_2476_ = 1;
v___x_2477_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2475_, v_fvarId_2469_, v___x_2476_);
lean_dec(v___x_2475_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_fvarId_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2490_; 
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
v_fvarId_2478_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2480_ = v___x_2477_;
v_isShared_2481_ = v_isSharedCheck_2490_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_fvarId_2478_);
lean_dec(v___x_2477_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2490_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2485_; 
v___x_2482_ = lean_st_ref_get(v_a_2388_);
lean_dec(v_a_2388_);
v___x_2483_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2385_, v___x_2482_, v_y_2471_, v___x_2476_);
lean_dec(v___x_2482_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 2, v___x_2483_);
lean_ctor_set(v___x_2473_, 0, v_fvarId_2478_);
v___x_2485_ = v___x_2473_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_fvarId_2478_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_i_2470_);
lean_ctor_set(v_reuseFailAlloc_2489_, 2, v___x_2483_);
v___x_2485_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2487_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2485_);
v___x_2487_ = v___x_2480_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2485_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
else
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
lean_dec(v___x_2477_);
lean_del_object(v___x_2473_);
lean_dec(v_y_2471_);
lean_dec(v_i_2470_);
v___x_2491_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1);
v___x_2492_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2385_, v___x_2491_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
return v___x_2492_;
}
}
}
case 4:
{
lean_object* v_fvarId_2494_; lean_object* v_i_2495_; lean_object* v_y_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2521_; 
v_fvarId_2494_ = lean_ctor_get(v_decl_2386_, 0);
v_i_2495_ = lean_ctor_get(v_decl_2386_, 1);
v_y_2496_ = lean_ctor_get(v_decl_2386_, 2);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_decl_2386_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2498_ = v_decl_2386_;
v_isShared_2499_ = v_isSharedCheck_2521_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_y_2496_);
lean_inc(v_i_2495_);
lean_inc(v_fvarId_2494_);
lean_dec(v_decl_2386_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2521_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; uint8_t v___x_2501_; lean_object* v___x_2502_; 
v___x_2500_ = lean_st_ref_get(v_a_2388_);
v___x_2501_ = 1;
v___x_2502_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2500_, v_fvarId_2494_, v___x_2501_);
lean_dec(v___x_2500_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_fvarId_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v_fvarId_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_fvarId_2503_);
lean_dec_ref(v___x_2502_);
v___x_2504_ = lean_st_ref_get(v_a_2388_);
v___x_2505_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2504_, v_y_2496_, v___x_2501_);
lean_dec(v___x_2504_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_fvarId_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2516_; 
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
v_fvarId_2506_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2508_ = v___x_2505_;
v_isShared_2509_ = v_isSharedCheck_2516_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_fvarId_2506_);
lean_dec(v___x_2505_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2516_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 2, v_fvarId_2506_);
lean_ctor_set(v___x_2498_, 0, v_fvarId_2503_);
v___x_2511_ = v___x_2498_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_fvarId_2503_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_i_2495_);
lean_ctor_set(v_reuseFailAlloc_2515_, 2, v_fvarId_2506_);
v___x_2511_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
lean_object* v___x_2513_; 
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 0, v___x_2511_);
v___x_2513_ = v___x_2508_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2511_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
lean_dec(v___x_2505_);
lean_dec(v_fvarId_2503_);
lean_del_object(v___x_2498_);
lean_dec(v_i_2495_);
v___x_2517_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2);
v___x_2518_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2385_, v___x_2517_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
return v___x_2518_;
}
}
else
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
lean_dec(v___x_2502_);
lean_del_object(v___x_2498_);
lean_dec(v_y_2496_);
lean_dec(v_i_2495_);
v___x_2519_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3);
v___x_2520_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2385_, v___x_2519_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
return v___x_2520_;
}
}
}
case 5:
{
lean_object* v_fvarId_2522_; lean_object* v_i_2523_; lean_object* v_offset_2524_; lean_object* v_y_2525_; lean_object* v_ty_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2553_; 
v_fvarId_2522_ = lean_ctor_get(v_decl_2386_, 0);
v_i_2523_ = lean_ctor_get(v_decl_2386_, 1);
v_offset_2524_ = lean_ctor_get(v_decl_2386_, 2);
v_y_2525_ = lean_ctor_get(v_decl_2386_, 3);
v_ty_2526_ = lean_ctor_get(v_decl_2386_, 4);
v_isSharedCheck_2553_ = !lean_is_exclusive(v_decl_2386_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2528_ = v_decl_2386_;
v_isShared_2529_ = v_isSharedCheck_2553_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_ty_2526_);
lean_inc(v_y_2525_);
lean_inc(v_offset_2524_);
lean_inc(v_i_2523_);
lean_inc(v_fvarId_2522_);
lean_dec(v_decl_2386_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2553_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; uint8_t v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = lean_st_ref_get(v_a_2388_);
v___x_2531_ = 1;
v___x_2532_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2530_, v_fvarId_2522_, v___x_2531_);
lean_dec(v___x_2530_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_fvarId_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v_fvarId_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_fvarId_2533_);
lean_dec_ref(v___x_2532_);
v___x_2534_ = lean_st_ref_get(v_a_2388_);
v___x_2535_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2534_, v_y_2525_, v___x_2531_);
lean_dec(v___x_2534_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_fvarId_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2548_; 
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
v_fvarId_2536_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2538_ = v___x_2535_;
v_isShared_2539_ = v_isSharedCheck_2548_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_fvarId_2536_);
lean_dec(v___x_2535_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2548_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2543_; 
v___x_2540_ = lean_st_ref_get(v_a_2388_);
lean_dec(v_a_2388_);
v___x_2541_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2385_, v___x_2540_, v___x_2531_, v_ty_2526_);
lean_dec(v___x_2540_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 4, v___x_2541_);
lean_ctor_set(v___x_2528_, 3, v_fvarId_2536_);
lean_ctor_set(v___x_2528_, 0, v_fvarId_2533_);
v___x_2543_ = v___x_2528_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_fvarId_2533_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_i_2523_);
lean_ctor_set(v_reuseFailAlloc_2547_, 2, v_offset_2524_);
lean_ctor_set(v_reuseFailAlloc_2547_, 3, v_fvarId_2536_);
lean_ctor_set(v_reuseFailAlloc_2547_, 4, v___x_2541_);
v___x_2543_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
lean_object* v___x_2545_; 
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 0, v___x_2543_);
v___x_2545_ = v___x_2538_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2543_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
else
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
lean_dec(v___x_2535_);
lean_dec(v_fvarId_2533_);
lean_del_object(v___x_2528_);
lean_dec_ref(v_ty_2526_);
lean_dec(v_offset_2524_);
lean_dec(v_i_2523_);
v___x_2549_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4);
v___x_2550_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2385_, v___x_2549_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
return v___x_2550_;
}
}
else
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
lean_dec(v___x_2532_);
lean_del_object(v___x_2528_);
lean_dec_ref(v_ty_2526_);
lean_dec(v_y_2525_);
lean_dec(v_offset_2524_);
lean_dec(v_i_2523_);
v___x_2551_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5);
v___x_2552_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2385_, v___x_2551_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
return v___x_2552_;
}
}
}
case 6:
{
lean_object* v_fvarId_2554_; lean_object* v_cidx_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2575_; 
v_fvarId_2554_ = lean_ctor_get(v_decl_2386_, 0);
v_cidx_2555_ = lean_ctor_get(v_decl_2386_, 1);
v_isSharedCheck_2575_ = !lean_is_exclusive(v_decl_2386_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2557_ = v_decl_2386_;
v_isShared_2558_ = v_isSharedCheck_2575_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_cidx_2555_);
lean_inc(v_fvarId_2554_);
lean_dec(v_decl_2386_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2575_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2559_; uint8_t v___x_2560_; lean_object* v___x_2561_; 
v___x_2559_ = lean_st_ref_get(v_a_2388_);
v___x_2560_ = 1;
v___x_2561_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2559_, v_fvarId_2554_, v___x_2560_);
lean_dec(v___x_2559_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_fvarId_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2572_; 
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
v_fvarId_2562_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2564_ = v___x_2561_;
v_isShared_2565_ = v_isSharedCheck_2572_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_fvarId_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2572_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v_fvarId_2562_);
v___x_2567_ = v___x_2557_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_fvarId_2562_);
lean_ctor_set(v_reuseFailAlloc_2571_, 1, v_cidx_2555_);
v___x_2567_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
lean_object* v___x_2569_; 
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v___x_2567_);
v___x_2569_ = v___x_2564_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2567_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
else
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
lean_dec(v___x_2561_);
lean_del_object(v___x_2557_);
lean_dec(v_cidx_2555_);
v___x_2573_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6);
v___x_2574_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2385_, v___x_2573_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
return v___x_2574_;
}
}
}
case 7:
{
lean_object* v_fvarId_2576_; lean_object* v_n_2577_; uint8_t v_check_2578_; uint8_t v_persistent_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2599_; 
v_fvarId_2576_ = lean_ctor_get(v_decl_2386_, 0);
v_n_2577_ = lean_ctor_get(v_decl_2386_, 1);
v_check_2578_ = lean_ctor_get_uint8(v_decl_2386_, sizeof(void*)*2);
v_persistent_2579_ = lean_ctor_get_uint8(v_decl_2386_, sizeof(void*)*2 + 1);
v_isSharedCheck_2599_ = !lean_is_exclusive(v_decl_2386_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2581_ = v_decl_2386_;
v_isShared_2582_ = v_isSharedCheck_2599_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_n_2577_);
lean_inc(v_fvarId_2576_);
lean_dec(v_decl_2386_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2599_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; uint8_t v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = lean_st_ref_get(v_a_2388_);
v___x_2584_ = 1;
v___x_2585_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2583_, v_fvarId_2576_, v___x_2584_);
lean_dec(v___x_2583_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_fvarId_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2596_; 
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
v_fvarId_2586_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2588_ = v___x_2585_;
v_isShared_2589_ = v_isSharedCheck_2596_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_fvarId_2586_);
lean_dec(v___x_2585_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2596_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v_fvarId_2586_);
v___x_2591_ = v___x_2581_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_fvarId_2586_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v_n_2577_);
lean_ctor_set_uint8(v_reuseFailAlloc_2595_, sizeof(void*)*2, v_check_2578_);
lean_ctor_set_uint8(v_reuseFailAlloc_2595_, sizeof(void*)*2 + 1, v_persistent_2579_);
v___x_2591_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
lean_object* v___x_2593_; 
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 0, v___x_2591_);
v___x_2593_ = v___x_2588_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
else
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
lean_dec(v___x_2585_);
lean_del_object(v___x_2581_);
lean_dec(v_n_2577_);
v___x_2597_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7);
v___x_2598_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2385_, v___x_2597_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
return v___x_2598_;
}
}
}
case 8:
{
lean_object* v_fvarId_2600_; lean_object* v_n_2601_; uint8_t v_check_2602_; uint8_t v_persistent_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2623_; 
v_fvarId_2600_ = lean_ctor_get(v_decl_2386_, 0);
v_n_2601_ = lean_ctor_get(v_decl_2386_, 1);
v_check_2602_ = lean_ctor_get_uint8(v_decl_2386_, sizeof(void*)*2);
v_persistent_2603_ = lean_ctor_get_uint8(v_decl_2386_, sizeof(void*)*2 + 1);
v_isSharedCheck_2623_ = !lean_is_exclusive(v_decl_2386_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2605_ = v_decl_2386_;
v_isShared_2606_ = v_isSharedCheck_2623_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_n_2601_);
lean_inc(v_fvarId_2600_);
lean_dec(v_decl_2386_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2623_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2607_; uint8_t v___x_2608_; lean_object* v___x_2609_; 
v___x_2607_ = lean_st_ref_get(v_a_2388_);
v___x_2608_ = 1;
v___x_2609_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2607_, v_fvarId_2600_, v___x_2608_);
lean_dec(v___x_2607_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_fvarId_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2620_; 
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
v_fvarId_2610_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2612_ = v___x_2609_;
v_isShared_2613_ = v_isSharedCheck_2620_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_fvarId_2610_);
lean_dec(v___x_2609_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2620_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v_fvarId_2610_);
v___x_2615_ = v___x_2605_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(8, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_fvarId_2610_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_n_2601_);
lean_ctor_set_uint8(v_reuseFailAlloc_2619_, sizeof(void*)*2, v_check_2602_);
lean_ctor_set_uint8(v_reuseFailAlloc_2619_, sizeof(void*)*2 + 1, v_persistent_2603_);
v___x_2615_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
lean_object* v___x_2617_; 
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v___x_2615_);
v___x_2617_ = v___x_2612_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
else
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
lean_dec(v___x_2609_);
lean_del_object(v___x_2605_);
lean_dec(v_n_2601_);
v___x_2621_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8);
v___x_2622_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2385_, v___x_2621_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
return v___x_2622_;
}
}
}
default: 
{
lean_object* v_fvarId_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2644_; 
v_fvarId_2624_ = lean_ctor_get(v_decl_2386_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v_decl_2386_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2626_ = v_decl_2386_;
v_isShared_2627_ = v_isSharedCheck_2644_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_fvarId_2624_);
lean_dec(v_decl_2386_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2644_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2628_; uint8_t v___x_2629_; lean_object* v___x_2630_; 
v___x_2628_ = lean_st_ref_get(v_a_2388_);
v___x_2629_ = 1;
v___x_2630_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2628_, v_fvarId_2624_, v___x_2629_);
lean_dec(v___x_2628_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_fvarId_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2641_; 
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
v_fvarId_2631_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2633_ = v___x_2630_;
v_isShared_2634_ = v_isSharedCheck_2641_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_fvarId_2631_);
lean_dec(v___x_2630_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2641_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v_fvarId_2631_);
v___x_2636_ = v___x_2626_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_fvarId_2631_);
v___x_2636_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
lean_object* v___x_2638_; 
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v___x_2636_);
v___x_2638_ = v___x_2633_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2636_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
else
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
lean_dec(v___x_2630_);
lean_del_object(v___x_2626_);
v___x_2642_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9);
v___x_2643_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2385_, v___x_2642_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
return v___x_2643_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(lean_object* v_pu_2645_, lean_object* v_decl_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
uint8_t v_pu_boxed_2654_; uint8_t v_a_12134__boxed_2655_; lean_object* v_res_2656_; 
v_pu_boxed_2654_ = lean_unbox(v_pu_2645_);
v_a_12134__boxed_2655_ = lean_unbox(v_a_2647_);
v_res_2656_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v_pu_boxed_2654_, v_decl_2646_, v_a_12134__boxed_2655_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t v_pu_2657_, lean_object* v_code_2658_, lean_object* v_s_2659_, uint8_t v_uniqueIdents_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = lean_st_mk_ref(v_s_2659_);
lean_inc(v___x_2666_);
v___x_2667_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2657_, v_code_2658_, v_uniqueIdents_2660_, v___x_2666_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2676_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2676_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2676_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; lean_object* v___x_2674_; 
v___x_2672_ = lean_st_ref_get(v___x_2666_);
lean_dec(v___x_2666_);
lean_dec(v___x_2672_);
if (v_isShared_2671_ == 0)
{
v___x_2674_ = v___x_2670_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2668_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
else
{
lean_dec(v___x_2666_);
return v___x_2667_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize___boxed(lean_object* v_pu_2677_, lean_object* v_code_2678_, lean_object* v_s_2679_, lean_object* v_uniqueIdents_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
uint8_t v_pu_boxed_2686_; uint8_t v_uniqueIdents_boxed_2687_; lean_object* v_res_2688_; 
v_pu_boxed_2686_ = lean_unbox(v_pu_2677_);
v_uniqueIdents_boxed_2687_ = lean_unbox(v_uniqueIdents_2680_);
v_res_2688_ = l_Lean_Compiler_LCNF_Code_internalize(v_pu_boxed_2686_, v_code_2678_, v_s_2679_, v_uniqueIdents_boxed_2687_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(lean_object* v_f_2689_, lean_object* v_v_2690_, uint8_t v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
if (lean_obj_tag(v_v_2690_) == 0)
{
lean_object* v_code_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2723_; 
v_code_2698_ = lean_ctor_get(v_v_2690_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_v_2690_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2700_ = v_v_2690_;
v_isShared_2701_ = v_isSharedCheck_2723_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_code_2698_);
lean_dec(v_v_2690_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2723_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = lean_box(v___y_2691_);
v___x_2703_ = lean_apply_8(v_f_2689_, v_code_2698_, v___x_2702_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, lean_box(0));
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2714_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2706_ = v___x_2703_;
v_isShared_2707_ = v_isSharedCheck_2714_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2714_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v_a_2704_);
v___x_2709_ = v___x_2700_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
lean_object* v___x_2711_; 
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 0, v___x_2709_);
v___x_2711_ = v___x_2706_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2709_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_del_object(v___x_2700_);
v_a_2715_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2703_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2703_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
}
else
{
lean_object* v___x_2724_; 
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v_f_2689_);
v___x_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2724_, 0, v_v_2690_);
return v___x_2724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg___boxed(lean_object* v_f_2725_, lean_object* v_v_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
uint8_t v___y_1471__boxed_2734_; lean_object* v_res_2735_; 
v___y_1471__boxed_2734_ = lean_unbox(v___y_2727_);
v_res_2735_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2725_, v_v_2726_, v___y_1471__boxed_2734_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(uint8_t v_pu_2736_, lean_object* v_f_2737_, lean_object* v_v_2738_, uint8_t v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2737_, v_v_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___boxed(lean_object* v_pu_2747_, lean_object* v_f_2748_, lean_object* v_v_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
uint8_t v_pu_boxed_2757_; uint8_t v___y_1547__boxed_2758_; lean_object* v_res_2759_; 
v_pu_boxed_2757_ = lean_unbox(v_pu_2747_);
v___y_1547__boxed_2758_ = lean_unbox(v___y_2750_);
v_res_2759_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(v_pu_boxed_2757_, v_f_2748_, v_v_2749_, v___y_1547__boxed_2758_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(uint8_t v_pu_2760_, lean_object* v_decl_2761_, uint8_t v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_){
_start:
{
lean_object* v_toSignature_2769_; lean_object* v_value_2770_; uint8_t v_recursive_2771_; lean_object* v_inlineAttr_x3f_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2832_; 
v_toSignature_2769_ = lean_ctor_get(v_decl_2761_, 0);
v_value_2770_ = lean_ctor_get(v_decl_2761_, 1);
v_recursive_2771_ = lean_ctor_get_uint8(v_decl_2761_, sizeof(void*)*3);
v_inlineAttr_x3f_2772_ = lean_ctor_get(v_decl_2761_, 2);
v_isSharedCheck_2832_ = !lean_is_exclusive(v_decl_2761_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2774_ = v_decl_2761_;
v_isShared_2775_ = v_isSharedCheck_2832_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_inlineAttr_x3f_2772_);
lean_inc(v_value_2770_);
lean_inc(v_toSignature_2769_);
lean_dec(v_decl_2761_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2832_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v_name_2776_; lean_object* v_levelParams_2777_; lean_object* v_type_2778_; lean_object* v_params_2779_; uint8_t v_safe_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2831_; 
v_name_2776_ = lean_ctor_get(v_toSignature_2769_, 0);
v_levelParams_2777_ = lean_ctor_get(v_toSignature_2769_, 1);
v_type_2778_ = lean_ctor_get(v_toSignature_2769_, 2);
v_params_2779_ = lean_ctor_get(v_toSignature_2769_, 3);
v_safe_2780_ = lean_ctor_get_uint8(v_toSignature_2769_, sizeof(void*)*4);
v_isSharedCheck_2831_ = !lean_is_exclusive(v_toSignature_2769_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2782_ = v_toSignature_2769_;
v_isShared_2783_ = v_isSharedCheck_2831_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_params_2779_);
lean_inc(v_type_2778_);
lean_inc(v_levelParams_2777_);
lean_inc(v_name_2776_);
lean_dec(v_toSignature_2769_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2831_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; 
lean_inc(v_a_2767_);
lean_inc_ref(v_a_2766_);
lean_inc(v_a_2765_);
lean_inc_ref(v_a_2764_);
lean_inc(v_a_2763_);
v___x_2784_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2760_, v_type_2778_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; size_t v_sz_2786_; size_t v___x_2787_; lean_object* v___x_2788_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref(v___x_2784_);
v_sz_2786_ = lean_array_size(v_params_2779_);
v___x_2787_ = ((size_t)0ULL);
lean_inc(v_a_2767_);
lean_inc_ref(v_a_2766_);
lean_inc(v_a_2765_);
lean_inc_ref(v_a_2764_);
lean_inc(v_a_2763_);
v___x_2788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2760_, v_sz_2786_, v___x_2787_, v_params_2779_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref(v___x_2788_);
v___x_2790_ = lean_box(v_pu_2760_);
v___x_2791_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed), 9, 1);
lean_closure_set(v___x_2791_, 0, v___x_2790_);
v___x_2792_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v___x_2791_, v_value_2770_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2806_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2795_ = v___x_2792_;
v_isShared_2796_ = v_isSharedCheck_2806_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2792_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2806_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 3, v_a_2789_);
lean_ctor_set(v___x_2782_, 2, v_a_2785_);
v___x_2798_ = v___x_2782_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_name_2776_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_levelParams_2777_);
lean_ctor_set(v_reuseFailAlloc_2805_, 2, v_a_2785_);
lean_ctor_set(v_reuseFailAlloc_2805_, 3, v_a_2789_);
lean_ctor_set_uint8(v_reuseFailAlloc_2805_, sizeof(void*)*4, v_safe_2780_);
v___x_2798_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v___x_2800_; 
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 1, v_a_2793_);
lean_ctor_set(v___x_2774_, 0, v___x_2798_);
v___x_2800_ = v___x_2774_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2798_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v_a_2793_);
lean_ctor_set(v_reuseFailAlloc_2804_, 2, v_inlineAttr_x3f_2772_);
lean_ctor_set_uint8(v_reuseFailAlloc_2804_, sizeof(void*)*3, v_recursive_2771_);
v___x_2800_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
lean_object* v___x_2802_; 
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 0, v___x_2800_);
v___x_2802_ = v___x_2795_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2800_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_dec(v_a_2789_);
lean_dec(v_a_2785_);
lean_del_object(v___x_2782_);
lean_dec(v_levelParams_2777_);
lean_dec(v_name_2776_);
lean_del_object(v___x_2774_);
lean_dec(v_inlineAttr_x3f_2772_);
v_a_2807_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2792_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2792_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_dec(v_a_2785_);
lean_del_object(v___x_2782_);
lean_dec(v_levelParams_2777_);
lean_dec(v_name_2776_);
lean_del_object(v___x_2774_);
lean_dec(v_inlineAttr_x3f_2772_);
lean_dec_ref(v_value_2770_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
lean_dec_ref(v_a_2764_);
lean_dec(v_a_2763_);
v_a_2815_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2788_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2788_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_del_object(v___x_2782_);
lean_dec_ref(v_params_2779_);
lean_dec(v_levelParams_2777_);
lean_dec(v_name_2776_);
lean_del_object(v___x_2774_);
lean_dec(v_inlineAttr_x3f_2772_);
lean_dec_ref(v_value_2770_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
lean_dec_ref(v_a_2764_);
lean_dec(v_a_2763_);
v_a_2823_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2784_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2784_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go___boxed(lean_object* v_pu_2833_, lean_object* v_decl_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_){
_start:
{
uint8_t v_pu_boxed_2842_; uint8_t v_a_1570__boxed_2843_; lean_object* v_res_2844_; 
v_pu_boxed_2842_ = lean_unbox(v_pu_2833_);
v_a_1570__boxed_2843_ = lean_unbox(v_a_2835_);
v_res_2844_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_boxed_2842_, v_decl_2834_, v_a_1570__boxed_2843_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t v_pu_2845_, lean_object* v_decl_2846_, lean_object* v_s_2847_, uint8_t v_uniqueIdents_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = lean_st_mk_ref(v_s_2847_);
lean_inc(v___x_2854_);
v___x_2855_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_2845_, v_decl_2846_, v_uniqueIdents_2848_, v___x_2854_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2864_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2858_ = v___x_2855_;
v_isShared_2859_ = v_isSharedCheck_2864_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2855_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2864_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2860_; lean_object* v___x_2862_; 
v___x_2860_ = lean_st_ref_get(v___x_2854_);
lean_dec(v___x_2854_);
lean_dec(v___x_2860_);
if (v_isShared_2859_ == 0)
{
v___x_2862_ = v___x_2858_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2856_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
else
{
lean_dec(v___x_2854_);
return v___x_2855_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize___boxed(lean_object* v_pu_2865_, lean_object* v_decl_2866_, lean_object* v_s_2867_, lean_object* v_uniqueIdents_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_){
_start:
{
uint8_t v_pu_boxed_2874_; uint8_t v_uniqueIdents_boxed_2875_; lean_object* v_res_2876_; 
v_pu_boxed_2874_ = lean_unbox(v_pu_2865_);
v_uniqueIdents_boxed_2875_ = lean_unbox(v_uniqueIdents_2868_);
v_res_2876_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_boxed_2874_, v_decl_2866_, v_s_2867_, v_uniqueIdents_boxed_2875_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_);
return v_res_2876_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2877_ = lean_box(0);
v___x_2878_ = lean_unsigned_to_nat(16u);
v___x_2879_ = lean_mk_array(v___x_2878_, v___x_2877_);
return v___x_2879_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2880_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0);
v___x_2881_ = lean_unsigned_to_nat(0u);
v___x_2882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
lean_ctor_set(v___x_2882_, 1, v___x_2880_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(uint8_t v_pu_2883_, size_t v_sz_2884_, size_t v_i_2885_, lean_object* v_bs_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
uint8_t v___x_2892_; 
v___x_2892_ = lean_usize_dec_lt(v_i_2885_, v_sz_2884_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2893_; 
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
v___x_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2893_, 0, v_bs_2886_);
return v___x_2893_;
}
else
{
lean_object* v___x_2894_; lean_object* v_lctx_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2923_; 
v___x_2894_ = lean_st_ref_take(v___y_2888_);
v_lctx_2895_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2923_ == 0)
{
lean_object* v_unused_2924_; 
v_unused_2924_ = lean_ctor_get(v___x_2894_, 1);
lean_dec(v_unused_2924_);
v___x_2897_ = v___x_2894_;
v_isShared_2898_ = v_isSharedCheck_2923_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_lctx_2895_);
lean_dec(v___x_2894_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2923_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2899_; lean_object* v___x_2901_; 
v___x_2899_ = lean_unsigned_to_nat(1u);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 1, v___x_2899_);
v___x_2901_ = v___x_2897_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_lctx_2895_);
lean_ctor_set(v_reuseFailAlloc_2922_, 1, v___x_2899_);
v___x_2901_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
lean_object* v___x_2902_; lean_object* v_v_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; lean_object* v___x_2907_; 
v___x_2902_ = lean_st_ref_set(v___y_2888_, v___x_2901_);
v_v_2903_ = lean_array_uget_borrowed(v_bs_2886_, v_i_2885_);
v___x_2904_ = lean_unsigned_to_nat(0u);
v___x_2905_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_2906_ = 0;
lean_inc(v___y_2890_);
lean_inc_ref(v___y_2889_);
lean_inc(v___y_2888_);
lean_inc_ref(v___y_2887_);
lean_inc(v_v_2903_);
v___x_2907_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_2883_, v_v_2903_, v___x_2905_, v___x_2906_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v_bs_x27_2909_; size_t v___x_2910_; size_t v___x_2911_; lean_object* v___x_2912_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2908_);
lean_dec_ref(v___x_2907_);
v_bs_x27_2909_ = lean_array_uset(v_bs_2886_, v_i_2885_, v___x_2904_);
v___x_2910_ = ((size_t)1ULL);
v___x_2911_ = lean_usize_add(v_i_2885_, v___x_2910_);
v___x_2912_ = lean_array_uset(v_bs_x27_2909_, v_i_2885_, v_a_2908_);
v_i_2885_ = v___x_2911_;
v_bs_2886_ = v___x_2912_;
goto _start;
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec_ref(v_bs_2886_);
v_a_2914_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2907_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2907_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___boxed(lean_object* v_pu_2925_, lean_object* v_sz_2926_, lean_object* v_i_2927_, lean_object* v_bs_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
uint8_t v_pu_boxed_2934_; size_t v_sz_boxed_2935_; size_t v_i_boxed_2936_; lean_object* v_res_2937_; 
v_pu_boxed_2934_ = lean_unbox(v_pu_2925_);
v_sz_boxed_2935_ = lean_unbox_usize(v_sz_2926_);
lean_dec(v_sz_2926_);
v_i_boxed_2936_ = lean_unbox_usize(v_i_2927_);
lean_dec(v_i_2927_);
v_res_2937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_boxed_2934_, v_sz_boxed_2935_, v_i_boxed_2936_, v_bs_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
return v_res_2937_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__0(void){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_2939_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2938_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
lean_ctor_set(v___x_2939_, 2, v___x_2938_);
lean_ctor_set(v___x_2939_, 3, v___x_2938_);
lean_ctor_set(v___x_2939_, 4, v___x_2938_);
lean_ctor_set(v___x_2939_, 5, v___x_2938_);
return v___x_2939_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__1(void){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2940_ = lean_unsigned_to_nat(1u);
v___x_2941_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__0, &l_Lean_Compiler_LCNF_cleanup___closed__0_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__0);
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v___x_2940_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup(uint8_t v_pu_2943_, lean_object* v_decl_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; size_t v_sz_2953_; size_t v___x_2954_; lean_object* v___x_2955_; 
v___x_2950_ = lean_st_ref_take(v_a_2946_);
lean_dec(v___x_2950_);
v___x_2951_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
v___x_2952_ = lean_st_ref_set(v_a_2946_, v___x_2951_);
v_sz_2953_ = lean_array_size(v_decl_2944_);
v___x_2954_ = ((size_t)0ULL);
v___x_2955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_2943_, v_sz_2953_, v___x_2954_, v_decl_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup___boxed(lean_object* v_pu_2956_, lean_object* v_decl_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_){
_start:
{
uint8_t v_pu_boxed_2963_; lean_object* v_res_2964_; 
v_pu_boxed_2963_ = lean_unbox(v_pu_2956_);
v_res_2964_ = l_Lean_Compiler_LCNF_cleanup(v_pu_boxed_2963_, v_decl_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(lean_object* v_a_2965_, lean_object* v_ngen_2966_, lean_object* v_a_x3f_2967_){
_start:
{
lean_object* v___x_2969_; lean_object* v_env_2970_; lean_object* v_nextMacroScope_2971_; lean_object* v_auxDeclNGen_2972_; lean_object* v_traceState_2973_; lean_object* v_cache_2974_; lean_object* v_messages_2975_; lean_object* v_infoState_2976_; lean_object* v_snapshotTasks_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2987_; 
v___x_2969_ = lean_st_ref_take(v_a_2965_);
v_env_2970_ = lean_ctor_get(v___x_2969_, 0);
v_nextMacroScope_2971_ = lean_ctor_get(v___x_2969_, 1);
v_auxDeclNGen_2972_ = lean_ctor_get(v___x_2969_, 3);
v_traceState_2973_ = lean_ctor_get(v___x_2969_, 4);
v_cache_2974_ = lean_ctor_get(v___x_2969_, 5);
v_messages_2975_ = lean_ctor_get(v___x_2969_, 6);
v_infoState_2976_ = lean_ctor_get(v___x_2969_, 7);
v_snapshotTasks_2977_ = lean_ctor_get(v___x_2969_, 8);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v___x_2969_, 2);
lean_dec(v_unused_2988_);
v___x_2979_ = v___x_2969_;
v_isShared_2980_ = v_isSharedCheck_2987_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_snapshotTasks_2977_);
lean_inc(v_infoState_2976_);
lean_inc(v_messages_2975_);
lean_inc(v_cache_2974_);
lean_inc(v_traceState_2973_);
lean_inc(v_auxDeclNGen_2972_);
lean_inc(v_nextMacroScope_2971_);
lean_inc(v_env_2970_);
lean_dec(v___x_2969_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2987_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 2, v_ngen_2966_);
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_env_2970_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_nextMacroScope_2971_);
lean_ctor_set(v_reuseFailAlloc_2986_, 2, v_ngen_2966_);
lean_ctor_set(v_reuseFailAlloc_2986_, 3, v_auxDeclNGen_2972_);
lean_ctor_set(v_reuseFailAlloc_2986_, 4, v_traceState_2973_);
lean_ctor_set(v_reuseFailAlloc_2986_, 5, v_cache_2974_);
lean_ctor_set(v_reuseFailAlloc_2986_, 6, v_messages_2975_);
lean_ctor_set(v_reuseFailAlloc_2986_, 7, v_infoState_2976_);
lean_ctor_set(v_reuseFailAlloc_2986_, 8, v_snapshotTasks_2977_);
v___x_2982_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2983_ = lean_st_ref_set(v_a_2965_, v___x_2982_);
v___x_2984_ = lean_box(0);
v___x_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
return v___x_2985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0___boxed(lean_object* v_a_2989_, lean_object* v_ngen_2990_, lean_object* v_a_x3f_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_2989_, v_ngen_2990_, v_a_x3f_2991_);
lean_dec(v_a_x3f_2991_);
lean_dec(v_a_2989_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(uint8_t v_pu_3000_, lean_object* v_decl_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v_env_3007_; lean_object* v_nextMacroScope_3008_; lean_object* v_auxDeclNGen_3009_; lean_object* v_traceState_3010_; lean_object* v_cache_3011_; lean_object* v_messages_3012_; lean_object* v_infoState_3013_; lean_object* v_snapshotTasks_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3060_; 
v___x_3005_ = lean_st_ref_get(v_a_3003_);
v___x_3006_ = lean_st_ref_take(v_a_3003_);
v_env_3007_ = lean_ctor_get(v___x_3006_, 0);
v_nextMacroScope_3008_ = lean_ctor_get(v___x_3006_, 1);
v_auxDeclNGen_3009_ = lean_ctor_get(v___x_3006_, 3);
v_traceState_3010_ = lean_ctor_get(v___x_3006_, 4);
v_cache_3011_ = lean_ctor_get(v___x_3006_, 5);
v_messages_3012_ = lean_ctor_get(v___x_3006_, 6);
v_infoState_3013_ = lean_ctor_get(v___x_3006_, 7);
v_snapshotTasks_3014_ = lean_ctor_get(v___x_3006_, 8);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3060_ == 0)
{
lean_object* v_unused_3061_; 
v_unused_3061_ = lean_ctor_get(v___x_3006_, 2);
lean_dec(v_unused_3061_);
v___x_3016_ = v___x_3006_;
v_isShared_3017_ = v_isSharedCheck_3060_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_snapshotTasks_3014_);
lean_inc(v_infoState_3013_);
lean_inc(v_messages_3012_);
lean_inc(v_cache_3011_);
lean_inc(v_traceState_3010_);
lean_inc(v_auxDeclNGen_3009_);
lean_inc(v_nextMacroScope_3008_);
lean_inc(v_env_3007_);
lean_dec(v___x_3006_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3060_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; lean_object* v___x_3020_; 
v___x_3018_ = ((lean_object*)(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2));
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 2, v___x_3018_);
v___x_3020_ = v___x_3016_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_env_3007_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_nextMacroScope_3008_);
lean_ctor_set(v_reuseFailAlloc_3059_, 2, v___x_3018_);
lean_ctor_set(v_reuseFailAlloc_3059_, 3, v_auxDeclNGen_3009_);
lean_ctor_set(v_reuseFailAlloc_3059_, 4, v_traceState_3010_);
lean_ctor_set(v_reuseFailAlloc_3059_, 5, v_cache_3011_);
lean_ctor_set(v_reuseFailAlloc_3059_, 6, v_messages_3012_);
lean_ctor_set(v_reuseFailAlloc_3059_, 7, v_infoState_3013_);
lean_ctor_set(v_reuseFailAlloc_3059_, 8, v_snapshotTasks_3014_);
v___x_3020_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3021_; lean_object* v_ngen_3022_; lean_object* v___x_3023_; uint8_t v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; uint8_t v___x_3029_; lean_object* v_r_3030_; 
v___x_3021_ = lean_st_ref_set(v_a_3003_, v___x_3020_);
v_ngen_3022_ = lean_ctor_get(v___x_3005_, 2);
lean_inc_ref(v_ngen_3022_);
lean_dec(v___x_3005_);
v___x_3023_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_3024_ = 0;
v___x_3025_ = lean_box(v_pu_3000_);
v___x_3026_ = lean_box(v___x_3024_);
v___x_3027_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_internalize___boxed), 9, 4);
lean_closure_set(v___x_3027_, 0, v___x_3025_);
lean_closure_set(v___x_3027_, 1, v_decl_3001_);
lean_closure_set(v___x_3027_, 2, v___x_3023_);
lean_closure_set(v___x_3027_, 3, v___x_3026_);
v___x_3028_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
v___x_3029_ = 0;
lean_inc(v_a_3003_);
v_r_3030_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v___x_3027_, v___x_3028_, v___x_3029_, v_a_3002_, v_a_3003_);
if (lean_obj_tag(v_r_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3047_; 
v_a_3031_ = lean_ctor_get(v_r_3030_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v_r_3030_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3033_ = v_r_3030_;
v_isShared_3034_ = v_isSharedCheck_3047_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v_r_3030_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3047_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
lean_inc(v_a_3031_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set_tag(v___x_3033_, 1);
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
lean_object* v___x_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
v___x_3037_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3003_, v_ngen_3022_, v___x_3036_);
lean_dec_ref(v___x_3036_);
lean_dec(v_a_3003_);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3044_ == 0)
{
lean_object* v_unused_3045_; 
v_unused_3045_ = lean_ctor_get(v___x_3037_, 0);
lean_dec(v_unused_3045_);
v___x_3039_ = v___x_3037_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_dec(v___x_3037_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 0, v_a_3031_);
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3031_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
v_a_3048_ = lean_ctor_get(v_r_3030_, 0);
lean_inc(v_a_3048_);
lean_dec_ref(v_r_3030_);
v___x_3049_ = lean_box(0);
v___x_3050_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_3003_, v_ngen_3022_, v___x_3049_);
lean_dec(v_a_3003_);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3057_ == 0)
{
lean_object* v_unused_3058_; 
v_unused_3058_ = lean_ctor_get(v___x_3050_, 0);
lean_dec(v_unused_3058_);
v___x_3052_ = v___x_3050_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_dec(v___x_3050_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
lean_ctor_set_tag(v___x_3052_, 1);
lean_ctor_set(v___x_3052_, 0, v_a_3048_);
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3048_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___boxed(lean_object* v_pu_3062_, lean_object* v_decl_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_){
_start:
{
uint8_t v_pu_boxed_3067_; lean_object* v_res_3068_; 
v_pu_boxed_3067_ = lean_unbox(v_pu_3062_);
v_res_3068_ = l_Lean_Compiler_LCNF_normalizeFVarIds(v_pu_boxed_3067_, v_decl_3063_, v_a_3064_, v_a_3065_);
return v_res_3068_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
