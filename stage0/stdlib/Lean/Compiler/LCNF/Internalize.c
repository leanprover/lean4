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
v___x_428_ = lean_st_ref_set(v___y_400_, v___x_427_);
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
v___x_479_ = lean_st_ref_set(v_a_465_, v___x_478_);
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
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___f_662_; lean_object* v___x_8158__overap_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_659_ = l_StateRefT_x27_instMonad___redArg(v___x_658_);
v___x_660_ = l_Lean_instInhabitedExpr;
v___x_661_ = l_instInhabitedOfMonad___redArg(v___x_659_, v___x_660_);
v___f_662_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_662_, 0, v___x_661_);
v___x_8158__overap_663_ = lean_panic_fn_borrowed(v___f_662_, v_msg_602_);
lean_dec_ref(v___f_662_);
v___x_664_ = lean_box(v___y_603_);
lean_inc(v___y_608_);
lean_inc_ref(v___y_607_);
lean_inc(v___y_606_);
lean_inc_ref(v___y_605_);
lean_inc(v___y_604_);
v___x_665_ = lean_apply_7(v___x_8158__overap_663_, v___x_664_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, lean_box(0));
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
uint8_t v___y_8278__boxed_686_; lean_object* v_res_687_; 
v___y_8278__boxed_686_ = lean_unbox(v___y_679_);
v_res_687_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v_msg_678_, v___y_8278__boxed_686_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
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
lean_dec_ref(v_e_698_);
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
lean_dec_ref(v_val_712_);
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
lean_dec_ref(v___x_760_);
lean_inc_ref(v_arg_759_);
v___x_762_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_697_, v_arg_759_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_782_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_782_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_782_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_782_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___y_768_; uint8_t v___y_774_; size_t v___x_776_; size_t v___x_777_; uint8_t v___x_778_; 
v___x_776_ = lean_ptr_addr(v_fn_758_);
v___x_777_ = lean_ptr_addr(v_a_761_);
v___x_778_ = lean_usize_dec_eq(v___x_776_, v___x_777_);
if (v___x_778_ == 0)
{
v___y_774_ = v___x_778_;
goto v___jp_773_;
}
else
{
size_t v___x_779_; size_t v___x_780_; uint8_t v___x_781_; 
v___x_779_ = lean_ptr_addr(v_arg_759_);
v___x_780_ = lean_ptr_addr(v_a_763_);
v___x_781_ = lean_usize_dec_eq(v___x_779_, v___x_780_);
v___y_774_ = v___x_781_;
goto v___jp_773_;
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
v___jp_773_:
{
if (v___y_774_ == 0)
{
lean_object* v___x_775_; 
lean_dec_ref(v_e_698_);
v___x_775_ = l_Lean_Expr_app___override(v_a_761_, v_a_763_);
v___y_768_ = v___x_775_;
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
}
}
else
{
lean_dec(v_a_761_);
lean_dec_ref(v_e_698_);
return v___x_762_;
}
}
else
{
lean_dec_ref(v_e_698_);
return v___x_760_;
}
}
case 6:
{
lean_object* v_binderName_783_; lean_object* v_binderType_784_; lean_object* v_body_785_; uint8_t v_binderInfo_786_; lean_object* v___x_787_; 
v_binderName_783_ = lean_ctor_get(v_e_698_, 0);
v_binderType_784_ = lean_ctor_get(v_e_698_, 1);
v_body_785_ = lean_ctor_get(v_e_698_, 2);
v_binderInfo_786_ = lean_ctor_get_uint8(v_e_698_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_784_);
v___x_787_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_697_, v_binderType_784_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_789_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref(v___x_787_);
lean_inc_ref(v_body_785_);
v___x_789_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_697_, v_body_785_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_814_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_814_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_814_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_814_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
uint8_t v___y_795_; size_t v___x_808_; size_t v___x_809_; uint8_t v___x_810_; 
v___x_808_ = lean_ptr_addr(v_binderType_784_);
v___x_809_ = lean_ptr_addr(v_a_788_);
v___x_810_ = lean_usize_dec_eq(v___x_808_, v___x_809_);
if (v___x_810_ == 0)
{
v___y_795_ = v___x_810_;
goto v___jp_794_;
}
else
{
size_t v___x_811_; size_t v___x_812_; uint8_t v___x_813_; 
v___x_811_ = lean_ptr_addr(v_body_785_);
v___x_812_ = lean_ptr_addr(v_a_790_);
v___x_813_ = lean_usize_dec_eq(v___x_811_, v___x_812_);
v___y_795_ = v___x_813_;
goto v___jp_794_;
}
v___jp_794_:
{
if (v___y_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_798_; 
lean_inc(v_binderName_783_);
lean_dec_ref(v_e_698_);
v___x_796_ = l_Lean_Expr_lam___override(v_binderName_783_, v_a_788_, v_a_790_, v_binderInfo_786_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_796_);
v___x_798_ = v___x_792_;
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
uint8_t v___x_800_; 
v___x_800_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_786_, v_binderInfo_786_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v___x_803_; 
lean_inc(v_binderName_783_);
lean_dec_ref(v_e_698_);
v___x_801_ = l_Lean_Expr_lam___override(v_binderName_783_, v_a_788_, v_a_790_, v_binderInfo_786_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_801_);
v___x_803_ = v___x_792_;
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
lean_object* v___x_806_; 
lean_dec(v_a_790_);
lean_dec(v_a_788_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v_e_698_);
v___x_806_ = v___x_792_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_e_698_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
}
}
else
{
lean_dec(v_a_788_);
lean_dec_ref(v_e_698_);
return v___x_789_;
}
}
else
{
lean_dec_ref(v_e_698_);
return v___x_787_;
}
}
case 7:
{
lean_object* v_binderName_815_; lean_object* v_binderType_816_; lean_object* v_body_817_; uint8_t v_binderInfo_818_; lean_object* v___x_819_; 
v_binderName_815_ = lean_ctor_get(v_e_698_, 0);
v_binderType_816_ = lean_ctor_get(v_e_698_, 1);
v_body_817_ = lean_ctor_get(v_e_698_, 2);
v_binderInfo_818_ = lean_ctor_get_uint8(v_e_698_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_816_);
v___x_819_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_697_, v_binderType_816_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_821_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref(v___x_819_);
lean_inc_ref(v_body_817_);
v___x_821_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_697_, v_body_817_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_846_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_846_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_846_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_846_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
uint8_t v___y_827_; size_t v___x_840_; size_t v___x_841_; uint8_t v___x_842_; 
v___x_840_ = lean_ptr_addr(v_binderType_816_);
v___x_841_ = lean_ptr_addr(v_a_820_);
v___x_842_ = lean_usize_dec_eq(v___x_840_, v___x_841_);
if (v___x_842_ == 0)
{
v___y_827_ = v___x_842_;
goto v___jp_826_;
}
else
{
size_t v___x_843_; size_t v___x_844_; uint8_t v___x_845_; 
v___x_843_ = lean_ptr_addr(v_body_817_);
v___x_844_ = lean_ptr_addr(v_a_822_);
v___x_845_ = lean_usize_dec_eq(v___x_843_, v___x_844_);
v___y_827_ = v___x_845_;
goto v___jp_826_;
}
v___jp_826_:
{
if (v___y_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_830_; 
lean_inc(v_binderName_815_);
lean_dec_ref(v_e_698_);
v___x_828_ = l_Lean_Expr_forallE___override(v_binderName_815_, v_a_820_, v_a_822_, v_binderInfo_818_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_828_);
v___x_830_ = v___x_824_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
else
{
uint8_t v___x_832_; 
v___x_832_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_818_, v_binderInfo_818_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_835_; 
lean_inc(v_binderName_815_);
lean_dec_ref(v_e_698_);
v___x_833_ = l_Lean_Expr_forallE___override(v_binderName_815_, v_a_820_, v_a_822_, v_binderInfo_818_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_833_);
v___x_835_ = v___x_824_;
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
lean_object* v___x_838_; 
lean_dec(v_a_822_);
lean_dec(v_a_820_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v_e_698_);
v___x_838_ = v___x_824_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_e_698_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
}
else
{
lean_dec(v_a_820_);
lean_dec_ref(v_e_698_);
return v___x_821_;
}
}
else
{
lean_dec_ref(v_e_698_);
return v___x_819_;
}
}
case 8:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec_ref(v_e_698_);
v___x_847_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3, &l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3);
v___x_848_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v___x_847_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
return v___x_848_;
}
case 10:
{
lean_object* v_data_849_; lean_object* v_expr_850_; lean_object* v___x_851_; 
v_data_849_ = lean_ctor_get(v_e_698_, 0);
v_expr_850_ = lean_ctor_get(v_e_698_, 1);
lean_inc_ref(v_expr_850_);
v___x_851_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_697_, v_expr_850_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_866_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_866_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_866_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_866_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
size_t v___x_856_; size_t v___x_857_; uint8_t v___x_858_; 
v___x_856_ = lean_ptr_addr(v_expr_850_);
v___x_857_ = lean_ptr_addr(v_a_852_);
v___x_858_ = lean_usize_dec_eq(v___x_856_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_861_; 
lean_inc(v_data_849_);
lean_dec_ref(v_e_698_);
v___x_859_ = l_Lean_Expr_mdata___override(v_data_849_, v_a_852_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_859_);
v___x_861_ = v___x_854_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
else
{
lean_object* v___x_864_; 
lean_dec(v_a_852_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v_e_698_);
v___x_864_ = v___x_854_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_e_698_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
else
{
lean_dec_ref(v_e_698_);
return v___x_851_;
}
}
case 11:
{
lean_object* v_typeName_867_; lean_object* v_idx_868_; lean_object* v_struct_869_; lean_object* v___x_870_; 
v_typeName_867_ = lean_ctor_get(v_e_698_, 0);
v_idx_868_ = lean_ctor_get(v_e_698_, 1);
v_struct_869_ = lean_ctor_get(v_e_698_, 2);
lean_inc_ref(v_struct_869_);
v___x_870_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_697_, v_struct_869_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_885_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_885_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_885_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_885_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
size_t v___x_875_; size_t v___x_876_; uint8_t v___x_877_; 
v___x_875_ = lean_ptr_addr(v_struct_869_);
v___x_876_ = lean_ptr_addr(v_a_871_);
v___x_877_ = lean_usize_dec_eq(v___x_875_, v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v___x_880_; 
lean_inc(v_idx_868_);
lean_inc(v_typeName_867_);
lean_dec_ref(v_e_698_);
v___x_878_ = l_Lean_Expr_proj___override(v_typeName_867_, v_idx_868_, v_a_871_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_878_);
v___x_880_ = v___x_873_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
else
{
lean_object* v___x_883_; 
lean_dec(v_a_871_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v_e_698_);
v___x_883_ = v___x_873_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_e_698_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_dec_ref(v_e_698_);
return v___x_870_;
}
}
default: 
{
lean_object* v___x_886_; 
v___x_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_886_, 0, v_e_698_);
return v___x_886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(uint8_t v_pu_887_, lean_object* v_e_888_, uint8_t v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
if (lean_obj_tag(v_e_888_) == 5)
{
lean_object* v_fn_896_; lean_object* v_arg_897_; lean_object* v___x_898_; 
v_fn_896_ = lean_ctor_get(v_e_888_, 0);
v_arg_897_ = lean_ctor_get(v_e_888_, 1);
lean_inc_ref(v_fn_896_);
v___x_898_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_887_, v_fn_896_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_900_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref(v___x_898_);
lean_inc_ref(v_arg_897_);
v___x_900_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_887_, v_arg_897_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_920_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_920_ == 0)
{
v___x_903_ = v___x_900_;
v_isShared_904_ = v_isSharedCheck_920_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_920_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
uint8_t v___y_906_; size_t v___x_914_; size_t v___x_915_; uint8_t v___x_916_; 
v___x_914_ = lean_ptr_addr(v_fn_896_);
v___x_915_ = lean_ptr_addr(v_a_899_);
v___x_916_ = lean_usize_dec_eq(v___x_914_, v___x_915_);
if (v___x_916_ == 0)
{
v___y_906_ = v___x_916_;
goto v___jp_905_;
}
else
{
size_t v___x_917_; size_t v___x_918_; uint8_t v___x_919_; 
v___x_917_ = lean_ptr_addr(v_arg_897_);
v___x_918_ = lean_ptr_addr(v_a_901_);
v___x_919_ = lean_usize_dec_eq(v___x_917_, v___x_918_);
v___y_906_ = v___x_919_;
goto v___jp_905_;
}
v___jp_905_:
{
if (v___y_906_ == 0)
{
lean_object* v___x_907_; lean_object* v___x_909_; 
lean_dec_ref(v_e_888_);
v___x_907_ = l_Lean_Expr_app___override(v_a_899_, v_a_901_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_907_);
v___x_909_ = v___x_903_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
else
{
lean_object* v___x_912_; 
lean_dec(v_a_901_);
lean_dec(v_a_899_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v_e_888_);
v___x_912_ = v___x_903_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_e_888_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
else
{
lean_dec(v_a_899_);
lean_dec_ref(v_e_888_);
return v___x_900_;
}
}
else
{
lean_dec_ref(v_e_888_);
return v___x_898_;
}
}
else
{
lean_object* v___x_921_; 
v___x_921_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_887_, v_e_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
return v___x_921_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp___boxed(lean_object* v_pu_922_, lean_object* v_e_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
uint8_t v_pu_boxed_931_; uint8_t v_a_boxed_932_; lean_object* v_res_933_; 
v_pu_boxed_931_ = lean_unbox(v_pu_922_);
v_a_boxed_932_ = lean_unbox(v_a_924_);
v_res_933_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_boxed_931_, v_e_923_, v_a_boxed_932_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___boxed(lean_object* v_pu_934_, lean_object* v_e_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
uint8_t v_pu_boxed_943_; uint8_t v_a_boxed_944_; lean_object* v_res_945_; 
v_pu_boxed_943_ = lean_unbox(v_pu_934_);
v_a_boxed_944_ = lean_unbox(v_a_936_);
v_res_945_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_boxed_943_, v_e_935_, v_a_boxed_944_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec(v_a_937_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(lean_object* v_00_u03b2_946_, lean_object* v_m_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v_m_947_, v_a_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___boxed(lean_object* v_00_u03b2_950_, lean_object* v_m_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(v_00_u03b2_950_, v_m_951_, v_a_952_);
lean_dec(v_a_952_);
lean_dec_ref(v_m_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(lean_object* v_00_u03b2_954_, lean_object* v_a_955_, lean_object* v_x_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_955_, v_x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_958_, lean_object* v_a_959_, lean_object* v_x_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(v_00_u03b2_958_, v_a_959_, v_x_960_);
lean_dec(v_x_960_);
lean_dec(v_a_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(uint8_t v_pu_962_, lean_object* v_e_963_, uint8_t v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
uint8_t v___x_971_; uint8_t v___x_972_; 
v___x_971_ = 1;
v___x_972_ = l_Lean_Compiler_LCNF_instDecidableEqPurity(v_pu_962_, v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; 
v___x_973_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_962_, v_e_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
return v___x_973_;
}
else
{
lean_object* v___x_974_; 
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v_e_963_);
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___boxed(lean_object* v_pu_975_, lean_object* v_e_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
uint8_t v_pu_boxed_984_; uint8_t v_a_boxed_985_; lean_object* v_res_986_; 
v_pu_boxed_984_ = lean_unbox(v_pu_975_);
v_a_boxed_985_ = lean_unbox(v_a_977_);
v_res_986_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_boxed_984_, v_e_976_, v_a_boxed_985_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t v_pu_987_, lean_object* v_p_988_, uint8_t v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v_fvarId_996_; lean_object* v_binderName_997_; lean_object* v_type_998_; uint8_t v_borrow_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1047_; 
v_fvarId_996_ = lean_ctor_get(v_p_988_, 0);
v_binderName_997_ = lean_ctor_get(v_p_988_, 1);
v_type_998_ = lean_ctor_get(v_p_988_, 2);
v_borrow_999_ = lean_ctor_get_uint8(v_p_988_, sizeof(void*)*3);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_p_988_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1001_ = v_p_988_;
v_isShared_1002_ = v_isSharedCheck_1047_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_type_998_);
lean_inc(v_binderName_997_);
lean_inc(v_fvarId_996_);
lean_dec(v_p_988_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1047_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v_a_1004_; lean_object* v___x_1005_; 
v___x_1003_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_997_, v_a_989_, v_a_992_);
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref(v___x_1003_);
v___x_1005_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_987_, v_type_998_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref(v___x_1005_);
v___x_1007_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_996_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1030_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1010_ = v___x_1007_;
v_isShared_1011_ = v_isSharedCheck_1030_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1030_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; lean_object* v_lctx_1013_; lean_object* v_nextIdx_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1029_; 
v___x_1012_ = lean_st_ref_take(v_a_992_);
v_lctx_1013_ = lean_ctor_get(v___x_1012_, 0);
v_nextIdx_1014_ = lean_ctor_get(v___x_1012_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1016_ = v___x_1012_;
v_isShared_1017_ = v_isSharedCheck_1029_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_nextIdx_1014_);
lean_inc(v_lctx_1013_);
lean_dec(v___x_1012_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1029_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 2, v_a_1006_);
lean_ctor_set(v___x_1001_, 1, v_a_1004_);
lean_ctor_set(v___x_1001_, 0, v_a_1008_);
v___x_1019_ = v___x_1001_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1008_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_a_1004_);
lean_ctor_set(v_reuseFailAlloc_1028_, 2, v_a_1006_);
lean_ctor_set_uint8(v_reuseFailAlloc_1028_, sizeof(void*)*3, v_borrow_999_);
v___x_1019_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1020_; lean_object* v___x_1022_; 
lean_inc_ref(v___x_1019_);
v___x_1020_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_987_, v_lctx_1013_, v___x_1019_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1020_);
v___x_1022_ = v___x_1016_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_nextIdx_1014_);
v___x_1022_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1023_; lean_object* v___x_1025_; 
v___x_1023_ = lean_st_ref_set(v_a_992_, v___x_1022_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1019_);
v___x_1025_ = v___x_1010_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1019_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec(v_a_1006_);
lean_dec(v_a_1004_);
lean_del_object(v___x_1001_);
v_a_1031_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1007_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1007_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec(v_a_1004_);
lean_del_object(v___x_1001_);
lean_dec(v_fvarId_996_);
v_a_1039_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1005_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1005_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(lean_object* v_pu_1048_, lean_object* v_p_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
uint8_t v_pu_boxed_1057_; uint8_t v_a_boxed_1058_; lean_object* v_res_1059_; 
v_pu_boxed_1057_ = lean_unbox(v_pu_1048_);
v_a_boxed_1058_ = lean_unbox(v_a_1050_);
v_res_1059_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_boxed_1057_, v_p_1049_, v_a_boxed_1058_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg(uint8_t v_pu_1060_, lean_object* v_arg_1061_, uint8_t v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
switch(lean_obj_tag(v_arg_1061_))
{
case 0:
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1069_, 0, v_arg_1061_);
return v___x_1069_;
}
case 1:
{
lean_object* v_fvarId_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_fvarId_1070_ = lean_ctor_get(v_arg_1061_, 0);
v___x_1071_ = lean_st_ref_get(v_a_1063_);
v___x_1072_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v___x_1071_, v_fvarId_1070_);
lean_dec(v___x_1071_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v_arg_1061_);
return v___x_1073_;
}
else
{
lean_object* v_val_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref(v_arg_1061_);
v_val_1074_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1076_ = v___x_1072_;
v_isShared_1077_ = v_isSharedCheck_1104_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_val_1074_);
lean_dec(v___x_1072_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1104_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
switch(lean_obj_tag(v_val_1074_))
{
case 0:
{
lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1078_ = lean_box(0);
if (v_isShared_1077_ == 0)
{
lean_ctor_set_tag(v___x_1076_, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1078_);
v___x_1080_ = v___x_1076_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
case 1:
{
lean_object* v_fvarId_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1092_; 
v_fvarId_1082_ = lean_ctor_get(v_val_1074_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_val_1074_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1084_ = v_val_1074_;
v_isShared_1085_ = v_isSharedCheck_1092_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_fvarId_1082_);
lean_dec(v_val_1074_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1092_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_fvarId_1082_);
v___x_1087_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1089_; 
if (v_isShared_1077_ == 0)
{
lean_ctor_set_tag(v___x_1076_, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1087_);
v___x_1089_ = v___x_1076_;
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
}
}
default: 
{
lean_object* v_expr_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1103_; 
v_expr_1093_ = lean_ctor_get(v_val_1074_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_val_1074_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1095_ = v_val_1074_;
v_isShared_1096_ = v_isSharedCheck_1103_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_expr_1093_);
lean_dec(v_val_1074_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1103_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_expr_1093_);
v___x_1098_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1100_; 
if (v_isShared_1077_ == 0)
{
lean_ctor_set_tag(v___x_1076_, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1098_);
v___x_1100_ = v___x_1076_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
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
lean_object* v_expr_1105_; lean_object* v___x_1106_; 
v_expr_1105_ = lean_ctor_get(v_arg_1061_, 0);
lean_inc_ref(v_expr_1105_);
v___x_1106_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1060_, v_expr_1105_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1115_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1109_ = v___x_1106_;
v_isShared_1110_ = v_isSharedCheck_1115_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1106_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1115_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1111_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1060_, v_arg_1061_, v_a_1107_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1111_);
v___x_1113_ = v___x_1109_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec_ref(v_arg_1061_);
v_a_1116_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1106_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1106_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg___boxed(lean_object* v_pu_1124_, lean_object* v_arg_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
uint8_t v_pu_boxed_1133_; uint8_t v_a_boxed_1134_; lean_object* v_res_1135_; 
v_pu_boxed_1133_ = lean_unbox(v_pu_1124_);
v_a_boxed_1134_ = lean_unbox(v_a_1126_);
v_res_1135_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_boxed_1133_, v_arg_1125_, v_a_boxed_1134_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(uint8_t v_pu_1136_, size_t v_sz_1137_, size_t v_i_1138_, lean_object* v_bs_1139_, uint8_t v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
uint8_t v___x_1147_; 
v___x_1147_ = lean_usize_dec_lt(v_i_1138_, v_sz_1137_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_bs_1139_);
return v___x_1148_;
}
else
{
lean_object* v_v_1149_; lean_object* v___x_1150_; 
v_v_1149_ = lean_array_uget_borrowed(v_bs_1139_, v_i_1138_);
lean_inc(v_v_1149_);
v___x_1150_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_1136_, v_v_1149_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1152_; lean_object* v_bs_x27_1153_; size_t v___x_1154_; size_t v___x_1155_; lean_object* v___x_1156_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref(v___x_1150_);
v___x_1152_ = lean_unsigned_to_nat(0u);
v_bs_x27_1153_ = lean_array_uset(v_bs_1139_, v_i_1138_, v___x_1152_);
v___x_1154_ = ((size_t)1ULL);
v___x_1155_ = lean_usize_add(v_i_1138_, v___x_1154_);
v___x_1156_ = lean_array_uset(v_bs_x27_1153_, v_i_1138_, v_a_1151_);
v_i_1138_ = v___x_1155_;
v_bs_1139_ = v___x_1156_;
goto _start;
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec_ref(v_bs_1139_);
v_a_1158_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1150_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1150_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0___boxed(lean_object* v_pu_1166_, lean_object* v_sz_1167_, lean_object* v_i_1168_, lean_object* v_bs_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
uint8_t v_pu_boxed_1177_; size_t v_sz_boxed_1178_; size_t v_i_boxed_1179_; uint8_t v___y_341__boxed_1180_; lean_object* v_res_1181_; 
v_pu_boxed_1177_ = lean_unbox(v_pu_1166_);
v_sz_boxed_1178_ = lean_unbox_usize(v_sz_1167_);
lean_dec(v_sz_1167_);
v_i_boxed_1179_ = lean_unbox_usize(v_i_1168_);
lean_dec(v_i_1168_);
v___y_341__boxed_1180_ = lean_unbox(v___y_1170_);
v_res_1181_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_boxed_1177_, v_sz_boxed_1178_, v_i_boxed_1179_, v_bs_1169_, v___y_341__boxed_1180_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs(uint8_t v_pu_1182_, lean_object* v_args_1183_, uint8_t v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
size_t v_sz_1191_; size_t v___x_1192_; lean_object* v___x_1193_; 
v_sz_1191_ = lean_array_size(v_args_1183_);
v___x_1192_ = ((size_t)0ULL);
v___x_1193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_1182_, v_sz_1191_, v___x_1192_, v_args_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs___boxed(lean_object* v_pu_1194_, lean_object* v_args_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
uint8_t v_pu_boxed_1203_; uint8_t v_a_boxed_1204_; lean_object* v_res_1205_; 
v_pu_boxed_1203_ = lean_unbox(v_pu_1194_);
v_a_boxed_1204_ = lean_unbox(v_a_1196_);
v_res_1205_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_boxed_1203_, v_args_1195_, v_a_boxed_1204_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec(v_a_1197_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(uint8_t v_pu_1206_, lean_object* v_e_1207_, uint8_t v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_fvarId_1216_; lean_object* v___y_1217_; lean_object* v_args_1233_; uint8_t v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; 
switch(lean_obj_tag(v_e_1207_))
{
case 2:
{
lean_object* v_struct_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; lean_object* v___x_1261_; 
v_struct_1258_ = lean_ctor_get(v_e_1207_, 2);
v___x_1259_ = lean_st_ref_get(v_a_1209_);
v___x_1260_ = 1;
lean_inc(v_struct_1258_);
v___x_1261_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1259_, v_struct_1258_, v___x_1260_);
lean_dec(v___x_1259_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_fvarId_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1270_; 
v_fvarId_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_fvarId_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1266_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1206_, v_e_1207_, v_fvarId_1262_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1266_);
v___x_1268_ = v___x_1264_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
lean_dec_ref(v_e_1207_);
v___x_1271_ = lean_box(1);
v___x_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
return v___x_1272_;
}
}
case 3:
{
lean_object* v_args_1273_; lean_object* v___x_1274_; 
v_args_1273_ = lean_ctor_get(v_e_1207_, 2);
lean_inc_ref(v_args_1273_);
v___x_1274_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1206_, v_args_1273_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1283_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1283_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1283_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1279_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1206_, v_e_1207_, v_a_1275_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1279_);
v___x_1281_ = v___x_1277_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref(v_e_1207_);
v_a_1284_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1274_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1274_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
case 4:
{
lean_object* v_fvarId_1292_; lean_object* v_args_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; lean_object* v___x_1296_; 
v_fvarId_1292_ = lean_ctor_get(v_e_1207_, 0);
v_args_1293_ = lean_ctor_get(v_e_1207_, 1);
v___x_1294_ = lean_st_ref_get(v_a_1209_);
v___x_1295_ = 1;
lean_inc(v_fvarId_1292_);
v___x_1296_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1294_, v_fvarId_1292_, v___x_1295_);
lean_dec(v___x_1294_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_fvarId_1297_; lean_object* v___x_1298_; 
v_fvarId_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_fvarId_1297_);
lean_dec_ref(v___x_1296_);
lean_inc_ref(v_args_1293_);
v___x_1298_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1206_, v_args_1293_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1307_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1307_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1307_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1303_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_1206_, v_e_1207_, v_fvarId_1297_, v_a_1299_);
lean_dec_ref(v_e_1207_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1303_);
v___x_1305_ = v___x_1301_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec(v_fvarId_1297_);
lean_dec_ref(v_e_1207_);
v_a_1308_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1298_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1298_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_dec_ref(v_e_1207_);
v___x_1316_ = lean_box(1);
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
return v___x_1317_;
}
}
case 5:
{
lean_object* v_args_1318_; lean_object* v___x_1319_; 
v_args_1318_ = lean_ctor_get(v_e_1207_, 1);
lean_inc_ref(v_args_1318_);
v___x_1319_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1206_, v_args_1318_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1328_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1322_ = v___x_1319_;
v_isShared_1323_ = v_isSharedCheck_1328_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1319_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1328_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1324_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1206_, v_e_1207_, v_a_1320_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v___x_1324_);
v___x_1326_ = v___x_1322_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec_ref(v_e_1207_);
v_a_1329_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1319_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1319_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
case 6:
{
lean_object* v_var_1337_; 
v_var_1337_ = lean_ctor_get(v_e_1207_, 1);
lean_inc(v_var_1337_);
v_fvarId_1216_ = v_var_1337_;
v___y_1217_ = v_a_1209_;
goto v___jp_1215_;
}
case 7:
{
lean_object* v_var_1338_; 
v_var_1338_ = lean_ctor_get(v_e_1207_, 1);
lean_inc(v_var_1338_);
v_fvarId_1216_ = v_var_1338_;
v___y_1217_ = v_a_1209_;
goto v___jp_1215_;
}
case 8:
{
lean_object* v_var_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; lean_object* v___x_1342_; 
v_var_1339_ = lean_ctor_get(v_e_1207_, 2);
v___x_1340_ = lean_st_ref_get(v_a_1209_);
v___x_1341_ = 1;
lean_inc(v_var_1339_);
v___x_1342_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1340_, v_var_1339_, v___x_1341_);
lean_dec(v___x_1340_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_fvarId_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1351_; 
v_fvarId_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_fvarId_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1347_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1206_, v_e_1207_, v_fvarId_1343_);
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
lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_dec_ref(v_e_1207_);
v___x_1352_ = lean_box(1);
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
return v___x_1353_;
}
}
case 9:
{
lean_object* v_args_1354_; 
v_args_1354_ = lean_ctor_get(v_e_1207_, 1);
lean_inc_ref(v_args_1354_);
v_args_1233_ = v_args_1354_;
v___y_1234_ = v_a_1208_;
v___y_1235_ = v_a_1209_;
v___y_1236_ = v_a_1210_;
v___y_1237_ = v_a_1211_;
v___y_1238_ = v_a_1212_;
v___y_1239_ = v_a_1213_;
goto v___jp_1232_;
}
case 10:
{
lean_object* v_args_1355_; 
v_args_1355_ = lean_ctor_get(v_e_1207_, 1);
lean_inc_ref(v_args_1355_);
v_args_1233_ = v_args_1355_;
v___y_1234_ = v_a_1208_;
v___y_1235_ = v_a_1209_;
v___y_1236_ = v_a_1210_;
v___y_1237_ = v_a_1211_;
v___y_1238_ = v_a_1212_;
v___y_1239_ = v_a_1213_;
goto v___jp_1232_;
}
case 11:
{
lean_object* v_n_1356_; lean_object* v_var_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; lean_object* v___x_1360_; 
v_n_1356_ = lean_ctor_get(v_e_1207_, 0);
lean_inc(v_n_1356_);
v_var_1357_ = lean_ctor_get(v_e_1207_, 1);
v___x_1358_ = lean_st_ref_get(v_a_1209_);
v___x_1359_ = 1;
lean_inc(v_var_1357_);
v___x_1360_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1358_, v_var_1357_, v___x_1359_);
lean_dec(v___x_1358_);
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
v___x_1365_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_1206_, v_e_1207_, v_n_1356_, v_fvarId_1361_);
lean_dec_ref(v_e_1207_);
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
lean_dec(v_n_1356_);
lean_dec_ref(v_e_1207_);
v___x_1370_ = lean_box(1);
v___x_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
return v___x_1371_;
}
}
case 12:
{
lean_object* v_var_1372_; lean_object* v_i_1373_; uint8_t v_updateHeader_1374_; lean_object* v_args_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; lean_object* v___x_1378_; 
v_var_1372_ = lean_ctor_get(v_e_1207_, 0);
v_i_1373_ = lean_ctor_get(v_e_1207_, 1);
lean_inc_ref(v_i_1373_);
v_updateHeader_1374_ = lean_ctor_get_uint8(v_e_1207_, sizeof(void*)*3);
v_args_1375_ = lean_ctor_get(v_e_1207_, 2);
v___x_1376_ = lean_st_ref_get(v_a_1209_);
v___x_1377_ = 1;
lean_inc(v_var_1372_);
v___x_1378_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1376_, v_var_1372_, v___x_1377_);
lean_dec(v___x_1376_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_fvarId_1379_; lean_object* v___x_1380_; 
v_fvarId_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_fvarId_1379_);
lean_dec_ref(v___x_1378_);
lean_inc_ref(v_args_1375_);
v___x_1380_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1206_, v_args_1375_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1389_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1389_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1389_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1385_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_1206_, v_e_1207_, v_fvarId_1379_, v_i_1373_, v_updateHeader_1374_, v_a_1381_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1385_);
v___x_1387_ = v___x_1383_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec(v_fvarId_1379_);
lean_dec_ref(v_i_1373_);
lean_dec_ref(v_e_1207_);
v_a_1390_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1380_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1380_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_dec_ref(v_i_1373_);
lean_dec_ref(v_e_1207_);
v___x_1398_ = lean_box(1);
v___x_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
return v___x_1399_;
}
}
case 13:
{
lean_object* v_ty_1400_; lean_object* v_fvarId_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; lean_object* v___x_1404_; 
v_ty_1400_ = lean_ctor_get(v_e_1207_, 0);
lean_inc_ref(v_ty_1400_);
v_fvarId_1401_ = lean_ctor_get(v_e_1207_, 1);
v___x_1402_ = lean_st_ref_get(v_a_1209_);
v___x_1403_ = 1;
lean_inc(v_fvarId_1401_);
v___x_1404_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1402_, v_fvarId_1401_, v___x_1403_);
lean_dec(v___x_1402_);
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
v___x_1409_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_1206_, v_e_1207_, v_ty_1400_, v_fvarId_1405_);
lean_dec_ref(v_e_1207_);
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
lean_dec_ref(v_ty_1400_);
lean_dec_ref(v_e_1207_);
v___x_1414_ = lean_box(1);
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
return v___x_1415_;
}
}
case 14:
{
lean_object* v_fvarId_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; lean_object* v___x_1419_; 
v_fvarId_1416_ = lean_ctor_get(v_e_1207_, 0);
v___x_1417_ = lean_st_ref_get(v_a_1209_);
v___x_1418_ = 1;
lean_inc(v_fvarId_1416_);
v___x_1419_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1417_, v_fvarId_1416_, v___x_1418_);
lean_dec(v___x_1417_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_fvarId_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1428_; 
v_fvarId_1420_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1422_ = v___x_1419_;
v_isShared_1423_ = v_isSharedCheck_1428_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_fvarId_1420_);
lean_dec(v___x_1419_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1428_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1424_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_1206_, v_e_1207_, v_fvarId_1420_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v___x_1424_);
v___x_1426_ = v___x_1422_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
else
{
lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1436_; 
v_isSharedCheck_1436_ = !lean_is_exclusive(v_e_1207_);
if (v_isSharedCheck_1436_ == 0)
{
lean_object* v_unused_1437_; 
v_unused_1437_ = lean_ctor_get(v_e_1207_, 0);
lean_dec(v_unused_1437_);
v___x_1430_ = v_e_1207_;
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
else
{
lean_dec(v_e_1207_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = lean_box(1);
if (v_isShared_1431_ == 0)
{
lean_ctor_set_tag(v___x_1430_, 0);
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
}
case 15:
{
lean_object* v_fvarId_1438_; lean_object* v___x_1439_; uint8_t v___x_1440_; lean_object* v___x_1441_; 
v_fvarId_1438_ = lean_ctor_get(v_e_1207_, 0);
v___x_1439_ = lean_st_ref_get(v_a_1209_);
v___x_1440_ = 1;
lean_inc(v_fvarId_1438_);
v___x_1441_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1439_, v_fvarId_1438_, v___x_1440_);
lean_dec(v___x_1439_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_fvarId_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1450_; 
v_fvarId_1442_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1444_ = v___x_1441_;
v_isShared_1445_ = v_isSharedCheck_1450_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_fvarId_1442_);
lean_dec(v___x_1441_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1450_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1446_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_1206_, v_e_1207_, v_fvarId_1442_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1446_);
v___x_1448_ = v___x_1444_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1446_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
else
{
lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1458_; 
v_isSharedCheck_1458_ = !lean_is_exclusive(v_e_1207_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; 
v_unused_1459_ = lean_ctor_get(v_e_1207_, 0);
lean_dec(v_unused_1459_);
v___x_1452_ = v_e_1207_;
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
else
{
lean_dec(v_e_1207_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1454_ = lean_box(1);
if (v_isShared_1453_ == 0)
{
lean_ctor_set_tag(v___x_1452_, 0);
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
}
default: 
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v_e_1207_);
return v___x_1460_;
}
}
v___jp_1215_:
{
lean_object* v___x_1218_; uint8_t v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = lean_st_ref_get(v___y_1217_);
v___x_1219_ = 1;
v___x_1220_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1218_, v_fvarId_1216_, v___x_1219_);
lean_dec(v___x_1218_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_fvarId_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1229_; 
v_fvarId_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1229_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_fvarId_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1229_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1225_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1206_, v_e_1207_, v_fvarId_1221_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1225_);
v___x_1227_ = v___x_1223_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_dec(v_e_1207_);
v___x_1230_ = lean_box(1);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
return v___x_1231_;
}
}
v___jp_1232_:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1206_, v_args_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1249_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1245_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1206_, v_e_1207_, v_a_1241_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1245_);
v___x_1247_ = v___x_1243_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v_e_1207_);
v_a_1250_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1240_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1240_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue___boxed(lean_object* v_pu_1461_, lean_object* v_e_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
uint8_t v_pu_boxed_1470_; uint8_t v_a_boxed_1471_; lean_object* v_res_1472_; 
v_pu_boxed_1470_ = lean_unbox(v_pu_1461_);
v_a_boxed_1471_ = lean_unbox(v_a_1463_);
v_res_1472_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_boxed_1470_, v_e_1462_, v_a_boxed_1471_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(uint8_t v_pu_1473_, lean_object* v_decl_1474_, uint8_t v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_){
_start:
{
lean_object* v_fvarId_1482_; lean_object* v_binderName_1483_; lean_object* v_type_1484_; lean_object* v_value_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1543_; 
v_fvarId_1482_ = lean_ctor_get(v_decl_1474_, 0);
v_binderName_1483_ = lean_ctor_get(v_decl_1474_, 1);
v_type_1484_ = lean_ctor_get(v_decl_1474_, 2);
v_value_1485_ = lean_ctor_get(v_decl_1474_, 3);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_decl_1474_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1487_ = v_decl_1474_;
v_isShared_1488_ = v_isSharedCheck_1543_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_value_1485_);
lean_inc(v_type_1484_);
lean_inc(v_binderName_1483_);
lean_inc(v_fvarId_1482_);
lean_dec(v_decl_1474_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1543_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v_a_1490_; lean_object* v___x_1491_; 
v___x_1489_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_1483_, v_a_1475_, v_a_1478_);
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref(v___x_1489_);
v___x_1491_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1473_, v_type_1484_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1493_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref(v___x_1491_);
v___x_1493_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_1473_, v_value_1485_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1495_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref(v___x_1493_);
v___x_1495_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_1482_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1518_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1498_ = v___x_1495_;
v_isShared_1499_ = v_isSharedCheck_1518_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1495_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1518_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v_lctx_1501_; lean_object* v_nextIdx_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1517_; 
v___x_1500_ = lean_st_ref_take(v_a_1478_);
v_lctx_1501_ = lean_ctor_get(v___x_1500_, 0);
v_nextIdx_1502_ = lean_ctor_get(v___x_1500_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1504_ = v___x_1500_;
v_isShared_1505_ = v_isSharedCheck_1517_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_nextIdx_1502_);
lean_inc(v_lctx_1501_);
lean_dec(v___x_1500_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1517_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 3, v_a_1494_);
lean_ctor_set(v___x_1487_, 2, v_a_1492_);
lean_ctor_set(v___x_1487_, 1, v_a_1490_);
lean_ctor_set(v___x_1487_, 0, v_a_1496_);
v___x_1507_ = v___x_1487_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1496_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_a_1490_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v_a_1492_);
lean_ctor_set(v_reuseFailAlloc_1516_, 3, v_a_1494_);
v___x_1507_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1508_; lean_object* v___x_1510_; 
lean_inc_ref(v___x_1507_);
v___x_1508_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_1473_, v_lctx_1501_, v___x_1507_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1508_);
v___x_1510_ = v___x_1504_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1508_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_nextIdx_1502_);
v___x_1510_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1511_ = lean_st_ref_set(v_a_1478_, v___x_1510_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 0, v___x_1507_);
v___x_1513_ = v___x_1498_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1507_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec(v_a_1494_);
lean_dec(v_a_1492_);
lean_dec(v_a_1490_);
lean_del_object(v___x_1487_);
v_a_1519_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1495_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1495_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec(v_a_1492_);
lean_dec(v_a_1490_);
lean_del_object(v___x_1487_);
lean_dec(v_fvarId_1482_);
v_a_1527_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1493_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1493_);
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
lean_dec(v_a_1490_);
lean_del_object(v___x_1487_);
lean_dec(v_value_1485_);
lean_dec(v_fvarId_1482_);
v_a_1535_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1491_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1491_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(lean_object* v_pu_1544_, lean_object* v_decl_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
uint8_t v_pu_boxed_1553_; uint8_t v_a_boxed_1554_; lean_object* v_res_1555_; 
v_pu_boxed_1553_ = lean_unbox(v_pu_1544_);
v_a_boxed_1554_ = lean_unbox(v_a_1546_);
v_res_1555_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_boxed_1553_, v_decl_1545_, v_a_boxed_1554_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_);
lean_dec(v_a_1551_);
lean_dec_ref(v_a_1550_);
lean_dec(v_a_1549_);
lean_dec_ref(v_a_1548_);
lean_dec(v_a_1547_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(uint8_t v_pu_1556_, size_t v_sz_1557_, size_t v_i_1558_, lean_object* v_bs_1559_, uint8_t v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
uint8_t v___x_1567_; 
v___x_1567_ = lean_usize_dec_lt(v_i_1558_, v_sz_1557_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v_bs_1559_);
return v___x_1568_;
}
else
{
lean_object* v_v_1569_; lean_object* v___x_1570_; 
v_v_1569_ = lean_array_uget_borrowed(v_bs_1559_, v_i_1558_);
lean_inc(v_v_1569_);
v___x_1570_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_1556_, v_v_1569_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1572_; lean_object* v_bs_x27_1573_; size_t v___x_1574_; size_t v___x_1575_; lean_object* v___x_1576_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref(v___x_1570_);
v___x_1572_ = lean_unsigned_to_nat(0u);
v_bs_x27_1573_ = lean_array_uset(v_bs_1559_, v_i_1558_, v___x_1572_);
v___x_1574_ = ((size_t)1ULL);
v___x_1575_ = lean_usize_add(v_i_1558_, v___x_1574_);
v___x_1576_ = lean_array_uset(v_bs_x27_1573_, v_i_1558_, v_a_1571_);
v_i_1558_ = v___x_1575_;
v_bs_1559_ = v___x_1576_;
goto _start;
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec_ref(v_bs_1559_);
v_a_1578_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1570_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1570_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0___boxed(lean_object* v_pu_1586_, lean_object* v_sz_1587_, lean_object* v_i_1588_, lean_object* v_bs_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
uint8_t v_pu_boxed_1597_; size_t v_sz_boxed_1598_; size_t v_i_boxed_1599_; uint8_t v___y_26865__boxed_1600_; lean_object* v_res_1601_; 
v_pu_boxed_1597_ = lean_unbox(v_pu_1586_);
v_sz_boxed_1598_ = lean_unbox_usize(v_sz_1587_);
lean_dec(v_sz_1587_);
v_i_boxed_1599_ = lean_unbox_usize(v_i_1588_);
lean_dec(v_i_1588_);
v___y_26865__boxed_1600_ = lean_unbox(v___y_1590_);
v_res_1601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_boxed_1597_, v_sz_boxed_1598_, v_i_boxed_1599_, v_bs_1589_, v___y_26865__boxed_1600_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(uint8_t v_pu_1602_, size_t v_sz_1603_, size_t v_i_1604_, lean_object* v_bs_1605_, uint8_t v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
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
lean_object* v_v_1615_; lean_object* v___x_1616_; lean_object* v_bs_x27_1617_; lean_object* v_a_1619_; 
v_v_1615_ = lean_array_uget(v_bs_1605_, v_i_1604_);
v___x_1616_ = lean_unsigned_to_nat(0u);
v_bs_x27_1617_ = lean_array_uset(v_bs_1605_, v_i_1604_, v___x_1616_);
switch(lean_obj_tag(v_v_1615_))
{
case 0:
{
lean_object* v_ctorName_1624_; lean_object* v_params_1625_; lean_object* v_code_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1647_; 
v_ctorName_1624_ = lean_ctor_get(v_v_1615_, 0);
v_params_1625_ = lean_ctor_get(v_v_1615_, 1);
v_code_1626_ = lean_ctor_get(v_v_1615_, 2);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_v_1615_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1628_ = v_v_1615_;
v_isShared_1629_ = v_isSharedCheck_1647_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_code_1626_);
lean_inc(v_params_1625_);
lean_inc(v_ctorName_1624_);
lean_dec(v_v_1615_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1647_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
size_t v_sz_1630_; size_t v___x_1631_; lean_object* v___x_1632_; 
v_sz_1630_ = lean_array_size(v_params_1625_);
v___x_1631_ = ((size_t)0ULL);
v___x_1632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_1602_, v_sz_1630_, v___x_1631_, v_params_1625_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1634_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref(v___x_1632_);
v___x_1634_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1602_, v_code_1626_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
lean_dec_ref(v___x_1634_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 2, v_a_1635_);
lean_ctor_set(v___x_1628_, 1, v_a_1633_);
v___x_1637_ = v___x_1628_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_ctorName_1624_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_a_1633_);
lean_ctor_set(v_reuseFailAlloc_1638_, 2, v_a_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
v_a_1619_ = v___x_1637_;
goto v___jp_1618_;
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec(v_a_1633_);
lean_del_object(v___x_1628_);
lean_dec(v_ctorName_1624_);
lean_dec_ref(v_bs_x27_1617_);
v_a_1639_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1634_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1634_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
else
{
lean_del_object(v___x_1628_);
lean_dec_ref(v_code_1626_);
lean_dec(v_ctorName_1624_);
lean_dec_ref(v_bs_x27_1617_);
return v___x_1632_;
}
}
}
case 1:
{
lean_object* v_info_1648_; lean_object* v_code_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1666_; 
v_info_1648_ = lean_ctor_get(v_v_1615_, 0);
v_code_1649_ = lean_ctor_get(v_v_1615_, 1);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_v_1615_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1651_ = v_v_1615_;
v_isShared_1652_ = v_isSharedCheck_1666_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_code_1649_);
lean_inc(v_info_1648_);
lean_dec(v_v_1615_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1666_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1602_, v_code_1649_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1656_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref(v___x_1653_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 1, v_a_1654_);
v___x_1656_ = v___x_1651_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_info_1648_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_a_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
v_a_1619_ = v___x_1656_;
goto v___jp_1618_;
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_del_object(v___x_1651_);
lean_dec_ref(v_info_1648_);
lean_dec_ref(v_bs_x27_1617_);
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
}
default: 
{
lean_object* v_code_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1684_; 
v_code_1667_ = lean_ctor_get(v_v_1615_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_v_1615_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1669_ = v_v_1615_;
v_isShared_1670_ = v_isSharedCheck_1684_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_code_1667_);
lean_dec(v_v_1615_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1684_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1602_, v_code_1667_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1674_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
lean_dec_ref(v___x_1671_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v_a_1672_);
v___x_1674_ = v___x_1669_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
v_a_1619_ = v___x_1674_;
goto v___jp_1618_;
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_del_object(v___x_1669_);
lean_dec_ref(v_bs_x27_1617_);
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
}
v___jp_1618_:
{
size_t v___x_1620_; size_t v___x_1621_; lean_object* v___x_1622_; 
v___x_1620_ = ((size_t)1ULL);
v___x_1621_ = lean_usize_add(v_i_1604_, v___x_1620_);
v___x_1622_ = lean_array_uset(v_bs_x27_1617_, v_i_1604_, v_a_1619_);
v_i_1604_ = v___x_1621_;
v_bs_1605_ = v___x_1622_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t v_pu_1685_, lean_object* v_code_1686_, uint8_t v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
switch(lean_obj_tag(v_code_1686_))
{
case 0:
{
lean_object* v_decl_1694_; lean_object* v_k_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1721_; 
v_decl_1694_ = lean_ctor_get(v_code_1686_, 0);
v_k_1695_ = lean_ctor_get(v_code_1686_, 1);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_code_1686_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1697_ = v_code_1686_;
v_isShared_1698_ = v_isSharedCheck_1721_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_k_1695_);
lean_inc(v_decl_1694_);
lean_dec(v_code_1686_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1721_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_1685_, v_decl_1694_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1701_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1700_);
lean_dec_ref(v___x_1699_);
v___x_1701_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1685_, v_k_1695_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1712_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1704_ = v___x_1701_;
v_isShared_1705_ = v_isSharedCheck_1712_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1701_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1712_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 1, v_a_1702_);
lean_ctor_set(v___x_1697_, 0, v_a_1700_);
v___x_1707_ = v___x_1697_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1700_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1709_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v___x_1707_);
v___x_1709_ = v___x_1704_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
else
{
lean_dec(v_a_1700_);
lean_del_object(v___x_1697_);
return v___x_1701_;
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_del_object(v___x_1697_);
lean_dec_ref(v_k_1695_);
v_a_1713_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1699_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1699_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
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
}
case 1:
{
lean_object* v_decl_1722_; lean_object* v_k_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1749_; 
v_decl_1722_ = lean_ctor_get(v_code_1686_, 0);
v_k_1723_ = lean_ctor_get(v_code_1686_, 1);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_code_1686_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1725_ = v_code_1686_;
v_isShared_1726_ = v_isSharedCheck_1749_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_k_1723_);
lean_inc(v_decl_1722_);
lean_dec(v_code_1686_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1749_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1685_, v_decl_1722_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1729_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref(v___x_1727_);
v___x_1729_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1685_, v_k_1723_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1740_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1732_ = v___x_1729_;
v_isShared_1733_ = v_isSharedCheck_1740_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1729_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1740_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 1, v_a_1730_);
lean_ctor_set(v___x_1725_, 0, v_a_1728_);
v___x_1735_ = v___x_1725_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1728_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1737_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v___x_1735_);
v___x_1737_ = v___x_1732_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1735_);
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
else
{
lean_dec(v_a_1728_);
lean_del_object(v___x_1725_);
return v___x_1729_;
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_del_object(v___x_1725_);
lean_dec_ref(v_k_1723_);
v_a_1741_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1727_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1727_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
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
}
case 2:
{
lean_object* v_decl_1750_; lean_object* v_k_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1777_; 
v_decl_1750_ = lean_ctor_get(v_code_1686_, 0);
v_k_1751_ = lean_ctor_get(v_code_1686_, 1);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_code_1686_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1753_ = v_code_1686_;
v_isShared_1754_ = v_isSharedCheck_1777_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_k_1751_);
lean_inc(v_decl_1750_);
lean_dec(v_code_1686_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1777_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1685_, v_decl_1750_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1757_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref(v___x_1755_);
v___x_1757_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1685_, v_k_1751_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1768_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1768_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1768_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 1, v_a_1758_);
lean_ctor_set(v___x_1753_, 0, v_a_1756_);
v___x_1763_ = v___x_1753_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1756_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
lean_object* v___x_1765_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1763_);
v___x_1765_ = v___x_1760_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
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
else
{
lean_dec(v_a_1756_);
lean_del_object(v___x_1753_);
return v___x_1757_;
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_del_object(v___x_1753_);
lean_dec_ref(v_k_1751_);
v_a_1769_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1755_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1755_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
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
}
case 3:
{
lean_object* v_fvarId_1778_; lean_object* v_args_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1808_; 
v_fvarId_1778_ = lean_ctor_get(v_code_1686_, 0);
v_args_1779_ = lean_ctor_get(v_code_1686_, 1);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_code_1686_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1781_ = v_code_1686_;
v_isShared_1782_ = v_isSharedCheck_1808_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_args_1779_);
lean_inc(v_fvarId_1778_);
lean_dec(v_code_1686_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1808_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1783_; uint8_t v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = lean_st_ref_get(v_a_1688_);
v___x_1784_ = 1;
v___x_1785_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1783_, v_fvarId_1778_, v___x_1784_);
lean_dec(v___x_1783_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_fvarId_1786_; lean_object* v___x_1787_; 
v_fvarId_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_fvarId_1786_);
lean_dec_ref(v___x_1785_);
v___x_1787_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1685_, v_args_1779_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1798_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1798_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1798_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 1, v_a_1788_);
lean_ctor_set(v___x_1781_, 0, v_fvarId_1786_);
v___x_1793_ = v___x_1781_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_fvarId_1786_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1795_; 
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1793_);
v___x_1795_ = v___x_1790_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec(v_fvarId_1786_);
lean_del_object(v___x_1781_);
v_a_1799_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1787_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1787_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
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
lean_object* v___x_1807_; 
lean_del_object(v___x_1781_);
lean_dec_ref(v_args_1779_);
v___x_1807_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1685_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
return v___x_1807_;
}
}
}
case 4:
{
lean_object* v_cases_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1861_; 
v_cases_1809_ = lean_ctor_get(v_code_1686_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_code_1686_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1811_ = v_code_1686_;
v_isShared_1812_ = v_isSharedCheck_1861_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_cases_1809_);
lean_dec(v_code_1686_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1861_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v_typeName_1813_; lean_object* v_resultType_1814_; lean_object* v_discr_1815_; lean_object* v_alts_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1860_; 
v_typeName_1813_ = lean_ctor_get(v_cases_1809_, 0);
v_resultType_1814_ = lean_ctor_get(v_cases_1809_, 1);
v_discr_1815_ = lean_ctor_get(v_cases_1809_, 2);
v_alts_1816_ = lean_ctor_get(v_cases_1809_, 3);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_cases_1809_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1818_ = v_cases_1809_;
v_isShared_1819_ = v_isSharedCheck_1860_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_alts_1816_);
lean_inc(v_discr_1815_);
lean_inc(v_resultType_1814_);
lean_inc(v_typeName_1813_);
lean_dec(v_cases_1809_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1860_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; uint8_t v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = lean_st_ref_get(v_a_1688_);
v___x_1821_ = 1;
v___x_1822_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1820_, v_discr_1815_, v___x_1821_);
lean_dec(v___x_1820_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_fvarId_1823_; lean_object* v___x_1824_; 
v_fvarId_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_fvarId_1823_);
lean_dec_ref(v___x_1822_);
v___x_1824_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1685_, v_resultType_1814_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; size_t v_sz_1826_; size_t v___x_1827_; lean_object* v___x_1828_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_a_1825_);
lean_dec_ref(v___x_1824_);
v_sz_1826_ = lean_array_size(v_alts_1816_);
v___x_1827_ = ((size_t)0ULL);
v___x_1828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_1685_, v_sz_1826_, v___x_1827_, v_alts_1816_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1842_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1842_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1842_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 3, v_a_1829_);
lean_ctor_set(v___x_1818_, 2, v_fvarId_1823_);
lean_ctor_set(v___x_1818_, 1, v_a_1825_);
v___x_1834_ = v___x_1818_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_typeName_1813_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_a_1825_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_fvarId_1823_);
lean_ctor_set(v_reuseFailAlloc_1841_, 3, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v___x_1836_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1834_);
v___x_1836_ = v___x_1811_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
lean_object* v___x_1838_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1836_);
v___x_1838_ = v___x_1831_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec(v_a_1825_);
lean_dec(v_fvarId_1823_);
lean_del_object(v___x_1818_);
lean_dec(v_typeName_1813_);
lean_del_object(v___x_1811_);
v_a_1843_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1828_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1828_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec(v_fvarId_1823_);
lean_del_object(v___x_1818_);
lean_dec_ref(v_alts_1816_);
lean_dec(v_typeName_1813_);
lean_del_object(v___x_1811_);
v_a_1851_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1824_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1824_);
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
lean_object* v___x_1859_; 
lean_del_object(v___x_1818_);
lean_dec_ref(v_alts_1816_);
lean_dec_ref(v_resultType_1814_);
lean_dec(v_typeName_1813_);
lean_del_object(v___x_1811_);
v___x_1859_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1685_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
return v___x_1859_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1881_; 
v_fvarId_1862_ = lean_ctor_get(v_code_1686_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_code_1686_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1864_ = v_code_1686_;
v_isShared_1865_ = v_isSharedCheck_1881_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_fvarId_1862_);
lean_dec(v_code_1686_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1881_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1866_; uint8_t v___x_1867_; lean_object* v___x_1868_; 
v___x_1866_ = lean_st_ref_get(v_a_1688_);
v___x_1867_ = 1;
v___x_1868_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1866_, v_fvarId_1862_, v___x_1867_);
lean_dec(v___x_1866_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_fvarId_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1879_; 
v_fvarId_1869_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1871_ = v___x_1868_;
v_isShared_1872_ = v_isSharedCheck_1879_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_fvarId_1869_);
lean_dec(v___x_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1879_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v_fvarId_1869_);
v___x_1874_ = v___x_1864_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_fvarId_1869_);
v___x_1874_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1876_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1874_);
v___x_1876_ = v___x_1871_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
else
{
lean_object* v___x_1880_; 
lean_del_object(v___x_1864_);
v___x_1880_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1685_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
return v___x_1880_;
}
}
}
case 6:
{
lean_object* v_type_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1906_; 
v_type_1882_ = lean_ctor_get(v_code_1686_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v_code_1686_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1884_ = v_code_1686_;
v_isShared_1885_ = v_isSharedCheck_1906_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_type_1882_);
lean_dec(v_code_1686_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1906_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; 
v___x_1886_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1685_, v_type_1882_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1897_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1897_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1897_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v_a_1887_);
v___x_1892_ = v___x_1884_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1887_);
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
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_del_object(v___x_1884_);
v_a_1898_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1886_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1886_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
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
}
case 7:
{
lean_object* v_fvarId_1907_; lean_object* v_i_1908_; lean_object* v_y_1909_; lean_object* v_k_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1933_; 
v_fvarId_1907_ = lean_ctor_get(v_code_1686_, 0);
v_i_1908_ = lean_ctor_get(v_code_1686_, 1);
v_y_1909_ = lean_ctor_get(v_code_1686_, 2);
v_k_1910_ = lean_ctor_get(v_code_1686_, 3);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_code_1686_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1912_ = v_code_1686_;
v_isShared_1913_ = v_isSharedCheck_1933_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_k_1910_);
lean_inc(v_y_1909_);
lean_inc(v_i_1908_);
lean_inc(v_fvarId_1907_);
lean_dec(v_code_1686_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1933_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1914_; uint8_t v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = lean_st_ref_get(v_a_1688_);
v___x_1915_ = 1;
v___x_1916_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1914_, v_fvarId_1907_, v___x_1915_);
lean_dec(v___x_1914_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_fvarId_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v_fvarId_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_fvarId_1917_);
lean_dec_ref(v___x_1916_);
v___x_1918_ = lean_st_ref_get(v_a_1688_);
v___x_1919_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1685_, v___x_1918_, v_y_1909_, v___x_1915_);
lean_dec(v___x_1918_);
v___x_1920_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1685_, v_k_1910_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1931_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_1931_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1931_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 3, v_a_1921_);
lean_ctor_set(v___x_1912_, 2, v___x_1919_);
lean_ctor_set(v___x_1912_, 0, v_fvarId_1917_);
v___x_1926_ = v___x_1912_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_fvarId_1917_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_i_1908_);
lean_ctor_set(v_reuseFailAlloc_1930_, 2, v___x_1919_);
lean_ctor_set(v_reuseFailAlloc_1930_, 3, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1928_; 
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1926_);
v___x_1928_ = v___x_1923_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
else
{
lean_dec(v___x_1919_);
lean_dec(v_fvarId_1917_);
lean_del_object(v___x_1912_);
lean_dec(v_i_1908_);
return v___x_1920_;
}
}
else
{
lean_object* v___x_1932_; 
lean_del_object(v___x_1912_);
lean_dec_ref(v_k_1910_);
lean_dec(v_y_1909_);
lean_dec(v_i_1908_);
v___x_1932_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1685_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
return v___x_1932_;
}
}
}
case 8:
{
lean_object* v_fvarId_1934_; lean_object* v_i_1935_; lean_object* v_y_1936_; lean_object* v_k_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1962_; 
v_fvarId_1934_ = lean_ctor_get(v_code_1686_, 0);
v_i_1935_ = lean_ctor_get(v_code_1686_, 1);
v_y_1936_ = lean_ctor_get(v_code_1686_, 2);
v_k_1937_ = lean_ctor_get(v_code_1686_, 3);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_code_1686_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1939_ = v_code_1686_;
v_isShared_1940_ = v_isSharedCheck_1962_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_k_1937_);
lean_inc(v_y_1936_);
lean_inc(v_i_1935_);
lean_inc(v_fvarId_1934_);
lean_dec(v_code_1686_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1962_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; uint8_t v___x_1942_; lean_object* v___x_1943_; 
v___x_1941_ = lean_st_ref_get(v_a_1688_);
v___x_1942_ = 1;
v___x_1943_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1941_, v_fvarId_1934_, v___x_1942_);
lean_dec(v___x_1941_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_fvarId_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v_fvarId_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_fvarId_1944_);
lean_dec_ref(v___x_1943_);
v___x_1945_ = lean_st_ref_get(v_a_1688_);
v___x_1946_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1945_, v_y_1936_, v___x_1942_);
lean_dec(v___x_1945_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_fvarId_1947_; lean_object* v___x_1948_; 
v_fvarId_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_fvarId_1947_);
lean_dec_ref(v___x_1946_);
v___x_1948_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1685_, v_k_1937_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1959_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1951_ = v___x_1948_;
v_isShared_1952_ = v_isSharedCheck_1959_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1959_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 3, v_a_1949_);
lean_ctor_set(v___x_1939_, 2, v_fvarId_1947_);
lean_ctor_set(v___x_1939_, 0, v_fvarId_1944_);
v___x_1954_ = v___x_1939_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_fvarId_1944_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_i_1935_);
lean_ctor_set(v_reuseFailAlloc_1958_, 2, v_fvarId_1947_);
lean_ctor_set(v_reuseFailAlloc_1958_, 3, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_object* v___x_1956_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1954_);
v___x_1956_ = v___x_1951_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1954_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
else
{
lean_dec(v_fvarId_1947_);
lean_dec(v_fvarId_1944_);
lean_del_object(v___x_1939_);
lean_dec(v_i_1935_);
return v___x_1948_;
}
}
else
{
lean_object* v___x_1960_; 
lean_dec(v_fvarId_1944_);
lean_del_object(v___x_1939_);
lean_dec_ref(v_k_1937_);
lean_dec(v_i_1935_);
v___x_1960_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1685_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
return v___x_1960_;
}
}
else
{
lean_object* v___x_1961_; 
lean_del_object(v___x_1939_);
lean_dec_ref(v_k_1937_);
lean_dec(v_y_1936_);
lean_dec(v_i_1935_);
v___x_1961_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1685_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
return v___x_1961_;
}
}
}
case 9:
{
lean_object* v_fvarId_1963_; lean_object* v_i_1964_; lean_object* v_offset_1965_; lean_object* v_y_1966_; lean_object* v_ty_1967_; lean_object* v_k_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_2003_; 
v_fvarId_1963_ = lean_ctor_get(v_code_1686_, 0);
v_i_1964_ = lean_ctor_get(v_code_1686_, 1);
v_offset_1965_ = lean_ctor_get(v_code_1686_, 2);
v_y_1966_ = lean_ctor_get(v_code_1686_, 3);
v_ty_1967_ = lean_ctor_get(v_code_1686_, 4);
v_k_1968_ = lean_ctor_get(v_code_1686_, 5);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_code_1686_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1970_ = v_code_1686_;
v_isShared_1971_ = v_isSharedCheck_2003_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_k_1968_);
lean_inc(v_ty_1967_);
lean_inc(v_y_1966_);
lean_inc(v_offset_1965_);
lean_inc(v_i_1964_);
lean_inc(v_fvarId_1963_);
lean_dec(v_code_1686_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_2003_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; uint8_t v___x_1973_; lean_object* v___x_1974_; 
v___x_1972_ = lean_st_ref_get(v_a_1688_);
v___x_1973_ = 1;
v___x_1974_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1972_, v_fvarId_1963_, v___x_1973_);
lean_dec(v___x_1972_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_fvarId_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v_fvarId_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_fvarId_1975_);
lean_dec_ref(v___x_1974_);
v___x_1976_ = lean_st_ref_get(v_a_1688_);
v___x_1977_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1976_, v_y_1966_, v___x_1973_);
lean_dec(v___x_1976_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_fvarId_1978_; lean_object* v___x_1979_; 
v_fvarId_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_fvarId_1978_);
lean_dec_ref(v___x_1977_);
v___x_1979_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1685_, v_ty_1967_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1981_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref(v___x_1979_);
v___x_1981_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1685_, v_k_1968_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1992_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_1992_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1992_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 5, v_a_1982_);
lean_ctor_set(v___x_1970_, 4, v_a_1980_);
lean_ctor_set(v___x_1970_, 3, v_fvarId_1978_);
lean_ctor_set(v___x_1970_, 0, v_fvarId_1975_);
v___x_1987_ = v___x_1970_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_fvarId_1975_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_i_1964_);
lean_ctor_set(v_reuseFailAlloc_1991_, 2, v_offset_1965_);
lean_ctor_set(v_reuseFailAlloc_1991_, 3, v_fvarId_1978_);
lean_ctor_set(v_reuseFailAlloc_1991_, 4, v_a_1980_);
lean_ctor_set(v_reuseFailAlloc_1991_, 5, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1989_; 
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1987_);
v___x_1989_ = v___x_1984_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_dec(v_a_1980_);
lean_dec(v_fvarId_1978_);
lean_dec(v_fvarId_1975_);
lean_del_object(v___x_1970_);
lean_dec(v_offset_1965_);
lean_dec(v_i_1964_);
return v___x_1981_;
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec(v_fvarId_1978_);
lean_dec(v_fvarId_1975_);
lean_del_object(v___x_1970_);
lean_dec_ref(v_k_1968_);
lean_dec(v_offset_1965_);
lean_dec(v_i_1964_);
v_a_1993_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1979_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1979_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
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
lean_object* v___x_2001_; 
lean_dec(v_fvarId_1975_);
lean_del_object(v___x_1970_);
lean_dec_ref(v_k_1968_);
lean_dec_ref(v_ty_1967_);
lean_dec(v_offset_1965_);
lean_dec(v_i_1964_);
v___x_2001_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1685_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
return v___x_2001_;
}
}
else
{
lean_object* v___x_2002_; 
lean_del_object(v___x_1970_);
lean_dec_ref(v_k_1968_);
lean_dec_ref(v_ty_1967_);
lean_dec(v_y_1966_);
lean_dec(v_offset_1965_);
lean_dec(v_i_1964_);
v___x_2002_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1685_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
return v___x_2002_;
}
}
}
case 10:
{
lean_object* v_fvarId_2004_; lean_object* v_cidx_2005_; lean_object* v_k_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2027_; 
v_fvarId_2004_ = lean_ctor_get(v_code_1686_, 0);
v_cidx_2005_ = lean_ctor_get(v_code_1686_, 1);
v_k_2006_ = lean_ctor_get(v_code_1686_, 2);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_code_1686_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2008_ = v_code_1686_;
v_isShared_2009_ = v_isSharedCheck_2027_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_k_2006_);
lean_inc(v_cidx_2005_);
lean_inc(v_fvarId_2004_);
lean_dec(v_code_1686_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2027_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; uint8_t v___x_2011_; lean_object* v___x_2012_; 
v___x_2010_ = lean_st_ref_get(v_a_1688_);
v___x_2011_ = 1;
v___x_2012_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2010_, v_fvarId_2004_, v___x_2011_);
lean_dec(v___x_2010_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_fvarId_2013_; lean_object* v___x_2014_; 
v_fvarId_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_fvarId_2013_);
lean_dec_ref(v___x_2012_);
v___x_2014_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1685_, v_k_2006_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2025_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2025_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2025_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 2, v_a_2015_);
lean_ctor_set(v___x_2008_, 0, v_fvarId_2013_);
v___x_2020_ = v___x_2008_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_fvarId_2013_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_cidx_2005_);
lean_ctor_set(v_reuseFailAlloc_2024_, 2, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2022_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2020_);
v___x_2022_ = v___x_2017_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
else
{
lean_dec(v_fvarId_2013_);
lean_del_object(v___x_2008_);
lean_dec(v_cidx_2005_);
return v___x_2014_;
}
}
else
{
lean_object* v___x_2026_; 
lean_del_object(v___x_2008_);
lean_dec_ref(v_k_2006_);
lean_dec(v_cidx_2005_);
v___x_2026_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1685_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
return v___x_2026_;
}
}
}
case 11:
{
lean_object* v_fvarId_2028_; lean_object* v_n_2029_; uint8_t v_check_2030_; uint8_t v_persistent_2031_; lean_object* v_k_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2053_; 
v_fvarId_2028_ = lean_ctor_get(v_code_1686_, 0);
v_n_2029_ = lean_ctor_get(v_code_1686_, 1);
v_check_2030_ = lean_ctor_get_uint8(v_code_1686_, sizeof(void*)*3);
v_persistent_2031_ = lean_ctor_get_uint8(v_code_1686_, sizeof(void*)*3 + 1);
v_k_2032_ = lean_ctor_get(v_code_1686_, 2);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_code_1686_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2034_ = v_code_1686_;
v_isShared_2035_ = v_isSharedCheck_2053_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_k_2032_);
lean_inc(v_n_2029_);
lean_inc(v_fvarId_2028_);
lean_dec(v_code_1686_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2053_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; uint8_t v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = lean_st_ref_get(v_a_1688_);
v___x_2037_ = 1;
v___x_2038_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2036_, v_fvarId_2028_, v___x_2037_);
lean_dec(v___x_2036_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_fvarId_2039_; lean_object* v___x_2040_; 
v_fvarId_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_fvarId_2039_);
lean_dec_ref(v___x_2038_);
v___x_2040_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1685_, v_k_2032_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2051_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2051_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2051_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 2, v_a_2041_);
lean_ctor_set(v___x_2034_, 0, v_fvarId_2039_);
v___x_2046_ = v___x_2034_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_fvarId_2039_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_n_2029_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v_a_2041_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*3, v_check_2030_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*3 + 1, v_persistent_2031_);
v___x_2046_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2048_; 
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2046_);
v___x_2048_ = v___x_2043_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
else
{
lean_dec(v_fvarId_2039_);
lean_del_object(v___x_2034_);
lean_dec(v_n_2029_);
return v___x_2040_;
}
}
else
{
lean_object* v___x_2052_; 
lean_del_object(v___x_2034_);
lean_dec_ref(v_k_2032_);
lean_dec(v_n_2029_);
v___x_2052_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1685_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
return v___x_2052_;
}
}
}
case 12:
{
lean_object* v_fvarId_2054_; lean_object* v_n_2055_; uint8_t v_check_2056_; uint8_t v_persistent_2057_; lean_object* v_k_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2079_; 
v_fvarId_2054_ = lean_ctor_get(v_code_1686_, 0);
v_n_2055_ = lean_ctor_get(v_code_1686_, 1);
v_check_2056_ = lean_ctor_get_uint8(v_code_1686_, sizeof(void*)*3);
v_persistent_2057_ = lean_ctor_get_uint8(v_code_1686_, sizeof(void*)*3 + 1);
v_k_2058_ = lean_ctor_get(v_code_1686_, 2);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_code_1686_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2060_ = v_code_1686_;
v_isShared_2061_ = v_isSharedCheck_2079_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_k_2058_);
lean_inc(v_n_2055_);
lean_inc(v_fvarId_2054_);
lean_dec(v_code_1686_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2079_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; uint8_t v___x_2063_; lean_object* v___x_2064_; 
v___x_2062_ = lean_st_ref_get(v_a_1688_);
v___x_2063_ = 1;
v___x_2064_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2062_, v_fvarId_2054_, v___x_2063_);
lean_dec(v___x_2062_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_fvarId_2065_; lean_object* v___x_2066_; 
v_fvarId_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_fvarId_2065_);
lean_dec_ref(v___x_2064_);
v___x_2066_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1685_, v_k_2058_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2077_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2077_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2077_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 2, v_a_2067_);
lean_ctor_set(v___x_2060_, 0, v_fvarId_2065_);
v___x_2072_ = v___x_2060_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_fvarId_2065_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_n_2055_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_a_2067_);
lean_ctor_set_uint8(v_reuseFailAlloc_2076_, sizeof(void*)*3, v_check_2056_);
lean_ctor_set_uint8(v_reuseFailAlloc_2076_, sizeof(void*)*3 + 1, v_persistent_2057_);
v___x_2072_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2074_; 
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2072_);
v___x_2074_ = v___x_2069_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
else
{
lean_dec(v_fvarId_2065_);
lean_del_object(v___x_2060_);
lean_dec(v_n_2055_);
return v___x_2066_;
}
}
else
{
lean_object* v___x_2078_; 
lean_del_object(v___x_2060_);
lean_dec_ref(v_k_2058_);
lean_dec(v_n_2055_);
v___x_2078_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1685_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
return v___x_2078_;
}
}
}
default: 
{
lean_object* v_fvarId_2080_; lean_object* v_k_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2102_; 
v_fvarId_2080_ = lean_ctor_get(v_code_1686_, 0);
v_k_2081_ = lean_ctor_get(v_code_1686_, 1);
v_isSharedCheck_2102_ = !lean_is_exclusive(v_code_1686_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2083_ = v_code_1686_;
v_isShared_2084_ = v_isSharedCheck_2102_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_k_2081_);
lean_inc(v_fvarId_2080_);
lean_dec(v_code_1686_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2102_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2085_; uint8_t v___x_2086_; lean_object* v___x_2087_; 
v___x_2085_ = lean_st_ref_get(v_a_1688_);
v___x_2086_ = 1;
v___x_2087_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2085_, v_fvarId_2080_, v___x_2086_);
lean_dec(v___x_2085_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_fvarId_2088_; lean_object* v___x_2089_; 
v_fvarId_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_fvarId_2088_);
lean_dec_ref(v___x_2087_);
v___x_2089_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1685_, v_k_2081_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2100_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2100_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2100_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 1, v_a_2090_);
lean_ctor_set(v___x_2083_, 0, v_fvarId_2088_);
v___x_2095_ = v___x_2083_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_fvarId_2088_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2097_; 
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2095_);
v___x_2097_ = v___x_2092_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
else
{
lean_dec(v_fvarId_2088_);
lean_del_object(v___x_2083_);
return v___x_2089_;
}
}
else
{
lean_object* v___x_2101_; 
lean_del_object(v___x_2083_);
lean_dec_ref(v_k_2081_);
v___x_2101_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1685_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
return v___x_2101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(uint8_t v_pu_2103_, lean_object* v_decl_2104_, uint8_t v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v_fvarId_2112_; lean_object* v_binderName_2113_; lean_object* v_params_2114_; lean_object* v_type_2115_; lean_object* v_value_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2194_; 
v_fvarId_2112_ = lean_ctor_get(v_decl_2104_, 0);
v_binderName_2113_ = lean_ctor_get(v_decl_2104_, 1);
v_params_2114_ = lean_ctor_get(v_decl_2104_, 2);
v_type_2115_ = lean_ctor_get(v_decl_2104_, 3);
v_value_2116_ = lean_ctor_get(v_decl_2104_, 4);
v_isSharedCheck_2194_ = !lean_is_exclusive(v_decl_2104_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2118_ = v_decl_2104_;
v_isShared_2119_ = v_isSharedCheck_2194_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_value_2116_);
lean_inc(v_type_2115_);
lean_inc(v_params_2114_);
lean_inc(v_binderName_2113_);
lean_inc(v_fvarId_2112_);
lean_dec(v_decl_2104_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2194_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; 
v___x_2120_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2103_, v_type_2115_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref(v___x_2120_);
v___x_2122_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_2113_, v_a_2105_, v_a_2108_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; size_t v_sz_2124_; size_t v___x_2125_; lean_object* v___x_2126_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref(v___x_2122_);
v_sz_2124_ = lean_array_size(v_params_2114_);
v___x_2125_ = ((size_t)0ULL);
v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2103_, v_sz_2124_, v___x_2125_, v_params_2114_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref(v___x_2126_);
v___x_2128_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2103_, v_value_2116_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2130_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref(v___x_2128_);
v___x_2130_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_2112_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2153_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2133_ = v___x_2130_;
v_isShared_2134_ = v_isSharedCheck_2153_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2130_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2153_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; lean_object* v_lctx_2136_; lean_object* v_nextIdx_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2152_; 
v___x_2135_ = lean_st_ref_take(v_a_2108_);
v_lctx_2136_ = lean_ctor_get(v___x_2135_, 0);
v_nextIdx_2137_ = lean_ctor_get(v___x_2135_, 1);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2139_ = v___x_2135_;
v_isShared_2140_ = v_isSharedCheck_2152_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_nextIdx_2137_);
lean_inc(v_lctx_2136_);
lean_dec(v___x_2135_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2152_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 4, v_a_2129_);
lean_ctor_set(v___x_2118_, 3, v_a_2121_);
lean_ctor_set(v___x_2118_, 2, v_a_2127_);
lean_ctor_set(v___x_2118_, 1, v_a_2123_);
lean_ctor_set(v___x_2118_, 0, v_a_2131_);
v___x_2142_ = v___x_2118_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2131_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v_a_2123_);
lean_ctor_set(v_reuseFailAlloc_2151_, 2, v_a_2127_);
lean_ctor_set(v_reuseFailAlloc_2151_, 3, v_a_2121_);
lean_ctor_set(v_reuseFailAlloc_2151_, 4, v_a_2129_);
v___x_2142_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2143_; lean_object* v___x_2145_; 
lean_inc_ref(v___x_2142_);
v___x_2143_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2103_, v_lctx_2136_, v___x_2142_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2143_);
v___x_2145_ = v___x_2139_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2143_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v_nextIdx_2137_);
v___x_2145_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2146_ = lean_st_ref_set(v_a_2108_, v___x_2145_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v___x_2142_);
v___x_2148_ = v___x_2133_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2142_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec(v_a_2129_);
lean_dec(v_a_2127_);
lean_dec(v_a_2123_);
lean_dec(v_a_2121_);
lean_del_object(v___x_2118_);
v_a_2154_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2130_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2130_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec(v_a_2127_);
lean_dec(v_a_2123_);
lean_dec(v_a_2121_);
lean_del_object(v___x_2118_);
lean_dec(v_fvarId_2112_);
v_a_2162_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2128_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2128_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
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
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec(v_a_2123_);
lean_dec(v_a_2121_);
lean_del_object(v___x_2118_);
lean_dec_ref(v_value_2116_);
lean_dec(v_fvarId_2112_);
v_a_2170_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2126_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2126_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec(v_a_2121_);
lean_del_object(v___x_2118_);
lean_dec_ref(v_value_2116_);
lean_dec_ref(v_params_2114_);
lean_dec(v_fvarId_2112_);
v_a_2178_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2122_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2122_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_del_object(v___x_2118_);
lean_dec_ref(v_value_2116_);
lean_dec_ref(v_params_2114_);
lean_dec(v_binderName_2113_);
lean_dec(v_fvarId_2112_);
v_a_2186_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2120_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2120_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(lean_object* v_pu_2195_, lean_object* v_decl_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
uint8_t v_pu_boxed_2204_; uint8_t v_a_boxed_2205_; lean_object* v_res_2206_; 
v_pu_boxed_2204_ = lean_unbox(v_pu_2195_);
v_a_boxed_2205_ = lean_unbox(v_a_2197_);
v_res_2206_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_boxed_2204_, v_decl_2196_, v_a_boxed_2205_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
lean_dec(v_a_2198_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2___boxed(lean_object* v_pu_2207_, lean_object* v_sz_2208_, lean_object* v_i_2209_, lean_object* v_bs_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
uint8_t v_pu_boxed_2218_; size_t v_sz_boxed_2219_; size_t v_i_boxed_2220_; uint8_t v___y_26953__boxed_2221_; lean_object* v_res_2222_; 
v_pu_boxed_2218_ = lean_unbox(v_pu_2207_);
v_sz_boxed_2219_ = lean_unbox_usize(v_sz_2208_);
lean_dec(v_sz_2208_);
v_i_boxed_2220_ = lean_unbox_usize(v_i_2209_);
lean_dec(v_i_2209_);
v___y_26953__boxed_2221_ = lean_unbox(v___y_2211_);
v_res_2222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_boxed_2218_, v_sz_boxed_2219_, v_i_boxed_2220_, v_bs_2210_, v___y_26953__boxed_2221_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(lean_object* v_pu_2223_, lean_object* v_code_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_){
_start:
{
uint8_t v_pu_boxed_2232_; uint8_t v_a_boxed_2233_; lean_object* v_res_2234_; 
v_pu_boxed_2232_ = lean_unbox(v_pu_2223_);
v_a_boxed_2233_ = lean_unbox(v_a_2225_);
v_res_2234_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_boxed_2232_, v_code_2224_, v_a_boxed_2233_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
lean_dec(v_a_2226_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(uint8_t v_pu_2235_, lean_object* v_msg_2236_, uint8_t v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v_toApplicative_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2310_; 
v___x_2244_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
v___x_2245_ = l_StateRefT_x27_instMonad___redArg(v___x_2244_);
v_toApplicative_2246_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2310_ == 0)
{
lean_object* v_unused_2311_; 
v_unused_2311_ = lean_ctor_get(v___x_2245_, 1);
lean_dec(v_unused_2311_);
v___x_2248_ = v___x_2245_;
v_isShared_2249_ = v_isSharedCheck_2310_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_toApplicative_2246_);
lean_dec(v___x_2245_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2310_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v_toFunctor_2250_; lean_object* v_toSeq_2251_; lean_object* v_toSeqLeft_2252_; lean_object* v_toSeqRight_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2308_; 
v_toFunctor_2250_ = lean_ctor_get(v_toApplicative_2246_, 0);
v_toSeq_2251_ = lean_ctor_get(v_toApplicative_2246_, 2);
v_toSeqLeft_2252_ = lean_ctor_get(v_toApplicative_2246_, 3);
v_toSeqRight_2253_ = lean_ctor_get(v_toApplicative_2246_, 4);
v_isSharedCheck_2308_ = !lean_is_exclusive(v_toApplicative_2246_);
if (v_isSharedCheck_2308_ == 0)
{
lean_object* v_unused_2309_; 
v_unused_2309_ = lean_ctor_get(v_toApplicative_2246_, 1);
lean_dec(v_unused_2309_);
v___x_2255_ = v_toApplicative_2246_;
v_isShared_2256_ = v_isSharedCheck_2308_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_toSeqRight_2253_);
lean_inc(v_toSeqLeft_2252_);
lean_inc(v_toSeq_2251_);
lean_inc(v_toFunctor_2250_);
lean_dec(v_toApplicative_2246_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2308_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___f_2257_; lean_object* v___f_2258_; lean_object* v___f_2259_; lean_object* v___f_2260_; lean_object* v___x_2261_; lean_object* v___f_2262_; lean_object* v___f_2263_; lean_object* v___f_2264_; lean_object* v___x_2266_; 
v___f_2257_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
v___f_2258_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_2250_);
v___f_2259_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2259_, 0, v_toFunctor_2250_);
v___f_2260_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2260_, 0, v_toFunctor_2250_);
v___x_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___f_2259_);
lean_ctor_set(v___x_2261_, 1, v___f_2260_);
v___f_2262_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2262_, 0, v_toSeqRight_2253_);
v___f_2263_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2263_, 0, v_toSeqLeft_2252_);
v___f_2264_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2264_, 0, v_toSeq_2251_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 4, v___f_2262_);
lean_ctor_set(v___x_2255_, 3, v___f_2263_);
lean_ctor_set(v___x_2255_, 2, v___f_2264_);
lean_ctor_set(v___x_2255_, 1, v___f_2257_);
lean_ctor_set(v___x_2255_, 0, v___x_2261_);
v___x_2266_ = v___x_2255_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2261_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v___f_2257_);
lean_ctor_set(v_reuseFailAlloc_2307_, 2, v___f_2264_);
lean_ctor_set(v_reuseFailAlloc_2307_, 3, v___f_2263_);
lean_ctor_set(v_reuseFailAlloc_2307_, 4, v___f_2262_);
v___x_2266_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2268_; 
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 1, v___f_2258_);
lean_ctor_set(v___x_2248_, 0, v___x_2266_);
v___x_2268_ = v___x_2248_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v___f_2258_);
v___x_2268_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2269_; lean_object* v_toApplicative_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2304_; 
v___x_2269_ = l_StateRefT_x27_instMonad___redArg(v___x_2268_);
v_toApplicative_2270_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2304_ == 0)
{
lean_object* v_unused_2305_; 
v_unused_2305_ = lean_ctor_get(v___x_2269_, 1);
lean_dec(v_unused_2305_);
v___x_2272_ = v___x_2269_;
v_isShared_2273_ = v_isSharedCheck_2304_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_toApplicative_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2304_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v_toFunctor_2274_; lean_object* v_toSeq_2275_; lean_object* v_toSeqLeft_2276_; lean_object* v_toSeqRight_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2302_; 
v_toFunctor_2274_ = lean_ctor_get(v_toApplicative_2270_, 0);
v_toSeq_2275_ = lean_ctor_get(v_toApplicative_2270_, 2);
v_toSeqLeft_2276_ = lean_ctor_get(v_toApplicative_2270_, 3);
v_toSeqRight_2277_ = lean_ctor_get(v_toApplicative_2270_, 4);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_toApplicative_2270_);
if (v_isSharedCheck_2302_ == 0)
{
lean_object* v_unused_2303_; 
v_unused_2303_ = lean_ctor_get(v_toApplicative_2270_, 1);
lean_dec(v_unused_2303_);
v___x_2279_ = v_toApplicative_2270_;
v_isShared_2280_ = v_isSharedCheck_2302_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_toSeqRight_2277_);
lean_inc(v_toSeqLeft_2276_);
lean_inc(v_toSeq_2275_);
lean_inc(v_toFunctor_2274_);
lean_dec(v_toApplicative_2270_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2302_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___f_2281_; lean_object* v___f_2282_; lean_object* v___f_2283_; lean_object* v___f_2284_; lean_object* v___x_2285_; lean_object* v___f_2286_; lean_object* v___f_2287_; lean_object* v___f_2288_; lean_object* v___x_2290_; 
v___f_2281_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
v___f_2282_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(v_toFunctor_2274_);
v___f_2283_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2283_, 0, v_toFunctor_2274_);
v___f_2284_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2284_, 0, v_toFunctor_2274_);
v___x_2285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___f_2283_);
lean_ctor_set(v___x_2285_, 1, v___f_2284_);
v___f_2286_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2286_, 0, v_toSeqRight_2277_);
v___f_2287_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2287_, 0, v_toSeqLeft_2276_);
v___f_2288_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2288_, 0, v_toSeq_2275_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 4, v___f_2286_);
lean_ctor_set(v___x_2279_, 3, v___f_2287_);
lean_ctor_set(v___x_2279_, 2, v___f_2288_);
lean_ctor_set(v___x_2279_, 1, v___f_2281_);
lean_ctor_set(v___x_2279_, 0, v___x_2285_);
v___x_2290_ = v___x_2279_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2285_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v___f_2281_);
lean_ctor_set(v_reuseFailAlloc_2301_, 2, v___f_2288_);
lean_ctor_set(v_reuseFailAlloc_2301_, 3, v___f_2287_);
lean_ctor_set(v_reuseFailAlloc_2301_, 4, v___f_2286_);
v___x_2290_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2292_; 
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 1, v___f_2282_);
lean_ctor_set(v___x_2272_, 0, v___x_2290_);
v___x_2292_ = v___x_2272_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2290_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v___f_2282_);
v___x_2292_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___f_2296_; lean_object* v___x_11424__overap_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2293_ = l_StateRefT_x27_instMonad___redArg(v___x_2292_);
v___x_2294_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v_pu_2235_);
v___x_2295_ = l_instInhabitedOfMonad___redArg(v___x_2293_, v___x_2294_);
v___f_2296_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2296_, 0, v___x_2295_);
v___x_11424__overap_2297_ = lean_panic_fn_borrowed(v___f_2296_, v_msg_2236_);
lean_dec_ref(v___f_2296_);
v___x_2298_ = lean_box(v___y_2237_);
lean_inc(v___y_2242_);
lean_inc_ref(v___y_2241_);
lean_inc(v___y_2240_);
lean_inc_ref(v___y_2239_);
lean_inc(v___y_2238_);
v___x_2299_ = lean_apply_7(v___x_11424__overap_2297_, v___x_2298_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, lean_box(0));
return v___x_2299_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___boxed(lean_object* v_pu_2312_, lean_object* v_msg_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
uint8_t v_pu_boxed_2321_; uint8_t v___y_11455__boxed_2322_; lean_object* v_res_2323_; 
v_pu_boxed_2321_ = lean_unbox(v_pu_2312_);
v___y_11455__boxed_2322_ = lean_unbox(v___y_2314_);
v_res_2323_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_boxed_2321_, v_msg_2313_, v___y_11455__boxed_2322_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
return v_res_2323_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1(void){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2325_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2326_ = lean_unsigned_to_nat(41u);
v___x_2327_ = lean_unsigned_to_nat(217u);
v___x_2328_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2329_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2330_ = l_mkPanicMessageWithDecl(v___x_2329_, v___x_2328_, v___x_2327_, v___x_2326_, v___x_2325_);
return v___x_2330_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2(void){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2331_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2332_ = lean_unsigned_to_nat(31u);
v___x_2333_ = lean_unsigned_to_nat(222u);
v___x_2334_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2335_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2336_ = l_mkPanicMessageWithDecl(v___x_2335_, v___x_2334_, v___x_2333_, v___x_2332_, v___x_2331_);
return v___x_2336_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3(void){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2337_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2338_ = lean_unsigned_to_nat(41u);
v___x_2339_ = lean_unsigned_to_nat(221u);
v___x_2340_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2341_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2342_ = l_mkPanicMessageWithDecl(v___x_2341_, v___x_2340_, v___x_2339_, v___x_2338_, v___x_2337_);
return v___x_2342_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2343_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2344_ = lean_unsigned_to_nat(31u);
v___x_2345_ = lean_unsigned_to_nat(226u);
v___x_2346_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2347_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2348_ = l_mkPanicMessageWithDecl(v___x_2347_, v___x_2346_, v___x_2345_, v___x_2344_, v___x_2343_);
return v___x_2348_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5(void){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2349_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2350_ = lean_unsigned_to_nat(41u);
v___x_2351_ = lean_unsigned_to_nat(225u);
v___x_2352_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2353_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2354_ = l_mkPanicMessageWithDecl(v___x_2353_, v___x_2352_, v___x_2351_, v___x_2350_, v___x_2349_);
return v___x_2354_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6(void){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2355_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2356_ = lean_unsigned_to_nat(41u);
v___x_2357_ = lean_unsigned_to_nat(230u);
v___x_2358_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2359_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2360_ = l_mkPanicMessageWithDecl(v___x_2359_, v___x_2358_, v___x_2357_, v___x_2356_, v___x_2355_);
return v___x_2360_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7(void){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2361_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2362_ = lean_unsigned_to_nat(41u);
v___x_2363_ = lean_unsigned_to_nat(233u);
v___x_2364_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2365_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2366_ = l_mkPanicMessageWithDecl(v___x_2365_, v___x_2364_, v___x_2363_, v___x_2362_, v___x_2361_);
return v___x_2366_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8(void){
_start:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2367_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2368_ = lean_unsigned_to_nat(41u);
v___x_2369_ = lean_unsigned_to_nat(236u);
v___x_2370_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2371_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2372_ = l_mkPanicMessageWithDecl(v___x_2371_, v___x_2370_, v___x_2369_, v___x_2368_, v___x_2367_);
return v___x_2372_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2373_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2374_ = lean_unsigned_to_nat(41u);
v___x_2375_ = lean_unsigned_to_nat(239u);
v___x_2376_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2377_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2378_ = l_mkPanicMessageWithDecl(v___x_2377_, v___x_2376_, v___x_2375_, v___x_2374_, v___x_2373_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t v_pu_2379_, lean_object* v_decl_2380_, uint8_t v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
switch(lean_obj_tag(v_decl_2380_))
{
case 0:
{
lean_object* v_decl_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2412_; 
v_decl_2388_ = lean_ctor_get(v_decl_2380_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_decl_2380_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2390_ = v_decl_2380_;
v_isShared_2391_ = v_isSharedCheck_2412_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_decl_2388_);
lean_dec(v_decl_2380_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2412_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; 
v___x_2392_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_2379_, v_decl_2388_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2403_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2395_ = v___x_2392_;
v_isShared_2396_ = v_isSharedCheck_2403_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2403_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v_a_2393_);
v___x_2398_ = v___x_2390_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
lean_object* v___x_2400_; 
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2398_);
v___x_2400_ = v___x_2395_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_del_object(v___x_2390_);
v_a_2404_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2392_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2392_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
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
}
case 1:
{
lean_object* v_decl_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2437_; 
v_decl_2413_ = lean_ctor_get(v_decl_2380_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v_decl_2380_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2415_ = v_decl_2380_;
v_isShared_2416_ = v_isSharedCheck_2437_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_decl_2413_);
lean_dec(v_decl_2380_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2437_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2379_, v_decl_2413_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2428_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2428_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2428_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 0, v_a_2418_);
v___x_2423_ = v___x_2415_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2425_; 
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v___x_2423_);
v___x_2425_ = v___x_2420_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_del_object(v___x_2415_);
v_a_2429_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2417_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2417_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
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
}
case 2:
{
lean_object* v_decl_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2462_; 
v_decl_2438_ = lean_ctor_get(v_decl_2380_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v_decl_2380_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2440_ = v_decl_2380_;
v_isShared_2441_ = v_isSharedCheck_2462_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_decl_2438_);
lean_dec(v_decl_2380_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2462_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2379_, v_decl_2438_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2453_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2453_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2453_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v_a_2443_);
v___x_2448_ = v___x_2440_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2450_; 
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2448_);
v___x_2450_ = v___x_2445_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2448_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_del_object(v___x_2440_);
v_a_2454_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2442_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2442_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
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
}
case 3:
{
lean_object* v_fvarId_2463_; lean_object* v_i_2464_; lean_object* v_y_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2487_; 
v_fvarId_2463_ = lean_ctor_get(v_decl_2380_, 0);
v_i_2464_ = lean_ctor_get(v_decl_2380_, 1);
v_y_2465_ = lean_ctor_get(v_decl_2380_, 2);
v_isSharedCheck_2487_ = !lean_is_exclusive(v_decl_2380_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2467_ = v_decl_2380_;
v_isShared_2468_ = v_isSharedCheck_2487_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_y_2465_);
lean_inc(v_i_2464_);
lean_inc(v_fvarId_2463_);
lean_dec(v_decl_2380_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2487_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2469_; uint8_t v___x_2470_; lean_object* v___x_2471_; 
v___x_2469_ = lean_st_ref_get(v_a_2382_);
v___x_2470_ = 1;
v___x_2471_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2469_, v_fvarId_2463_, v___x_2470_);
lean_dec(v___x_2469_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_fvarId_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2484_; 
v_fvarId_2472_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2474_ = v___x_2471_;
v_isShared_2475_ = v_isSharedCheck_2484_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_fvarId_2472_);
lean_dec(v___x_2471_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2484_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
v___x_2476_ = lean_st_ref_get(v_a_2382_);
v___x_2477_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2379_, v___x_2476_, v_y_2465_, v___x_2470_);
lean_dec(v___x_2476_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 2, v___x_2477_);
lean_ctor_set(v___x_2467_, 0, v_fvarId_2472_);
v___x_2479_ = v___x_2467_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_fvarId_2472_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v_i_2464_);
lean_ctor_set(v_reuseFailAlloc_2483_, 2, v___x_2477_);
v___x_2479_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
lean_object* v___x_2481_; 
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v___x_2479_);
v___x_2481_ = v___x_2474_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2479_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
else
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_dec(v___x_2471_);
lean_del_object(v___x_2467_);
lean_dec(v_y_2465_);
lean_dec(v_i_2464_);
v___x_2485_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1);
v___x_2486_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2379_, v___x_2485_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_2486_;
}
}
}
case 4:
{
lean_object* v_fvarId_2488_; lean_object* v_i_2489_; lean_object* v_y_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2515_; 
v_fvarId_2488_ = lean_ctor_get(v_decl_2380_, 0);
v_i_2489_ = lean_ctor_get(v_decl_2380_, 1);
v_y_2490_ = lean_ctor_get(v_decl_2380_, 2);
v_isSharedCheck_2515_ = !lean_is_exclusive(v_decl_2380_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2492_ = v_decl_2380_;
v_isShared_2493_ = v_isSharedCheck_2515_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_y_2490_);
lean_inc(v_i_2489_);
lean_inc(v_fvarId_2488_);
lean_dec(v_decl_2380_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2515_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2494_; uint8_t v___x_2495_; lean_object* v___x_2496_; 
v___x_2494_ = lean_st_ref_get(v_a_2382_);
v___x_2495_ = 1;
v___x_2496_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2494_, v_fvarId_2488_, v___x_2495_);
lean_dec(v___x_2494_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_fvarId_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v_fvarId_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_fvarId_2497_);
lean_dec_ref(v___x_2496_);
v___x_2498_ = lean_st_ref_get(v_a_2382_);
v___x_2499_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2498_, v_y_2490_, v___x_2495_);
lean_dec(v___x_2498_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_fvarId_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2510_; 
v_fvarId_2500_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2502_ = v___x_2499_;
v_isShared_2503_ = v_isSharedCheck_2510_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_fvarId_2500_);
lean_dec(v___x_2499_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2510_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 2, v_fvarId_2500_);
lean_ctor_set(v___x_2492_, 0, v_fvarId_2497_);
v___x_2505_ = v___x_2492_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_fvarId_2497_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_i_2489_);
lean_ctor_set(v_reuseFailAlloc_2509_, 2, v_fvarId_2500_);
v___x_2505_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2507_; 
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 0, v___x_2505_);
v___x_2507_ = v___x_2502_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2505_);
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
else
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
lean_dec(v___x_2499_);
lean_dec(v_fvarId_2497_);
lean_del_object(v___x_2492_);
lean_dec(v_i_2489_);
v___x_2511_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2);
v___x_2512_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2379_, v___x_2511_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_2512_;
}
}
else
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
lean_dec(v___x_2496_);
lean_del_object(v___x_2492_);
lean_dec(v_y_2490_);
lean_dec(v_i_2489_);
v___x_2513_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3);
v___x_2514_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2379_, v___x_2513_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_2514_;
}
}
}
case 5:
{
lean_object* v_fvarId_2516_; lean_object* v_i_2517_; lean_object* v_offset_2518_; lean_object* v_y_2519_; lean_object* v_ty_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2547_; 
v_fvarId_2516_ = lean_ctor_get(v_decl_2380_, 0);
v_i_2517_ = lean_ctor_get(v_decl_2380_, 1);
v_offset_2518_ = lean_ctor_get(v_decl_2380_, 2);
v_y_2519_ = lean_ctor_get(v_decl_2380_, 3);
v_ty_2520_ = lean_ctor_get(v_decl_2380_, 4);
v_isSharedCheck_2547_ = !lean_is_exclusive(v_decl_2380_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2522_ = v_decl_2380_;
v_isShared_2523_ = v_isSharedCheck_2547_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_ty_2520_);
lean_inc(v_y_2519_);
lean_inc(v_offset_2518_);
lean_inc(v_i_2517_);
lean_inc(v_fvarId_2516_);
lean_dec(v_decl_2380_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2547_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2524_; uint8_t v___x_2525_; lean_object* v___x_2526_; 
v___x_2524_ = lean_st_ref_get(v_a_2382_);
v___x_2525_ = 1;
v___x_2526_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2524_, v_fvarId_2516_, v___x_2525_);
lean_dec(v___x_2524_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_fvarId_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v_fvarId_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_fvarId_2527_);
lean_dec_ref(v___x_2526_);
v___x_2528_ = lean_st_ref_get(v_a_2382_);
v___x_2529_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2528_, v_y_2519_, v___x_2525_);
lean_dec(v___x_2528_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_fvarId_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2542_; 
v_fvarId_2530_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2532_ = v___x_2529_;
v_isShared_2533_ = v_isSharedCheck_2542_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_fvarId_2530_);
lean_dec(v___x_2529_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2542_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2537_; 
v___x_2534_ = lean_st_ref_get(v_a_2382_);
v___x_2535_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2379_, v___x_2534_, v___x_2525_, v_ty_2520_);
lean_dec(v___x_2534_);
if (v_isShared_2523_ == 0)
{
lean_ctor_set(v___x_2522_, 4, v___x_2535_);
lean_ctor_set(v___x_2522_, 3, v_fvarId_2530_);
lean_ctor_set(v___x_2522_, 0, v_fvarId_2527_);
v___x_2537_ = v___x_2522_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_fvarId_2527_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_i_2517_);
lean_ctor_set(v_reuseFailAlloc_2541_, 2, v_offset_2518_);
lean_ctor_set(v_reuseFailAlloc_2541_, 3, v_fvarId_2530_);
lean_ctor_set(v_reuseFailAlloc_2541_, 4, v___x_2535_);
v___x_2537_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2539_; 
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2537_);
v___x_2539_ = v___x_2532_;
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
lean_object* v___x_2543_; lean_object* v___x_2544_; 
lean_dec(v___x_2529_);
lean_dec(v_fvarId_2527_);
lean_del_object(v___x_2522_);
lean_dec_ref(v_ty_2520_);
lean_dec(v_offset_2518_);
lean_dec(v_i_2517_);
v___x_2543_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4);
v___x_2544_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2379_, v___x_2543_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_2544_;
}
}
else
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
lean_dec(v___x_2526_);
lean_del_object(v___x_2522_);
lean_dec_ref(v_ty_2520_);
lean_dec(v_y_2519_);
lean_dec(v_offset_2518_);
lean_dec(v_i_2517_);
v___x_2545_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5);
v___x_2546_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2379_, v___x_2545_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_2546_;
}
}
}
case 6:
{
lean_object* v_fvarId_2548_; lean_object* v_cidx_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2569_; 
v_fvarId_2548_ = lean_ctor_get(v_decl_2380_, 0);
v_cidx_2549_ = lean_ctor_get(v_decl_2380_, 1);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_decl_2380_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2551_ = v_decl_2380_;
v_isShared_2552_ = v_isSharedCheck_2569_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_cidx_2549_);
lean_inc(v_fvarId_2548_);
lean_dec(v_decl_2380_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2569_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2553_; uint8_t v___x_2554_; lean_object* v___x_2555_; 
v___x_2553_ = lean_st_ref_get(v_a_2382_);
v___x_2554_ = 1;
v___x_2555_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2553_, v_fvarId_2548_, v___x_2554_);
lean_dec(v___x_2553_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_fvarId_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2566_; 
v_fvarId_2556_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2558_ = v___x_2555_;
v_isShared_2559_ = v_isSharedCheck_2566_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_fvarId_2556_);
lean_dec(v___x_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2566_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v_fvarId_2556_);
v___x_2561_ = v___x_2551_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_fvarId_2556_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_cidx_2549_);
v___x_2561_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
lean_object* v___x_2563_; 
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 0, v___x_2561_);
v___x_2563_ = v___x_2558_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
else
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
lean_dec(v___x_2555_);
lean_del_object(v___x_2551_);
lean_dec(v_cidx_2549_);
v___x_2567_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6);
v___x_2568_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2379_, v___x_2567_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_2568_;
}
}
}
case 7:
{
lean_object* v_fvarId_2570_; lean_object* v_n_2571_; uint8_t v_check_2572_; uint8_t v_persistent_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2593_; 
v_fvarId_2570_ = lean_ctor_get(v_decl_2380_, 0);
v_n_2571_ = lean_ctor_get(v_decl_2380_, 1);
v_check_2572_ = lean_ctor_get_uint8(v_decl_2380_, sizeof(void*)*2);
v_persistent_2573_ = lean_ctor_get_uint8(v_decl_2380_, sizeof(void*)*2 + 1);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_decl_2380_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2575_ = v_decl_2380_;
v_isShared_2576_ = v_isSharedCheck_2593_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_n_2571_);
lean_inc(v_fvarId_2570_);
lean_dec(v_decl_2380_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2593_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2577_; uint8_t v___x_2578_; lean_object* v___x_2579_; 
v___x_2577_ = lean_st_ref_get(v_a_2382_);
v___x_2578_ = 1;
v___x_2579_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2577_, v_fvarId_2570_, v___x_2578_);
lean_dec(v___x_2577_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_fvarId_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2590_; 
v_fvarId_2580_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2582_ = v___x_2579_;
v_isShared_2583_ = v_isSharedCheck_2590_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_fvarId_2580_);
lean_dec(v___x_2579_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2590_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v_fvarId_2580_);
v___x_2585_ = v___x_2575_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_fvarId_2580_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v_n_2571_);
lean_ctor_set_uint8(v_reuseFailAlloc_2589_, sizeof(void*)*2, v_check_2572_);
lean_ctor_set_uint8(v_reuseFailAlloc_2589_, sizeof(void*)*2 + 1, v_persistent_2573_);
v___x_2585_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
lean_object* v___x_2587_; 
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 0, v___x_2585_);
v___x_2587_ = v___x_2582_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
lean_dec(v___x_2579_);
lean_del_object(v___x_2575_);
lean_dec(v_n_2571_);
v___x_2591_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7);
v___x_2592_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2379_, v___x_2591_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_2592_;
}
}
}
case 8:
{
lean_object* v_fvarId_2594_; lean_object* v_n_2595_; uint8_t v_check_2596_; uint8_t v_persistent_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2617_; 
v_fvarId_2594_ = lean_ctor_get(v_decl_2380_, 0);
v_n_2595_ = lean_ctor_get(v_decl_2380_, 1);
v_check_2596_ = lean_ctor_get_uint8(v_decl_2380_, sizeof(void*)*2);
v_persistent_2597_ = lean_ctor_get_uint8(v_decl_2380_, sizeof(void*)*2 + 1);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_decl_2380_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2599_ = v_decl_2380_;
v_isShared_2600_ = v_isSharedCheck_2617_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_n_2595_);
lean_inc(v_fvarId_2594_);
lean_dec(v_decl_2380_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2617_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2601_; uint8_t v___x_2602_; lean_object* v___x_2603_; 
v___x_2601_ = lean_st_ref_get(v_a_2382_);
v___x_2602_ = 1;
v___x_2603_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2601_, v_fvarId_2594_, v___x_2602_);
lean_dec(v___x_2601_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_fvarId_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2614_; 
v_fvarId_2604_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2606_ = v___x_2603_;
v_isShared_2607_ = v_isSharedCheck_2614_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_fvarId_2604_);
lean_dec(v___x_2603_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2614_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 0, v_fvarId_2604_);
v___x_2609_ = v___x_2599_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(8, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_fvarId_2604_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v_n_2595_);
lean_ctor_set_uint8(v_reuseFailAlloc_2613_, sizeof(void*)*2, v_check_2596_);
lean_ctor_set_uint8(v_reuseFailAlloc_2613_, sizeof(void*)*2 + 1, v_persistent_2597_);
v___x_2609_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_object* v___x_2611_; 
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v___x_2609_);
v___x_2611_ = v___x_2606_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2609_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
else
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
lean_dec(v___x_2603_);
lean_del_object(v___x_2599_);
lean_dec(v_n_2595_);
v___x_2615_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8);
v___x_2616_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2379_, v___x_2615_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_2616_;
}
}
}
default: 
{
lean_object* v_fvarId_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2638_; 
v_fvarId_2618_ = lean_ctor_get(v_decl_2380_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_decl_2380_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2620_ = v_decl_2380_;
v_isShared_2621_ = v_isSharedCheck_2638_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_fvarId_2618_);
lean_dec(v_decl_2380_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2638_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; uint8_t v___x_2623_; lean_object* v___x_2624_; 
v___x_2622_ = lean_st_ref_get(v_a_2382_);
v___x_2623_ = 1;
v___x_2624_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2622_, v_fvarId_2618_, v___x_2623_);
lean_dec(v___x_2622_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_fvarId_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2635_; 
v_fvarId_2625_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2627_ = v___x_2624_;
v_isShared_2628_ = v_isSharedCheck_2635_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_fvarId_2625_);
lean_dec(v___x_2624_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2635_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v_fvarId_2625_);
v___x_2630_ = v___x_2620_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_fvarId_2625_);
v___x_2630_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2632_; 
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v___x_2630_);
v___x_2632_ = v___x_2627_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2630_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
else
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
lean_dec(v___x_2624_);
lean_del_object(v___x_2620_);
v___x_2636_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9);
v___x_2637_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2379_, v___x_2636_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_2637_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(lean_object* v_pu_2639_, lean_object* v_decl_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
uint8_t v_pu_boxed_2648_; uint8_t v_a_boxed_2649_; lean_object* v_res_2650_; 
v_pu_boxed_2648_ = lean_unbox(v_pu_2639_);
v_a_boxed_2649_ = lean_unbox(v_a_2641_);
v_res_2650_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v_pu_boxed_2648_, v_decl_2640_, v_a_boxed_2649_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
lean_dec(v_a_2642_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t v_pu_2651_, lean_object* v_code_2652_, lean_object* v_s_2653_, uint8_t v_uniqueIdents_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = lean_st_mk_ref(v_s_2653_);
v___x_2661_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2651_, v_code_2652_, v_uniqueIdents_2654_, v___x_2660_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2670_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2664_ = v___x_2661_;
v_isShared_2665_ = v_isSharedCheck_2670_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2661_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2670_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2666_; lean_object* v___x_2668_; 
v___x_2666_ = lean_st_ref_get(v___x_2660_);
lean_dec(v___x_2660_);
lean_dec(v___x_2666_);
if (v_isShared_2665_ == 0)
{
v___x_2668_ = v___x_2664_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2662_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
else
{
lean_dec(v___x_2660_);
return v___x_2661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize___boxed(lean_object* v_pu_2671_, lean_object* v_code_2672_, lean_object* v_s_2673_, lean_object* v_uniqueIdents_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_){
_start:
{
uint8_t v_pu_boxed_2680_; uint8_t v_uniqueIdents_boxed_2681_; lean_object* v_res_2682_; 
v_pu_boxed_2680_ = lean_unbox(v_pu_2671_);
v_uniqueIdents_boxed_2681_ = lean_unbox(v_uniqueIdents_2674_);
v_res_2682_ = l_Lean_Compiler_LCNF_Code_internalize(v_pu_boxed_2680_, v_code_2672_, v_s_2673_, v_uniqueIdents_boxed_2681_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
lean_dec_ref(v_a_2675_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(lean_object* v_f_2683_, lean_object* v_v_2684_, uint8_t v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
if (lean_obj_tag(v_v_2684_) == 0)
{
lean_object* v_code_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2717_; 
v_code_2692_ = lean_ctor_get(v_v_2684_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v_v_2684_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2694_ = v_v_2684_;
v_isShared_2695_ = v_isSharedCheck_2717_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_code_2692_);
lean_dec(v_v_2684_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2717_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2696_ = lean_box(v___y_2685_);
lean_inc(v___y_2690_);
lean_inc_ref(v___y_2689_);
lean_inc(v___y_2688_);
lean_inc_ref(v___y_2687_);
lean_inc(v___y_2686_);
v___x_2697_ = lean_apply_8(v_f_2683_, v_code_2692_, v___x_2696_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, lean_box(0));
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2708_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2700_ = v___x_2697_;
v_isShared_2701_ = v_isSharedCheck_2708_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2697_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2708_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v_a_2698_);
v___x_2703_ = v___x_2694_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2705_; 
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2703_);
v___x_2705_ = v___x_2700_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_del_object(v___x_2694_);
v_a_2709_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2697_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2697_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
}
else
{
lean_object* v___x_2718_; 
lean_dec_ref(v_f_2683_);
v___x_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2718_, 0, v_v_2684_);
return v___x_2718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg___boxed(lean_object* v_f_2719_, lean_object* v_v_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
uint8_t v___y_1412__boxed_2728_; lean_object* v_res_2729_; 
v___y_1412__boxed_2728_ = lean_unbox(v___y_2721_);
v_res_2729_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2719_, v_v_2720_, v___y_1412__boxed_2728_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(uint8_t v_pu_2730_, lean_object* v_f_2731_, lean_object* v_v_2732_, uint8_t v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2731_, v_v_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___boxed(lean_object* v_pu_2741_, lean_object* v_f_2742_, lean_object* v_v_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
uint8_t v_pu_boxed_2751_; uint8_t v___y_1488__boxed_2752_; lean_object* v_res_2753_; 
v_pu_boxed_2751_ = lean_unbox(v_pu_2741_);
v___y_1488__boxed_2752_ = lean_unbox(v___y_2744_);
v_res_2753_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(v_pu_boxed_2751_, v_f_2742_, v_v_2743_, v___y_1488__boxed_2752_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(uint8_t v_pu_2754_, lean_object* v_decl_2755_, uint8_t v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v_toSignature_2763_; lean_object* v_value_2764_; uint8_t v_recursive_2765_; lean_object* v_inlineAttr_x3f_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2826_; 
v_toSignature_2763_ = lean_ctor_get(v_decl_2755_, 0);
v_value_2764_ = lean_ctor_get(v_decl_2755_, 1);
v_recursive_2765_ = lean_ctor_get_uint8(v_decl_2755_, sizeof(void*)*3);
v_inlineAttr_x3f_2766_ = lean_ctor_get(v_decl_2755_, 2);
v_isSharedCheck_2826_ = !lean_is_exclusive(v_decl_2755_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2768_ = v_decl_2755_;
v_isShared_2769_ = v_isSharedCheck_2826_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_inlineAttr_x3f_2766_);
lean_inc(v_value_2764_);
lean_inc(v_toSignature_2763_);
lean_dec(v_decl_2755_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2826_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v_name_2770_; lean_object* v_levelParams_2771_; lean_object* v_type_2772_; lean_object* v_params_2773_; uint8_t v_safe_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2825_; 
v_name_2770_ = lean_ctor_get(v_toSignature_2763_, 0);
v_levelParams_2771_ = lean_ctor_get(v_toSignature_2763_, 1);
v_type_2772_ = lean_ctor_get(v_toSignature_2763_, 2);
v_params_2773_ = lean_ctor_get(v_toSignature_2763_, 3);
v_safe_2774_ = lean_ctor_get_uint8(v_toSignature_2763_, sizeof(void*)*4);
v_isSharedCheck_2825_ = !lean_is_exclusive(v_toSignature_2763_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2776_ = v_toSignature_2763_;
v_isShared_2777_ = v_isSharedCheck_2825_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_params_2773_);
lean_inc(v_type_2772_);
lean_inc(v_levelParams_2771_);
lean_inc(v_name_2770_);
lean_dec(v_toSignature_2763_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2825_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; 
v___x_2778_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2754_, v_type_2772_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; size_t v_sz_2780_; size_t v___x_2781_; lean_object* v___x_2782_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref(v___x_2778_);
v_sz_2780_ = lean_array_size(v_params_2773_);
v___x_2781_ = ((size_t)0ULL);
v___x_2782_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2754_, v_sz_2780_, v___x_2781_, v_params_2773_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref(v___x_2782_);
v___x_2784_ = lean_box(v_pu_2754_);
v___x_2785_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed), 9, 1);
lean_closure_set(v___x_2785_, 0, v___x_2784_);
v___x_2786_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v___x_2785_, v_value_2764_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2800_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2789_ = v___x_2786_;
v_isShared_2790_ = v_isSharedCheck_2800_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2786_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2800_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 3, v_a_2783_);
lean_ctor_set(v___x_2776_, 2, v_a_2779_);
v___x_2792_ = v___x_2776_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_name_2770_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_levelParams_2771_);
lean_ctor_set(v_reuseFailAlloc_2799_, 2, v_a_2779_);
lean_ctor_set(v_reuseFailAlloc_2799_, 3, v_a_2783_);
lean_ctor_set_uint8(v_reuseFailAlloc_2799_, sizeof(void*)*4, v_safe_2774_);
v___x_2792_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2794_; 
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 1, v_a_2787_);
lean_ctor_set(v___x_2768_, 0, v___x_2792_);
v___x_2794_ = v___x_2768_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2792_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_a_2787_);
lean_ctor_set(v_reuseFailAlloc_2798_, 2, v_inlineAttr_x3f_2766_);
lean_ctor_set_uint8(v_reuseFailAlloc_2798_, sizeof(void*)*3, v_recursive_2765_);
v___x_2794_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_object* v___x_2796_; 
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 0, v___x_2794_);
v___x_2796_ = v___x_2789_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v_a_2783_);
lean_dec(v_a_2779_);
lean_del_object(v___x_2776_);
lean_dec(v_levelParams_2771_);
lean_dec(v_name_2770_);
lean_del_object(v___x_2768_);
lean_dec(v_inlineAttr_x3f_2766_);
v_a_2801_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2786_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2786_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
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
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec(v_a_2779_);
lean_del_object(v___x_2776_);
lean_dec(v_levelParams_2771_);
lean_dec(v_name_2770_);
lean_del_object(v___x_2768_);
lean_dec(v_inlineAttr_x3f_2766_);
lean_dec_ref(v_value_2764_);
v_a_2809_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2782_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2782_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
lean_del_object(v___x_2776_);
lean_dec_ref(v_params_2773_);
lean_dec(v_levelParams_2771_);
lean_dec(v_name_2770_);
lean_del_object(v___x_2768_);
lean_dec(v_inlineAttr_x3f_2766_);
lean_dec_ref(v_value_2764_);
v_a_2817_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2778_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2778_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go___boxed(lean_object* v_pu_2827_, lean_object* v_decl_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_){
_start:
{
uint8_t v_pu_boxed_2836_; uint8_t v_a_boxed_2837_; lean_object* v_res_2838_; 
v_pu_boxed_2836_ = lean_unbox(v_pu_2827_);
v_a_boxed_2837_ = lean_unbox(v_a_2829_);
v_res_2838_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_boxed_2836_, v_decl_2828_, v_a_boxed_2837_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_);
lean_dec(v_a_2834_);
lean_dec_ref(v_a_2833_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t v_pu_2839_, lean_object* v_decl_2840_, lean_object* v_s_2841_, uint8_t v_uniqueIdents_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = lean_st_mk_ref(v_s_2841_);
v___x_2849_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_2839_, v_decl_2840_, v_uniqueIdents_2842_, v___x_2848_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2858_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2852_ = v___x_2849_;
v_isShared_2853_ = v_isSharedCheck_2858_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2849_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2858_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2854_; lean_object* v___x_2856_; 
v___x_2854_ = lean_st_ref_get(v___x_2848_);
lean_dec(v___x_2848_);
lean_dec(v___x_2854_);
if (v_isShared_2853_ == 0)
{
v___x_2856_ = v___x_2852_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2850_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
else
{
lean_dec(v___x_2848_);
return v___x_2849_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize___boxed(lean_object* v_pu_2859_, lean_object* v_decl_2860_, lean_object* v_s_2861_, lean_object* v_uniqueIdents_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_){
_start:
{
uint8_t v_pu_boxed_2868_; uint8_t v_uniqueIdents_boxed_2869_; lean_object* v_res_2870_; 
v_pu_boxed_2868_ = lean_unbox(v_pu_2859_);
v_uniqueIdents_boxed_2869_ = lean_unbox(v_uniqueIdents_2862_);
v_res_2870_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_boxed_2868_, v_decl_2860_, v_s_2861_, v_uniqueIdents_boxed_2869_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
lean_dec(v_a_2864_);
lean_dec_ref(v_a_2863_);
return v_res_2870_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2871_ = lean_box(0);
v___x_2872_ = lean_unsigned_to_nat(16u);
v___x_2873_ = lean_mk_array(v___x_2872_, v___x_2871_);
return v___x_2873_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2874_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0);
v___x_2875_ = lean_unsigned_to_nat(0u);
v___x_2876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
lean_ctor_set(v___x_2876_, 1, v___x_2874_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(uint8_t v_pu_2877_, size_t v_sz_2878_, size_t v_i_2879_, lean_object* v_bs_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
uint8_t v___x_2886_; 
v___x_2886_ = lean_usize_dec_lt(v_i_2879_, v_sz_2878_);
if (v___x_2886_ == 0)
{
lean_object* v___x_2887_; 
v___x_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2887_, 0, v_bs_2880_);
return v___x_2887_;
}
else
{
lean_object* v___x_2888_; lean_object* v_lctx_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2917_; 
v___x_2888_ = lean_st_ref_take(v___y_2882_);
v_lctx_2889_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2917_ == 0)
{
lean_object* v_unused_2918_; 
v_unused_2918_ = lean_ctor_get(v___x_2888_, 1);
lean_dec(v_unused_2918_);
v___x_2891_ = v___x_2888_;
v_isShared_2892_ = v_isSharedCheck_2917_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_lctx_2889_);
lean_dec(v___x_2888_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2917_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2893_; lean_object* v___x_2895_; 
v___x_2893_ = lean_unsigned_to_nat(1u);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 1, v___x_2893_);
v___x_2895_ = v___x_2891_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_lctx_2889_);
lean_ctor_set(v_reuseFailAlloc_2916_, 1, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2896_; lean_object* v_v_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; uint8_t v___x_2900_; lean_object* v___x_2901_; 
v___x_2896_ = lean_st_ref_set(v___y_2882_, v___x_2895_);
v_v_2897_ = lean_array_uget_borrowed(v_bs_2880_, v_i_2879_);
v___x_2898_ = lean_unsigned_to_nat(0u);
v___x_2899_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_2900_ = 0;
lean_inc(v_v_2897_);
v___x_2901_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_2877_, v_v_2897_, v___x_2899_, v___x_2900_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v_bs_x27_2903_; size_t v___x_2904_; size_t v___x_2905_; lean_object* v___x_2906_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref(v___x_2901_);
v_bs_x27_2903_ = lean_array_uset(v_bs_2880_, v_i_2879_, v___x_2898_);
v___x_2904_ = ((size_t)1ULL);
v___x_2905_ = lean_usize_add(v_i_2879_, v___x_2904_);
v___x_2906_ = lean_array_uset(v_bs_x27_2903_, v_i_2879_, v_a_2902_);
v_i_2879_ = v___x_2905_;
v_bs_2880_ = v___x_2906_;
goto _start;
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec_ref(v_bs_2880_);
v_a_2908_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2901_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2901_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___boxed(lean_object* v_pu_2919_, lean_object* v_sz_2920_, lean_object* v_i_2921_, lean_object* v_bs_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
uint8_t v_pu_boxed_2928_; size_t v_sz_boxed_2929_; size_t v_i_boxed_2930_; lean_object* v_res_2931_; 
v_pu_boxed_2928_ = lean_unbox(v_pu_2919_);
v_sz_boxed_2929_ = lean_unbox_usize(v_sz_2920_);
lean_dec(v_sz_2920_);
v_i_boxed_2930_ = lean_unbox_usize(v_i_2921_);
lean_dec(v_i_2921_);
v_res_2931_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_boxed_2928_, v_sz_boxed_2929_, v_i_boxed_2930_, v_bs_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
return v_res_2931_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__0(void){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2932_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_2933_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2932_);
lean_ctor_set(v___x_2933_, 1, v___x_2932_);
lean_ctor_set(v___x_2933_, 2, v___x_2932_);
lean_ctor_set(v___x_2933_, 3, v___x_2932_);
lean_ctor_set(v___x_2933_, 4, v___x_2932_);
lean_ctor_set(v___x_2933_, 5, v___x_2932_);
return v___x_2933_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__1(void){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = lean_unsigned_to_nat(1u);
v___x_2935_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__0, &l_Lean_Compiler_LCNF_cleanup___closed__0_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__0);
v___x_2936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
lean_ctor_set(v___x_2936_, 1, v___x_2934_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup(uint8_t v_pu_2937_, lean_object* v_decl_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; size_t v_sz_2947_; size_t v___x_2948_; lean_object* v___x_2949_; 
v___x_2944_ = lean_st_ref_take(v_a_2940_);
lean_dec(v___x_2944_);
v___x_2945_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
v___x_2946_ = lean_st_ref_set(v_a_2940_, v___x_2945_);
v_sz_2947_ = lean_array_size(v_decl_2938_);
v___x_2948_ = ((size_t)0ULL);
v___x_2949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_2937_, v_sz_2947_, v___x_2948_, v_decl_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup___boxed(lean_object* v_pu_2950_, lean_object* v_decl_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_){
_start:
{
uint8_t v_pu_boxed_2957_; lean_object* v_res_2958_; 
v_pu_boxed_2957_ = lean_unbox(v_pu_2950_);
v_res_2958_ = l_Lean_Compiler_LCNF_cleanup(v_pu_boxed_2957_, v_decl_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_);
lean_dec(v_a_2955_);
lean_dec_ref(v_a_2954_);
lean_dec(v_a_2953_);
lean_dec_ref(v_a_2952_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(lean_object* v_a_2959_, lean_object* v_ngen_2960_, lean_object* v_a_x3f_2961_){
_start:
{
lean_object* v___x_2963_; lean_object* v_env_2964_; lean_object* v_nextMacroScope_2965_; lean_object* v_auxDeclNGen_2966_; lean_object* v_traceState_2967_; lean_object* v_cache_2968_; lean_object* v_messages_2969_; lean_object* v_infoState_2970_; lean_object* v_snapshotTasks_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2981_; 
v___x_2963_ = lean_st_ref_take(v_a_2959_);
v_env_2964_ = lean_ctor_get(v___x_2963_, 0);
v_nextMacroScope_2965_ = lean_ctor_get(v___x_2963_, 1);
v_auxDeclNGen_2966_ = lean_ctor_get(v___x_2963_, 3);
v_traceState_2967_ = lean_ctor_get(v___x_2963_, 4);
v_cache_2968_ = lean_ctor_get(v___x_2963_, 5);
v_messages_2969_ = lean_ctor_get(v___x_2963_, 6);
v_infoState_2970_ = lean_ctor_get(v___x_2963_, 7);
v_snapshotTasks_2971_ = lean_ctor_get(v___x_2963_, 8);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2981_ == 0)
{
lean_object* v_unused_2982_; 
v_unused_2982_ = lean_ctor_get(v___x_2963_, 2);
lean_dec(v_unused_2982_);
v___x_2973_ = v___x_2963_;
v_isShared_2974_ = v_isSharedCheck_2981_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_snapshotTasks_2971_);
lean_inc(v_infoState_2970_);
lean_inc(v_messages_2969_);
lean_inc(v_cache_2968_);
lean_inc(v_traceState_2967_);
lean_inc(v_auxDeclNGen_2966_);
lean_inc(v_nextMacroScope_2965_);
lean_inc(v_env_2964_);
lean_dec(v___x_2963_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2981_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 2, v_ngen_2960_);
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_env_2964_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_nextMacroScope_2965_);
lean_ctor_set(v_reuseFailAlloc_2980_, 2, v_ngen_2960_);
lean_ctor_set(v_reuseFailAlloc_2980_, 3, v_auxDeclNGen_2966_);
lean_ctor_set(v_reuseFailAlloc_2980_, 4, v_traceState_2967_);
lean_ctor_set(v_reuseFailAlloc_2980_, 5, v_cache_2968_);
lean_ctor_set(v_reuseFailAlloc_2980_, 6, v_messages_2969_);
lean_ctor_set(v_reuseFailAlloc_2980_, 7, v_infoState_2970_);
lean_ctor_set(v_reuseFailAlloc_2980_, 8, v_snapshotTasks_2971_);
v___x_2976_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2977_ = lean_st_ref_set(v_a_2959_, v___x_2976_);
v___x_2978_ = lean_box(0);
v___x_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2978_);
return v___x_2979_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0___boxed(lean_object* v_a_2983_, lean_object* v_ngen_2984_, lean_object* v_a_x3f_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_2983_, v_ngen_2984_, v_a_x3f_2985_);
lean_dec(v_a_x3f_2985_);
lean_dec(v_a_2983_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(uint8_t v_pu_2994_, lean_object* v_decl_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v_env_3001_; lean_object* v_nextMacroScope_3002_; lean_object* v_auxDeclNGen_3003_; lean_object* v_traceState_3004_; lean_object* v_cache_3005_; lean_object* v_messages_3006_; lean_object* v_infoState_3007_; lean_object* v_snapshotTasks_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3054_; 
v___x_2999_ = lean_st_ref_get(v_a_2997_);
v___x_3000_ = lean_st_ref_take(v_a_2997_);
v_env_3001_ = lean_ctor_get(v___x_3000_, 0);
v_nextMacroScope_3002_ = lean_ctor_get(v___x_3000_, 1);
v_auxDeclNGen_3003_ = lean_ctor_get(v___x_3000_, 3);
v_traceState_3004_ = lean_ctor_get(v___x_3000_, 4);
v_cache_3005_ = lean_ctor_get(v___x_3000_, 5);
v_messages_3006_ = lean_ctor_get(v___x_3000_, 6);
v_infoState_3007_ = lean_ctor_get(v___x_3000_, 7);
v_snapshotTasks_3008_ = lean_ctor_get(v___x_3000_, 8);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3054_ == 0)
{
lean_object* v_unused_3055_; 
v_unused_3055_ = lean_ctor_get(v___x_3000_, 2);
lean_dec(v_unused_3055_);
v___x_3010_ = v___x_3000_;
v_isShared_3011_ = v_isSharedCheck_3054_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_snapshotTasks_3008_);
lean_inc(v_infoState_3007_);
lean_inc(v_messages_3006_);
lean_inc(v_cache_3005_);
lean_inc(v_traceState_3004_);
lean_inc(v_auxDeclNGen_3003_);
lean_inc(v_nextMacroScope_3002_);
lean_inc(v_env_3001_);
lean_dec(v___x_3000_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3054_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3012_; lean_object* v___x_3014_; 
v___x_3012_ = ((lean_object*)(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2));
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 2, v___x_3012_);
v___x_3014_ = v___x_3010_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_env_3001_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v_nextMacroScope_3002_);
lean_ctor_set(v_reuseFailAlloc_3053_, 2, v___x_3012_);
lean_ctor_set(v_reuseFailAlloc_3053_, 3, v_auxDeclNGen_3003_);
lean_ctor_set(v_reuseFailAlloc_3053_, 4, v_traceState_3004_);
lean_ctor_set(v_reuseFailAlloc_3053_, 5, v_cache_3005_);
lean_ctor_set(v_reuseFailAlloc_3053_, 6, v_messages_3006_);
lean_ctor_set(v_reuseFailAlloc_3053_, 7, v_infoState_3007_);
lean_ctor_set(v_reuseFailAlloc_3053_, 8, v_snapshotTasks_3008_);
v___x_3014_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
lean_object* v___x_3015_; lean_object* v_ngen_3016_; lean_object* v___x_3017_; uint8_t v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; uint8_t v___x_3023_; lean_object* v_r_3024_; 
v___x_3015_ = lean_st_ref_set(v_a_2997_, v___x_3014_);
v_ngen_3016_ = lean_ctor_get(v___x_2999_, 2);
lean_inc_ref(v_ngen_3016_);
lean_dec(v___x_2999_);
v___x_3017_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_3018_ = 0;
v___x_3019_ = lean_box(v_pu_2994_);
v___x_3020_ = lean_box(v___x_3018_);
v___x_3021_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_internalize___boxed), 9, 4);
lean_closure_set(v___x_3021_, 0, v___x_3019_);
lean_closure_set(v___x_3021_, 1, v_decl_2995_);
lean_closure_set(v___x_3021_, 2, v___x_3017_);
lean_closure_set(v___x_3021_, 3, v___x_3020_);
v___x_3022_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
v___x_3023_ = 0;
v_r_3024_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v___x_3021_, v___x_3022_, v___x_3023_, v_a_2996_, v_a_2997_);
if (lean_obj_tag(v_r_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3041_; 
v_a_3025_ = lean_ctor_get(v_r_3024_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v_r_3024_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3027_ = v_r_3024_;
v_isShared_3028_ = v_isSharedCheck_3041_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v_r_3024_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3041_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
lean_inc(v_a_3025_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set_tag(v___x_3027_, 1);
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
v___x_3031_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_2997_, v_ngen_3016_, v___x_3030_);
lean_dec_ref(v___x_3030_);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3038_ == 0)
{
lean_object* v_unused_3039_; 
v_unused_3039_ = lean_ctor_get(v___x_3031_, 0);
lean_dec(v_unused_3039_);
v___x_3033_ = v___x_3031_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_dec(v___x_3031_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v_a_3025_);
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3025_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
v_a_3042_ = lean_ctor_get(v_r_3024_, 0);
lean_inc(v_a_3042_);
lean_dec_ref(v_r_3024_);
v___x_3043_ = lean_box(0);
v___x_3044_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_2997_, v_ngen_3016_, v___x_3043_);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3051_ == 0)
{
lean_object* v_unused_3052_; 
v_unused_3052_ = lean_ctor_get(v___x_3044_, 0);
lean_dec(v_unused_3052_);
v___x_3046_ = v___x_3044_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_dec(v___x_3044_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
lean_ctor_set_tag(v___x_3046_, 1);
lean_ctor_set(v___x_3046_, 0, v_a_3042_);
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3042_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___boxed(lean_object* v_pu_3056_, lean_object* v_decl_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_){
_start:
{
uint8_t v_pu_boxed_3061_; lean_object* v_res_3062_; 
v_pu_boxed_3061_ = lean_unbox(v_pu_3056_);
v_res_3062_ = l_Lean_Compiler_LCNF_normalizeFVarIds(v_pu_boxed_3061_, v_decl_3057_, v_a_3058_, v_a_3059_);
lean_dec(v_a_3059_);
lean_dec_ref(v_a_3058_);
return v_res_3062_;
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
