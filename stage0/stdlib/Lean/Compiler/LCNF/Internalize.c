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
lean_object* v___x_402_; lean_object* v_ngen_403_; lean_object* v_namePrefix_404_; lean_object* v_idx_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_435_; 
v___x_402_ = lean_st_ref_get(v___y_400_);
v_ngen_403_ = lean_ctor_get(v___x_402_, 2);
lean_inc_ref(v_ngen_403_);
lean_dec(v___x_402_);
v_namePrefix_404_ = lean_ctor_get(v_ngen_403_, 0);
v_idx_405_ = lean_ctor_get(v_ngen_403_, 1);
v_isSharedCheck_435_ = !lean_is_exclusive(v_ngen_403_);
if (v_isSharedCheck_435_ == 0)
{
v___x_407_ = v_ngen_403_;
v_isShared_408_ = v_isSharedCheck_435_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_idx_405_);
lean_inc(v_namePrefix_404_);
lean_dec(v_ngen_403_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_435_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v_env_410_; lean_object* v_nextMacroScope_411_; lean_object* v_auxDeclNGen_412_; lean_object* v_traceState_413_; lean_object* v_cache_414_; lean_object* v_messages_415_; lean_object* v_infoState_416_; lean_object* v_snapshotTasks_417_; lean_object* v_newDecls_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_433_; 
v___x_409_ = lean_st_ref_take(v___y_400_);
v_env_410_ = lean_ctor_get(v___x_409_, 0);
v_nextMacroScope_411_ = lean_ctor_get(v___x_409_, 1);
v_auxDeclNGen_412_ = lean_ctor_get(v___x_409_, 3);
v_traceState_413_ = lean_ctor_get(v___x_409_, 4);
v_cache_414_ = lean_ctor_get(v___x_409_, 5);
v_messages_415_ = lean_ctor_get(v___x_409_, 6);
v_infoState_416_ = lean_ctor_get(v___x_409_, 7);
v_snapshotTasks_417_ = lean_ctor_get(v___x_409_, 8);
v_newDecls_418_ = lean_ctor_get(v___x_409_, 9);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; 
v_unused_434_ = lean_ctor_get(v___x_409_, 2);
lean_dec(v_unused_434_);
v___x_420_ = v___x_409_;
v_isShared_421_ = v_isSharedCheck_433_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_newDecls_418_);
lean_inc(v_snapshotTasks_417_);
lean_inc(v_infoState_416_);
lean_inc(v_messages_415_);
lean_inc(v_cache_414_);
lean_inc(v_traceState_413_);
lean_inc(v_auxDeclNGen_412_);
lean_inc(v_nextMacroScope_411_);
lean_inc(v_env_410_);
lean_dec(v___x_409_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_433_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v_r_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
lean_inc(v_idx_405_);
lean_inc(v_namePrefix_404_);
v_r_422_ = l_Lean_Name_num___override(v_namePrefix_404_, v_idx_405_);
v___x_423_ = lean_unsigned_to_nat(1u);
v___x_424_ = lean_nat_add(v_idx_405_, v___x_423_);
lean_dec(v_idx_405_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 1, v___x_424_);
v___x_426_ = v___x_407_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_namePrefix_404_);
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
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_env_410_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_nextMacroScope_411_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v_auxDeclNGen_412_);
lean_ctor_set(v_reuseFailAlloc_431_, 4, v_traceState_413_);
lean_ctor_set(v_reuseFailAlloc_431_, 5, v_cache_414_);
lean_ctor_set(v_reuseFailAlloc_431_, 6, v_messages_415_);
lean_ctor_set(v_reuseFailAlloc_431_, 7, v_infoState_416_);
lean_ctor_set(v_reuseFailAlloc_431_, 8, v_snapshotTasks_417_);
lean_ctor_set(v_reuseFailAlloc_431_, 9, v_newDecls_418_);
v___x_428_ = v_reuseFailAlloc_431_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_st_ref_set(v___y_400_, v___x_428_);
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
uint8_t v___y_3128__boxed_462_; lean_object* v_res_463_; 
v___y_3128__boxed_462_ = lean_unbox(v___y_455_);
v_res_463_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(v___y_3128__boxed_462_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
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
v___x_480_ = lean_st_ref_set(v_a_466_, v___x_479_);
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
uint8_t v___y_3203__boxed_532_; lean_object* v_res_533_; 
v___y_3203__boxed_532_ = lean_unbox(v___y_525_);
v_res_533_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(v___y_3203__boxed_532_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
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
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___f_663_; lean_object* v___x_8158__overap_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_660_ = l_StateRefT_x27_instMonad___redArg(v___x_659_);
v___x_661_ = l_Lean_instInhabitedExpr;
v___x_662_ = l_instInhabitedOfMonad___redArg(v___x_660_, v___x_661_);
v___f_663_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_663_, 0, v___x_662_);
v___x_8158__overap_664_ = lean_panic_fn_borrowed(v___f_663_, v_msg_603_);
lean_dec_ref(v___f_663_);
v___x_665_ = lean_box(v___y_604_);
lean_inc(v___y_609_);
lean_inc_ref(v___y_608_);
lean_inc(v___y_607_);
lean_inc_ref(v___y_606_);
lean_inc(v___y_605_);
v___x_666_ = lean_apply_7(v___x_8158__overap_664_, v___x_665_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, lean_box(0));
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
uint8_t v___y_8278__boxed_687_; lean_object* v_res_688_; 
v___y_8278__boxed_687_ = lean_unbox(v___y_680_);
v_res_688_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v_msg_679_, v___y_8278__boxed_687_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
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
lean_dec_ref(v_e_699_);
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
lean_dec_ref(v_val_713_);
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
lean_dec_ref(v___x_761_);
lean_inc_ref(v_arg_760_);
v___x_763_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_698_, v_arg_760_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_783_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_783_ == 0)
{
v___x_766_ = v___x_763_;
v_isShared_767_ = v_isSharedCheck_783_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_763_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_783_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___y_769_; uint8_t v___y_775_; size_t v___x_777_; size_t v___x_778_; uint8_t v___x_779_; 
v___x_777_ = lean_ptr_addr(v_fn_759_);
v___x_778_ = lean_ptr_addr(v_a_762_);
v___x_779_ = lean_usize_dec_eq(v___x_777_, v___x_778_);
if (v___x_779_ == 0)
{
v___y_775_ = v___x_779_;
goto v___jp_774_;
}
else
{
size_t v___x_780_; size_t v___x_781_; uint8_t v___x_782_; 
v___x_780_ = lean_ptr_addr(v_arg_760_);
v___x_781_ = lean_ptr_addr(v_a_764_);
v___x_782_ = lean_usize_dec_eq(v___x_780_, v___x_781_);
v___y_775_ = v___x_782_;
goto v___jp_774_;
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
v___jp_774_:
{
if (v___y_775_ == 0)
{
lean_object* v___x_776_; 
lean_dec_ref(v_e_699_);
v___x_776_ = l_Lean_Expr_app___override(v_a_762_, v_a_764_);
v___y_769_ = v___x_776_;
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
}
}
else
{
lean_dec(v_a_762_);
lean_dec_ref(v_e_699_);
return v___x_763_;
}
}
else
{
lean_dec_ref(v_e_699_);
return v___x_761_;
}
}
case 6:
{
lean_object* v_binderName_784_; lean_object* v_binderType_785_; lean_object* v_body_786_; uint8_t v_binderInfo_787_; lean_object* v___x_788_; 
v_binderName_784_ = lean_ctor_get(v_e_699_, 0);
v_binderType_785_ = lean_ctor_get(v_e_699_, 1);
v_body_786_ = lean_ctor_get(v_e_699_, 2);
v_binderInfo_787_ = lean_ctor_get_uint8(v_e_699_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_785_);
v___x_788_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_698_, v_binderType_785_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_790_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref(v___x_788_);
lean_inc_ref(v_body_786_);
v___x_790_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_698_, v_body_786_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_815_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_815_ == 0)
{
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_815_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_815_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
uint8_t v___y_796_; size_t v___x_809_; size_t v___x_810_; uint8_t v___x_811_; 
v___x_809_ = lean_ptr_addr(v_binderType_785_);
v___x_810_ = lean_ptr_addr(v_a_789_);
v___x_811_ = lean_usize_dec_eq(v___x_809_, v___x_810_);
if (v___x_811_ == 0)
{
v___y_796_ = v___x_811_;
goto v___jp_795_;
}
else
{
size_t v___x_812_; size_t v___x_813_; uint8_t v___x_814_; 
v___x_812_ = lean_ptr_addr(v_body_786_);
v___x_813_ = lean_ptr_addr(v_a_791_);
v___x_814_ = lean_usize_dec_eq(v___x_812_, v___x_813_);
v___y_796_ = v___x_814_;
goto v___jp_795_;
}
v___jp_795_:
{
if (v___y_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_799_; 
lean_inc(v_binderName_784_);
lean_dec_ref(v_e_699_);
v___x_797_ = l_Lean_Expr_lam___override(v_binderName_784_, v_a_789_, v_a_791_, v_binderInfo_787_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_797_);
v___x_799_ = v___x_793_;
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
uint8_t v___x_801_; 
v___x_801_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_787_, v_binderInfo_787_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_804_; 
lean_inc(v_binderName_784_);
lean_dec_ref(v_e_699_);
v___x_802_ = l_Lean_Expr_lam___override(v_binderName_784_, v_a_789_, v_a_791_, v_binderInfo_787_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_802_);
v___x_804_ = v___x_793_;
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
lean_object* v___x_807_; 
lean_dec(v_a_791_);
lean_dec(v_a_789_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v_e_699_);
v___x_807_ = v___x_793_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_e_699_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
}
else
{
lean_dec(v_a_789_);
lean_dec_ref(v_e_699_);
return v___x_790_;
}
}
else
{
lean_dec_ref(v_e_699_);
return v___x_788_;
}
}
case 7:
{
lean_object* v_binderName_816_; lean_object* v_binderType_817_; lean_object* v_body_818_; uint8_t v_binderInfo_819_; lean_object* v___x_820_; 
v_binderName_816_ = lean_ctor_get(v_e_699_, 0);
v_binderType_817_ = lean_ctor_get(v_e_699_, 1);
v_body_818_ = lean_ctor_get(v_e_699_, 2);
v_binderInfo_819_ = lean_ctor_get_uint8(v_e_699_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_817_);
v___x_820_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_698_, v_binderType_817_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_822_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref(v___x_820_);
lean_inc_ref(v_body_818_);
v___x_822_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_698_, v_body_818_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_847_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_847_ == 0)
{
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_847_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_847_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
uint8_t v___y_828_; size_t v___x_841_; size_t v___x_842_; uint8_t v___x_843_; 
v___x_841_ = lean_ptr_addr(v_binderType_817_);
v___x_842_ = lean_ptr_addr(v_a_821_);
v___x_843_ = lean_usize_dec_eq(v___x_841_, v___x_842_);
if (v___x_843_ == 0)
{
v___y_828_ = v___x_843_;
goto v___jp_827_;
}
else
{
size_t v___x_844_; size_t v___x_845_; uint8_t v___x_846_; 
v___x_844_ = lean_ptr_addr(v_body_818_);
v___x_845_ = lean_ptr_addr(v_a_823_);
v___x_846_ = lean_usize_dec_eq(v___x_844_, v___x_845_);
v___y_828_ = v___x_846_;
goto v___jp_827_;
}
v___jp_827_:
{
if (v___y_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_831_; 
lean_inc(v_binderName_816_);
lean_dec_ref(v_e_699_);
v___x_829_ = l_Lean_Expr_forallE___override(v_binderName_816_, v_a_821_, v_a_823_, v_binderInfo_819_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_829_);
v___x_831_ = v___x_825_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
else
{
uint8_t v___x_833_; 
v___x_833_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_819_, v_binderInfo_819_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_836_; 
lean_inc(v_binderName_816_);
lean_dec_ref(v_e_699_);
v___x_834_ = l_Lean_Expr_forallE___override(v_binderName_816_, v_a_821_, v_a_823_, v_binderInfo_819_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_834_);
v___x_836_ = v___x_825_;
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
lean_object* v___x_839_; 
lean_dec(v_a_823_);
lean_dec(v_a_821_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v_e_699_);
v___x_839_ = v___x_825_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_e_699_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
}
}
else
{
lean_dec(v_a_821_);
lean_dec_ref(v_e_699_);
return v___x_822_;
}
}
else
{
lean_dec_ref(v_e_699_);
return v___x_820_;
}
}
case 8:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec_ref(v_e_699_);
v___x_848_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3, &l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3);
v___x_849_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v___x_848_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
return v___x_849_;
}
case 10:
{
lean_object* v_data_850_; lean_object* v_expr_851_; lean_object* v___x_852_; 
v_data_850_ = lean_ctor_get(v_e_699_, 0);
v_expr_851_ = lean_ctor_get(v_e_699_, 1);
lean_inc_ref(v_expr_851_);
v___x_852_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_698_, v_expr_851_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_867_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_867_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_867_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_867_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
size_t v___x_857_; size_t v___x_858_; uint8_t v___x_859_; 
v___x_857_ = lean_ptr_addr(v_expr_851_);
v___x_858_ = lean_ptr_addr(v_a_853_);
v___x_859_ = lean_usize_dec_eq(v___x_857_, v___x_858_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; lean_object* v___x_862_; 
lean_inc(v_data_850_);
lean_dec_ref(v_e_699_);
v___x_860_ = l_Lean_Expr_mdata___override(v_data_850_, v_a_853_);
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
lean_object* v___x_865_; 
lean_dec(v_a_853_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v_e_699_);
v___x_865_ = v___x_855_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_e_699_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
else
{
lean_dec_ref(v_e_699_);
return v___x_852_;
}
}
case 11:
{
lean_object* v_typeName_868_; lean_object* v_idx_869_; lean_object* v_struct_870_; lean_object* v___x_871_; 
v_typeName_868_ = lean_ctor_get(v_e_699_, 0);
v_idx_869_ = lean_ctor_get(v_e_699_, 1);
v_struct_870_ = lean_ctor_get(v_e_699_, 2);
lean_inc_ref(v_struct_870_);
v___x_871_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_698_, v_struct_870_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_886_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_886_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_886_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_886_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
size_t v___x_876_; size_t v___x_877_; uint8_t v___x_878_; 
v___x_876_ = lean_ptr_addr(v_struct_870_);
v___x_877_ = lean_ptr_addr(v_a_872_);
v___x_878_ = lean_usize_dec_eq(v___x_876_, v___x_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_881_; 
lean_inc(v_idx_869_);
lean_inc(v_typeName_868_);
lean_dec_ref(v_e_699_);
v___x_879_ = l_Lean_Expr_proj___override(v_typeName_868_, v_idx_869_, v_a_872_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_879_);
v___x_881_ = v___x_874_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
else
{
lean_object* v___x_884_; 
lean_dec(v_a_872_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v_e_699_);
v___x_884_ = v___x_874_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_e_699_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
else
{
lean_dec_ref(v_e_699_);
return v___x_871_;
}
}
default: 
{
lean_object* v___x_887_; 
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v_e_699_);
return v___x_887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(uint8_t v_pu_888_, lean_object* v_e_889_, uint8_t v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
if (lean_obj_tag(v_e_889_) == 5)
{
lean_object* v_fn_897_; lean_object* v_arg_898_; lean_object* v___x_899_; 
v_fn_897_ = lean_ctor_get(v_e_889_, 0);
v_arg_898_ = lean_ctor_get(v_e_889_, 1);
lean_inc_ref(v_fn_897_);
v___x_899_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_888_, v_fn_897_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_901_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref(v___x_899_);
lean_inc_ref(v_arg_898_);
v___x_901_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_888_, v_arg_898_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_921_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_921_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_921_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_921_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
uint8_t v___y_907_; size_t v___x_915_; size_t v___x_916_; uint8_t v___x_917_; 
v___x_915_ = lean_ptr_addr(v_fn_897_);
v___x_916_ = lean_ptr_addr(v_a_900_);
v___x_917_ = lean_usize_dec_eq(v___x_915_, v___x_916_);
if (v___x_917_ == 0)
{
v___y_907_ = v___x_917_;
goto v___jp_906_;
}
else
{
size_t v___x_918_; size_t v___x_919_; uint8_t v___x_920_; 
v___x_918_ = lean_ptr_addr(v_arg_898_);
v___x_919_ = lean_ptr_addr(v_a_902_);
v___x_920_ = lean_usize_dec_eq(v___x_918_, v___x_919_);
v___y_907_ = v___x_920_;
goto v___jp_906_;
}
v___jp_906_:
{
if (v___y_907_ == 0)
{
lean_object* v___x_908_; lean_object* v___x_910_; 
lean_dec_ref(v_e_889_);
v___x_908_ = l_Lean_Expr_app___override(v_a_900_, v_a_902_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_908_);
v___x_910_ = v___x_904_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
else
{
lean_object* v___x_913_; 
lean_dec(v_a_902_);
lean_dec(v_a_900_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v_e_889_);
v___x_913_ = v___x_904_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_e_889_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
else
{
lean_dec(v_a_900_);
lean_dec_ref(v_e_889_);
return v___x_901_;
}
}
else
{
lean_dec_ref(v_e_889_);
return v___x_899_;
}
}
else
{
lean_object* v___x_922_; 
v___x_922_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_888_, v_e_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
return v___x_922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp___boxed(lean_object* v_pu_923_, lean_object* v_e_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
uint8_t v_pu_boxed_932_; uint8_t v_a_boxed_933_; lean_object* v_res_934_; 
v_pu_boxed_932_ = lean_unbox(v_pu_923_);
v_a_boxed_933_ = lean_unbox(v_a_925_);
v_res_934_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_boxed_932_, v_e_924_, v_a_boxed_933_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___boxed(lean_object* v_pu_935_, lean_object* v_e_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
uint8_t v_pu_boxed_944_; uint8_t v_a_boxed_945_; lean_object* v_res_946_; 
v_pu_boxed_944_ = lean_unbox(v_pu_935_);
v_a_boxed_945_ = lean_unbox(v_a_937_);
v_res_946_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_boxed_944_, v_e_936_, v_a_boxed_945_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(lean_object* v_00_u03b2_947_, lean_object* v_m_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v_m_948_, v_a_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___boxed(lean_object* v_00_u03b2_951_, lean_object* v_m_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(v_00_u03b2_951_, v_m_952_, v_a_953_);
lean_dec(v_a_953_);
lean_dec_ref(v_m_952_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(lean_object* v_00_u03b2_955_, lean_object* v_a_956_, lean_object* v_x_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_956_, v_x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_959_, lean_object* v_a_960_, lean_object* v_x_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(v_00_u03b2_959_, v_a_960_, v_x_961_);
lean_dec(v_x_961_);
lean_dec(v_a_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(uint8_t v_pu_963_, lean_object* v_e_964_, uint8_t v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
uint8_t v___x_972_; uint8_t v___x_973_; 
v___x_972_ = 1;
v___x_973_ = l_Lean_Compiler_LCNF_instDecidableEqPurity(v_pu_963_, v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
v___x_974_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_963_, v_e_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_974_;
}
else
{
lean_object* v___x_975_; 
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v_e_964_);
return v___x_975_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___boxed(lean_object* v_pu_976_, lean_object* v_e_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
uint8_t v_pu_boxed_985_; uint8_t v_a_boxed_986_; lean_object* v_res_987_; 
v_pu_boxed_985_ = lean_unbox(v_pu_976_);
v_a_boxed_986_ = lean_unbox(v_a_978_);
v_res_987_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_boxed_985_, v_e_977_, v_a_boxed_986_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
lean_dec(v_a_979_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t v_pu_988_, lean_object* v_p_989_, uint8_t v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_fvarId_997_; lean_object* v_binderName_998_; lean_object* v_type_999_; uint8_t v_borrow_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1048_; 
v_fvarId_997_ = lean_ctor_get(v_p_989_, 0);
v_binderName_998_ = lean_ctor_get(v_p_989_, 1);
v_type_999_ = lean_ctor_get(v_p_989_, 2);
v_borrow_1000_ = lean_ctor_get_uint8(v_p_989_, sizeof(void*)*3);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_p_989_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1002_ = v_p_989_;
v_isShared_1003_ = v_isSharedCheck_1048_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_type_999_);
lean_inc(v_binderName_998_);
lean_inc(v_fvarId_997_);
lean_dec(v_p_989_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1048_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v_a_1005_; lean_object* v___x_1006_; 
v___x_1004_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_998_, v_a_990_, v_a_993_);
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref(v___x_1004_);
v___x_1006_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_988_, v_type_999_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1008_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref(v___x_1006_);
v___x_1008_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_997_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1031_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1031_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1031_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v_lctx_1014_; lean_object* v_nextIdx_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1030_; 
v___x_1013_ = lean_st_ref_take(v_a_993_);
v_lctx_1014_ = lean_ctor_get(v___x_1013_, 0);
v_nextIdx_1015_ = lean_ctor_get(v___x_1013_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1017_ = v___x_1013_;
v_isShared_1018_ = v_isSharedCheck_1030_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_nextIdx_1015_);
lean_inc(v_lctx_1014_);
lean_dec(v___x_1013_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1030_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 2, v_a_1007_);
lean_ctor_set(v___x_1002_, 1, v_a_1005_);
lean_ctor_set(v___x_1002_, 0, v_a_1009_);
v___x_1020_ = v___x_1002_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1009_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_a_1005_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v_a_1007_);
lean_ctor_set_uint8(v_reuseFailAlloc_1029_, sizeof(void*)*3, v_borrow_1000_);
v___x_1020_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; lean_object* v___x_1023_; 
lean_inc_ref(v___x_1020_);
v___x_1021_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_988_, v_lctx_1014_, v___x_1020_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v___x_1021_);
v___x_1023_ = v___x_1017_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_nextIdx_1015_);
v___x_1023_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1024_ = lean_st_ref_set(v_a_993_, v___x_1023_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1020_);
v___x_1026_ = v___x_1011_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1020_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v_a_1007_);
lean_dec(v_a_1005_);
lean_del_object(v___x_1002_);
v_a_1032_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1008_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1008_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
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
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_dec(v_a_1005_);
lean_del_object(v___x_1002_);
lean_dec(v_fvarId_997_);
v_a_1040_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1006_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1006_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(lean_object* v_pu_1049_, lean_object* v_p_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
uint8_t v_pu_boxed_1058_; uint8_t v_a_boxed_1059_; lean_object* v_res_1060_; 
v_pu_boxed_1058_ = lean_unbox(v_pu_1049_);
v_a_boxed_1059_ = lean_unbox(v_a_1051_);
v_res_1060_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_boxed_1058_, v_p_1050_, v_a_boxed_1059_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg(uint8_t v_pu_1061_, lean_object* v_arg_1062_, uint8_t v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
switch(lean_obj_tag(v_arg_1062_))
{
case 0:
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v_arg_1062_);
return v___x_1070_;
}
case 1:
{
lean_object* v_fvarId_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v_fvarId_1071_ = lean_ctor_get(v_arg_1062_, 0);
v___x_1072_ = lean_st_ref_get(v_a_1064_);
v___x_1073_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v___x_1072_, v_fvarId_1071_);
lean_dec(v___x_1072_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v_arg_1062_);
return v___x_1074_;
}
else
{
lean_object* v_val_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref(v_arg_1062_);
v_val_1075_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1077_ = v___x_1073_;
v_isShared_1078_ = v_isSharedCheck_1105_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_val_1075_);
lean_dec(v___x_1073_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1105_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
switch(lean_obj_tag(v_val_1075_))
{
case 0:
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = lean_box(0);
if (v_isShared_1078_ == 0)
{
lean_ctor_set_tag(v___x_1077_, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1079_);
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
case 1:
{
lean_object* v_fvarId_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1093_; 
v_fvarId_1083_ = lean_ctor_get(v_val_1075_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_val_1075_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1085_ = v_val_1075_;
v_isShared_1086_ = v_isSharedCheck_1093_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_fvarId_1083_);
lean_dec(v_val_1075_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1093_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_fvarId_1083_);
v___x_1088_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1090_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set_tag(v___x_1077_, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1088_);
v___x_1090_ = v___x_1077_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
default: 
{
lean_object* v_expr_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1104_; 
v_expr_1094_ = lean_ctor_get(v_val_1075_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_val_1075_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1096_ = v_val_1075_;
v_isShared_1097_ = v_isSharedCheck_1104_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_expr_1094_);
lean_dec(v_val_1075_);
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
v_reuseFailAlloc_1103_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_expr_1094_);
v___x_1099_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1101_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set_tag(v___x_1077_, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1099_);
v___x_1101_ = v___x_1077_;
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
}
}
}
}
default: 
{
lean_object* v_expr_1106_; lean_object* v___x_1107_; 
v_expr_1106_ = lean_ctor_get(v_arg_1062_, 0);
lean_inc_ref(v_expr_1106_);
v___x_1107_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1061_, v_expr_1106_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1116_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1116_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1116_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1112_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1061_, v_arg_1062_, v_a_1108_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1112_);
v___x_1114_ = v___x_1110_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec_ref(v_arg_1062_);
v_a_1117_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1107_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1107_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg___boxed(lean_object* v_pu_1125_, lean_object* v_arg_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
uint8_t v_pu_boxed_1134_; uint8_t v_a_boxed_1135_; lean_object* v_res_1136_; 
v_pu_boxed_1134_ = lean_unbox(v_pu_1125_);
v_a_boxed_1135_ = lean_unbox(v_a_1127_);
v_res_1136_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_boxed_1134_, v_arg_1126_, v_a_boxed_1135_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(uint8_t v_pu_1137_, size_t v_sz_1138_, size_t v_i_1139_, lean_object* v_bs_1140_, uint8_t v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
uint8_t v___x_1148_; 
v___x_1148_ = lean_usize_dec_lt(v_i_1139_, v_sz_1138_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v_bs_1140_);
return v___x_1149_;
}
else
{
lean_object* v_v_1150_; lean_object* v___x_1151_; 
v_v_1150_ = lean_array_uget_borrowed(v_bs_1140_, v_i_1139_);
lean_inc(v_v_1150_);
v___x_1151_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(v_pu_1137_, v_v_1150_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1153_; lean_object* v_bs_x27_1154_; size_t v___x_1155_; size_t v___x_1156_; lean_object* v___x_1157_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_a_1152_);
lean_dec_ref(v___x_1151_);
v___x_1153_ = lean_unsigned_to_nat(0u);
v_bs_x27_1154_ = lean_array_uset(v_bs_1140_, v_i_1139_, v___x_1153_);
v___x_1155_ = ((size_t)1ULL);
v___x_1156_ = lean_usize_add(v_i_1139_, v___x_1155_);
v___x_1157_ = lean_array_uset(v_bs_x27_1154_, v_i_1139_, v_a_1152_);
v_i_1139_ = v___x_1156_;
v_bs_1140_ = v___x_1157_;
goto _start;
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec_ref(v_bs_1140_);
v_a_1159_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1151_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1151_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0___boxed(lean_object* v_pu_1167_, lean_object* v_sz_1168_, lean_object* v_i_1169_, lean_object* v_bs_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
uint8_t v_pu_boxed_1178_; size_t v_sz_boxed_1179_; size_t v_i_boxed_1180_; uint8_t v___y_341__boxed_1181_; lean_object* v_res_1182_; 
v_pu_boxed_1178_ = lean_unbox(v_pu_1167_);
v_sz_boxed_1179_ = lean_unbox_usize(v_sz_1168_);
lean_dec(v_sz_1168_);
v_i_boxed_1180_ = lean_unbox_usize(v_i_1169_);
lean_dec(v_i_1169_);
v___y_341__boxed_1181_ = lean_unbox(v___y_1171_);
v_res_1182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_boxed_1178_, v_sz_boxed_1179_, v_i_boxed_1180_, v_bs_1170_, v___y_341__boxed_1181_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs(uint8_t v_pu_1183_, lean_object* v_args_1184_, uint8_t v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
size_t v_sz_1192_; size_t v___x_1193_; lean_object* v___x_1194_; 
v_sz_1192_ = lean_array_size(v_args_1184_);
v___x_1193_ = ((size_t)0ULL);
v___x_1194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_1183_, v_sz_1192_, v___x_1193_, v_args_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs___boxed(lean_object* v_pu_1195_, lean_object* v_args_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_){
_start:
{
uint8_t v_pu_boxed_1204_; uint8_t v_a_boxed_1205_; lean_object* v_res_1206_; 
v_pu_boxed_1204_ = lean_unbox(v_pu_1195_);
v_a_boxed_1205_ = lean_unbox(v_a_1197_);
v_res_1206_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_boxed_1204_, v_args_1196_, v_a_boxed_1205_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec(v_a_1198_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(uint8_t v_pu_1207_, lean_object* v_e_1208_, uint8_t v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_fvarId_1217_; lean_object* v___y_1218_; lean_object* v_args_1234_; uint8_t v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; 
switch(lean_obj_tag(v_e_1208_))
{
case 2:
{
lean_object* v_struct_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; lean_object* v___x_1262_; 
v_struct_1259_ = lean_ctor_get(v_e_1208_, 2);
v___x_1260_ = lean_st_ref_get(v_a_1210_);
v___x_1261_ = 1;
lean_inc(v_struct_1259_);
v___x_1262_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1260_, v_struct_1259_, v___x_1261_);
lean_dec(v___x_1260_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_fvarId_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1271_; 
v_fvarId_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_fvarId_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1267_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1207_, v_e_1208_, v_fvarId_1263_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v___x_1267_);
v___x_1269_ = v___x_1265_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
else
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
lean_dec_ref(v_e_1208_);
v___x_1272_ = lean_box(1);
v___x_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
return v___x_1273_;
}
}
case 3:
{
lean_object* v_args_1274_; lean_object* v___x_1275_; 
v_args_1274_ = lean_ctor_get(v_e_1208_, 2);
lean_inc_ref(v_args_1274_);
v___x_1275_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1207_, v_args_1274_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1284_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1284_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1284_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1280_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1207_, v_e_1208_, v_a_1276_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1280_);
v___x_1282_ = v___x_1278_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref(v_e_1208_);
v_a_1285_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1275_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1275_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
case 4:
{
lean_object* v_fvarId_1293_; lean_object* v_args_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; lean_object* v___x_1297_; 
v_fvarId_1293_ = lean_ctor_get(v_e_1208_, 0);
v_args_1294_ = lean_ctor_get(v_e_1208_, 1);
v___x_1295_ = lean_st_ref_get(v_a_1210_);
v___x_1296_ = 1;
lean_inc(v_fvarId_1293_);
v___x_1297_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1295_, v_fvarId_1293_, v___x_1296_);
lean_dec(v___x_1295_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_fvarId_1298_; lean_object* v___x_1299_; 
v_fvarId_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_fvarId_1298_);
lean_dec_ref(v___x_1297_);
lean_inc_ref(v_args_1294_);
v___x_1299_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1207_, v_args_1294_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1308_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1302_ = v___x_1299_;
v_isShared_1303_ = v_isSharedCheck_1308_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1299_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1308_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1304_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_1207_, v_e_1208_, v_fvarId_1298_, v_a_1300_);
lean_dec_ref(v_e_1208_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v___x_1304_);
v___x_1306_ = v___x_1302_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec(v_fvarId_1298_);
lean_dec_ref(v_e_1208_);
v_a_1309_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1299_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1299_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
else
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
lean_dec_ref(v_e_1208_);
v___x_1317_ = lean_box(1);
v___x_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
return v___x_1318_;
}
}
case 5:
{
lean_object* v_args_1319_; lean_object* v___x_1320_; 
v_args_1319_ = lean_ctor_get(v_e_1208_, 1);
lean_inc_ref(v_args_1319_);
v___x_1320_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1207_, v_args_1319_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1329_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1327_; 
v___x_1325_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1207_, v_e_1208_, v_a_1321_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1325_);
v___x_1327_ = v___x_1323_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec_ref(v_e_1208_);
v_a_1330_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1320_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1320_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
case 6:
{
lean_object* v_var_1338_; 
v_var_1338_ = lean_ctor_get(v_e_1208_, 1);
lean_inc(v_var_1338_);
v_fvarId_1217_ = v_var_1338_;
v___y_1218_ = v_a_1210_;
goto v___jp_1216_;
}
case 7:
{
lean_object* v_var_1339_; 
v_var_1339_ = lean_ctor_get(v_e_1208_, 1);
lean_inc(v_var_1339_);
v_fvarId_1217_ = v_var_1339_;
v___y_1218_ = v_a_1210_;
goto v___jp_1216_;
}
case 8:
{
lean_object* v_var_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; lean_object* v___x_1343_; 
v_var_1340_ = lean_ctor_get(v_e_1208_, 2);
v___x_1341_ = lean_st_ref_get(v_a_1210_);
v___x_1342_ = 1;
lean_inc(v_var_1340_);
v___x_1343_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1341_, v_var_1340_, v___x_1342_);
lean_dec(v___x_1341_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_fvarId_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1352_; 
v_fvarId_1344_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1346_ = v___x_1343_;
v_isShared_1347_ = v_isSharedCheck_1352_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_fvarId_1344_);
lean_dec(v___x_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1352_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1348_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1207_, v_e_1208_, v_fvarId_1344_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v___x_1348_);
v___x_1350_ = v___x_1346_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_dec_ref(v_e_1208_);
v___x_1353_ = lean_box(1);
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
return v___x_1354_;
}
}
case 9:
{
lean_object* v_args_1355_; 
v_args_1355_ = lean_ctor_get(v_e_1208_, 1);
lean_inc_ref(v_args_1355_);
v_args_1234_ = v_args_1355_;
v___y_1235_ = v_a_1209_;
v___y_1236_ = v_a_1210_;
v___y_1237_ = v_a_1211_;
v___y_1238_ = v_a_1212_;
v___y_1239_ = v_a_1213_;
v___y_1240_ = v_a_1214_;
goto v___jp_1233_;
}
case 10:
{
lean_object* v_args_1356_; 
v_args_1356_ = lean_ctor_get(v_e_1208_, 1);
lean_inc_ref(v_args_1356_);
v_args_1234_ = v_args_1356_;
v___y_1235_ = v_a_1209_;
v___y_1236_ = v_a_1210_;
v___y_1237_ = v_a_1211_;
v___y_1238_ = v_a_1212_;
v___y_1239_ = v_a_1213_;
v___y_1240_ = v_a_1214_;
goto v___jp_1233_;
}
case 11:
{
lean_object* v_n_1357_; lean_object* v_var_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; lean_object* v___x_1361_; 
v_n_1357_ = lean_ctor_get(v_e_1208_, 0);
lean_inc(v_n_1357_);
v_var_1358_ = lean_ctor_get(v_e_1208_, 1);
v___x_1359_ = lean_st_ref_get(v_a_1210_);
v___x_1360_ = 1;
lean_inc(v_var_1358_);
v___x_1361_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1359_, v_var_1358_, v___x_1360_);
lean_dec(v___x_1359_);
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
v___x_1366_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_1207_, v_e_1208_, v_n_1357_, v_fvarId_1362_);
lean_dec_ref(v_e_1208_);
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
lean_dec_ref(v_e_1208_);
lean_dec(v_n_1357_);
v___x_1371_ = lean_box(1);
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
return v___x_1372_;
}
}
case 12:
{
lean_object* v_var_1373_; lean_object* v_i_1374_; uint8_t v_updateHeader_1375_; lean_object* v_args_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; lean_object* v___x_1379_; 
v_var_1373_ = lean_ctor_get(v_e_1208_, 0);
v_i_1374_ = lean_ctor_get(v_e_1208_, 1);
lean_inc_ref(v_i_1374_);
v_updateHeader_1375_ = lean_ctor_get_uint8(v_e_1208_, sizeof(void*)*3);
v_args_1376_ = lean_ctor_get(v_e_1208_, 2);
v___x_1377_ = lean_st_ref_get(v_a_1210_);
v___x_1378_ = 1;
lean_inc(v_var_1373_);
v___x_1379_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1377_, v_var_1373_, v___x_1378_);
lean_dec(v___x_1377_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_fvarId_1380_; lean_object* v___x_1381_; 
v_fvarId_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_fvarId_1380_);
lean_dec_ref(v___x_1379_);
lean_inc_ref(v_args_1376_);
v___x_1381_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1207_, v_args_1376_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1390_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1390_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1390_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1386_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_1207_, v_e_1208_, v_fvarId_1380_, v_i_1374_, v_updateHeader_1375_, v_a_1382_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v___x_1386_);
v___x_1388_ = v___x_1384_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_dec(v_fvarId_1380_);
lean_dec_ref(v_i_1374_);
lean_dec_ref(v_e_1208_);
v_a_1391_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1381_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1381_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec_ref(v_i_1374_);
lean_dec_ref(v_e_1208_);
v___x_1399_ = lean_box(1);
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
}
}
case 13:
{
lean_object* v_ty_1401_; lean_object* v_fvarId_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; lean_object* v___x_1405_; 
v_ty_1401_ = lean_ctor_get(v_e_1208_, 0);
lean_inc_ref(v_ty_1401_);
v_fvarId_1402_ = lean_ctor_get(v_e_1208_, 1);
v___x_1403_ = lean_st_ref_get(v_a_1210_);
v___x_1404_ = 1;
lean_inc(v_fvarId_1402_);
v___x_1405_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1403_, v_fvarId_1402_, v___x_1404_);
lean_dec(v___x_1403_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_fvarId_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1414_; 
v_fvarId_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_fvarId_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1410_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_1207_, v_e_1208_, v_ty_1401_, v_fvarId_1406_);
lean_dec_ref(v_e_1208_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1410_);
v___x_1412_ = v___x_1408_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_dec_ref(v_e_1208_);
lean_dec_ref(v_ty_1401_);
v___x_1415_ = lean_box(1);
v___x_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
return v___x_1416_;
}
}
case 14:
{
lean_object* v_fvarId_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; 
v_fvarId_1417_ = lean_ctor_get(v_e_1208_, 0);
v___x_1418_ = lean_st_ref_get(v_a_1210_);
v___x_1419_ = 1;
lean_inc(v_fvarId_1417_);
v___x_1420_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1418_, v_fvarId_1417_, v___x_1419_);
lean_dec(v___x_1418_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_fvarId_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1429_; 
v_fvarId_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_fvarId_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1425_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_1207_, v_e_1208_, v_fvarId_1421_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1425_);
v___x_1427_ = v___x_1423_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
else
{
lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1437_; 
v_isSharedCheck_1437_ = !lean_is_exclusive(v_e_1208_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; 
v_unused_1438_ = lean_ctor_get(v_e_1208_, 0);
lean_dec(v_unused_1438_);
v___x_1431_ = v_e_1208_;
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
else
{
lean_dec(v_e_1208_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1433_ = lean_box(1);
if (v_isShared_1432_ == 0)
{
lean_ctor_set_tag(v___x_1431_, 0);
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
}
case 15:
{
lean_object* v_fvarId_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; lean_object* v___x_1442_; 
v_fvarId_1439_ = lean_ctor_get(v_e_1208_, 0);
v___x_1440_ = lean_st_ref_get(v_a_1210_);
v___x_1441_ = 1;
lean_inc(v_fvarId_1439_);
v___x_1442_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1440_, v_fvarId_1439_, v___x_1441_);
lean_dec(v___x_1440_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_fvarId_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1451_; 
v_fvarId_1443_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1445_ = v___x_1442_;
v_isShared_1446_ = v_isSharedCheck_1451_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_fvarId_1443_);
lean_dec(v___x_1442_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1451_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1447_; lean_object* v___x_1449_; 
v___x_1447_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_1207_, v_e_1208_, v_fvarId_1443_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v___x_1447_);
v___x_1449_ = v___x_1445_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
else
{
lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1459_; 
v_isSharedCheck_1459_ = !lean_is_exclusive(v_e_1208_);
if (v_isSharedCheck_1459_ == 0)
{
lean_object* v_unused_1460_; 
v_unused_1460_ = lean_ctor_get(v_e_1208_, 0);
lean_dec(v_unused_1460_);
v___x_1453_ = v_e_1208_;
v_isShared_1454_ = v_isSharedCheck_1459_;
goto v_resetjp_1452_;
}
else
{
lean_dec(v_e_1208_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1459_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1455_ = lean_box(1);
if (v_isShared_1454_ == 0)
{
lean_ctor_set_tag(v___x_1453_, 0);
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
}
default: 
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1461_, 0, v_e_1208_);
return v___x_1461_;
}
}
v___jp_1216_:
{
lean_object* v___x_1219_; uint8_t v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = lean_st_ref_get(v___y_1218_);
v___x_1220_ = 1;
v___x_1221_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1219_, v_fvarId_1217_, v___x_1220_);
lean_dec(v___x_1219_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_fvarId_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1230_; 
v_fvarId_1222_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_fvarId_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1226_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1207_, v_e_1208_, v_fvarId_1222_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1226_);
v___x_1228_ = v___x_1224_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_dec(v_e_1208_);
v___x_1231_ = lean_box(1);
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
return v___x_1232_;
}
}
v___jp_1233_:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1207_, v_args_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1250_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1246_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1207_, v_e_1208_, v_a_1242_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1246_);
v___x_1248_ = v___x_1244_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec(v_e_1208_);
v_a_1251_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1241_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1241_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue___boxed(lean_object* v_pu_1462_, lean_object* v_e_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
uint8_t v_pu_boxed_1471_; uint8_t v_a_boxed_1472_; lean_object* v_res_1473_; 
v_pu_boxed_1471_ = lean_unbox(v_pu_1462_);
v_a_boxed_1472_ = lean_unbox(v_a_1464_);
v_res_1473_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_boxed_1471_, v_e_1463_, v_a_boxed_1472_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(uint8_t v_pu_1474_, lean_object* v_decl_1475_, uint8_t v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v_fvarId_1483_; lean_object* v_binderName_1484_; lean_object* v_type_1485_; lean_object* v_value_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1544_; 
v_fvarId_1483_ = lean_ctor_get(v_decl_1475_, 0);
v_binderName_1484_ = lean_ctor_get(v_decl_1475_, 1);
v_type_1485_ = lean_ctor_get(v_decl_1475_, 2);
v_value_1486_ = lean_ctor_get(v_decl_1475_, 3);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_decl_1475_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1488_ = v_decl_1475_;
v_isShared_1489_ = v_isSharedCheck_1544_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_value_1486_);
lean_inc(v_type_1485_);
lean_inc(v_binderName_1484_);
lean_inc(v_fvarId_1483_);
lean_dec(v_decl_1475_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1544_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v_a_1491_; lean_object* v___x_1492_; 
v___x_1490_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_1484_, v_a_1476_, v_a_1479_);
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
lean_dec_ref(v___x_1490_);
v___x_1492_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1474_, v_type_1485_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; lean_object* v___x_1494_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_a_1493_);
lean_dec_ref(v___x_1492_);
v___x_1494_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_1474_, v_value_1486_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1496_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref(v___x_1494_);
v___x_1496_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_1483_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1519_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1499_ = v___x_1496_;
v_isShared_1500_ = v_isSharedCheck_1519_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1519_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v_lctx_1502_; lean_object* v_nextIdx_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1518_; 
v___x_1501_ = lean_st_ref_take(v_a_1479_);
v_lctx_1502_ = lean_ctor_get(v___x_1501_, 0);
v_nextIdx_1503_ = lean_ctor_get(v___x_1501_, 1);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1505_ = v___x_1501_;
v_isShared_1506_ = v_isSharedCheck_1518_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_nextIdx_1503_);
lean_inc(v_lctx_1502_);
lean_dec(v___x_1501_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1518_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 3, v_a_1495_);
lean_ctor_set(v___x_1488_, 2, v_a_1493_);
lean_ctor_set(v___x_1488_, 1, v_a_1491_);
lean_ctor_set(v___x_1488_, 0, v_a_1497_);
v___x_1508_ = v___x_1488_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1497_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_a_1491_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_a_1493_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v_a_1495_);
v___x_1508_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1509_; lean_object* v___x_1511_; 
lean_inc_ref(v___x_1508_);
v___x_1509_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_1474_, v_lctx_1502_, v___x_1508_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1509_);
v___x_1511_ = v___x_1505_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_nextIdx_1503_);
v___x_1511_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1512_ = lean_st_ref_set(v_a_1479_, v___x_1511_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1508_);
v___x_1514_ = v___x_1499_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1508_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec(v_a_1495_);
lean_dec(v_a_1493_);
lean_dec(v_a_1491_);
lean_del_object(v___x_1488_);
v_a_1520_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1496_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1496_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
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
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec(v_a_1493_);
lean_dec(v_a_1491_);
lean_del_object(v___x_1488_);
lean_dec(v_fvarId_1483_);
v_a_1528_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1494_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1494_);
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
lean_dec(v_a_1491_);
lean_del_object(v___x_1488_);
lean_dec(v_value_1486_);
lean_dec(v_fvarId_1483_);
v_a_1536_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1492_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1492_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(lean_object* v_pu_1545_, lean_object* v_decl_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_){
_start:
{
uint8_t v_pu_boxed_1554_; uint8_t v_a_boxed_1555_; lean_object* v_res_1556_; 
v_pu_boxed_1554_ = lean_unbox(v_pu_1545_);
v_a_boxed_1555_ = lean_unbox(v_a_1547_);
v_res_1556_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_boxed_1554_, v_decl_1546_, v_a_boxed_1555_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
lean_dec(v_a_1552_);
lean_dec_ref(v_a_1551_);
lean_dec(v_a_1550_);
lean_dec_ref(v_a_1549_);
lean_dec(v_a_1548_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(uint8_t v_pu_1557_, size_t v_sz_1558_, size_t v_i_1559_, lean_object* v_bs_1560_, uint8_t v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
uint8_t v___x_1568_; 
v___x_1568_ = lean_usize_dec_lt(v_i_1559_, v_sz_1558_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1569_, 0, v_bs_1560_);
return v___x_1569_;
}
else
{
lean_object* v_v_1570_; lean_object* v___x_1571_; 
v_v_1570_ = lean_array_uget_borrowed(v_bs_1560_, v_i_1559_);
lean_inc(v_v_1570_);
v___x_1571_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v_pu_1557_, v_v_1570_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1573_; lean_object* v_bs_x27_1574_; size_t v___x_1575_; size_t v___x_1576_; lean_object* v___x_1577_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref(v___x_1571_);
v___x_1573_ = lean_unsigned_to_nat(0u);
v_bs_x27_1574_ = lean_array_uset(v_bs_1560_, v_i_1559_, v___x_1573_);
v___x_1575_ = ((size_t)1ULL);
v___x_1576_ = lean_usize_add(v_i_1559_, v___x_1575_);
v___x_1577_ = lean_array_uset(v_bs_x27_1574_, v_i_1559_, v_a_1572_);
v_i_1559_ = v___x_1576_;
v_bs_1560_ = v___x_1577_;
goto _start;
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec_ref(v_bs_1560_);
v_a_1579_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1571_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1571_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0___boxed(lean_object* v_pu_1587_, lean_object* v_sz_1588_, lean_object* v_i_1589_, lean_object* v_bs_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
uint8_t v_pu_boxed_1598_; size_t v_sz_boxed_1599_; size_t v_i_boxed_1600_; uint8_t v___y_26865__boxed_1601_; lean_object* v_res_1602_; 
v_pu_boxed_1598_ = lean_unbox(v_pu_1587_);
v_sz_boxed_1599_ = lean_unbox_usize(v_sz_1588_);
lean_dec(v_sz_1588_);
v_i_boxed_1600_ = lean_unbox_usize(v_i_1589_);
lean_dec(v_i_1589_);
v___y_26865__boxed_1601_ = lean_unbox(v___y_1591_);
v_res_1602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_boxed_1598_, v_sz_boxed_1599_, v_i_boxed_1600_, v_bs_1590_, v___y_26865__boxed_1601_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(uint8_t v_pu_1603_, size_t v_sz_1604_, size_t v_i_1605_, lean_object* v_bs_1606_, uint8_t v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
uint8_t v___x_1614_; 
v___x_1614_ = lean_usize_dec_lt(v_i_1605_, v_sz_1604_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; 
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v_bs_1606_);
return v___x_1615_;
}
else
{
lean_object* v_v_1616_; lean_object* v___x_1617_; lean_object* v_bs_x27_1618_; lean_object* v_a_1620_; 
v_v_1616_ = lean_array_uget(v_bs_1606_, v_i_1605_);
v___x_1617_ = lean_unsigned_to_nat(0u);
v_bs_x27_1618_ = lean_array_uset(v_bs_1606_, v_i_1605_, v___x_1617_);
switch(lean_obj_tag(v_v_1616_))
{
case 0:
{
lean_object* v_ctorName_1625_; lean_object* v_params_1626_; lean_object* v_code_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1648_; 
v_ctorName_1625_ = lean_ctor_get(v_v_1616_, 0);
v_params_1626_ = lean_ctor_get(v_v_1616_, 1);
v_code_1627_ = lean_ctor_get(v_v_1616_, 2);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_v_1616_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1629_ = v_v_1616_;
v_isShared_1630_ = v_isSharedCheck_1648_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_code_1627_);
lean_inc(v_params_1626_);
lean_inc(v_ctorName_1625_);
lean_dec(v_v_1616_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1648_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
size_t v_sz_1631_; size_t v___x_1632_; lean_object* v___x_1633_; 
v_sz_1631_ = lean_array_size(v_params_1626_);
v___x_1632_ = ((size_t)0ULL);
v___x_1633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_1603_, v_sz_1631_, v___x_1632_, v_params_1626_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1635_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref(v___x_1633_);
v___x_1635_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1603_, v_code_1627_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1638_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref(v___x_1635_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 2, v_a_1636_);
lean_ctor_set(v___x_1629_, 1, v_a_1634_);
v___x_1638_ = v___x_1629_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_ctorName_1625_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_a_1634_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_a_1636_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
v_a_1620_ = v___x_1638_;
goto v___jp_1619_;
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec(v_a_1634_);
lean_del_object(v___x_1629_);
lean_dec(v_ctorName_1625_);
lean_dec_ref(v_bs_x27_1618_);
v_a_1640_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1635_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1635_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
else
{
lean_del_object(v___x_1629_);
lean_dec_ref(v_code_1627_);
lean_dec(v_ctorName_1625_);
lean_dec_ref(v_bs_x27_1618_);
return v___x_1633_;
}
}
}
case 1:
{
lean_object* v_info_1649_; lean_object* v_code_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1667_; 
v_info_1649_ = lean_ctor_get(v_v_1616_, 0);
v_code_1650_ = lean_ctor_get(v_v_1616_, 1);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_v_1616_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1652_ = v_v_1616_;
v_isShared_1653_ = v_isSharedCheck_1667_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_code_1650_);
lean_inc(v_info_1649_);
lean_dec(v_v_1616_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1667_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1603_, v_code_1650_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1657_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1655_);
lean_dec_ref(v___x_1654_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 1, v_a_1655_);
v___x_1657_ = v___x_1652_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_info_1649_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_a_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
v_a_1620_ = v___x_1657_;
goto v___jp_1619_;
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_del_object(v___x_1652_);
lean_dec_ref(v_info_1649_);
lean_dec_ref(v_bs_x27_1618_);
v_a_1659_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1654_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1654_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
default: 
{
lean_object* v_code_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1685_; 
v_code_1668_ = lean_ctor_get(v_v_1616_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_v_1616_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1670_ = v_v_1616_;
v_isShared_1671_ = v_isSharedCheck_1685_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_code_1668_);
lean_dec(v_v_1616_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1685_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1603_, v_code_1668_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1675_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_a_1673_);
lean_dec_ref(v___x_1672_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v_a_1673_);
v___x_1675_ = v___x_1670_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
v_a_1620_ = v___x_1675_;
goto v___jp_1619_;
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
lean_del_object(v___x_1670_);
lean_dec_ref(v_bs_x27_1618_);
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
}
v___jp_1619_:
{
size_t v___x_1621_; size_t v___x_1622_; lean_object* v___x_1623_; 
v___x_1621_ = ((size_t)1ULL);
v___x_1622_ = lean_usize_add(v_i_1605_, v___x_1621_);
v___x_1623_ = lean_array_uset(v_bs_x27_1618_, v_i_1605_, v_a_1620_);
v_i_1605_ = v___x_1622_;
v_bs_1606_ = v___x_1623_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t v_pu_1686_, lean_object* v_code_1687_, uint8_t v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
switch(lean_obj_tag(v_code_1687_))
{
case 0:
{
lean_object* v_decl_1695_; lean_object* v_k_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1722_; 
v_decl_1695_ = lean_ctor_get(v_code_1687_, 0);
v_k_1696_ = lean_ctor_get(v_code_1687_, 1);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_code_1687_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1698_ = v_code_1687_;
v_isShared_1699_ = v_isSharedCheck_1722_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_k_1696_);
lean_inc(v_decl_1695_);
lean_dec(v_code_1687_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1722_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_1686_, v_decl_1695_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1702_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1701_);
lean_dec_ref(v___x_1700_);
v___x_1702_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1686_, v_k_1696_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1713_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1705_ = v___x_1702_;
v_isShared_1706_ = v_isSharedCheck_1713_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1702_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1713_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 1, v_a_1703_);
lean_ctor_set(v___x_1698_, 0, v_a_1701_);
v___x_1708_ = v___x_1698_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1701_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1710_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1708_);
v___x_1710_ = v___x_1705_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1708_);
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
else
{
lean_dec(v_a_1701_);
lean_del_object(v___x_1698_);
return v___x_1702_;
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_del_object(v___x_1698_);
lean_dec_ref(v_k_1696_);
v_a_1714_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1700_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1700_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_1723_; lean_object* v_k_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1750_; 
v_decl_1723_ = lean_ctor_get(v_code_1687_, 0);
v_k_1724_ = lean_ctor_get(v_code_1687_, 1);
v_isSharedCheck_1750_ = !lean_is_exclusive(v_code_1687_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1726_ = v_code_1687_;
v_isShared_1727_ = v_isSharedCheck_1750_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_k_1724_);
lean_inc(v_decl_1723_);
lean_dec(v_code_1687_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1750_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1686_, v_decl_1723_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1730_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref(v___x_1728_);
v___x_1730_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1686_, v_k_1724_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1741_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1733_ = v___x_1730_;
v_isShared_1734_ = v_isSharedCheck_1741_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1730_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1741_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 1, v_a_1731_);
lean_ctor_set(v___x_1726_, 0, v_a_1729_);
v___x_1736_ = v___x_1726_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1729_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1738_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 0, v___x_1736_);
v___x_1738_ = v___x_1733_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
else
{
lean_dec(v_a_1729_);
lean_del_object(v___x_1726_);
return v___x_1730_;
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_del_object(v___x_1726_);
lean_dec_ref(v_k_1724_);
v_a_1742_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1728_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1728_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
case 2:
{
lean_object* v_decl_1751_; lean_object* v_k_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1778_; 
v_decl_1751_ = lean_ctor_get(v_code_1687_, 0);
v_k_1752_ = lean_ctor_get(v_code_1687_, 1);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_code_1687_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1754_ = v_code_1687_;
v_isShared_1755_ = v_isSharedCheck_1778_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_k_1752_);
lean_inc(v_decl_1751_);
lean_dec(v_code_1687_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1778_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_1686_, v_decl_1751_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1758_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref(v___x_1756_);
v___x_1758_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1686_, v_k_1752_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1769_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1769_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1769_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 1, v_a_1759_);
lean_ctor_set(v___x_1754_, 0, v_a_1757_);
v___x_1764_ = v___x_1754_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1757_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1766_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1764_);
v___x_1766_ = v___x_1761_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
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
else
{
lean_dec(v_a_1757_);
lean_del_object(v___x_1754_);
return v___x_1758_;
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_del_object(v___x_1754_);
lean_dec_ref(v_k_1752_);
v_a_1770_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1756_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1756_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_1779_; lean_object* v_args_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1809_; 
v_fvarId_1779_ = lean_ctor_get(v_code_1687_, 0);
v_args_1780_ = lean_ctor_get(v_code_1687_, 1);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_code_1687_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1782_ = v_code_1687_;
v_isShared_1783_ = v_isSharedCheck_1809_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_args_1780_);
lean_inc(v_fvarId_1779_);
lean_dec(v_code_1687_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1809_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1784_; uint8_t v___x_1785_; lean_object* v___x_1786_; 
v___x_1784_ = lean_st_ref_get(v_a_1689_);
v___x_1785_ = 1;
v___x_1786_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1784_, v_fvarId_1779_, v___x_1785_);
lean_dec(v___x_1784_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_fvarId_1787_; lean_object* v___x_1788_; 
v_fvarId_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_fvarId_1787_);
lean_dec_ref(v___x_1786_);
v___x_1788_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(v_pu_1686_, v_args_1780_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1799_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1799_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1799_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 1, v_a_1789_);
lean_ctor_set(v___x_1782_, 0, v_fvarId_1787_);
v___x_1794_ = v___x_1782_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_fvarId_1787_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1796_; 
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v___x_1794_);
v___x_1796_ = v___x_1791_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1794_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec(v_fvarId_1787_);
lean_del_object(v___x_1782_);
v_a_1800_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1788_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1788_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
else
{
lean_object* v___x_1808_; 
lean_del_object(v___x_1782_);
lean_dec_ref(v_args_1780_);
v___x_1808_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1686_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
return v___x_1808_;
}
}
}
case 4:
{
lean_object* v_cases_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1862_; 
v_cases_1810_ = lean_ctor_get(v_code_1687_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_code_1687_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1812_ = v_code_1687_;
v_isShared_1813_ = v_isSharedCheck_1862_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_cases_1810_);
lean_dec(v_code_1687_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1862_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v_typeName_1814_; lean_object* v_resultType_1815_; lean_object* v_discr_1816_; lean_object* v_alts_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1861_; 
v_typeName_1814_ = lean_ctor_get(v_cases_1810_, 0);
v_resultType_1815_ = lean_ctor_get(v_cases_1810_, 1);
v_discr_1816_ = lean_ctor_get(v_cases_1810_, 2);
v_alts_1817_ = lean_ctor_get(v_cases_1810_, 3);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_cases_1810_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1819_ = v_cases_1810_;
v_isShared_1820_ = v_isSharedCheck_1861_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_alts_1817_);
lean_inc(v_discr_1816_);
lean_inc(v_resultType_1815_);
lean_inc(v_typeName_1814_);
lean_dec(v_cases_1810_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1861_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; uint8_t v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = lean_st_ref_get(v_a_1689_);
v___x_1822_ = 1;
v___x_1823_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1821_, v_discr_1816_, v___x_1822_);
lean_dec(v___x_1821_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_fvarId_1824_; lean_object* v___x_1825_; 
v_fvarId_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_fvarId_1824_);
lean_dec_ref(v___x_1823_);
v___x_1825_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1686_, v_resultType_1815_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; size_t v_sz_1827_; size_t v___x_1828_; lean_object* v___x_1829_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1826_);
lean_dec_ref(v___x_1825_);
v_sz_1827_ = lean_array_size(v_alts_1817_);
v___x_1828_ = ((size_t)0ULL);
v___x_1829_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_1686_, v_sz_1827_, v___x_1828_, v_alts_1817_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1843_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1843_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1843_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 3, v_a_1830_);
lean_ctor_set(v___x_1819_, 2, v_fvarId_1824_);
lean_ctor_set(v___x_1819_, 1, v_a_1826_);
v___x_1835_ = v___x_1819_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_typeName_1814_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_a_1826_);
lean_ctor_set(v_reuseFailAlloc_1842_, 2, v_fvarId_1824_);
lean_ctor_set(v_reuseFailAlloc_1842_, 3, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1837_; 
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1835_);
v___x_1837_ = v___x_1812_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v___x_1839_; 
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1837_);
v___x_1839_ = v___x_1832_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec(v_a_1826_);
lean_dec(v_fvarId_1824_);
lean_del_object(v___x_1819_);
lean_dec(v_typeName_1814_);
lean_del_object(v___x_1812_);
v_a_1844_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1829_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1829_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec(v_fvarId_1824_);
lean_del_object(v___x_1819_);
lean_dec_ref(v_alts_1817_);
lean_dec(v_typeName_1814_);
lean_del_object(v___x_1812_);
v_a_1852_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1825_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1825_);
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
lean_object* v___x_1860_; 
lean_del_object(v___x_1819_);
lean_dec_ref(v_alts_1817_);
lean_dec_ref(v_resultType_1815_);
lean_dec(v_typeName_1814_);
lean_del_object(v___x_1812_);
v___x_1860_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1686_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
return v___x_1860_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1882_; 
v_fvarId_1863_ = lean_ctor_get(v_code_1687_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_code_1687_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1865_ = v_code_1687_;
v_isShared_1866_ = v_isSharedCheck_1882_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_fvarId_1863_);
lean_dec(v_code_1687_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1882_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; uint8_t v___x_1868_; lean_object* v___x_1869_; 
v___x_1867_ = lean_st_ref_get(v_a_1689_);
v___x_1868_ = 1;
v___x_1869_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1867_, v_fvarId_1863_, v___x_1868_);
lean_dec(v___x_1867_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_fvarId_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1880_; 
v_fvarId_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1880_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_fvarId_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1880_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v_fvarId_1870_);
v___x_1875_ = v___x_1865_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_fvarId_1870_);
v___x_1875_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1877_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1875_);
v___x_1877_ = v___x_1872_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
else
{
lean_object* v___x_1881_; 
lean_del_object(v___x_1865_);
v___x_1881_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1686_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
return v___x_1881_;
}
}
}
case 6:
{
lean_object* v_type_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1907_; 
v_type_1883_ = lean_ctor_get(v_code_1687_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v_code_1687_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1885_ = v_code_1687_;
v_isShared_1886_ = v_isSharedCheck_1907_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_type_1883_);
lean_dec(v_code_1687_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1907_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; 
v___x_1887_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1686_, v_type_1883_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1898_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1890_ = v___x_1887_;
v_isShared_1891_ = v_isSharedCheck_1898_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1887_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1898_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v_a_1888_);
v___x_1893_ = v___x_1885_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1888_);
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
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_del_object(v___x_1885_);
v_a_1899_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1887_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1887_);
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
}
case 7:
{
lean_object* v_fvarId_1908_; lean_object* v_i_1909_; lean_object* v_y_1910_; lean_object* v_k_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1934_; 
v_fvarId_1908_ = lean_ctor_get(v_code_1687_, 0);
v_i_1909_ = lean_ctor_get(v_code_1687_, 1);
v_y_1910_ = lean_ctor_get(v_code_1687_, 2);
v_k_1911_ = lean_ctor_get(v_code_1687_, 3);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_code_1687_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1913_ = v_code_1687_;
v_isShared_1914_ = v_isSharedCheck_1934_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_k_1911_);
lean_inc(v_y_1910_);
lean_inc(v_i_1909_);
lean_inc(v_fvarId_1908_);
lean_dec(v_code_1687_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1934_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1915_; uint8_t v___x_1916_; lean_object* v___x_1917_; 
v___x_1915_ = lean_st_ref_get(v_a_1689_);
v___x_1916_ = 1;
v___x_1917_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1915_, v_fvarId_1908_, v___x_1916_);
lean_dec(v___x_1915_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_fvarId_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v_fvarId_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_fvarId_1918_);
lean_dec_ref(v___x_1917_);
v___x_1919_ = lean_st_ref_get(v_a_1689_);
v___x_1920_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1686_, v___x_1919_, v_y_1910_, v___x_1916_);
lean_dec(v___x_1919_);
v___x_1921_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1686_, v_k_1911_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1932_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1924_ = v___x_1921_;
v_isShared_1925_ = v_isSharedCheck_1932_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1921_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1932_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 3, v_a_1922_);
lean_ctor_set(v___x_1913_, 2, v___x_1920_);
lean_ctor_set(v___x_1913_, 0, v_fvarId_1918_);
v___x_1927_ = v___x_1913_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_fvarId_1918_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_i_1909_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1929_; 
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v___x_1927_);
v___x_1929_ = v___x_1924_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
else
{
lean_dec(v___x_1920_);
lean_dec(v_fvarId_1918_);
lean_del_object(v___x_1913_);
lean_dec(v_i_1909_);
return v___x_1921_;
}
}
else
{
lean_object* v___x_1933_; 
lean_del_object(v___x_1913_);
lean_dec_ref(v_k_1911_);
lean_dec(v_y_1910_);
lean_dec(v_i_1909_);
v___x_1933_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1686_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
return v___x_1933_;
}
}
}
case 8:
{
lean_object* v_fvarId_1935_; lean_object* v_i_1936_; lean_object* v_y_1937_; lean_object* v_k_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1963_; 
v_fvarId_1935_ = lean_ctor_get(v_code_1687_, 0);
v_i_1936_ = lean_ctor_get(v_code_1687_, 1);
v_y_1937_ = lean_ctor_get(v_code_1687_, 2);
v_k_1938_ = lean_ctor_get(v_code_1687_, 3);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_code_1687_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1940_ = v_code_1687_;
v_isShared_1941_ = v_isSharedCheck_1963_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_k_1938_);
lean_inc(v_y_1937_);
lean_inc(v_i_1936_);
lean_inc(v_fvarId_1935_);
lean_dec(v_code_1687_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1963_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; uint8_t v___x_1943_; lean_object* v___x_1944_; 
v___x_1942_ = lean_st_ref_get(v_a_1689_);
v___x_1943_ = 1;
v___x_1944_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1942_, v_fvarId_1935_, v___x_1943_);
lean_dec(v___x_1942_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_fvarId_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v_fvarId_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_fvarId_1945_);
lean_dec_ref(v___x_1944_);
v___x_1946_ = lean_st_ref_get(v_a_1689_);
v___x_1947_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1946_, v_y_1937_, v___x_1943_);
lean_dec(v___x_1946_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_fvarId_1948_; lean_object* v___x_1949_; 
v_fvarId_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_fvarId_1948_);
lean_dec_ref(v___x_1947_);
v___x_1949_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1686_, v_k_1938_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1960_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1952_ = v___x_1949_;
v_isShared_1953_ = v_isSharedCheck_1960_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1949_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1960_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 3, v_a_1950_);
lean_ctor_set(v___x_1940_, 2, v_fvarId_1948_);
lean_ctor_set(v___x_1940_, 0, v_fvarId_1945_);
v___x_1955_ = v___x_1940_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_fvarId_1945_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_i_1936_);
lean_ctor_set(v_reuseFailAlloc_1959_, 2, v_fvarId_1948_);
lean_ctor_set(v_reuseFailAlloc_1959_, 3, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1957_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v___x_1955_);
v___x_1957_ = v___x_1952_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
else
{
lean_dec(v_fvarId_1948_);
lean_dec(v_fvarId_1945_);
lean_del_object(v___x_1940_);
lean_dec(v_i_1936_);
return v___x_1949_;
}
}
else
{
lean_object* v___x_1961_; 
lean_dec(v_fvarId_1945_);
lean_del_object(v___x_1940_);
lean_dec_ref(v_k_1938_);
lean_dec(v_i_1936_);
v___x_1961_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1686_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
return v___x_1961_;
}
}
else
{
lean_object* v___x_1962_; 
lean_del_object(v___x_1940_);
lean_dec_ref(v_k_1938_);
lean_dec(v_y_1937_);
lean_dec(v_i_1936_);
v___x_1962_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1686_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
return v___x_1962_;
}
}
}
case 9:
{
lean_object* v_fvarId_1964_; lean_object* v_i_1965_; lean_object* v_offset_1966_; lean_object* v_y_1967_; lean_object* v_ty_1968_; lean_object* v_k_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2004_; 
v_fvarId_1964_ = lean_ctor_get(v_code_1687_, 0);
v_i_1965_ = lean_ctor_get(v_code_1687_, 1);
v_offset_1966_ = lean_ctor_get(v_code_1687_, 2);
v_y_1967_ = lean_ctor_get(v_code_1687_, 3);
v_ty_1968_ = lean_ctor_get(v_code_1687_, 4);
v_k_1969_ = lean_ctor_get(v_code_1687_, 5);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_code_1687_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1971_ = v_code_1687_;
v_isShared_1972_ = v_isSharedCheck_2004_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_k_1969_);
lean_inc(v_ty_1968_);
lean_inc(v_y_1967_);
lean_inc(v_offset_1966_);
lean_inc(v_i_1965_);
lean_inc(v_fvarId_1964_);
lean_dec(v_code_1687_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2004_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; uint8_t v___x_1974_; lean_object* v___x_1975_; 
v___x_1973_ = lean_st_ref_get(v_a_1689_);
v___x_1974_ = 1;
v___x_1975_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1973_, v_fvarId_1964_, v___x_1974_);
lean_dec(v___x_1973_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_fvarId_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v_fvarId_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_fvarId_1976_);
lean_dec_ref(v___x_1975_);
v___x_1977_ = lean_st_ref_get(v_a_1689_);
v___x_1978_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_1977_, v_y_1967_, v___x_1974_);
lean_dec(v___x_1977_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_fvarId_1979_; lean_object* v___x_1980_; 
v_fvarId_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_fvarId_1979_);
lean_dec_ref(v___x_1978_);
v___x_1980_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_1686_, v_ty_1968_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1982_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref(v___x_1980_);
v___x_1982_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1686_, v_k_1969_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1993_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1985_ = v___x_1982_;
v_isShared_1986_ = v_isSharedCheck_1993_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1993_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 5, v_a_1983_);
lean_ctor_set(v___x_1971_, 4, v_a_1981_);
lean_ctor_set(v___x_1971_, 3, v_fvarId_1979_);
lean_ctor_set(v___x_1971_, 0, v_fvarId_1976_);
v___x_1988_ = v___x_1971_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_fvarId_1976_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_i_1965_);
lean_ctor_set(v_reuseFailAlloc_1992_, 2, v_offset_1966_);
lean_ctor_set(v_reuseFailAlloc_1992_, 3, v_fvarId_1979_);
lean_ctor_set(v_reuseFailAlloc_1992_, 4, v_a_1981_);
lean_ctor_set(v_reuseFailAlloc_1992_, 5, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1990_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_1988_);
v___x_1990_ = v___x_1985_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
lean_dec(v_a_1981_);
lean_dec(v_fvarId_1979_);
lean_dec(v_fvarId_1976_);
lean_del_object(v___x_1971_);
lean_dec(v_offset_1966_);
lean_dec(v_i_1965_);
return v___x_1982_;
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec(v_fvarId_1979_);
lean_dec(v_fvarId_1976_);
lean_del_object(v___x_1971_);
lean_dec_ref(v_k_1969_);
lean_dec(v_offset_1966_);
lean_dec(v_i_1965_);
v_a_1994_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1980_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1980_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
else
{
lean_object* v___x_2002_; 
lean_dec(v_fvarId_1976_);
lean_del_object(v___x_1971_);
lean_dec_ref(v_k_1969_);
lean_dec_ref(v_ty_1968_);
lean_dec(v_offset_1966_);
lean_dec(v_i_1965_);
v___x_2002_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1686_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
return v___x_2002_;
}
}
else
{
lean_object* v___x_2003_; 
lean_del_object(v___x_1971_);
lean_dec_ref(v_k_1969_);
lean_dec_ref(v_ty_1968_);
lean_dec(v_y_1967_);
lean_dec(v_offset_1966_);
lean_dec(v_i_1965_);
v___x_2003_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1686_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
return v___x_2003_;
}
}
}
case 10:
{
lean_object* v_fvarId_2005_; lean_object* v_cidx_2006_; lean_object* v_k_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2028_; 
v_fvarId_2005_ = lean_ctor_get(v_code_1687_, 0);
v_cidx_2006_ = lean_ctor_get(v_code_1687_, 1);
v_k_2007_ = lean_ctor_get(v_code_1687_, 2);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_code_1687_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2009_ = v_code_1687_;
v_isShared_2010_ = v_isSharedCheck_2028_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_k_2007_);
lean_inc(v_cidx_2006_);
lean_inc(v_fvarId_2005_);
lean_dec(v_code_1687_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2028_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; uint8_t v___x_2012_; lean_object* v___x_2013_; 
v___x_2011_ = lean_st_ref_get(v_a_1689_);
v___x_2012_ = 1;
v___x_2013_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2011_, v_fvarId_2005_, v___x_2012_);
lean_dec(v___x_2011_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_fvarId_2014_; lean_object* v___x_2015_; 
v_fvarId_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_fvarId_2014_);
lean_dec_ref(v___x_2013_);
v___x_2015_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1686_, v_k_2007_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2026_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2026_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2026_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 2, v_a_2016_);
lean_ctor_set(v___x_2009_, 0, v_fvarId_2014_);
v___x_2021_ = v___x_2009_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_fvarId_2014_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_cidx_2006_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2023_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2021_);
v___x_2023_ = v___x_2018_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
else
{
lean_dec(v_fvarId_2014_);
lean_del_object(v___x_2009_);
lean_dec(v_cidx_2006_);
return v___x_2015_;
}
}
else
{
lean_object* v___x_2027_; 
lean_del_object(v___x_2009_);
lean_dec_ref(v_k_2007_);
lean_dec(v_cidx_2006_);
v___x_2027_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1686_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
return v___x_2027_;
}
}
}
case 11:
{
lean_object* v_fvarId_2029_; lean_object* v_n_2030_; uint8_t v_check_2031_; uint8_t v_persistent_2032_; lean_object* v_k_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2054_; 
v_fvarId_2029_ = lean_ctor_get(v_code_1687_, 0);
v_n_2030_ = lean_ctor_get(v_code_1687_, 1);
v_check_2031_ = lean_ctor_get_uint8(v_code_1687_, sizeof(void*)*3);
v_persistent_2032_ = lean_ctor_get_uint8(v_code_1687_, sizeof(void*)*3 + 1);
v_k_2033_ = lean_ctor_get(v_code_1687_, 2);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_code_1687_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2035_ = v_code_1687_;
v_isShared_2036_ = v_isSharedCheck_2054_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_k_2033_);
lean_inc(v_n_2030_);
lean_inc(v_fvarId_2029_);
lean_dec(v_code_1687_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2054_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; uint8_t v___x_2038_; lean_object* v___x_2039_; 
v___x_2037_ = lean_st_ref_get(v_a_1689_);
v___x_2038_ = 1;
v___x_2039_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2037_, v_fvarId_2029_, v___x_2038_);
lean_dec(v___x_2037_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_fvarId_2040_; lean_object* v___x_2041_; 
v_fvarId_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_fvarId_2040_);
lean_dec_ref(v___x_2039_);
v___x_2041_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1686_, v_k_2033_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2052_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2052_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2052_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 2, v_a_2042_);
lean_ctor_set(v___x_2035_, 0, v_fvarId_2040_);
v___x_2047_ = v___x_2035_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_fvarId_2040_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_n_2030_);
lean_ctor_set(v_reuseFailAlloc_2051_, 2, v_a_2042_);
lean_ctor_set_uint8(v_reuseFailAlloc_2051_, sizeof(void*)*3, v_check_2031_);
lean_ctor_set_uint8(v_reuseFailAlloc_2051_, sizeof(void*)*3 + 1, v_persistent_2032_);
v___x_2047_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2049_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v___x_2047_);
v___x_2049_ = v___x_2044_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
else
{
lean_dec(v_fvarId_2040_);
lean_del_object(v___x_2035_);
lean_dec(v_n_2030_);
return v___x_2041_;
}
}
else
{
lean_object* v___x_2053_; 
lean_del_object(v___x_2035_);
lean_dec_ref(v_k_2033_);
lean_dec(v_n_2030_);
v___x_2053_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1686_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
return v___x_2053_;
}
}
}
case 12:
{
lean_object* v_fvarId_2055_; lean_object* v_n_2056_; uint8_t v_check_2057_; uint8_t v_persistent_2058_; lean_object* v_k_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2080_; 
v_fvarId_2055_ = lean_ctor_get(v_code_1687_, 0);
v_n_2056_ = lean_ctor_get(v_code_1687_, 1);
v_check_2057_ = lean_ctor_get_uint8(v_code_1687_, sizeof(void*)*3);
v_persistent_2058_ = lean_ctor_get_uint8(v_code_1687_, sizeof(void*)*3 + 1);
v_k_2059_ = lean_ctor_get(v_code_1687_, 2);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_code_1687_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2061_ = v_code_1687_;
v_isShared_2062_ = v_isSharedCheck_2080_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_k_2059_);
lean_inc(v_n_2056_);
lean_inc(v_fvarId_2055_);
lean_dec(v_code_1687_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2080_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; 
v___x_2063_ = lean_st_ref_get(v_a_1689_);
v___x_2064_ = 1;
v___x_2065_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2063_, v_fvarId_2055_, v___x_2064_);
lean_dec(v___x_2063_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_fvarId_2066_; lean_object* v___x_2067_; 
v_fvarId_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_fvarId_2066_);
lean_dec_ref(v___x_2065_);
v___x_2067_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1686_, v_k_2059_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2078_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2070_ = v___x_2067_;
v_isShared_2071_ = v_isSharedCheck_2078_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2067_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2078_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 2, v_a_2068_);
lean_ctor_set(v___x_2061_, 0, v_fvarId_2066_);
v___x_2073_ = v___x_2061_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_fvarId_2066_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_n_2056_);
lean_ctor_set(v_reuseFailAlloc_2077_, 2, v_a_2068_);
lean_ctor_set_uint8(v_reuseFailAlloc_2077_, sizeof(void*)*3, v_check_2057_);
lean_ctor_set_uint8(v_reuseFailAlloc_2077_, sizeof(void*)*3 + 1, v_persistent_2058_);
v___x_2073_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2075_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2073_);
v___x_2075_ = v___x_2070_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
else
{
lean_dec(v_fvarId_2066_);
lean_del_object(v___x_2061_);
lean_dec(v_n_2056_);
return v___x_2067_;
}
}
else
{
lean_object* v___x_2079_; 
lean_del_object(v___x_2061_);
lean_dec_ref(v_k_2059_);
lean_dec(v_n_2056_);
v___x_2079_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1686_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
return v___x_2079_;
}
}
}
default: 
{
lean_object* v_fvarId_2081_; lean_object* v_k_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2103_; 
v_fvarId_2081_ = lean_ctor_get(v_code_1687_, 0);
v_k_2082_ = lean_ctor_get(v_code_1687_, 1);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_code_1687_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2084_ = v_code_1687_;
v_isShared_2085_ = v_isSharedCheck_2103_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_k_2082_);
lean_inc(v_fvarId_2081_);
lean_dec(v_code_1687_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2103_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; uint8_t v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = lean_st_ref_get(v_a_1689_);
v___x_2087_ = 1;
v___x_2088_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2086_, v_fvarId_2081_, v___x_2087_);
lean_dec(v___x_2086_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_fvarId_2089_; lean_object* v___x_2090_; 
v_fvarId_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_fvarId_2089_);
lean_dec_ref(v___x_2088_);
v___x_2090_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_1686_, v_k_2082_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2101_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2093_ = v___x_2090_;
v_isShared_2094_ = v_isSharedCheck_2101_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2090_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2101_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 1, v_a_2091_);
lean_ctor_set(v___x_2084_, 0, v_fvarId_2089_);
v___x_2096_ = v___x_2084_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_fvarId_2089_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2098_; 
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v___x_2096_);
v___x_2098_ = v___x_2093_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
else
{
lean_dec(v_fvarId_2089_);
lean_del_object(v___x_2084_);
return v___x_2090_;
}
}
else
{
lean_object* v___x_2102_; 
lean_del_object(v___x_2084_);
lean_dec_ref(v_k_2082_);
v___x_2102_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_1686_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
return v___x_2102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(uint8_t v_pu_2104_, lean_object* v_decl_2105_, uint8_t v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v_fvarId_2113_; lean_object* v_binderName_2114_; lean_object* v_params_2115_; lean_object* v_type_2116_; lean_object* v_value_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2195_; 
v_fvarId_2113_ = lean_ctor_get(v_decl_2105_, 0);
v_binderName_2114_ = lean_ctor_get(v_decl_2105_, 1);
v_params_2115_ = lean_ctor_get(v_decl_2105_, 2);
v_type_2116_ = lean_ctor_get(v_decl_2105_, 3);
v_value_2117_ = lean_ctor_get(v_decl_2105_, 4);
v_isSharedCheck_2195_ = !lean_is_exclusive(v_decl_2105_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2119_ = v_decl_2105_;
v_isShared_2120_ = v_isSharedCheck_2195_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_value_2117_);
lean_inc(v_type_2116_);
lean_inc(v_params_2115_);
lean_inc(v_binderName_2114_);
lean_inc(v_fvarId_2113_);
lean_dec(v_decl_2105_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2195_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2121_; 
v___x_2121_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2104_, v_type_2116_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2123_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref(v___x_2121_);
v___x_2123_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_2114_, v_a_2106_, v_a_2109_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; size_t v_sz_2125_; size_t v___x_2126_; lean_object* v___x_2127_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref(v___x_2123_);
v_sz_2125_ = lean_array_size(v_params_2115_);
v___x_2126_ = ((size_t)0ULL);
v___x_2127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2104_, v_sz_2125_, v___x_2126_, v_params_2115_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2129_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref(v___x_2127_);
v___x_2129_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2104_, v_value_2117_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref(v___x_2129_);
v___x_2131_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_2113_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2154_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2134_ = v___x_2131_;
v_isShared_2135_ = v_isSharedCheck_2154_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2131_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2154_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; lean_object* v_lctx_2137_; lean_object* v_nextIdx_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2153_; 
v___x_2136_ = lean_st_ref_take(v_a_2109_);
v_lctx_2137_ = lean_ctor_get(v___x_2136_, 0);
v_nextIdx_2138_ = lean_ctor_get(v___x_2136_, 1);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2140_ = v___x_2136_;
v_isShared_2141_ = v_isSharedCheck_2153_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_nextIdx_2138_);
lean_inc(v_lctx_2137_);
lean_dec(v___x_2136_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2153_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 4, v_a_2130_);
lean_ctor_set(v___x_2119_, 3, v_a_2122_);
lean_ctor_set(v___x_2119_, 2, v_a_2128_);
lean_ctor_set(v___x_2119_, 1, v_a_2124_);
lean_ctor_set(v___x_2119_, 0, v_a_2132_);
v___x_2143_ = v___x_2119_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2132_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_a_2124_);
lean_ctor_set(v_reuseFailAlloc_2152_, 2, v_a_2128_);
lean_ctor_set(v_reuseFailAlloc_2152_, 3, v_a_2122_);
lean_ctor_set(v_reuseFailAlloc_2152_, 4, v_a_2130_);
v___x_2143_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2144_; lean_object* v___x_2146_; 
lean_inc_ref(v___x_2143_);
v___x_2144_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2104_, v_lctx_2137_, v___x_2143_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2144_);
v___x_2146_ = v___x_2140_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2144_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v_nextIdx_2138_);
v___x_2146_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2147_; lean_object* v___x_2149_; 
v___x_2147_ = lean_st_ref_set(v_a_2109_, v___x_2146_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v___x_2143_);
v___x_2149_ = v___x_2134_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2143_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec(v_a_2130_);
lean_dec(v_a_2128_);
lean_dec(v_a_2124_);
lean_dec(v_a_2122_);
lean_del_object(v___x_2119_);
v_a_2155_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2131_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2131_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_dec(v_a_2128_);
lean_dec(v_a_2124_);
lean_dec(v_a_2122_);
lean_del_object(v___x_2119_);
lean_dec(v_fvarId_2113_);
v_a_2163_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2129_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2129_);
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
lean_dec(v_a_2124_);
lean_dec(v_a_2122_);
lean_del_object(v___x_2119_);
lean_dec_ref(v_value_2117_);
lean_dec(v_fvarId_2113_);
v_a_2171_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2127_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2127_);
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
lean_dec(v_a_2122_);
lean_del_object(v___x_2119_);
lean_dec_ref(v_value_2117_);
lean_dec_ref(v_params_2115_);
lean_dec(v_fvarId_2113_);
v_a_2179_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2123_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2123_);
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
lean_del_object(v___x_2119_);
lean_dec_ref(v_value_2117_);
lean_dec_ref(v_params_2115_);
lean_dec(v_binderName_2114_);
lean_dec(v_fvarId_2113_);
v_a_2187_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2121_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2121_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(lean_object* v_pu_2196_, lean_object* v_decl_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_){
_start:
{
uint8_t v_pu_boxed_2205_; uint8_t v_a_boxed_2206_; lean_object* v_res_2207_; 
v_pu_boxed_2205_ = lean_unbox(v_pu_2196_);
v_a_boxed_2206_ = lean_unbox(v_a_2198_);
v_res_2207_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_boxed_2205_, v_decl_2197_, v_a_boxed_2206_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
lean_dec(v_a_2199_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2___boxed(lean_object* v_pu_2208_, lean_object* v_sz_2209_, lean_object* v_i_2210_, lean_object* v_bs_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
uint8_t v_pu_boxed_2219_; size_t v_sz_boxed_2220_; size_t v_i_boxed_2221_; uint8_t v___y_26953__boxed_2222_; lean_object* v_res_2223_; 
v_pu_boxed_2219_ = lean_unbox(v_pu_2208_);
v_sz_boxed_2220_ = lean_unbox_usize(v_sz_2209_);
lean_dec(v_sz_2209_);
v_i_boxed_2221_ = lean_unbox_usize(v_i_2210_);
lean_dec(v_i_2210_);
v___y_26953__boxed_2222_ = lean_unbox(v___y_2212_);
v_res_2223_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_boxed_2219_, v_sz_boxed_2220_, v_i_boxed_2221_, v_bs_2211_, v___y_26953__boxed_2222_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(lean_object* v_pu_2224_, lean_object* v_code_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
uint8_t v_pu_boxed_2233_; uint8_t v_a_boxed_2234_; lean_object* v_res_2235_; 
v_pu_boxed_2233_ = lean_unbox(v_pu_2224_);
v_a_boxed_2234_ = lean_unbox(v_a_2226_);
v_res_2235_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_boxed_2233_, v_code_2225_, v_a_boxed_2234_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(uint8_t v_pu_2236_, lean_object* v_msg_2237_, uint8_t v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v_toApplicative_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2311_; 
v___x_2245_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
v___x_2246_ = l_StateRefT_x27_instMonad___redArg(v___x_2245_);
v_toApplicative_2247_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2311_ == 0)
{
lean_object* v_unused_2312_; 
v_unused_2312_ = lean_ctor_get(v___x_2246_, 1);
lean_dec(v_unused_2312_);
v___x_2249_ = v___x_2246_;
v_isShared_2250_ = v_isSharedCheck_2311_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_toApplicative_2247_);
lean_dec(v___x_2246_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2311_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v_toFunctor_2251_; lean_object* v_toSeq_2252_; lean_object* v_toSeqLeft_2253_; lean_object* v_toSeqRight_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2309_; 
v_toFunctor_2251_ = lean_ctor_get(v_toApplicative_2247_, 0);
v_toSeq_2252_ = lean_ctor_get(v_toApplicative_2247_, 2);
v_toSeqLeft_2253_ = lean_ctor_get(v_toApplicative_2247_, 3);
v_toSeqRight_2254_ = lean_ctor_get(v_toApplicative_2247_, 4);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_toApplicative_2247_);
if (v_isSharedCheck_2309_ == 0)
{
lean_object* v_unused_2310_; 
v_unused_2310_ = lean_ctor_get(v_toApplicative_2247_, 1);
lean_dec(v_unused_2310_);
v___x_2256_ = v_toApplicative_2247_;
v_isShared_2257_ = v_isSharedCheck_2309_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_toSeqRight_2254_);
lean_inc(v_toSeqLeft_2253_);
lean_inc(v_toSeq_2252_);
lean_inc(v_toFunctor_2251_);
lean_dec(v_toApplicative_2247_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2309_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___f_2258_; lean_object* v___f_2259_; lean_object* v___f_2260_; lean_object* v___f_2261_; lean_object* v___x_2262_; lean_object* v___f_2263_; lean_object* v___f_2264_; lean_object* v___f_2265_; lean_object* v___x_2267_; 
v___f_2258_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
v___f_2259_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_2251_);
v___f_2260_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2260_, 0, v_toFunctor_2251_);
v___f_2261_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2261_, 0, v_toFunctor_2251_);
v___x_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___f_2260_);
lean_ctor_set(v___x_2262_, 1, v___f_2261_);
v___f_2263_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2263_, 0, v_toSeqRight_2254_);
v___f_2264_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2264_, 0, v_toSeqLeft_2253_);
v___f_2265_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2265_, 0, v_toSeq_2252_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 4, v___f_2263_);
lean_ctor_set(v___x_2256_, 3, v___f_2264_);
lean_ctor_set(v___x_2256_, 2, v___f_2265_);
lean_ctor_set(v___x_2256_, 1, v___f_2258_);
lean_ctor_set(v___x_2256_, 0, v___x_2262_);
v___x_2267_ = v___x_2256_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2262_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v___f_2258_);
lean_ctor_set(v_reuseFailAlloc_2308_, 2, v___f_2265_);
lean_ctor_set(v_reuseFailAlloc_2308_, 3, v___f_2264_);
lean_ctor_set(v_reuseFailAlloc_2308_, 4, v___f_2263_);
v___x_2267_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
lean_object* v___x_2269_; 
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 1, v___f_2259_);
lean_ctor_set(v___x_2249_, 0, v___x_2267_);
v___x_2269_ = v___x_2249_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2267_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v___f_2259_);
v___x_2269_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
lean_object* v___x_2270_; lean_object* v_toApplicative_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2305_; 
v___x_2270_ = l_StateRefT_x27_instMonad___redArg(v___x_2269_);
v_toApplicative_2271_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2305_ == 0)
{
lean_object* v_unused_2306_; 
v_unused_2306_ = lean_ctor_get(v___x_2270_, 1);
lean_dec(v_unused_2306_);
v___x_2273_ = v___x_2270_;
v_isShared_2274_ = v_isSharedCheck_2305_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_toApplicative_2271_);
lean_dec(v___x_2270_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2305_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v_toFunctor_2275_; lean_object* v_toSeq_2276_; lean_object* v_toSeqLeft_2277_; lean_object* v_toSeqRight_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2303_; 
v_toFunctor_2275_ = lean_ctor_get(v_toApplicative_2271_, 0);
v_toSeq_2276_ = lean_ctor_get(v_toApplicative_2271_, 2);
v_toSeqLeft_2277_ = lean_ctor_get(v_toApplicative_2271_, 3);
v_toSeqRight_2278_ = lean_ctor_get(v_toApplicative_2271_, 4);
v_isSharedCheck_2303_ = !lean_is_exclusive(v_toApplicative_2271_);
if (v_isSharedCheck_2303_ == 0)
{
lean_object* v_unused_2304_; 
v_unused_2304_ = lean_ctor_get(v_toApplicative_2271_, 1);
lean_dec(v_unused_2304_);
v___x_2280_ = v_toApplicative_2271_;
v_isShared_2281_ = v_isSharedCheck_2303_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_toSeqRight_2278_);
lean_inc(v_toSeqLeft_2277_);
lean_inc(v_toSeq_2276_);
lean_inc(v_toFunctor_2275_);
lean_dec(v_toApplicative_2271_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2303_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___f_2282_; lean_object* v___f_2283_; lean_object* v___f_2284_; lean_object* v___f_2285_; lean_object* v___x_2286_; lean_object* v___f_2287_; lean_object* v___f_2288_; lean_object* v___f_2289_; lean_object* v___x_2291_; 
v___f_2282_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
v___f_2283_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(v_toFunctor_2275_);
v___f_2284_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2284_, 0, v_toFunctor_2275_);
v___f_2285_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2285_, 0, v_toFunctor_2275_);
v___x_2286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___f_2284_);
lean_ctor_set(v___x_2286_, 1, v___f_2285_);
v___f_2287_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2287_, 0, v_toSeqRight_2278_);
v___f_2288_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2288_, 0, v_toSeqLeft_2277_);
v___f_2289_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2289_, 0, v_toSeq_2276_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 4, v___f_2287_);
lean_ctor_set(v___x_2280_, 3, v___f_2288_);
lean_ctor_set(v___x_2280_, 2, v___f_2289_);
lean_ctor_set(v___x_2280_, 1, v___f_2282_);
lean_ctor_set(v___x_2280_, 0, v___x_2286_);
v___x_2291_ = v___x_2280_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2302_, 1, v___f_2282_);
lean_ctor_set(v_reuseFailAlloc_2302_, 2, v___f_2289_);
lean_ctor_set(v_reuseFailAlloc_2302_, 3, v___f_2288_);
lean_ctor_set(v_reuseFailAlloc_2302_, 4, v___f_2287_);
v___x_2291_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
lean_object* v___x_2293_; 
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 1, v___f_2283_);
lean_ctor_set(v___x_2273_, 0, v___x_2291_);
v___x_2293_ = v___x_2273_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2291_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v___f_2283_);
v___x_2293_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___f_2297_; lean_object* v___x_11424__overap_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2294_ = l_StateRefT_x27_instMonad___redArg(v___x_2293_);
v___x_2295_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v_pu_2236_);
v___x_2296_ = l_instInhabitedOfMonad___redArg(v___x_2294_, v___x_2295_);
v___f_2297_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2297_, 0, v___x_2296_);
v___x_11424__overap_2298_ = lean_panic_fn_borrowed(v___f_2297_, v_msg_2237_);
lean_dec_ref(v___f_2297_);
v___x_2299_ = lean_box(v___y_2238_);
lean_inc(v___y_2243_);
lean_inc_ref(v___y_2242_);
lean_inc(v___y_2241_);
lean_inc_ref(v___y_2240_);
lean_inc(v___y_2239_);
v___x_2300_ = lean_apply_7(v___x_11424__overap_2298_, v___x_2299_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, lean_box(0));
return v___x_2300_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___boxed(lean_object* v_pu_2313_, lean_object* v_msg_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
uint8_t v_pu_boxed_2322_; uint8_t v___y_11455__boxed_2323_; lean_object* v_res_2324_; 
v_pu_boxed_2322_ = lean_unbox(v_pu_2313_);
v___y_11455__boxed_2323_ = lean_unbox(v___y_2315_);
v_res_2324_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_boxed_2322_, v_msg_2314_, v___y_11455__boxed_2323_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
return v_res_2324_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1(void){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2326_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2327_ = lean_unsigned_to_nat(41u);
v___x_2328_ = lean_unsigned_to_nat(217u);
v___x_2329_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2330_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2331_ = l_mkPanicMessageWithDecl(v___x_2330_, v___x_2329_, v___x_2328_, v___x_2327_, v___x_2326_);
return v___x_2331_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2(void){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2332_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2333_ = lean_unsigned_to_nat(31u);
v___x_2334_ = lean_unsigned_to_nat(222u);
v___x_2335_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2336_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2337_ = l_mkPanicMessageWithDecl(v___x_2336_, v___x_2335_, v___x_2334_, v___x_2333_, v___x_2332_);
return v___x_2337_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2338_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2339_ = lean_unsigned_to_nat(41u);
v___x_2340_ = lean_unsigned_to_nat(221u);
v___x_2341_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2342_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2343_ = l_mkPanicMessageWithDecl(v___x_2342_, v___x_2341_, v___x_2340_, v___x_2339_, v___x_2338_);
return v___x_2343_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2344_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2345_ = lean_unsigned_to_nat(31u);
v___x_2346_ = lean_unsigned_to_nat(226u);
v___x_2347_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2348_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2349_ = l_mkPanicMessageWithDecl(v___x_2348_, v___x_2347_, v___x_2346_, v___x_2345_, v___x_2344_);
return v___x_2349_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2350_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2351_ = lean_unsigned_to_nat(41u);
v___x_2352_ = lean_unsigned_to_nat(225u);
v___x_2353_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2354_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2355_ = l_mkPanicMessageWithDecl(v___x_2354_, v___x_2353_, v___x_2352_, v___x_2351_, v___x_2350_);
return v___x_2355_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6(void){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2356_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2357_ = lean_unsigned_to_nat(41u);
v___x_2358_ = lean_unsigned_to_nat(230u);
v___x_2359_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2360_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2361_ = l_mkPanicMessageWithDecl(v___x_2360_, v___x_2359_, v___x_2358_, v___x_2357_, v___x_2356_);
return v___x_2361_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7(void){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2362_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2363_ = lean_unsigned_to_nat(41u);
v___x_2364_ = lean_unsigned_to_nat(233u);
v___x_2365_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2366_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2367_ = l_mkPanicMessageWithDecl(v___x_2366_, v___x_2365_, v___x_2364_, v___x_2363_, v___x_2362_);
return v___x_2367_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8(void){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2368_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2369_ = lean_unsigned_to_nat(41u);
v___x_2370_ = lean_unsigned_to_nat(236u);
v___x_2371_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2372_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2373_ = l_mkPanicMessageWithDecl(v___x_2372_, v___x_2371_, v___x_2370_, v___x_2369_, v___x_2368_);
return v___x_2373_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9(void){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2374_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
v___x_2375_ = lean_unsigned_to_nat(41u);
v___x_2376_ = lean_unsigned_to_nat(239u);
v___x_2377_ = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
v___x_2378_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
v___x_2379_ = l_mkPanicMessageWithDecl(v___x_2378_, v___x_2377_, v___x_2376_, v___x_2375_, v___x_2374_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t v_pu_2380_, lean_object* v_decl_2381_, uint8_t v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
switch(lean_obj_tag(v_decl_2381_))
{
case 0:
{
lean_object* v_decl_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2413_; 
v_decl_2389_ = lean_ctor_get(v_decl_2381_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_decl_2381_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2391_ = v_decl_2381_;
v_isShared_2392_ = v_isSharedCheck_2413_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_decl_2389_);
lean_dec(v_decl_2381_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2413_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(v_pu_2380_, v_decl_2389_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2404_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2396_ = v___x_2393_;
v_isShared_2397_ = v_isSharedCheck_2404_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2393_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2404_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 0, v_a_2394_);
v___x_2399_ = v___x_2391_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
lean_object* v___x_2401_; 
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2399_);
v___x_2401_ = v___x_2396_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2399_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_del_object(v___x_2391_);
v_a_2405_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2393_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2393_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
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
}
case 1:
{
lean_object* v_decl_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2438_; 
v_decl_2414_ = lean_ctor_get(v_decl_2381_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v_decl_2381_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2416_ = v_decl_2381_;
v_isShared_2417_ = v_isSharedCheck_2438_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_decl_2414_);
lean_dec(v_decl_2381_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2438_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2380_, v_decl_2414_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2429_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2421_ = v___x_2418_;
v_isShared_2422_ = v_isSharedCheck_2429_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2429_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v_a_2419_);
v___x_2424_ = v___x_2416_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2426_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v___x_2424_);
v___x_2426_ = v___x_2421_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_del_object(v___x_2416_);
v_a_2430_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2418_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2418_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
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
}
case 2:
{
lean_object* v_decl_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2463_; 
v_decl_2439_ = lean_ctor_get(v_decl_2381_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_decl_2381_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2441_ = v_decl_2381_;
v_isShared_2442_ = v_isSharedCheck_2463_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_decl_2439_);
lean_dec(v_decl_2381_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2463_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(v_pu_2380_, v_decl_2439_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2454_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2446_ = v___x_2443_;
v_isShared_2447_ = v_isSharedCheck_2454_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2443_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2454_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 0, v_a_2444_);
v___x_2449_ = v___x_2441_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2451_; 
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v___x_2449_);
v___x_2451_ = v___x_2446_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2449_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_del_object(v___x_2441_);
v_a_2455_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2443_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2443_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
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
}
case 3:
{
lean_object* v_fvarId_2464_; lean_object* v_i_2465_; lean_object* v_y_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2488_; 
v_fvarId_2464_ = lean_ctor_get(v_decl_2381_, 0);
v_i_2465_ = lean_ctor_get(v_decl_2381_, 1);
v_y_2466_ = lean_ctor_get(v_decl_2381_, 2);
v_isSharedCheck_2488_ = !lean_is_exclusive(v_decl_2381_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2468_ = v_decl_2381_;
v_isShared_2469_ = v_isSharedCheck_2488_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_y_2466_);
lean_inc(v_i_2465_);
lean_inc(v_fvarId_2464_);
lean_dec(v_decl_2381_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2488_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2470_; uint8_t v___x_2471_; lean_object* v___x_2472_; 
v___x_2470_ = lean_st_ref_get(v_a_2383_);
v___x_2471_ = 1;
v___x_2472_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2470_, v_fvarId_2464_, v___x_2471_);
lean_dec(v___x_2470_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_fvarId_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2485_; 
v_fvarId_2473_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2475_ = v___x_2472_;
v_isShared_2476_ = v_isSharedCheck_2485_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_fvarId_2473_);
lean_dec(v___x_2472_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2485_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2480_; 
v___x_2477_ = lean_st_ref_get(v_a_2383_);
v___x_2478_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2380_, v___x_2477_, v_y_2466_, v___x_2471_);
lean_dec(v___x_2477_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 2, v___x_2478_);
lean_ctor_set(v___x_2468_, 0, v_fvarId_2473_);
v___x_2480_ = v___x_2468_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_fvarId_2473_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v_i_2465_);
lean_ctor_set(v_reuseFailAlloc_2484_, 2, v___x_2478_);
v___x_2480_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
lean_object* v___x_2482_; 
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 0, v___x_2480_);
v___x_2482_ = v___x_2475_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2480_);
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
else
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
lean_dec(v___x_2472_);
lean_del_object(v___x_2468_);
lean_dec(v_y_2466_);
lean_dec(v_i_2465_);
v___x_2486_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1);
v___x_2487_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2380_, v___x_2486_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2487_;
}
}
}
case 4:
{
lean_object* v_fvarId_2489_; lean_object* v_i_2490_; lean_object* v_y_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2516_; 
v_fvarId_2489_ = lean_ctor_get(v_decl_2381_, 0);
v_i_2490_ = lean_ctor_get(v_decl_2381_, 1);
v_y_2491_ = lean_ctor_get(v_decl_2381_, 2);
v_isSharedCheck_2516_ = !lean_is_exclusive(v_decl_2381_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2493_ = v_decl_2381_;
v_isShared_2494_ = v_isSharedCheck_2516_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_y_2491_);
lean_inc(v_i_2490_);
lean_inc(v_fvarId_2489_);
lean_dec(v_decl_2381_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2516_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2495_; uint8_t v___x_2496_; lean_object* v___x_2497_; 
v___x_2495_ = lean_st_ref_get(v_a_2383_);
v___x_2496_ = 1;
v___x_2497_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2495_, v_fvarId_2489_, v___x_2496_);
lean_dec(v___x_2495_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_fvarId_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v_fvarId_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_fvarId_2498_);
lean_dec_ref(v___x_2497_);
v___x_2499_ = lean_st_ref_get(v_a_2383_);
v___x_2500_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2499_, v_y_2491_, v___x_2496_);
lean_dec(v___x_2499_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_fvarId_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2511_; 
v_fvarId_2501_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2503_ = v___x_2500_;
v_isShared_2504_ = v_isSharedCheck_2511_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_fvarId_2501_);
lean_dec(v___x_2500_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2511_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 2, v_fvarId_2501_);
lean_ctor_set(v___x_2493_, 0, v_fvarId_2498_);
v___x_2506_ = v___x_2493_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_fvarId_2498_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_i_2490_);
lean_ctor_set(v_reuseFailAlloc_2510_, 2, v_fvarId_2501_);
v___x_2506_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2508_; 
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 0, v___x_2506_);
v___x_2508_ = v___x_2503_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2506_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
else
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
lean_dec(v___x_2500_);
lean_dec(v_fvarId_2498_);
lean_del_object(v___x_2493_);
lean_dec(v_i_2490_);
v___x_2512_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2);
v___x_2513_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2380_, v___x_2512_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2513_;
}
}
else
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_dec(v___x_2497_);
lean_del_object(v___x_2493_);
lean_dec(v_y_2491_);
lean_dec(v_i_2490_);
v___x_2514_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3);
v___x_2515_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2380_, v___x_2514_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2515_;
}
}
}
case 5:
{
lean_object* v_fvarId_2517_; lean_object* v_i_2518_; lean_object* v_offset_2519_; lean_object* v_y_2520_; lean_object* v_ty_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2548_; 
v_fvarId_2517_ = lean_ctor_get(v_decl_2381_, 0);
v_i_2518_ = lean_ctor_get(v_decl_2381_, 1);
v_offset_2519_ = lean_ctor_get(v_decl_2381_, 2);
v_y_2520_ = lean_ctor_get(v_decl_2381_, 3);
v_ty_2521_ = lean_ctor_get(v_decl_2381_, 4);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_decl_2381_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2523_ = v_decl_2381_;
v_isShared_2524_ = v_isSharedCheck_2548_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_ty_2521_);
lean_inc(v_y_2520_);
lean_inc(v_offset_2519_);
lean_inc(v_i_2518_);
lean_inc(v_fvarId_2517_);
lean_dec(v_decl_2381_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2548_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2525_; uint8_t v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = lean_st_ref_get(v_a_2383_);
v___x_2526_ = 1;
v___x_2527_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2525_, v_fvarId_2517_, v___x_2526_);
lean_dec(v___x_2525_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_fvarId_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v_fvarId_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_fvarId_2528_);
lean_dec_ref(v___x_2527_);
v___x_2529_ = lean_st_ref_get(v_a_2383_);
v___x_2530_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2529_, v_y_2520_, v___x_2526_);
lean_dec(v___x_2529_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_fvarId_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2543_; 
v_fvarId_2531_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2533_ = v___x_2530_;
v_isShared_2534_ = v_isSharedCheck_2543_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_fvarId_2531_);
lean_dec(v___x_2530_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2543_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2538_; 
v___x_2535_ = lean_st_ref_get(v_a_2383_);
v___x_2536_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2380_, v___x_2535_, v___x_2526_, v_ty_2521_);
lean_dec(v___x_2535_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 4, v___x_2536_);
lean_ctor_set(v___x_2523_, 3, v_fvarId_2531_);
lean_ctor_set(v___x_2523_, 0, v_fvarId_2528_);
v___x_2538_ = v___x_2523_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_fvarId_2528_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v_i_2518_);
lean_ctor_set(v_reuseFailAlloc_2542_, 2, v_offset_2519_);
lean_ctor_set(v_reuseFailAlloc_2542_, 3, v_fvarId_2531_);
lean_ctor_set(v_reuseFailAlloc_2542_, 4, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
lean_object* v___x_2540_; 
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v___x_2538_);
v___x_2540_ = v___x_2533_;
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
lean_dec(v___x_2530_);
lean_dec(v_fvarId_2528_);
lean_del_object(v___x_2523_);
lean_dec_ref(v_ty_2521_);
lean_dec(v_offset_2519_);
lean_dec(v_i_2518_);
v___x_2544_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4);
v___x_2545_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2380_, v___x_2544_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2545_;
}
}
else
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
lean_dec(v___x_2527_);
lean_del_object(v___x_2523_);
lean_dec_ref(v_ty_2521_);
lean_dec(v_y_2520_);
lean_dec(v_offset_2519_);
lean_dec(v_i_2518_);
v___x_2546_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5);
v___x_2547_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2380_, v___x_2546_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2547_;
}
}
}
case 6:
{
lean_object* v_fvarId_2549_; lean_object* v_cidx_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2570_; 
v_fvarId_2549_ = lean_ctor_get(v_decl_2381_, 0);
v_cidx_2550_ = lean_ctor_get(v_decl_2381_, 1);
v_isSharedCheck_2570_ = !lean_is_exclusive(v_decl_2381_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2552_ = v_decl_2381_;
v_isShared_2553_ = v_isSharedCheck_2570_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_cidx_2550_);
lean_inc(v_fvarId_2549_);
lean_dec(v_decl_2381_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2570_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2554_; uint8_t v___x_2555_; lean_object* v___x_2556_; 
v___x_2554_ = lean_st_ref_get(v_a_2383_);
v___x_2555_ = 1;
v___x_2556_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2554_, v_fvarId_2549_, v___x_2555_);
lean_dec(v___x_2554_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_fvarId_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2567_; 
v_fvarId_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2567_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_fvarId_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2567_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v_fvarId_2557_);
v___x_2562_ = v___x_2552_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_fvarId_2557_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v_cidx_2550_);
v___x_2562_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
lean_object* v___x_2564_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2562_);
v___x_2564_ = v___x_2559_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2562_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
else
{
lean_object* v___x_2568_; lean_object* v___x_2569_; 
lean_dec(v___x_2556_);
lean_del_object(v___x_2552_);
lean_dec(v_cidx_2550_);
v___x_2568_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6);
v___x_2569_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2380_, v___x_2568_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2569_;
}
}
}
case 7:
{
lean_object* v_fvarId_2571_; lean_object* v_n_2572_; uint8_t v_check_2573_; uint8_t v_persistent_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2594_; 
v_fvarId_2571_ = lean_ctor_get(v_decl_2381_, 0);
v_n_2572_ = lean_ctor_get(v_decl_2381_, 1);
v_check_2573_ = lean_ctor_get_uint8(v_decl_2381_, sizeof(void*)*2);
v_persistent_2574_ = lean_ctor_get_uint8(v_decl_2381_, sizeof(void*)*2 + 1);
v_isSharedCheck_2594_ = !lean_is_exclusive(v_decl_2381_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2576_ = v_decl_2381_;
v_isShared_2577_ = v_isSharedCheck_2594_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_n_2572_);
lean_inc(v_fvarId_2571_);
lean_dec(v_decl_2381_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2594_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2578_; uint8_t v___x_2579_; lean_object* v___x_2580_; 
v___x_2578_ = lean_st_ref_get(v_a_2383_);
v___x_2579_ = 1;
v___x_2580_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2578_, v_fvarId_2571_, v___x_2579_);
lean_dec(v___x_2578_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_fvarId_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2591_; 
v_fvarId_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2591_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_fvarId_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2591_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v_fvarId_2581_);
v___x_2586_ = v___x_2576_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_fvarId_2581_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_n_2572_);
lean_ctor_set_uint8(v_reuseFailAlloc_2590_, sizeof(void*)*2, v_check_2573_);
lean_ctor_set_uint8(v_reuseFailAlloc_2590_, sizeof(void*)*2 + 1, v_persistent_2574_);
v___x_2586_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
lean_object* v___x_2588_; 
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v___x_2586_);
v___x_2588_ = v___x_2583_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
else
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
lean_dec(v___x_2580_);
lean_del_object(v___x_2576_);
lean_dec(v_n_2572_);
v___x_2592_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7);
v___x_2593_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2380_, v___x_2592_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2593_;
}
}
}
case 8:
{
lean_object* v_fvarId_2595_; lean_object* v_n_2596_; uint8_t v_check_2597_; uint8_t v_persistent_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2618_; 
v_fvarId_2595_ = lean_ctor_get(v_decl_2381_, 0);
v_n_2596_ = lean_ctor_get(v_decl_2381_, 1);
v_check_2597_ = lean_ctor_get_uint8(v_decl_2381_, sizeof(void*)*2);
v_persistent_2598_ = lean_ctor_get_uint8(v_decl_2381_, sizeof(void*)*2 + 1);
v_isSharedCheck_2618_ = !lean_is_exclusive(v_decl_2381_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2600_ = v_decl_2381_;
v_isShared_2601_ = v_isSharedCheck_2618_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_n_2596_);
lean_inc(v_fvarId_2595_);
lean_dec(v_decl_2381_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2618_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2602_; uint8_t v___x_2603_; lean_object* v___x_2604_; 
v___x_2602_ = lean_st_ref_get(v_a_2383_);
v___x_2603_ = 1;
v___x_2604_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2602_, v_fvarId_2595_, v___x_2603_);
lean_dec(v___x_2602_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_fvarId_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2615_; 
v_fvarId_2605_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2607_ = v___x_2604_;
v_isShared_2608_ = v_isSharedCheck_2615_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_fvarId_2605_);
lean_dec(v___x_2604_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2615_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v_fvarId_2605_);
v___x_2610_ = v___x_2600_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(8, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_fvarId_2605_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v_n_2596_);
lean_ctor_set_uint8(v_reuseFailAlloc_2614_, sizeof(void*)*2, v_check_2597_);
lean_ctor_set_uint8(v_reuseFailAlloc_2614_, sizeof(void*)*2 + 1, v_persistent_2598_);
v___x_2610_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2612_; 
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v___x_2610_);
v___x_2612_ = v___x_2607_;
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
lean_dec(v___x_2604_);
lean_del_object(v___x_2600_);
lean_dec(v_n_2596_);
v___x_2616_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8);
v___x_2617_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2380_, v___x_2616_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2617_;
}
}
}
default: 
{
lean_object* v_fvarId_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2639_; 
v_fvarId_2619_ = lean_ctor_get(v_decl_2381_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_decl_2381_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2621_ = v_decl_2381_;
v_isShared_2622_ = v_isSharedCheck_2639_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_fvarId_2619_);
lean_dec(v_decl_2381_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2639_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; uint8_t v___x_2624_; lean_object* v___x_2625_; 
v___x_2623_ = lean_st_ref_get(v_a_2383_);
v___x_2624_ = 1;
v___x_2625_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v___x_2623_, v_fvarId_2619_, v___x_2624_);
lean_dec(v___x_2623_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_fvarId_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2636_; 
v_fvarId_2626_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2628_ = v___x_2625_;
v_isShared_2629_ = v_isSharedCheck_2636_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_fvarId_2626_);
lean_dec(v___x_2625_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2636_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v_fvarId_2626_);
v___x_2631_ = v___x_2621_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_fvarId_2626_);
v___x_2631_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
lean_object* v___x_2633_; 
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v___x_2631_);
v___x_2633_ = v___x_2628_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
else
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
lean_dec(v___x_2625_);
lean_del_object(v___x_2621_);
v___x_2637_ = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9);
v___x_2638_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_2380_, v___x_2637_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2638_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(lean_object* v_pu_2640_, lean_object* v_decl_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_){
_start:
{
uint8_t v_pu_boxed_2649_; uint8_t v_a_boxed_2650_; lean_object* v_res_2651_; 
v_pu_boxed_2649_ = lean_unbox(v_pu_2640_);
v_a_boxed_2650_ = lean_unbox(v_a_2642_);
v_res_2651_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v_pu_boxed_2649_, v_decl_2641_, v_a_boxed_2650_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t v_pu_2652_, lean_object* v_code_2653_, lean_object* v_s_2654_, uint8_t v_uniqueIdents_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = lean_st_mk_ref(v_s_2654_);
v___x_2662_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v_pu_2652_, v_code_2653_, v_uniqueIdents_2655_, v___x_2661_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2671_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2665_ = v___x_2662_;
v_isShared_2666_ = v_isSharedCheck_2671_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2662_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2671_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; lean_object* v___x_2669_; 
v___x_2667_ = lean_st_ref_get(v___x_2661_);
lean_dec(v___x_2661_);
lean_dec(v___x_2667_);
if (v_isShared_2666_ == 0)
{
v___x_2669_ = v___x_2665_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2663_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
else
{
lean_dec(v___x_2661_);
return v___x_2662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize___boxed(lean_object* v_pu_2672_, lean_object* v_code_2673_, lean_object* v_s_2674_, lean_object* v_uniqueIdents_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_){
_start:
{
uint8_t v_pu_boxed_2681_; uint8_t v_uniqueIdents_boxed_2682_; lean_object* v_res_2683_; 
v_pu_boxed_2681_ = lean_unbox(v_pu_2672_);
v_uniqueIdents_boxed_2682_ = lean_unbox(v_uniqueIdents_2675_);
v_res_2683_ = l_Lean_Compiler_LCNF_Code_internalize(v_pu_boxed_2681_, v_code_2673_, v_s_2674_, v_uniqueIdents_boxed_2682_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(lean_object* v_f_2684_, lean_object* v_v_2685_, uint8_t v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
if (lean_obj_tag(v_v_2685_) == 0)
{
lean_object* v_code_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2718_; 
v_code_2693_ = lean_ctor_get(v_v_2685_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v_v_2685_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2695_ = v_v_2685_;
v_isShared_2696_ = v_isSharedCheck_2718_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_code_2693_);
lean_dec(v_v_2685_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2718_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2697_ = lean_box(v___y_2686_);
lean_inc(v___y_2691_);
lean_inc_ref(v___y_2690_);
lean_inc(v___y_2689_);
lean_inc_ref(v___y_2688_);
lean_inc(v___y_2687_);
v___x_2698_ = lean_apply_8(v_f_2684_, v_code_2693_, v___x_2697_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, lean_box(0));
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2709_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2701_ = v___x_2698_;
v_isShared_2702_ = v_isSharedCheck_2709_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2698_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2709_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 0, v_a_2699_);
v___x_2704_ = v___x_2695_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2699_);
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
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
lean_del_object(v___x_2695_);
v_a_2710_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2698_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2698_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
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
}
else
{
lean_object* v___x_2719_; 
lean_dec_ref(v_f_2684_);
v___x_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2719_, 0, v_v_2685_);
return v___x_2719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg___boxed(lean_object* v_f_2720_, lean_object* v_v_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
uint8_t v___y_1412__boxed_2729_; lean_object* v_res_2730_; 
v___y_1412__boxed_2729_ = lean_unbox(v___y_2722_);
v_res_2730_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2720_, v_v_2721_, v___y_1412__boxed_2729_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(uint8_t v_pu_2731_, lean_object* v_f_2732_, lean_object* v_v_2733_, uint8_t v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_2732_, v_v_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___boxed(lean_object* v_pu_2742_, lean_object* v_f_2743_, lean_object* v_v_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
uint8_t v_pu_boxed_2752_; uint8_t v___y_1488__boxed_2753_; lean_object* v_res_2754_; 
v_pu_boxed_2752_ = lean_unbox(v_pu_2742_);
v___y_1488__boxed_2753_ = lean_unbox(v___y_2745_);
v_res_2754_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(v_pu_boxed_2752_, v_f_2743_, v_v_2744_, v___y_1488__boxed_2753_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(uint8_t v_pu_2755_, lean_object* v_decl_2756_, uint8_t v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v_toSignature_2764_; lean_object* v_value_2765_; uint8_t v_recursive_2766_; lean_object* v_inlineAttr_x3f_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2827_; 
v_toSignature_2764_ = lean_ctor_get(v_decl_2756_, 0);
v_value_2765_ = lean_ctor_get(v_decl_2756_, 1);
v_recursive_2766_ = lean_ctor_get_uint8(v_decl_2756_, sizeof(void*)*3);
v_inlineAttr_x3f_2767_ = lean_ctor_get(v_decl_2756_, 2);
v_isSharedCheck_2827_ = !lean_is_exclusive(v_decl_2756_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2769_ = v_decl_2756_;
v_isShared_2770_ = v_isSharedCheck_2827_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_inlineAttr_x3f_2767_);
lean_inc(v_value_2765_);
lean_inc(v_toSignature_2764_);
lean_dec(v_decl_2756_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2827_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v_name_2771_; lean_object* v_levelParams_2772_; lean_object* v_type_2773_; lean_object* v_params_2774_; uint8_t v_safe_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2826_; 
v_name_2771_ = lean_ctor_get(v_toSignature_2764_, 0);
v_levelParams_2772_ = lean_ctor_get(v_toSignature_2764_, 1);
v_type_2773_ = lean_ctor_get(v_toSignature_2764_, 2);
v_params_2774_ = lean_ctor_get(v_toSignature_2764_, 3);
v_safe_2775_ = lean_ctor_get_uint8(v_toSignature_2764_, sizeof(void*)*4);
v_isSharedCheck_2826_ = !lean_is_exclusive(v_toSignature_2764_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2777_ = v_toSignature_2764_;
v_isShared_2778_ = v_isSharedCheck_2826_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_params_2774_);
lean_inc(v_type_2773_);
lean_inc(v_levelParams_2772_);
lean_inc(v_name_2771_);
lean_dec(v_toSignature_2764_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2826_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; 
v___x_2779_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_2755_, v_type_2773_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; size_t v_sz_2781_; size_t v___x_2782_; lean_object* v___x_2783_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref(v___x_2779_);
v_sz_2781_ = lean_array_size(v_params_2774_);
v___x_2782_ = ((size_t)0ULL);
v___x_2783_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_2755_, v_sz_2781_, v___x_2782_, v_params_2774_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2784_);
lean_dec_ref(v___x_2783_);
v___x_2785_ = lean_box(v_pu_2755_);
v___x_2786_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed), 9, 1);
lean_closure_set(v___x_2786_, 0, v___x_2785_);
v___x_2787_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v___x_2786_, v_value_2765_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2801_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2790_ = v___x_2787_;
v_isShared_2791_ = v_isSharedCheck_2801_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2787_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2801_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 3, v_a_2784_);
lean_ctor_set(v___x_2777_, 2, v_a_2780_);
v___x_2793_ = v___x_2777_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_name_2771_);
lean_ctor_set(v_reuseFailAlloc_2800_, 1, v_levelParams_2772_);
lean_ctor_set(v_reuseFailAlloc_2800_, 2, v_a_2780_);
lean_ctor_set(v_reuseFailAlloc_2800_, 3, v_a_2784_);
lean_ctor_set_uint8(v_reuseFailAlloc_2800_, sizeof(void*)*4, v_safe_2775_);
v___x_2793_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2795_; 
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 1, v_a_2788_);
lean_ctor_set(v___x_2769_, 0, v___x_2793_);
v___x_2795_ = v___x_2769_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2793_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_a_2788_);
lean_ctor_set(v_reuseFailAlloc_2799_, 2, v_inlineAttr_x3f_2767_);
lean_ctor_set_uint8(v_reuseFailAlloc_2799_, sizeof(void*)*3, v_recursive_2766_);
v___x_2795_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2797_; 
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v___x_2795_);
v___x_2797_ = v___x_2790_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2795_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec(v_a_2784_);
lean_dec(v_a_2780_);
lean_del_object(v___x_2777_);
lean_dec(v_levelParams_2772_);
lean_dec(v_name_2771_);
lean_del_object(v___x_2769_);
lean_dec(v_inlineAttr_x3f_2767_);
v_a_2802_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2787_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2787_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
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
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec(v_a_2780_);
lean_del_object(v___x_2777_);
lean_dec(v_levelParams_2772_);
lean_dec(v_name_2771_);
lean_del_object(v___x_2769_);
lean_dec(v_inlineAttr_x3f_2767_);
lean_dec_ref(v_value_2765_);
v_a_2810_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2783_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2783_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_del_object(v___x_2777_);
lean_dec_ref(v_params_2774_);
lean_dec(v_levelParams_2772_);
lean_dec(v_name_2771_);
lean_del_object(v___x_2769_);
lean_dec(v_inlineAttr_x3f_2767_);
lean_dec_ref(v_value_2765_);
v_a_2818_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2779_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2779_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go___boxed(lean_object* v_pu_2828_, lean_object* v_decl_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_){
_start:
{
uint8_t v_pu_boxed_2837_; uint8_t v_a_boxed_2838_; lean_object* v_res_2839_; 
v_pu_boxed_2837_ = lean_unbox(v_pu_2828_);
v_a_boxed_2838_ = lean_unbox(v_a_2830_);
v_res_2839_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_boxed_2837_, v_decl_2829_, v_a_boxed_2838_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t v_pu_2840_, lean_object* v_decl_2841_, lean_object* v_s_2842_, uint8_t v_uniqueIdents_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = lean_st_mk_ref(v_s_2842_);
v___x_2850_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_2840_, v_decl_2841_, v_uniqueIdents_2843_, v___x_2849_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2859_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2853_ = v___x_2850_;
v_isShared_2854_ = v_isSharedCheck_2859_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2850_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2859_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2855_; lean_object* v___x_2857_; 
v___x_2855_ = lean_st_ref_get(v___x_2849_);
lean_dec(v___x_2849_);
lean_dec(v___x_2855_);
if (v_isShared_2854_ == 0)
{
v___x_2857_ = v___x_2853_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2851_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
else
{
lean_dec(v___x_2849_);
return v___x_2850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize___boxed(lean_object* v_pu_2860_, lean_object* v_decl_2861_, lean_object* v_s_2862_, lean_object* v_uniqueIdents_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_){
_start:
{
uint8_t v_pu_boxed_2869_; uint8_t v_uniqueIdents_boxed_2870_; lean_object* v_res_2871_; 
v_pu_boxed_2869_ = lean_unbox(v_pu_2860_);
v_uniqueIdents_boxed_2870_ = lean_unbox(v_uniqueIdents_2863_);
v_res_2871_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_boxed_2869_, v_decl_2861_, v_s_2862_, v_uniqueIdents_boxed_2870_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_);
lean_dec(v_a_2867_);
lean_dec_ref(v_a_2866_);
lean_dec(v_a_2865_);
lean_dec_ref(v_a_2864_);
return v_res_2871_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2872_ = lean_box(0);
v___x_2873_ = lean_unsigned_to_nat(16u);
v___x_2874_ = lean_mk_array(v___x_2873_, v___x_2872_);
return v___x_2874_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2875_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0);
v___x_2876_ = lean_unsigned_to_nat(0u);
v___x_2877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
lean_ctor_set(v___x_2877_, 1, v___x_2875_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(uint8_t v_pu_2878_, size_t v_sz_2879_, size_t v_i_2880_, lean_object* v_bs_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
uint8_t v___x_2887_; 
v___x_2887_ = lean_usize_dec_lt(v_i_2880_, v_sz_2879_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; 
v___x_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2888_, 0, v_bs_2881_);
return v___x_2888_;
}
else
{
lean_object* v___x_2889_; lean_object* v_lctx_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2918_; 
v___x_2889_ = lean_st_ref_take(v___y_2883_);
v_lctx_2890_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2918_ == 0)
{
lean_object* v_unused_2919_; 
v_unused_2919_ = lean_ctor_get(v___x_2889_, 1);
lean_dec(v_unused_2919_);
v___x_2892_ = v___x_2889_;
v_isShared_2893_ = v_isSharedCheck_2918_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_lctx_2890_);
lean_dec(v___x_2889_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2918_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2894_ = lean_unsigned_to_nat(1u);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 1, v___x_2894_);
v___x_2896_ = v___x_2892_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_lctx_2890_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2897_; lean_object* v_v_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; uint8_t v___x_2901_; lean_object* v___x_2902_; 
v___x_2897_ = lean_st_ref_set(v___y_2883_, v___x_2896_);
v_v_2898_ = lean_array_uget_borrowed(v_bs_2881_, v_i_2880_);
v___x_2899_ = lean_unsigned_to_nat(0u);
v___x_2900_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_2901_ = 0;
lean_inc(v_v_2898_);
v___x_2902_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_2878_, v_v_2898_, v___x_2900_, v___x_2901_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v_bs_x27_2904_; size_t v___x_2905_; size_t v___x_2906_; lean_object* v___x_2907_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2903_);
lean_dec_ref(v___x_2902_);
v_bs_x27_2904_ = lean_array_uset(v_bs_2881_, v_i_2880_, v___x_2899_);
v___x_2905_ = ((size_t)1ULL);
v___x_2906_ = lean_usize_add(v_i_2880_, v___x_2905_);
v___x_2907_ = lean_array_uset(v_bs_x27_2904_, v_i_2880_, v_a_2903_);
v_i_2880_ = v___x_2906_;
v_bs_2881_ = v___x_2907_;
goto _start;
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
lean_dec_ref(v_bs_2881_);
v_a_2909_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2902_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2902_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___boxed(lean_object* v_pu_2920_, lean_object* v_sz_2921_, lean_object* v_i_2922_, lean_object* v_bs_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
uint8_t v_pu_boxed_2929_; size_t v_sz_boxed_2930_; size_t v_i_boxed_2931_; lean_object* v_res_2932_; 
v_pu_boxed_2929_ = lean_unbox(v_pu_2920_);
v_sz_boxed_2930_ = lean_unbox_usize(v_sz_2921_);
lean_dec(v_sz_2921_);
v_i_boxed_2931_ = lean_unbox_usize(v_i_2922_);
lean_dec(v_i_2922_);
v_res_2932_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_boxed_2929_, v_sz_boxed_2930_, v_i_boxed_2931_, v_bs_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
return v_res_2932_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__0(void){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_2934_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
lean_ctor_set(v___x_2934_, 2, v___x_2933_);
lean_ctor_set(v___x_2934_, 3, v___x_2933_);
lean_ctor_set(v___x_2934_, 4, v___x_2933_);
lean_ctor_set(v___x_2934_, 5, v___x_2933_);
return v___x_2934_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__1(void){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2935_ = lean_unsigned_to_nat(1u);
v___x_2936_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__0, &l_Lean_Compiler_LCNF_cleanup___closed__0_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__0);
v___x_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
lean_ctor_set(v___x_2937_, 1, v___x_2935_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup(uint8_t v_pu_2938_, lean_object* v_decl_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; size_t v_sz_2948_; size_t v___x_2949_; lean_object* v___x_2950_; 
v___x_2945_ = lean_st_ref_take(v_a_2941_);
lean_dec(v___x_2945_);
v___x_2946_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
v___x_2947_ = lean_st_ref_set(v_a_2941_, v___x_2946_);
v_sz_2948_ = lean_array_size(v_decl_2939_);
v___x_2949_ = ((size_t)0ULL);
v___x_2950_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_2938_, v_sz_2948_, v___x_2949_, v_decl_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup___boxed(lean_object* v_pu_2951_, lean_object* v_decl_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_){
_start:
{
uint8_t v_pu_boxed_2958_; lean_object* v_res_2959_; 
v_pu_boxed_2958_ = lean_unbox(v_pu_2951_);
v_res_2959_ = l_Lean_Compiler_LCNF_cleanup(v_pu_boxed_2958_, v_decl_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(lean_object* v_a_2960_, lean_object* v_ngen_2961_, lean_object* v_a_x3f_2962_){
_start:
{
lean_object* v___x_2964_; lean_object* v_env_2965_; lean_object* v_nextMacroScope_2966_; lean_object* v_auxDeclNGen_2967_; lean_object* v_traceState_2968_; lean_object* v_cache_2969_; lean_object* v_messages_2970_; lean_object* v_infoState_2971_; lean_object* v_snapshotTasks_2972_; lean_object* v_newDecls_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2983_; 
v___x_2964_ = lean_st_ref_take(v_a_2960_);
v_env_2965_ = lean_ctor_get(v___x_2964_, 0);
v_nextMacroScope_2966_ = lean_ctor_get(v___x_2964_, 1);
v_auxDeclNGen_2967_ = lean_ctor_get(v___x_2964_, 3);
v_traceState_2968_ = lean_ctor_get(v___x_2964_, 4);
v_cache_2969_ = lean_ctor_get(v___x_2964_, 5);
v_messages_2970_ = lean_ctor_get(v___x_2964_, 6);
v_infoState_2971_ = lean_ctor_get(v___x_2964_, 7);
v_snapshotTasks_2972_ = lean_ctor_get(v___x_2964_, 8);
v_newDecls_2973_ = lean_ctor_get(v___x_2964_, 9);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2983_ == 0)
{
lean_object* v_unused_2984_; 
v_unused_2984_ = lean_ctor_get(v___x_2964_, 2);
lean_dec(v_unused_2984_);
v___x_2975_ = v___x_2964_;
v_isShared_2976_ = v_isSharedCheck_2983_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_newDecls_2973_);
lean_inc(v_snapshotTasks_2972_);
lean_inc(v_infoState_2971_);
lean_inc(v_messages_2970_);
lean_inc(v_cache_2969_);
lean_inc(v_traceState_2968_);
lean_inc(v_auxDeclNGen_2967_);
lean_inc(v_nextMacroScope_2966_);
lean_inc(v_env_2965_);
lean_dec(v___x_2964_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2983_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 2, v_ngen_2961_);
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_env_2965_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_nextMacroScope_2966_);
lean_ctor_set(v_reuseFailAlloc_2982_, 2, v_ngen_2961_);
lean_ctor_set(v_reuseFailAlloc_2982_, 3, v_auxDeclNGen_2967_);
lean_ctor_set(v_reuseFailAlloc_2982_, 4, v_traceState_2968_);
lean_ctor_set(v_reuseFailAlloc_2982_, 5, v_cache_2969_);
lean_ctor_set(v_reuseFailAlloc_2982_, 6, v_messages_2970_);
lean_ctor_set(v_reuseFailAlloc_2982_, 7, v_infoState_2971_);
lean_ctor_set(v_reuseFailAlloc_2982_, 8, v_snapshotTasks_2972_);
lean_ctor_set(v_reuseFailAlloc_2982_, 9, v_newDecls_2973_);
v___x_2978_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2979_ = lean_st_ref_set(v_a_2960_, v___x_2978_);
v___x_2980_ = lean_box(0);
v___x_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
return v___x_2981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0___boxed(lean_object* v_a_2985_, lean_object* v_ngen_2986_, lean_object* v_a_x3f_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_2985_, v_ngen_2986_, v_a_x3f_2987_);
lean_dec(v_a_x3f_2987_);
lean_dec(v_a_2985_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(uint8_t v_pu_2996_, lean_object* v_decl_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v_env_3003_; lean_object* v_nextMacroScope_3004_; lean_object* v_auxDeclNGen_3005_; lean_object* v_traceState_3006_; lean_object* v_cache_3007_; lean_object* v_messages_3008_; lean_object* v_infoState_3009_; lean_object* v_snapshotTasks_3010_; lean_object* v_newDecls_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3057_; 
v___x_3001_ = lean_st_ref_get(v_a_2999_);
v___x_3002_ = lean_st_ref_take(v_a_2999_);
v_env_3003_ = lean_ctor_get(v___x_3002_, 0);
v_nextMacroScope_3004_ = lean_ctor_get(v___x_3002_, 1);
v_auxDeclNGen_3005_ = lean_ctor_get(v___x_3002_, 3);
v_traceState_3006_ = lean_ctor_get(v___x_3002_, 4);
v_cache_3007_ = lean_ctor_get(v___x_3002_, 5);
v_messages_3008_ = lean_ctor_get(v___x_3002_, 6);
v_infoState_3009_ = lean_ctor_get(v___x_3002_, 7);
v_snapshotTasks_3010_ = lean_ctor_get(v___x_3002_, 8);
v_newDecls_3011_ = lean_ctor_get(v___x_3002_, 9);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3057_ == 0)
{
lean_object* v_unused_3058_; 
v_unused_3058_ = lean_ctor_get(v___x_3002_, 2);
lean_dec(v_unused_3058_);
v___x_3013_ = v___x_3002_;
v_isShared_3014_ = v_isSharedCheck_3057_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_newDecls_3011_);
lean_inc(v_snapshotTasks_3010_);
lean_inc(v_infoState_3009_);
lean_inc(v_messages_3008_);
lean_inc(v_cache_3007_);
lean_inc(v_traceState_3006_);
lean_inc(v_auxDeclNGen_3005_);
lean_inc(v_nextMacroScope_3004_);
lean_inc(v_env_3003_);
lean_dec(v___x_3002_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3057_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3015_; lean_object* v___x_3017_; 
v___x_3015_ = ((lean_object*)(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2));
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 2, v___x_3015_);
v___x_3017_ = v___x_3013_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_env_3003_);
lean_ctor_set(v_reuseFailAlloc_3056_, 1, v_nextMacroScope_3004_);
lean_ctor_set(v_reuseFailAlloc_3056_, 2, v___x_3015_);
lean_ctor_set(v_reuseFailAlloc_3056_, 3, v_auxDeclNGen_3005_);
lean_ctor_set(v_reuseFailAlloc_3056_, 4, v_traceState_3006_);
lean_ctor_set(v_reuseFailAlloc_3056_, 5, v_cache_3007_);
lean_ctor_set(v_reuseFailAlloc_3056_, 6, v_messages_3008_);
lean_ctor_set(v_reuseFailAlloc_3056_, 7, v_infoState_3009_);
lean_ctor_set(v_reuseFailAlloc_3056_, 8, v_snapshotTasks_3010_);
lean_ctor_set(v_reuseFailAlloc_3056_, 9, v_newDecls_3011_);
v___x_3017_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
lean_object* v___x_3018_; lean_object* v_ngen_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; uint8_t v___x_3026_; lean_object* v_r_3027_; 
v___x_3018_ = lean_st_ref_set(v_a_2999_, v___x_3017_);
v_ngen_3019_ = lean_ctor_get(v___x_3001_, 2);
lean_inc_ref(v_ngen_3019_);
lean_dec(v___x_3001_);
v___x_3020_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
v___x_3021_ = 0;
v___x_3022_ = lean_box(v_pu_2996_);
v___x_3023_ = lean_box(v___x_3021_);
v___x_3024_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_internalize___boxed), 9, 4);
lean_closure_set(v___x_3024_, 0, v___x_3022_);
lean_closure_set(v___x_3024_, 1, v_decl_2997_);
lean_closure_set(v___x_3024_, 2, v___x_3020_);
lean_closure_set(v___x_3024_, 3, v___x_3023_);
v___x_3025_ = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
v___x_3026_ = 0;
v_r_3027_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v___x_3024_, v___x_3025_, v___x_3026_, v_a_2998_, v_a_2999_);
if (lean_obj_tag(v_r_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3044_; 
v_a_3028_ = lean_ctor_get(v_r_3027_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v_r_3027_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3030_ = v_r_3027_;
v_isShared_3031_ = v_isSharedCheck_3044_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v_r_3027_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3044_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
lean_inc(v_a_3028_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set_tag(v___x_3030_, 1);
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v___x_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
v___x_3034_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_2999_, v_ngen_3019_, v___x_3033_);
lean_dec_ref(v___x_3033_);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; 
v_unused_3042_ = lean_ctor_get(v___x_3034_, 0);
lean_dec(v_unused_3042_);
v___x_3036_ = v___x_3034_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_dec(v___x_3034_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v_a_3028_);
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3028_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
v_a_3045_ = lean_ctor_get(v_r_3027_, 0);
lean_inc(v_a_3045_);
lean_dec_ref(v_r_3027_);
v___x_3046_ = lean_box(0);
v___x_3047_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_2999_, v_ngen_3019_, v___x_3046_);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3054_ == 0)
{
lean_object* v_unused_3055_; 
v_unused_3055_ = lean_ctor_get(v___x_3047_, 0);
lean_dec(v_unused_3055_);
v___x_3049_ = v___x_3047_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_dec(v___x_3047_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
lean_ctor_set_tag(v___x_3049_, 1);
lean_ctor_set(v___x_3049_, 0, v_a_3045_);
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3045_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___boxed(lean_object* v_pu_3059_, lean_object* v_decl_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_){
_start:
{
uint8_t v_pu_boxed_3064_; lean_object* v_res_3065_; 
v_pu_boxed_3064_ = lean_unbox(v_pu_3059_);
v_res_3065_ = l_Lean_Compiler_LCNF_normalizeFVarIds(v_pu_boxed_3064_, v_decl_3060_, v_a_3061_, v_a_3062_);
lean_dec(v_a_3062_);
lean_dec_ref(v_a_3061_);
return v_res_3065_;
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
