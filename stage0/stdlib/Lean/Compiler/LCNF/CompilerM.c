// Lean compiler output
// Module: Lean.Compiler.LCNF.CompilerM
// Imports: public import Lean.Compiler.LCNF.LCtx public import Lean.Compiler.LCNF.ConfigOptions
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
uint8_t l_Lean_Expr_hasFVar(lean_object*);
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
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_toConfigOptions(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___aux__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParam(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(uint8_t, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseCode(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParams(uint8_t, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instInhabitedPhase_default;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instInhabitedPhase;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Phase_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instDecidableEqPhase(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableEqPhase___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toPurity___boxed(lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_instInhabitedState;
static lean_once_cell_t l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1;
static const lean_closure_object l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM = (const lean_object*)&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_getType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "unknown free variable "};
static const lean_object* l_Lean_Compiler_LCNF_getType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_getType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_getType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_getParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown parameter "};
static const lean_object* l_Lean_Compiler_LCNF_getParam___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_getParam___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_getParam___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getParam___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_getLetDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "unknown let-declaration "};
static const lean_object* l_Lean_Compiler_LCNF_getLetDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_getLetDecl___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_getLetDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getLetDecl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_getFunDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "unknown local function "};
static const lean_object* l_Lean_Compiler_LCNF_getFunDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_getFunDecl___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_getFunDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getFunDecl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "_private.Lean.Compiler.LCNF.CompilerM.0.Lean.Compiler.LCNF.normExprImp.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Compiler.LCNF.CompilerM"};
static const lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instInhabitedNormFVarResult = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp(uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_addSubst___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_addSubst___redArg___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_addSubst___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_addSubst___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore(uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_mkParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_y"};
static const lean_object* l_Lean_Compiler_LCNF_mkParam___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkParam___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 112, 10, 137, 239, 103, 163, 90)}};
static const lean_object* l_Lean_Compiler_LCNF_mkParam___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_mkParam___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_mkLetDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l_Lean_Compiler_LCNF_mkLetDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkLetDecl___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkLetDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkLetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l_Lean_Compiler_LCNF_mkLetDecl___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_mkLetDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_mkFunDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_f"};
static const lean_object* l_Lean_Compiler_LCNF_mkFunDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkFunDecl___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkFunDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkFunDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 65, 185, 154, 193, 83, 240, 170)}};
static const lean_object* l_Lean_Compiler_LCNF_mkFunDecl___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_mkFunDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "_jp"};
static const lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 69, 15, 56, 172, 246, 212, 179)}};
static const lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Data.PersistentHashMap"};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.PersistentHashMap.find!"};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "key is not in the map"};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_Compiler_LCNF_Phase_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Compiler_LCNF_Phase_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_Compiler_LCNF_Phase_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___redArg(lean_object* v_base_28_){
_start:
{
lean_inc(v_base_28_);
return v_base_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___redArg___boxed(lean_object* v_base_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Compiler_LCNF_Phase_base_elim___redArg(v_base_29_);
lean_dec(v_base_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_base_34_){
_start:
{
lean_inc(v_base_34_);
return v_base_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_base_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_Compiler_LCNF_Phase_base_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_base_38_);
lean_dec(v_base_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(lean_object* v_mono_41_){
_start:
{
lean_inc(v_mono_41_);
return v_mono_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___redArg___boxed(lean_object* v_mono_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(v_mono_42_);
lean_dec(v_mono_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_mono_47_){
_start:
{
lean_inc(v_mono_47_);
return v_mono_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_mono_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_Compiler_LCNF_Phase_mono_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_mono_51_);
lean_dec(v_mono_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(lean_object* v_impure_54_){
_start:
{
lean_inc(v_impure_54_);
return v_impure_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___redArg___boxed(lean_object* v_impure_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(v_impure_55_);
lean_dec(v_impure_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_impure_60_){
_start:
{
lean_inc(v_impure_60_);
return v_impure_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_impure_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_Compiler_LCNF_Phase_impure_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_impure_64_);
lean_dec(v_impure_64_);
return v_res_66_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_instInhabitedPhase_default(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_instInhabitedPhase(void){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Phase_ofNat(lean_object* v_n_69_){
_start:
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_nat_dec_le(v_n_69_, v___x_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_dec_le(v_n_69_, v___x_72_);
if (v___x_73_ == 0)
{
uint8_t v___x_74_; 
v___x_74_ = 2;
return v___x_74_;
}
else
{
uint8_t v___x_75_; 
v___x_75_ = 1;
return v___x_75_;
}
}
else
{
uint8_t v___x_76_; 
v___x_76_ = 0;
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ofNat___boxed(lean_object* v_n_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Lean_Compiler_LCNF_Phase_ofNat(v_n_77_);
lean_dec(v_n_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instDecidableEqPhase(uint8_t v_x_80_, uint8_t v_y_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_82_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_x_80_);
v___x_83_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_y_81_);
v___x_84_ = lean_nat_dec_eq(v___x_82_, v___x_83_);
lean_dec(v___x_83_);
lean_dec(v___x_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableEqPhase___boxed(lean_object* v_x_85_, lean_object* v_y_86_){
_start:
{
uint8_t v_x_13__boxed_87_; uint8_t v_y_14__boxed_88_; uint8_t v_res_89_; lean_object* v_r_90_; 
v_x_13__boxed_87_ = lean_unbox(v_x_85_);
v_y_14__boxed_88_ = lean_unbox(v_y_86_);
v_res_89_ = l_Lean_Compiler_LCNF_instDecidableEqPhase(v_x_13__boxed_87_, v_y_14__boxed_88_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t v_x_91_){
_start:
{
if (v_x_91_ == 2)
{
uint8_t v___x_92_; 
v___x_92_ = 1;
return v___x_92_;
}
else
{
uint8_t v___x_93_; 
v___x_93_ = 0;
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toPurity___boxed(lean_object* v_x_94_){
_start:
{
uint8_t v_x_23__boxed_95_; uint8_t v_res_96_; lean_object* v_r_97_; 
v_x_23__boxed_95_ = lean_unbox(v_x_94_);
v_res_96_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_x_23__boxed_95_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = lean_box(0);
v___x_99_ = lean_unsigned_to_nat(16u);
v___x_100_ = lean_mk_array(v___x_99_, v___x_98_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0);
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_101_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1);
v___x_105_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
lean_ctor_set(v___x_105_, 2, v___x_104_);
lean_ctor_set(v___x_105_, 3, v___x_104_);
lean_ctor_set(v___x_105_, 4, v___x_104_);
lean_ctor_set(v___x_105_, 5, v___x_104_);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_106_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default(void){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState(void){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default;
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0(void){
_start:
{
lean_object* v___x_111_; uint8_t v___x_112_; lean_object* v___x_113_; 
v___x_111_ = l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default;
v___x_112_ = 0;
v___x_113_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*1, v___x_112_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext(void){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default;
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(lean_object* v_00_u03b1_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_123_, 0, v___y_117_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object* v_00_u03b1_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(v_00_u03b1_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object* v_00_u03b1_132_, lean_object* v_00_u03b2_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v___x_141_; 
lean_inc(v___y_139_);
lean_inc_ref(v___y_138_);
lean_inc(v___y_137_);
lean_inc_ref(v___y_136_);
v___x_141_ = lean_apply_5(v___y_134_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, lean_box(0));
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_143_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_a_142_);
lean_dec_ref(v___x_141_);
lean_inc(v___y_139_);
lean_inc_ref(v___y_138_);
lean_inc(v___y_137_);
lean_inc_ref(v___y_136_);
v___x_143_ = lean_apply_6(v___y_135_, v_a_142_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, lean_box(0));
return v___x_143_;
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
lean_dec_ref(v___y_135_);
v_a_144_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_141_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_141_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object* v_00_u03b1_152_, lean_object* v_00_u03b2_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(v_00_u03b1_152_, v_00_u03b2_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
return v_res_161_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0(void){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_instMonadEIO(lean_box(0));
return v___x_162_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0);
v___x_164_ = l_StateRefT_x27_instMonad___redArg(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM(void){
_start:
{
lean_object* v___x_169_; lean_object* v_toApplicative_170_; lean_object* v_toFunctor_171_; lean_object* v_toSeq_172_; lean_object* v_toSeqLeft_173_; lean_object* v_toSeqRight_174_; lean_object* v___f_175_; lean_object* v___f_176_; lean_object* v___f_177_; lean_object* v___f_178_; lean_object* v___x_179_; lean_object* v___f_180_; lean_object* v___f_181_; lean_object* v___f_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v_toApplicative_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_213_; 
v___x_169_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_170_ = lean_ctor_get(v___x_169_, 0);
v_toFunctor_171_ = lean_ctor_get(v_toApplicative_170_, 0);
v_toSeq_172_ = lean_ctor_get(v_toApplicative_170_, 2);
v_toSeqLeft_173_ = lean_ctor_get(v_toApplicative_170_, 3);
v_toSeqRight_174_ = lean_ctor_get(v_toApplicative_170_, 4);
v___f_175_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_176_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_171_, 2);
v___f_177_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_177_, 0, v_toFunctor_171_);
v___f_178_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_178_, 0, v_toFunctor_171_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___f_177_);
lean_ctor_set(v___x_179_, 1, v___f_178_);
lean_inc(v_toSeqRight_174_);
v___f_180_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_180_, 0, v_toSeqRight_174_);
lean_inc(v_toSeqLeft_173_);
v___f_181_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_181_, 0, v_toSeqLeft_173_);
lean_inc(v_toSeq_172_);
v___f_182_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_182_, 0, v_toSeq_172_);
v___x_183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_183_, 0, v___x_179_);
lean_ctor_set(v___x_183_, 1, v___f_175_);
lean_ctor_set(v___x_183_, 2, v___f_182_);
lean_ctor_set(v___x_183_, 3, v___f_181_);
lean_ctor_set(v___x_183_, 4, v___f_180_);
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___f_176_);
v___x_185_ = l_StateRefT_x27_instMonad___redArg(v___x_184_);
v_toApplicative_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; 
v_unused_214_ = lean_ctor_get(v___x_185_, 1);
lean_dec(v_unused_214_);
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_213_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_toApplicative_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_213_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v_toFunctor_190_; lean_object* v_toSeq_191_; lean_object* v_toSeqLeft_192_; lean_object* v_toSeqRight_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_211_; 
v_toFunctor_190_ = lean_ctor_get(v_toApplicative_186_, 0);
v_toSeq_191_ = lean_ctor_get(v_toApplicative_186_, 2);
v_toSeqLeft_192_ = lean_ctor_get(v_toApplicative_186_, 3);
v_toSeqRight_193_ = lean_ctor_get(v_toApplicative_186_, 4);
v_isSharedCheck_211_ = !lean_is_exclusive(v_toApplicative_186_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; 
v_unused_212_ = lean_ctor_get(v_toApplicative_186_, 1);
lean_dec(v_unused_212_);
v___x_195_ = v_toApplicative_186_;
v_isShared_196_ = v_isSharedCheck_211_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_toSeqRight_193_);
lean_inc(v_toSeqLeft_192_);
lean_inc(v_toSeq_191_);
lean_inc(v_toFunctor_190_);
lean_dec(v_toApplicative_186_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_211_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___f_200_; lean_object* v___x_201_; lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___f_204_; lean_object* v___x_206_; 
v___f_197_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_198_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_190_);
v___f_199_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_199_, 0, v_toFunctor_190_);
v___f_200_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_200_, 0, v_toFunctor_190_);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___f_199_);
lean_ctor_set(v___x_201_, 1, v___f_200_);
v___f_202_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_202_, 0, v_toSeqRight_193_);
v___f_203_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_203_, 0, v_toSeqLeft_192_);
v___f_204_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_204_, 0, v_toSeq_191_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 4, v___f_202_);
lean_ctor_set(v___x_195_, 3, v___f_203_);
lean_ctor_set(v___x_195_, 2, v___f_204_);
lean_ctor_set(v___x_195_, 1, v___f_197_);
lean_ctor_set(v___x_195_, 0, v___x_201_);
v___x_206_ = v___x_195_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v___f_197_);
lean_ctor_set(v_reuseFailAlloc_210_, 2, v___f_204_);
lean_ctor_set(v_reuseFailAlloc_210_, 3, v___f_203_);
lean_ctor_set(v_reuseFailAlloc_210_, 4, v___f_202_);
v___x_206_ = v_reuseFailAlloc_210_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_208_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 1, v___f_198_);
lean_ctor_set(v___x_188_, 0, v___x_206_);
v___x_208_ = v___x_188_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v___f_198_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg(uint8_t v_phase_215_, lean_object* v_x_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_config_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_config_222_ = lean_ctor_get(v_a_217_, 0);
lean_inc_ref(v_config_222_);
v___x_223_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_223_, 0, v_config_222_);
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*1, v_phase_215_);
lean_inc(v_a_220_);
lean_inc_ref(v_a_219_);
lean_inc(v_a_218_);
v___x_224_ = lean_apply_5(v_x_216_, v___x_223_, v_a_218_, v_a_219_, v_a_220_, lean_box(0));
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg___boxed(lean_object* v_phase_225_, lean_object* v_x_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
uint8_t v_phase_boxed_232_; lean_object* v_res_233_; 
v_phase_boxed_232_ = lean_unbox(v_phase_225_);
v_res_233_ = l_Lean_Compiler_LCNF_withPhase___redArg(v_phase_boxed_232_, v_x_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase(lean_object* v_00_u03b1_234_, uint8_t v_phase_235_, lean_object* v_x_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_config_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_config_242_ = lean_ctor_get(v_a_237_, 0);
lean_inc_ref(v_config_242_);
v___x_243_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_243_, 0, v_config_242_);
lean_ctor_set_uint8(v___x_243_, sizeof(void*)*1, v_phase_235_);
lean_inc(v_a_240_);
lean_inc_ref(v_a_239_);
lean_inc(v_a_238_);
v___x_244_ = lean_apply_5(v_x_236_, v___x_243_, v_a_238_, v_a_239_, v_a_240_, lean_box(0));
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___boxed(lean_object* v_00_u03b1_245_, lean_object* v_phase_246_, lean_object* v_x_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
uint8_t v_phase_boxed_253_; lean_object* v_res_254_; 
v_phase_boxed_253_ = lean_unbox(v_phase_246_);
v_res_254_ = l_Lean_Compiler_LCNF_withPhase(v_00_u03b1_245_, v_phase_boxed_253_, v_x_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object* v_a_255_){
_start:
{
uint8_t v_phase_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_phase_257_ = lean_ctor_get_uint8(v_a_255_, sizeof(void*)*1);
v___x_258_ = lean_box(v_phase_257_);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg___boxed(lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_260_);
lean_dec_ref(v_a_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase(lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_263_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___boxed(lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Compiler_LCNF_getPhase(v_a_269_, v_a_270_, v_a_271_, v_a_272_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object* v_a_275_){
_start:
{
lean_object* v___x_277_; lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_288_; 
v___x_277_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_275_);
v_a_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_288_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_288_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_288_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
uint8_t v___x_282_; uint8_t v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_282_ = lean_unbox(v_a_278_);
lean_dec(v_a_278_);
v___x_283_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_282_);
v___x_284_ = lean_box(v___x_283_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_284_);
v___x_286_ = v___x_280_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg___boxed(lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_289_);
lean_dec_ref(v_a_289_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity(lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_292_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___boxed(lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Compiler_LCNF_getPurity(v_a_298_, v_a_299_, v_a_300_, v_a_301_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg(lean_object* v_a_304_){
_start:
{
lean_object* v___x_306_; lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_322_; 
v___x_306_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_304_);
v_a_307_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_322_ == 0)
{
v___x_309_ = v___x_306_;
v_isShared_310_ = v_isSharedCheck_322_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_306_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_322_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
uint8_t v___x_311_; 
v___x_311_ = lean_unbox(v_a_307_);
lean_dec(v_a_307_);
if (v___x_311_ == 0)
{
uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_312_ = 1;
v___x_313_ = lean_box(v___x_312_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_313_);
v___x_315_ = v___x_309_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
else
{
uint8_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_317_ = 0;
v___x_318_ = lean_box(v___x_317_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_318_);
v___x_320_ = v___x_309_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg___boxed(lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_323_);
lean_dec_ref(v_a_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase(lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_326_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___boxed(lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Compiler_LCNF_inBasePhase(v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
return v_res_337_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0(void){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_338_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1);
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
lean_ctor_set(v___x_343_, 2, v___x_342_);
lean_ctor_set(v___x_343_, 3, v___x_342_);
lean_ctor_set(v___x_343_, 4, v___x_341_);
lean_ctor_set(v___x_343_, 5, v___x_341_);
lean_ctor_set(v___x_343_, 6, v___x_341_);
lean_ctor_set(v___x_343_, 7, v___x_341_);
lean_ctor_set(v___x_343_, 8, v___x_341_);
lean_ctor_set(v___x_343_, 9, v___x_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(lean_object* v_msgData_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = lean_st_ref_get(v___y_348_);
v___x_351_ = lean_st_ref_get(v___y_346_);
v___x_352_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_345_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_375_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_375_ == 0)
{
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_375_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_375_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v_env_357_; lean_object* v_lctx_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_373_; 
v_env_357_ = lean_ctor_get(v___x_350_, 0);
lean_inc_ref(v_env_357_);
lean_dec(v___x_350_);
v_lctx_358_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; 
v_unused_374_ = lean_ctor_get(v___x_351_, 1);
lean_dec(v_unused_374_);
v___x_360_ = v___x_351_;
v_isShared_361_ = v_isSharedCheck_373_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_lctx_358_);
lean_dec(v___x_351_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_373_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v_options_362_; uint8_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v_options_362_ = lean_ctor_get(v___y_347_, 2);
v___x_363_ = lean_unbox(v_a_353_);
lean_dec(v_a_353_);
v___x_364_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_358_, v___x_363_);
lean_dec_ref(v_lctx_358_);
v___x_365_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_362_);
v___x_366_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_366_, 0, v_env_357_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
lean_ctor_set(v___x_366_, 2, v___x_364_);
lean_ctor_set(v___x_366_, 3, v_options_362_);
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 3);
lean_ctor_set(v___x_360_, 1, v_msgData_344_);
lean_ctor_set(v___x_360_, 0, v___x_366_);
v___x_368_ = v___x_360_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_msgData_344_);
v___x_368_ = v_reuseFailAlloc_372_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_370_; 
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_368_);
v___x_370_ = v___x_355_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec(v___x_351_);
lean_dec(v___x_350_);
lean_dec_ref(v_msgData_344_);
v_a_376_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_352_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_352_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed(lean_object* v_msgData_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(v_msgData_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(lean_object* v_msg_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_options_399_; lean_object* v_ref_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_options_399_ = lean_ctor_get(v___y_396_, 2);
v_ref_400_ = lean_ctor_get(v___y_396_, 5);
v___x_401_ = lean_st_ref_get(v___y_397_);
v___x_402_ = lean_st_ref_get(v___y_395_);
v___x_403_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_394_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_426_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_426_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_426_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_426_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v_env_408_; lean_object* v_lctx_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_424_; 
v_env_408_ = lean_ctor_get(v___x_401_, 0);
lean_inc_ref(v_env_408_);
lean_dec(v___x_401_);
v_lctx_409_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v___x_402_, 1);
lean_dec(v_unused_425_);
v___x_411_ = v___x_402_;
v_isShared_412_ = v_isSharedCheck_424_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_lctx_409_);
lean_dec(v___x_402_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_424_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
uint8_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_413_ = lean_unbox(v_a_404_);
lean_dec(v_a_404_);
v___x_414_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_409_, v___x_413_);
lean_dec_ref(v_lctx_409_);
v___x_415_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_399_);
v___x_416_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_416_, 0, v_env_408_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
lean_ctor_set(v___x_416_, 2, v___x_414_);
lean_ctor_set(v___x_416_, 3, v_options_399_);
if (v_isShared_412_ == 0)
{
lean_ctor_set_tag(v___x_411_, 3);
lean_ctor_set(v___x_411_, 1, v_msg_393_);
lean_ctor_set(v___x_411_, 0, v___x_416_);
v___x_418_ = v___x_411_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_msg_393_);
v___x_418_ = v_reuseFailAlloc_423_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
lean_inc(v_ref_400_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v_ref_400_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 1);
lean_ctor_set(v___x_406_, 0, v___x_419_);
v___x_421_ = v___x_406_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec(v___x_402_);
lean_dec(v___x_401_);
lean_dec_ref(v_msg_393_);
v_a_427_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_403_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_403_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg___boxed(lean_object* v_msg_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(lean_object* v_00_u03b1_442_, lean_object* v_msg_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___boxed(lean_object* v_00_u03b1_450_, lean_object* v_msg_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(v_00_u03b1_450_, v_msg_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(lean_object* v_a_458_, lean_object* v_x_459_){
_start:
{
if (lean_obj_tag(v_x_459_) == 0)
{
lean_object* v___x_460_; 
v___x_460_ = lean_box(0);
return v___x_460_;
}
else
{
lean_object* v_key_461_; lean_object* v_value_462_; lean_object* v_tail_463_; uint8_t v___x_464_; 
v_key_461_ = lean_ctor_get(v_x_459_, 0);
v_value_462_ = lean_ctor_get(v_x_459_, 1);
v_tail_463_ = lean_ctor_get(v_x_459_, 2);
v___x_464_ = l_Lean_instBEqFVarId_beq(v_key_461_, v_a_458_);
if (v___x_464_ == 0)
{
v_x_459_ = v_tail_463_;
goto _start;
}
else
{
lean_object* v___x_466_; 
lean_inc(v_value_462_);
v___x_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_466_, 0, v_value_462_);
return v___x_466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg___boxed(lean_object* v_a_467_, lean_object* v_x_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_467_, v_x_468_);
lean_dec(v_x_468_);
lean_dec(v_a_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object* v_m_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_buckets_472_; lean_object* v___x_473_; uint64_t v___x_474_; uint64_t v___x_475_; uint64_t v___x_476_; uint64_t v_fold_477_; uint64_t v___x_478_; uint64_t v___x_479_; uint64_t v___x_480_; size_t v___x_481_; size_t v___x_482_; size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v_buckets_472_ = lean_ctor_get(v_m_470_, 1);
v___x_473_ = lean_array_get_size(v_buckets_472_);
v___x_474_ = l_Lean_instHashableFVarId_hash(v_a_471_);
v___x_475_ = 32ULL;
v___x_476_ = lean_uint64_shift_right(v___x_474_, v___x_475_);
v_fold_477_ = lean_uint64_xor(v___x_474_, v___x_476_);
v___x_478_ = 16ULL;
v___x_479_ = lean_uint64_shift_right(v_fold_477_, v___x_478_);
v___x_480_ = lean_uint64_xor(v_fold_477_, v___x_479_);
v___x_481_ = lean_uint64_to_usize(v___x_480_);
v___x_482_ = lean_usize_of_nat(v___x_473_);
v___x_483_ = ((size_t)1ULL);
v___x_484_ = lean_usize_sub(v___x_482_, v___x_483_);
v___x_485_ = lean_usize_land(v___x_481_, v___x_484_);
v___x_486_ = lean_array_uget_borrowed(v_buckets_472_, v___x_485_);
v___x_487_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_471_, v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg___boxed(lean_object* v_m_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_488_, v_a_489_);
lean_dec(v_a_489_);
lean_dec_ref(v_m_488_);
return v_res_490_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getType___closed__1(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l_Lean_Compiler_LCNF_getType___closed__0));
v___x_493_ = l_Lean_stringToMessageData(v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType(lean_object* v_fvarId_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_st_ref_get(v_a_496_);
v___x_501_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_495_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_552_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_552_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_552_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_552_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___y_507_; lean_object* v_lctx_518_; lean_object* v___y_520_; lean_object* v___y_535_; uint8_t v___x_549_; 
v_lctx_518_ = lean_ctor_get(v___x_500_, 0);
lean_inc_ref(v_lctx_518_);
lean_dec(v___x_500_);
v___x_549_ = lean_unbox(v_a_502_);
if (v___x_549_ == 0)
{
lean_object* v_letDeclsPure_550_; 
v_letDeclsPure_550_ = lean_ctor_get(v_lctx_518_, 2);
lean_inc_ref(v_letDeclsPure_550_);
v___y_535_ = v_letDeclsPure_550_;
goto v___jp_534_;
}
else
{
lean_object* v_letDeclsImpure_551_; 
v_letDeclsImpure_551_ = lean_ctor_get(v_lctx_518_, 3);
lean_inc_ref(v_letDeclsImpure_551_);
v___y_535_ = v_letDeclsImpure_551_;
goto v___jp_534_;
}
v___jp_506_:
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_507_, v_fvarId_494_);
lean_dec_ref(v___y_507_);
if (lean_obj_tag(v___x_508_) == 1)
{
lean_object* v_val_509_; lean_object* v_type_510_; lean_object* v___x_512_; 
lean_dec(v_fvarId_494_);
v_val_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_val_509_);
lean_dec_ref(v___x_508_);
v_type_510_ = lean_ctor_get(v_val_509_, 3);
lean_inc_ref(v_type_510_);
lean_dec(v_val_509_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v_type_510_);
v___x_512_ = v___x_504_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_type_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec(v___x_508_);
lean_del_object(v___x_504_);
v___x_514_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_515_ = l_Lean_MessageData_ofName(v_fvarId_494_);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_516_, v_a_495_, v_a_496_, v_a_497_, v_a_498_);
return v___x_517_;
}
}
v___jp_519_:
{
lean_object* v___x_521_; 
v___x_521_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_520_, v_fvarId_494_);
lean_dec_ref(v___y_520_);
if (lean_obj_tag(v___x_521_) == 1)
{
lean_object* v_val_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_530_; 
lean_dec_ref(v_lctx_518_);
lean_del_object(v___x_504_);
lean_dec(v_a_502_);
lean_dec(v_fvarId_494_);
v_val_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_530_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_val_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_type_526_; lean_object* v___x_528_; 
v_type_526_ = lean_ctor_get(v_val_522_, 2);
lean_inc_ref(v_type_526_);
lean_dec(v_val_522_);
if (v_isShared_525_ == 0)
{
lean_ctor_set_tag(v___x_524_, 0);
lean_ctor_set(v___x_524_, 0, v_type_526_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_type_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
else
{
uint8_t v___x_531_; 
lean_dec(v___x_521_);
v___x_531_ = lean_unbox(v_a_502_);
lean_dec(v_a_502_);
if (v___x_531_ == 0)
{
lean_object* v_funDeclsPure_532_; 
v_funDeclsPure_532_ = lean_ctor_get(v_lctx_518_, 4);
lean_inc_ref(v_funDeclsPure_532_);
lean_dec_ref(v_lctx_518_);
v___y_507_ = v_funDeclsPure_532_;
goto v___jp_506_;
}
else
{
lean_object* v_funDeclsImpure_533_; 
v_funDeclsImpure_533_ = lean_ctor_get(v_lctx_518_, 5);
lean_inc_ref(v_funDeclsImpure_533_);
lean_dec_ref(v_lctx_518_);
v___y_507_ = v_funDeclsImpure_533_;
goto v___jp_506_;
}
}
}
v___jp_534_:
{
lean_object* v___x_536_; 
v___x_536_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_535_, v_fvarId_494_);
lean_dec_ref(v___y_535_);
if (lean_obj_tag(v___x_536_) == 1)
{
lean_object* v_val_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_545_; 
lean_dec_ref(v_lctx_518_);
lean_del_object(v___x_504_);
lean_dec(v_a_502_);
lean_dec(v_fvarId_494_);
v_val_537_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_545_ == 0)
{
v___x_539_ = v___x_536_;
v_isShared_540_ = v_isSharedCheck_545_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_val_537_);
lean_dec(v___x_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_545_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v_type_541_; lean_object* v___x_543_; 
v_type_541_ = lean_ctor_get(v_val_537_, 2);
lean_inc_ref(v_type_541_);
lean_dec(v_val_537_);
if (v_isShared_540_ == 0)
{
lean_ctor_set_tag(v___x_539_, 0);
lean_ctor_set(v___x_539_, 0, v_type_541_);
v___x_543_ = v___x_539_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_type_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
else
{
uint8_t v___x_546_; 
lean_dec(v___x_536_);
v___x_546_ = lean_unbox(v_a_502_);
if (v___x_546_ == 0)
{
lean_object* v_paramsPure_547_; 
v_paramsPure_547_ = lean_ctor_get(v_lctx_518_, 0);
lean_inc_ref(v_paramsPure_547_);
v___y_520_ = v_paramsPure_547_;
goto v___jp_519_;
}
else
{
lean_object* v_paramsImpure_548_; 
v_paramsImpure_548_ = lean_ctor_get(v_lctx_518_, 1);
lean_inc_ref(v_paramsImpure_548_);
v___y_520_ = v_paramsImpure_548_;
goto v___jp_519_;
}
}
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec(v___x_500_);
lean_dec(v_fvarId_494_);
v_a_553_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_501_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_501_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType___boxed(lean_object* v_fvarId_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Compiler_LCNF_getType(v_fvarId_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(lean_object* v_00_u03b2_568_, lean_object* v_m_569_, lean_object* v_a_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_569_, v_a_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___boxed(lean_object* v_00_u03b2_572_, lean_object* v_m_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(v_00_u03b2_572_, v_m_573_, v_a_574_);
lean_dec(v_a_574_);
lean_dec_ref(v_m_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(lean_object* v_00_u03b2_576_, lean_object* v_a_577_, lean_object* v_x_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_577_, v_x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_580_, lean_object* v_a_581_, lean_object* v_x_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(v_00_u03b2_580_, v_a_581_, v_x_582_);
lean_dec(v_x_582_);
lean_dec(v_a_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object* v_fvarId_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_st_ref_get(v_a_586_);
v___x_591_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_585_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_642_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_642_ == 0)
{
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_642_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_642_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___y_597_; lean_object* v_lctx_608_; lean_object* v___y_610_; lean_object* v___y_625_; uint8_t v___x_639_; 
v_lctx_608_ = lean_ctor_get(v___x_590_, 0);
lean_inc_ref(v_lctx_608_);
lean_dec(v___x_590_);
v___x_639_ = lean_unbox(v_a_592_);
if (v___x_639_ == 0)
{
lean_object* v_letDeclsPure_640_; 
v_letDeclsPure_640_ = lean_ctor_get(v_lctx_608_, 2);
lean_inc_ref(v_letDeclsPure_640_);
v___y_625_ = v_letDeclsPure_640_;
goto v___jp_624_;
}
else
{
lean_object* v_letDeclsImpure_641_; 
v_letDeclsImpure_641_ = lean_ctor_get(v_lctx_608_, 3);
lean_inc_ref(v_letDeclsImpure_641_);
v___y_625_ = v_letDeclsImpure_641_;
goto v___jp_624_;
}
v___jp_596_:
{
lean_object* v___x_598_; 
v___x_598_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_597_, v_fvarId_584_);
lean_dec_ref(v___y_597_);
if (lean_obj_tag(v___x_598_) == 1)
{
lean_object* v_val_599_; lean_object* v_binderName_600_; lean_object* v___x_602_; 
lean_dec(v_fvarId_584_);
v_val_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_val_599_);
lean_dec_ref(v___x_598_);
v_binderName_600_ = lean_ctor_get(v_val_599_, 1);
lean_inc(v_binderName_600_);
lean_dec(v_val_599_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v_binderName_600_);
v___x_602_ = v___x_594_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_binderName_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
lean_dec(v___x_598_);
lean_del_object(v___x_594_);
v___x_604_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_605_ = l_Lean_MessageData_ofName(v_fvarId_584_);
v___x_606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_606_, v_a_585_, v_a_586_, v_a_587_, v_a_588_);
return v___x_607_;
}
}
v___jp_609_:
{
lean_object* v___x_611_; 
v___x_611_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_610_, v_fvarId_584_);
lean_dec_ref(v___y_610_);
if (lean_obj_tag(v___x_611_) == 1)
{
lean_object* v_val_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_620_; 
lean_dec_ref(v_lctx_608_);
lean_del_object(v___x_594_);
lean_dec(v_a_592_);
lean_dec(v_fvarId_584_);
v_val_612_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_620_ == 0)
{
v___x_614_ = v___x_611_;
v_isShared_615_ = v_isSharedCheck_620_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_val_612_);
lean_dec(v___x_611_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_620_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_binderName_616_; lean_object* v___x_618_; 
v_binderName_616_ = lean_ctor_get(v_val_612_, 1);
lean_inc(v_binderName_616_);
lean_dec(v_val_612_);
if (v_isShared_615_ == 0)
{
lean_ctor_set_tag(v___x_614_, 0);
lean_ctor_set(v___x_614_, 0, v_binderName_616_);
v___x_618_ = v___x_614_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_binderName_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
else
{
uint8_t v___x_621_; 
lean_dec(v___x_611_);
v___x_621_ = lean_unbox(v_a_592_);
lean_dec(v_a_592_);
if (v___x_621_ == 0)
{
lean_object* v_funDeclsPure_622_; 
v_funDeclsPure_622_ = lean_ctor_get(v_lctx_608_, 4);
lean_inc_ref(v_funDeclsPure_622_);
lean_dec_ref(v_lctx_608_);
v___y_597_ = v_funDeclsPure_622_;
goto v___jp_596_;
}
else
{
lean_object* v_funDeclsImpure_623_; 
v_funDeclsImpure_623_ = lean_ctor_get(v_lctx_608_, 5);
lean_inc_ref(v_funDeclsImpure_623_);
lean_dec_ref(v_lctx_608_);
v___y_597_ = v_funDeclsImpure_623_;
goto v___jp_596_;
}
}
}
v___jp_624_:
{
lean_object* v___x_626_; 
v___x_626_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_625_, v_fvarId_584_);
lean_dec_ref(v___y_625_);
if (lean_obj_tag(v___x_626_) == 1)
{
lean_object* v_val_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref(v_lctx_608_);
lean_del_object(v___x_594_);
lean_dec(v_a_592_);
lean_dec(v_fvarId_584_);
v_val_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_635_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_val_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v_binderName_631_; lean_object* v___x_633_; 
v_binderName_631_ = lean_ctor_get(v_val_627_, 1);
lean_inc(v_binderName_631_);
lean_dec(v_val_627_);
if (v_isShared_630_ == 0)
{
lean_ctor_set_tag(v___x_629_, 0);
lean_ctor_set(v___x_629_, 0, v_binderName_631_);
v___x_633_ = v___x_629_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_binderName_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
else
{
uint8_t v___x_636_; 
lean_dec(v___x_626_);
v___x_636_ = lean_unbox(v_a_592_);
if (v___x_636_ == 0)
{
lean_object* v_paramsPure_637_; 
v_paramsPure_637_ = lean_ctor_get(v_lctx_608_, 0);
lean_inc_ref(v_paramsPure_637_);
v___y_610_ = v_paramsPure_637_;
goto v___jp_609_;
}
else
{
lean_object* v_paramsImpure_638_; 
v_paramsImpure_638_ = lean_ctor_get(v_lctx_608_, 1);
lean_inc_ref(v_paramsImpure_638_);
v___y_610_ = v_paramsImpure_638_;
goto v___jp_609_;
}
}
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec(v___x_590_);
lean_dec(v_fvarId_584_);
v_a_643_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_591_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_591_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName___boxed(lean_object* v_fvarId_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t v_pu_658_, lean_object* v_fvarId_659_, lean_object* v_a_660_){
_start:
{
lean_object* v___x_662_; lean_object* v___y_664_; 
v___x_662_ = lean_st_ref_get(v_a_660_);
if (v_pu_658_ == 0)
{
lean_object* v_lctx_667_; lean_object* v_paramsPure_668_; 
v_lctx_667_ = lean_ctor_get(v___x_662_, 0);
lean_inc_ref(v_lctx_667_);
lean_dec(v___x_662_);
v_paramsPure_668_ = lean_ctor_get(v_lctx_667_, 0);
lean_inc_ref(v_paramsPure_668_);
lean_dec_ref(v_lctx_667_);
v___y_664_ = v_paramsPure_668_;
goto v___jp_663_;
}
else
{
lean_object* v_lctx_669_; lean_object* v_paramsImpure_670_; 
v_lctx_669_ = lean_ctor_get(v___x_662_, 0);
lean_inc_ref(v_lctx_669_);
lean_dec(v___x_662_);
v_paramsImpure_670_ = lean_ctor_get(v_lctx_669_, 1);
lean_inc_ref(v_paramsImpure_670_);
lean_dec_ref(v_lctx_669_);
v___y_664_ = v_paramsImpure_670_;
goto v___jp_663_;
}
v___jp_663_:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_664_, v_fvarId_659_);
lean_dec_ref(v___y_664_);
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
return v___x_666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg___boxed(lean_object* v_pu_671_, lean_object* v_fvarId_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
uint8_t v_pu_boxed_675_; lean_object* v_res_676_; 
v_pu_boxed_675_ = lean_unbox(v_pu_671_);
v_res_676_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_boxed_675_, v_fvarId_672_, v_a_673_);
lean_dec(v_a_673_);
lean_dec(v_fvarId_672_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f(uint8_t v_pu_677_, lean_object* v_fvarId_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_677_, v_fvarId_678_, v_a_680_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___boxed(lean_object* v_pu_685_, lean_object* v_fvarId_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
uint8_t v_pu_boxed_692_; lean_object* v_res_693_; 
v_pu_boxed_692_ = lean_unbox(v_pu_685_);
v_res_693_ = l_Lean_Compiler_LCNF_findParam_x3f(v_pu_boxed_692_, v_fvarId_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_fvarId_686_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t v_pu_694_, lean_object* v_fvarId_695_, lean_object* v_a_696_){
_start:
{
lean_object* v___x_698_; lean_object* v___y_700_; 
v___x_698_ = lean_st_ref_get(v_a_696_);
if (v_pu_694_ == 0)
{
lean_object* v_lctx_703_; lean_object* v_letDeclsPure_704_; 
v_lctx_703_ = lean_ctor_get(v___x_698_, 0);
lean_inc_ref(v_lctx_703_);
lean_dec(v___x_698_);
v_letDeclsPure_704_ = lean_ctor_get(v_lctx_703_, 2);
lean_inc_ref(v_letDeclsPure_704_);
lean_dec_ref(v_lctx_703_);
v___y_700_ = v_letDeclsPure_704_;
goto v___jp_699_;
}
else
{
lean_object* v_lctx_705_; lean_object* v_letDeclsImpure_706_; 
v_lctx_705_ = lean_ctor_get(v___x_698_, 0);
lean_inc_ref(v_lctx_705_);
lean_dec(v___x_698_);
v_letDeclsImpure_706_ = lean_ctor_get(v_lctx_705_, 3);
lean_inc_ref(v_letDeclsImpure_706_);
lean_dec_ref(v_lctx_705_);
v___y_700_ = v_letDeclsImpure_706_;
goto v___jp_699_;
}
v___jp_699_:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_700_, v_fvarId_695_);
lean_dec_ref(v___y_700_);
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg___boxed(lean_object* v_pu_707_, lean_object* v_fvarId_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
uint8_t v_pu_boxed_711_; lean_object* v_res_712_; 
v_pu_boxed_711_ = lean_unbox(v_pu_707_);
v_res_712_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_boxed_711_, v_fvarId_708_, v_a_709_);
lean_dec(v_a_709_);
lean_dec(v_fvarId_708_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(uint8_t v_pu_713_, lean_object* v_fvarId_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_713_, v_fvarId_714_, v_a_716_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___boxed(lean_object* v_pu_721_, lean_object* v_fvarId_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
uint8_t v_pu_boxed_728_; lean_object* v_res_729_; 
v_pu_boxed_728_ = lean_unbox(v_pu_721_);
v_res_729_ = l_Lean_Compiler_LCNF_findLetDecl_x3f(v_pu_boxed_728_, v_fvarId_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
lean_dec(v_fvarId_722_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t v_pu_730_, lean_object* v_fvarId_731_, lean_object* v_a_732_){
_start:
{
lean_object* v___x_734_; lean_object* v___y_736_; 
v___x_734_ = lean_st_ref_get(v_a_732_);
if (v_pu_730_ == 0)
{
lean_object* v_lctx_739_; lean_object* v_funDeclsPure_740_; 
v_lctx_739_ = lean_ctor_get(v___x_734_, 0);
lean_inc_ref(v_lctx_739_);
lean_dec(v___x_734_);
v_funDeclsPure_740_ = lean_ctor_get(v_lctx_739_, 4);
lean_inc_ref(v_funDeclsPure_740_);
lean_dec_ref(v_lctx_739_);
v___y_736_ = v_funDeclsPure_740_;
goto v___jp_735_;
}
else
{
lean_object* v_lctx_741_; lean_object* v_funDeclsImpure_742_; 
v_lctx_741_ = lean_ctor_get(v___x_734_, 0);
lean_inc_ref(v_lctx_741_);
lean_dec(v___x_734_);
v_funDeclsImpure_742_ = lean_ctor_get(v_lctx_741_, 5);
lean_inc_ref(v_funDeclsImpure_742_);
lean_dec_ref(v_lctx_741_);
v___y_736_ = v_funDeclsImpure_742_;
goto v___jp_735_;
}
v___jp_735_:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_736_, v_fvarId_731_);
lean_dec_ref(v___y_736_);
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg___boxed(lean_object* v_pu_743_, lean_object* v_fvarId_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
uint8_t v_pu_boxed_747_; lean_object* v_res_748_; 
v_pu_boxed_747_ = lean_unbox(v_pu_743_);
v_res_748_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_boxed_747_, v_fvarId_744_, v_a_745_);
lean_dec(v_a_745_);
lean_dec(v_fvarId_744_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(uint8_t v_pu_749_, lean_object* v_fvarId_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_749_, v_fvarId_750_, v_a_752_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___boxed(lean_object* v_pu_757_, lean_object* v_fvarId_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
uint8_t v_pu_boxed_764_; lean_object* v_res_765_; 
v_pu_boxed_764_ = lean_unbox(v_pu_757_);
v_res_765_ = l_Lean_Compiler_LCNF_findFunDecl_x3f(v_pu_boxed_764_, v_fvarId_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec(v_fvarId_758_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t v_pu_766_, lean_object* v_fvarId_767_, lean_object* v_a_768_){
_start:
{
lean_object* v___x_770_; lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_791_; 
v___x_770_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_766_, v_fvarId_767_, v_a_768_);
v_a_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_791_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_791_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_791_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
if (lean_obj_tag(v_a_771_) == 1)
{
lean_object* v_val_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_786_; 
v_val_775_ = lean_ctor_get(v_a_771_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v_a_771_);
if (v_isSharedCheck_786_ == 0)
{
v___x_777_ = v_a_771_;
v_isShared_778_ = v_isSharedCheck_786_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_val_775_);
lean_dec(v_a_771_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_786_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v_value_779_; lean_object* v___x_781_; 
v_value_779_ = lean_ctor_get(v_val_775_, 3);
lean_inc(v_value_779_);
lean_dec(v_val_775_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v_value_779_);
v___x_781_ = v___x_777_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_value_779_);
v___x_781_ = v_reuseFailAlloc_785_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_783_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_781_);
v___x_783_ = v___x_773_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v___x_787_; lean_object* v___x_789_; 
lean_dec(v_a_771_);
v___x_787_ = lean_box(0);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_787_);
v___x_789_ = v___x_773_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg___boxed(lean_object* v_pu_792_, lean_object* v_fvarId_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
uint8_t v_pu_boxed_796_; lean_object* v_res_797_; 
v_pu_boxed_796_ = lean_unbox(v_pu_792_);
v_res_797_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_boxed_796_, v_fvarId_793_, v_a_794_);
lean_dec(v_a_794_);
lean_dec(v_fvarId_793_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f(uint8_t v_pu_798_, lean_object* v_fvarId_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_798_, v_fvarId_799_, v_a_801_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___boxed(lean_object* v_pu_806_, lean_object* v_fvarId_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
uint8_t v_pu_boxed_813_; lean_object* v_res_814_; 
v_pu_boxed_813_ = lean_unbox(v_pu_806_);
v_res_814_ = l_Lean_Compiler_LCNF_findLetValue_x3f(v_pu_boxed_813_, v_fvarId_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_fvarId_807_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg(lean_object* v_fvarId_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
uint8_t v___x_819_; lean_object* v___x_820_; 
v___x_819_ = 0;
v___x_820_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_819_, v_fvarId_815_, v_a_816_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_864_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_864_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_864_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_864_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
if (lean_obj_tag(v_a_821_) == 1)
{
lean_object* v_val_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_863_; 
v_val_831_ = lean_ctor_get(v_a_821_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v_a_821_);
if (v_isSharedCheck_863_ == 0)
{
v___x_833_ = v_a_821_;
v_isShared_834_ = v_isSharedCheck_863_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_val_831_);
lean_dec(v_a_821_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_863_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
if (lean_obj_tag(v_val_831_) == 3)
{
lean_object* v_declName_835_; lean_object* v___x_836_; lean_object* v_env_837_; uint8_t v___x_838_; lean_object* v___x_839_; 
lean_del_object(v___x_823_);
v_declName_835_ = lean_ctor_get(v_val_831_, 0);
lean_inc(v_declName_835_);
lean_dec_ref(v_val_831_);
v___x_836_ = lean_st_ref_get(v_a_817_);
v_env_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc_ref(v_env_837_);
lean_dec(v___x_836_);
v___x_838_ = 0;
v___x_839_ = l_Lean_Environment_find_x3f(v_env_837_, v_declName_835_, v___x_838_);
if (lean_obj_tag(v___x_839_) == 1)
{
lean_object* v_val_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_858_; 
lean_del_object(v___x_833_);
v_val_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_858_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_858_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_val_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_858_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
if (lean_obj_tag(v_val_840_) == 6)
{
lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_852_; 
lean_del_object(v___x_842_);
v_isSharedCheck_852_ = !lean_is_exclusive(v_val_840_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v_val_840_, 0);
lean_dec(v_unused_853_);
v___x_845_ = v_val_840_;
v_isShared_846_ = v_isSharedCheck_852_;
goto v_resetjp_844_;
}
else
{
lean_dec(v_val_840_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_852_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_847_ = 1;
v___x_848_ = lean_box(v___x_847_);
if (v_isShared_846_ == 0)
{
lean_ctor_set_tag(v___x_845_, 0);
lean_ctor_set(v___x_845_, 0, v___x_848_);
v___x_850_ = v___x_845_;
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
}
else
{
lean_object* v___x_854_; lean_object* v___x_856_; 
lean_dec(v_val_840_);
v___x_854_ = lean_box(v___x_838_);
if (v_isShared_843_ == 0)
{
lean_ctor_set_tag(v___x_842_, 0);
lean_ctor_set(v___x_842_, 0, v___x_854_);
v___x_856_ = v___x_842_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
else
{
lean_object* v___x_859_; lean_object* v___x_861_; 
lean_dec(v___x_839_);
v___x_859_ = lean_box(v___x_838_);
if (v_isShared_834_ == 0)
{
lean_ctor_set_tag(v___x_833_, 0);
lean_ctor_set(v___x_833_, 0, v___x_859_);
v___x_861_ = v___x_833_;
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
}
else
{
lean_del_object(v___x_833_);
lean_dec(v_val_831_);
goto v___jp_825_;
}
}
}
else
{
lean_dec(v_a_821_);
goto v___jp_825_;
}
v___jp_825_:
{
uint8_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_826_ = 0;
v___x_827_ = lean_box(v___x_826_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_827_);
v___x_829_ = v___x_823_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
v_a_865_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_820_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_820_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg___boxed(lean_object* v_fvarId_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_873_, v_a_874_, v_a_875_);
lean_dec(v_a_875_);
lean_dec(v_a_874_);
lean_dec(v_fvarId_873_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp(lean_object* v_fvarId_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_878_, v_a_880_, v_a_882_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___boxed(lean_object* v_fvarId_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Compiler_LCNF_isConstructorApp(v_fvarId_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_fvarId_885_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(lean_object* v_arg_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
if (lean_obj_tag(v_arg_892_) == 1)
{
lean_object* v_fvarId_896_; lean_object* v___x_897_; 
v_fvarId_896_ = lean_ctor_get(v_arg_892_, 0);
v___x_897_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_896_, v_a_893_, v_a_894_);
return v___x_897_;
}
else
{
uint8_t v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = 0;
v___x_899_ = lean_box(v___x_898_);
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg___boxed(lean_object* v_arg_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_901_, v_a_902_, v_a_903_);
lean_dec(v_a_903_);
lean_dec(v_a_902_);
lean_dec(v_arg_901_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp(uint8_t v_pu_906_, lean_object* v_arg_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_907_, v_a_909_, v_a_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___boxed(lean_object* v_pu_914_, lean_object* v_arg_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
uint8_t v_pu_boxed_921_; lean_object* v_res_922_; 
v_pu_boxed_921_ = lean_unbox(v_pu_914_);
v_res_922_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp(v_pu_boxed_921_, v_arg_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec(v_arg_915_);
return v_res_922_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getParam___closed__1(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParam___closed__0));
v___x_925_ = l_Lean_stringToMessageData(v___x_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam(uint8_t v_pu_926_, lean_object* v_fvarId_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v___x_933_; lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_946_; 
v___x_933_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_926_, v_fvarId_927_, v_a_929_);
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_946_ == 0)
{
v___x_936_ = v___x_933_;
v_isShared_937_ = v_isSharedCheck_946_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_933_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_946_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
if (lean_obj_tag(v_a_934_) == 1)
{
lean_object* v_val_938_; lean_object* v___x_940_; 
lean_dec(v_fvarId_927_);
v_val_938_ = lean_ctor_get(v_a_934_, 0);
lean_inc(v_val_938_);
lean_dec_ref(v_a_934_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v_val_938_);
v___x_940_ = v___x_936_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_val_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_del_object(v___x_936_);
lean_dec(v_a_934_);
v___x_942_ = lean_obj_once(&l_Lean_Compiler_LCNF_getParam___closed__1, &l_Lean_Compiler_LCNF_getParam___closed__1_once, _init_l_Lean_Compiler_LCNF_getParam___closed__1);
v___x_943_ = l_Lean_MessageData_ofName(v_fvarId_927_);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_944_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
return v___x_945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam___boxed(lean_object* v_pu_947_, lean_object* v_fvarId_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
uint8_t v_pu_boxed_954_; lean_object* v_res_955_; 
v_pu_boxed_954_ = lean_unbox(v_pu_947_);
v_res_955_ = l_Lean_Compiler_LCNF_getParam(v_pu_boxed_954_, v_fvarId_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
return v_res_955_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = ((lean_object*)(l_Lean_Compiler_LCNF_getLetDecl___closed__0));
v___x_958_ = l_Lean_stringToMessageData(v___x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl(uint8_t v_pu_959_, lean_object* v_fvarId_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v___x_966_; lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_979_; 
v___x_966_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_959_, v_fvarId_960_, v_a_962_);
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_979_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_979_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_979_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
if (lean_obj_tag(v_a_967_) == 1)
{
lean_object* v_val_971_; lean_object* v___x_973_; 
lean_dec(v_fvarId_960_);
v_val_971_ = lean_ctor_get(v_a_967_, 0);
lean_inc(v_val_971_);
lean_dec_ref(v_a_967_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v_val_971_);
v___x_973_ = v___x_969_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_val_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
else
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
lean_del_object(v___x_969_);
lean_dec(v_a_967_);
v___x_975_ = lean_obj_once(&l_Lean_Compiler_LCNF_getLetDecl___closed__1, &l_Lean_Compiler_LCNF_getLetDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1);
v___x_976_ = l_Lean_MessageData_ofName(v_fvarId_960_);
v___x_977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_977_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
return v___x_978_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl___boxed(lean_object* v_pu_980_, lean_object* v_fvarId_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
uint8_t v_pu_boxed_987_; lean_object* v_res_988_; 
v_pu_boxed_987_ = lean_unbox(v_pu_980_);
v_res_988_ = l_Lean_Compiler_LCNF_getLetDecl(v_pu_boxed_987_, v_fvarId_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
return v_res_988_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l_Lean_Compiler_LCNF_getFunDecl___closed__0));
v___x_991_ = l_Lean_stringToMessageData(v___x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t v_pu_992_, lean_object* v_fvarId_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v___x_999_; lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1012_; 
v___x_999_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_992_, v_fvarId_993_, v_a_995_);
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1012_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1012_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
if (lean_obj_tag(v_a_1000_) == 1)
{
lean_object* v_val_1004_; lean_object* v___x_1006_; 
lean_dec(v_fvarId_993_);
v_val_1004_ = lean_ctor_get(v_a_1000_, 0);
lean_inc(v_val_1004_);
lean_dec_ref(v_a_1000_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v_val_1004_);
v___x_1006_ = v___x_1002_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_val_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_del_object(v___x_1002_);
lean_dec(v_a_1000_);
v___x_1008_ = lean_obj_once(&l_Lean_Compiler_LCNF_getFunDecl___closed__1, &l_Lean_Compiler_LCNF_getFunDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1);
v___x_1009_ = l_Lean_MessageData_ofName(v_fvarId_993_);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_1010_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
return v___x_1011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl___boxed(lean_object* v_pu_1013_, lean_object* v_fvarId_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
uint8_t v_pu_boxed_1020_; lean_object* v_res_1021_; 
v_pu_boxed_1020_ = lean_unbox(v_pu_1013_);
v_res_1021_ = l_Lean_Compiler_LCNF_getFunDecl(v_pu_boxed_1020_, v_fvarId_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg(lean_object* v_f_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v___x_1025_; lean_object* v_lctx_1026_; lean_object* v_nextIdx_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1038_; 
v___x_1025_ = lean_st_ref_take(v_a_1023_);
v_lctx_1026_ = lean_ctor_get(v___x_1025_, 0);
v_nextIdx_1027_ = lean_ctor_get(v___x_1025_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1029_ = v___x_1025_;
v_isShared_1030_ = v_isSharedCheck_1038_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_nextIdx_1027_);
lean_inc(v_lctx_1026_);
lean_dec(v___x_1025_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1038_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = lean_apply_1(v_f_1022_, v_lctx_1026_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1031_);
v___x_1033_ = v___x_1029_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_nextIdx_1027_);
v___x_1033_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = lean_st_ref_set(v_a_1023_, v___x_1033_);
v___x_1035_ = lean_box(0);
v___x_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg___boxed(lean_object* v_f_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_Compiler_LCNF_modifyLCtx___redArg(v_f_1039_, v_a_1040_);
lean_dec(v_a_1040_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx(lean_object* v_f_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v___x_1049_; lean_object* v_lctx_1050_; lean_object* v_nextIdx_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1062_; 
v___x_1049_ = lean_st_ref_take(v_a_1045_);
v_lctx_1050_ = lean_ctor_get(v___x_1049_, 0);
v_nextIdx_1051_ = lean_ctor_get(v___x_1049_, 1);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1053_ = v___x_1049_;
v_isShared_1054_ = v_isSharedCheck_1062_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_nextIdx_1051_);
lean_inc(v_lctx_1050_);
lean_dec(v___x_1049_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1062_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1055_ = lean_apply_1(v_f_1043_, v_lctx_1050_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1055_);
v___x_1057_ = v___x_1053_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_nextIdx_1051_);
v___x_1057_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = lean_st_ref_set(v_a_1045_, v___x_1057_);
v___x_1059_ = lean_box(0);
v___x_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
return v___x_1060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___boxed(lean_object* v_f_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_Compiler_LCNF_modifyLCtx(v_f_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t v_pu_1070_, lean_object* v_decl_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v___x_1074_; lean_object* v_lctx_1075_; lean_object* v_nextIdx_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1087_; 
v___x_1074_ = lean_st_ref_take(v_a_1072_);
v_lctx_1075_ = lean_ctor_get(v___x_1074_, 0);
v_nextIdx_1076_ = lean_ctor_get(v___x_1074_, 1);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1078_ = v___x_1074_;
v_isShared_1079_ = v_isSharedCheck_1087_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_nextIdx_1076_);
lean_inc(v_lctx_1075_);
lean_dec(v___x_1074_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1087_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1080_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_1070_, v_lctx_1075_, v_decl_1071_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1080_);
v___x_1082_ = v___x_1078_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_nextIdx_1076_);
v___x_1082_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1083_ = lean_st_ref_set(v_a_1072_, v___x_1082_);
v___x_1084_ = lean_box(0);
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg___boxed(lean_object* v_pu_1088_, lean_object* v_decl_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
uint8_t v_pu_boxed_1092_; lean_object* v_res_1093_; 
v_pu_boxed_1092_ = lean_unbox(v_pu_1088_);
v_res_1093_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_boxed_1092_, v_decl_1089_, v_a_1090_);
lean_dec(v_a_1090_);
lean_dec_ref(v_decl_1089_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(uint8_t v_pu_1094_, lean_object* v_decl_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1094_, v_decl_1095_, v_a_1097_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___boxed(lean_object* v_pu_1102_, lean_object* v_decl_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
uint8_t v_pu_boxed_1109_; lean_object* v_res_1110_; 
v_pu_boxed_1109_ = lean_unbox(v_pu_1102_);
v_res_1110_ = l_Lean_Compiler_LCNF_eraseLetDecl(v_pu_boxed_1109_, v_decl_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec_ref(v_decl_1103_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t v_pu_1111_, lean_object* v_decl_1112_, uint8_t v_recursive_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v___x_1116_; lean_object* v_lctx_1117_; lean_object* v_nextIdx_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1129_; 
v___x_1116_ = lean_st_ref_take(v_a_1114_);
v_lctx_1117_ = lean_ctor_get(v___x_1116_, 0);
v_nextIdx_1118_ = lean_ctor_get(v___x_1116_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1120_ = v___x_1116_;
v_isShared_1121_ = v_isSharedCheck_1129_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_nextIdx_1118_);
lean_inc(v_lctx_1117_);
lean_dec(v___x_1116_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1129_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1122_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_1111_, v_lctx_1117_, v_decl_1112_, v_recursive_1113_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1122_);
v___x_1124_ = v___x_1120_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_nextIdx_1118_);
v___x_1124_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = lean_st_ref_set(v_a_1114_, v___x_1124_);
v___x_1126_ = lean_box(0);
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
return v___x_1127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg___boxed(lean_object* v_pu_1130_, lean_object* v_decl_1131_, lean_object* v_recursive_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
uint8_t v_pu_boxed_1135_; uint8_t v_recursive_boxed_1136_; lean_object* v_res_1137_; 
v_pu_boxed_1135_ = lean_unbox(v_pu_1130_);
v_recursive_boxed_1136_ = lean_unbox(v_recursive_1132_);
v_res_1137_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_boxed_1135_, v_decl_1131_, v_recursive_boxed_1136_, v_a_1133_);
lean_dec(v_a_1133_);
lean_dec_ref(v_decl_1131_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(uint8_t v_pu_1138_, lean_object* v_decl_1139_, uint8_t v_recursive_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1138_, v_decl_1139_, v_recursive_1140_, v_a_1142_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___boxed(lean_object* v_pu_1147_, lean_object* v_decl_1148_, lean_object* v_recursive_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
uint8_t v_pu_boxed_1155_; uint8_t v_recursive_boxed_1156_; lean_object* v_res_1157_; 
v_pu_boxed_1155_ = lean_unbox(v_pu_1147_);
v_recursive_boxed_1156_ = lean_unbox(v_recursive_1149_);
v_res_1157_ = l_Lean_Compiler_LCNF_eraseFunDecl(v_pu_boxed_1155_, v_decl_1148_, v_recursive_boxed_1156_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec_ref(v_decl_1148_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t v_pu_1158_, lean_object* v_code_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v___x_1162_; lean_object* v_lctx_1163_; lean_object* v_nextIdx_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1175_; 
v___x_1162_ = lean_st_ref_take(v_a_1160_);
v_lctx_1163_ = lean_ctor_get(v___x_1162_, 0);
v_nextIdx_1164_ = lean_ctor_get(v___x_1162_, 1);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1166_ = v___x_1162_;
v_isShared_1167_ = v_isSharedCheck_1175_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_nextIdx_1164_);
lean_inc(v_lctx_1163_);
lean_dec(v___x_1162_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1175_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1168_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_1158_, v_code_1159_, v_lctx_1163_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v___x_1168_);
v___x_1170_ = v___x_1166_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_nextIdx_1164_);
v___x_1170_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1171_ = lean_st_ref_set(v_a_1160_, v___x_1170_);
v___x_1172_ = lean_box(0);
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
return v___x_1173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg___boxed(lean_object* v_pu_1176_, lean_object* v_code_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
uint8_t v_pu_boxed_1180_; lean_object* v_res_1181_; 
v_pu_boxed_1180_ = lean_unbox(v_pu_1176_);
v_res_1181_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_boxed_1180_, v_code_1177_, v_a_1178_);
lean_dec(v_a_1178_);
lean_dec_ref(v_code_1177_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode(uint8_t v_pu_1182_, lean_object* v_code_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_1182_, v_code_1183_, v_a_1185_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___boxed(lean_object* v_pu_1190_, lean_object* v_code_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
uint8_t v_pu_boxed_1197_; lean_object* v_res_1198_; 
v_pu_boxed_1197_ = lean_unbox(v_pu_1190_);
v_res_1198_ = l_Lean_Compiler_LCNF_eraseCode(v_pu_boxed_1197_, v_code_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec_ref(v_code_1191_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t v_pu_1199_, lean_object* v_param_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v___x_1203_; lean_object* v_lctx_1204_; lean_object* v_nextIdx_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1216_; 
v___x_1203_ = lean_st_ref_take(v_a_1201_);
v_lctx_1204_ = lean_ctor_get(v___x_1203_, 0);
v_nextIdx_1205_ = lean_ctor_get(v___x_1203_, 1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1207_ = v___x_1203_;
v_isShared_1208_ = v_isSharedCheck_1216_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_nextIdx_1205_);
lean_inc(v_lctx_1204_);
lean_dec(v___x_1203_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1216_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1209_ = l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_1199_, v_lctx_1204_, v_param_1200_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1209_);
v___x_1211_ = v___x_1207_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_nextIdx_1205_);
v___x_1211_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1212_ = lean_st_ref_set(v_a_1201_, v___x_1211_);
v___x_1213_ = lean_box(0);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
return v___x_1214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg___boxed(lean_object* v_pu_1217_, lean_object* v_param_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
uint8_t v_pu_boxed_1221_; lean_object* v_res_1222_; 
v_pu_boxed_1221_ = lean_unbox(v_pu_1217_);
v_res_1222_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_boxed_1221_, v_param_1218_, v_a_1219_);
lean_dec(v_a_1219_);
lean_dec_ref(v_param_1218_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam(uint8_t v_pu_1223_, lean_object* v_param_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_1223_, v_param_1224_, v_a_1226_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___boxed(lean_object* v_pu_1231_, lean_object* v_param_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
uint8_t v_pu_boxed_1238_; lean_object* v_res_1239_; 
v_pu_boxed_1238_ = lean_unbox(v_pu_1231_);
v_res_1239_ = l_Lean_Compiler_LCNF_eraseParam(v_pu_boxed_1238_, v_param_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec_ref(v_param_1232_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t v_pu_1240_, lean_object* v_params_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v___x_1244_; lean_object* v_lctx_1245_; lean_object* v_nextIdx_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1257_; 
v___x_1244_ = lean_st_ref_take(v_a_1242_);
v_lctx_1245_ = lean_ctor_get(v___x_1244_, 0);
v_nextIdx_1246_ = lean_ctor_get(v___x_1244_, 1);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1248_ = v___x_1244_;
v_isShared_1249_ = v_isSharedCheck_1257_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_nextIdx_1246_);
lean_inc(v_lctx_1245_);
lean_dec(v___x_1244_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1257_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1250_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_1240_, v_lctx_1245_, v_params_1241_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v___x_1250_);
v___x_1252_ = v___x_1248_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_nextIdx_1246_);
v___x_1252_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = lean_st_ref_set(v_a_1242_, v___x_1252_);
v___x_1254_ = lean_box(0);
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
return v___x_1255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg___boxed(lean_object* v_pu_1258_, lean_object* v_params_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
uint8_t v_pu_boxed_1262_; lean_object* v_res_1263_; 
v_pu_boxed_1262_ = lean_unbox(v_pu_1258_);
v_res_1263_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_boxed_1262_, v_params_1259_, v_a_1260_);
lean_dec(v_a_1260_);
lean_dec_ref(v_params_1259_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams(uint8_t v_pu_1264_, lean_object* v_params_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1264_, v_params_1265_, v_a_1267_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___boxed(lean_object* v_pu_1272_, lean_object* v_params_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
uint8_t v_pu_boxed_1279_; lean_object* v_res_1280_; 
v_pu_boxed_1279_ = lean_unbox(v_pu_1272_);
v_res_1280_ = l_Lean_Compiler_LCNF_eraseParams(v_pu_boxed_1279_, v_params_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec_ref(v_params_1273_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t v_pu_1281_, lean_object* v_decl_1282_, lean_object* v_a_1283_){
_start:
{
switch(lean_obj_tag(v_decl_1282_))
{
case 0:
{
lean_object* v_decl_1285_; lean_object* v___x_1286_; 
v_decl_1285_ = lean_ctor_get(v_decl_1282_, 0);
v___x_1286_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1281_, v_decl_1285_, v_a_1283_);
return v___x_1286_;
}
case 1:
{
lean_object* v_decl_1287_; uint8_t v___x_1288_; lean_object* v___x_1289_; 
v_decl_1287_ = lean_ctor_get(v_decl_1282_, 0);
v___x_1288_ = 1;
v___x_1289_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1281_, v_decl_1287_, v___x_1288_, v_a_1283_);
return v___x_1289_;
}
case 2:
{
lean_object* v_decl_1290_; uint8_t v___x_1291_; lean_object* v___x_1292_; 
v_decl_1290_ = lean_ctor_get(v_decl_1282_, 0);
v___x_1291_ = 1;
v___x_1292_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1281_, v_decl_1290_, v___x_1291_, v_a_1283_);
return v___x_1292_;
}
default: 
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_box(0);
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
return v___x_1294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg___boxed(lean_object* v_pu_1295_, lean_object* v_decl_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
uint8_t v_pu_boxed_1299_; lean_object* v_res_1300_; 
v_pu_boxed_1299_ = lean_unbox(v_pu_1295_);
v_res_1300_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_boxed_1299_, v_decl_1296_, v_a_1297_);
lean_dec(v_a_1297_);
lean_dec_ref(v_decl_1296_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl(uint8_t v_pu_1301_, lean_object* v_decl_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1301_, v_decl_1302_, v_a_1304_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___boxed(lean_object* v_pu_1309_, lean_object* v_decl_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
uint8_t v_pu_boxed_1316_; lean_object* v_res_1317_; 
v_pu_boxed_1316_ = lean_unbox(v_pu_1309_);
v_res_1317_ = l_Lean_Compiler_LCNF_eraseCodeDecl(v_pu_boxed_1316_, v_decl_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec_ref(v_decl_1310_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(uint8_t v_pu_1318_, lean_object* v_as_1319_, size_t v_i_1320_, size_t v_stop_1321_, lean_object* v_b_1322_, lean_object* v___y_1323_){
_start:
{
uint8_t v___x_1325_; 
v___x_1325_ = lean_usize_dec_eq(v_i_1320_, v_stop_1321_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_array_uget_borrowed(v_as_1319_, v_i_1320_);
v___x_1327_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1318_, v___x_1326_, v___y_1323_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; size_t v___x_1329_; size_t v___x_1330_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref(v___x_1327_);
v___x_1329_ = ((size_t)1ULL);
v___x_1330_ = lean_usize_add(v_i_1320_, v___x_1329_);
v_i_1320_ = v___x_1330_;
v_b_1322_ = v_a_1328_;
goto _start;
}
else
{
return v___x_1327_;
}
}
else
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1332_, 0, v_b_1322_);
return v___x_1332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg___boxed(lean_object* v_pu_1333_, lean_object* v_as_1334_, lean_object* v_i_1335_, lean_object* v_stop_1336_, lean_object* v_b_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
uint8_t v_pu_boxed_1340_; size_t v_i_boxed_1341_; size_t v_stop_boxed_1342_; lean_object* v_res_1343_; 
v_pu_boxed_1340_ = lean_unbox(v_pu_1333_);
v_i_boxed_1341_ = lean_unbox_usize(v_i_1335_);
lean_dec(v_i_1335_);
v_stop_boxed_1342_ = lean_unbox_usize(v_stop_1336_);
lean_dec(v_stop_1336_);
v_res_1343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_boxed_1340_, v_as_1334_, v_i_boxed_1341_, v_stop_boxed_1342_, v_b_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v_as_1334_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls(uint8_t v_pu_1344_, lean_object* v_decls_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1351_ = lean_unsigned_to_nat(0u);
v___x_1352_ = lean_array_get_size(v_decls_1345_);
v___x_1353_ = lean_box(0);
v___x_1354_ = lean_nat_dec_lt(v___x_1351_, v___x_1352_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
return v___x_1355_;
}
else
{
uint8_t v___x_1356_; 
v___x_1356_ = lean_nat_dec_le(v___x_1352_, v___x_1352_);
if (v___x_1356_ == 0)
{
if (v___x_1354_ == 0)
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1353_);
return v___x_1357_;
}
else
{
size_t v___x_1358_; size_t v___x_1359_; lean_object* v___x_1360_; 
v___x_1358_ = ((size_t)0ULL);
v___x_1359_ = lean_usize_of_nat(v___x_1352_);
v___x_1360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1344_, v_decls_1345_, v___x_1358_, v___x_1359_, v___x_1353_, v_a_1347_);
return v___x_1360_;
}
}
else
{
size_t v___x_1361_; size_t v___x_1362_; lean_object* v___x_1363_; 
v___x_1361_ = ((size_t)0ULL);
v___x_1362_ = lean_usize_of_nat(v___x_1352_);
v___x_1363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1344_, v_decls_1345_, v___x_1361_, v___x_1362_, v___x_1353_, v_a_1347_);
return v___x_1363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls___boxed(lean_object* v_pu_1364_, lean_object* v_decls_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_){
_start:
{
uint8_t v_pu_boxed_1371_; lean_object* v_res_1372_; 
v_pu_boxed_1371_ = lean_unbox(v_pu_1364_);
v_res_1372_ = l_Lean_Compiler_LCNF_eraseCodeDecls(v_pu_boxed_1371_, v_decls_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec_ref(v_decls_1365_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(uint8_t v_pu_1373_, lean_object* v_as_1374_, size_t v_i_1375_, size_t v_stop_1376_, lean_object* v_b_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1373_, v_as_1374_, v_i_1375_, v_stop_1376_, v_b_1377_, v___y_1379_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___boxed(lean_object* v_pu_1384_, lean_object* v_as_1385_, lean_object* v_i_1386_, lean_object* v_stop_1387_, lean_object* v_b_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
uint8_t v_pu_boxed_1394_; size_t v_i_boxed_1395_; size_t v_stop_boxed_1396_; lean_object* v_res_1397_; 
v_pu_boxed_1394_ = lean_unbox(v_pu_1384_);
v_i_boxed_1395_ = lean_unbox_usize(v_i_1386_);
lean_dec(v_i_1386_);
v_stop_boxed_1396_ = lean_unbox_usize(v_stop_1387_);
lean_dec(v_stop_1387_);
v_res_1397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(v_pu_boxed_1394_, v_as_1385_, v_i_boxed_1395_, v_stop_boxed_1396_, v_b_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec_ref(v_as_1385_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(lean_object* v_f_1398_, lean_object* v_v_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
if (lean_obj_tag(v_v_1399_) == 0)
{
lean_object* v_code_1405_; lean_object* v___x_1406_; 
v_code_1405_ = lean_ctor_get(v_v_1399_, 0);
lean_inc_ref(v_code_1405_);
lean_dec_ref(v_v_1399_);
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
lean_inc(v___y_1401_);
lean_inc_ref(v___y_1400_);
v___x_1406_ = lean_apply_6(v_f_1398_, v_code_1405_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, lean_box(0));
return v___x_1406_;
}
else
{
lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1414_; 
lean_dec_ref(v_f_1398_);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_v_1399_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; 
v_unused_1415_ = lean_ctor_get(v_v_1399_, 0);
lean_dec(v_unused_1415_);
v___x_1408_ = v_v_1399_;
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
else
{
lean_dec(v_v_1399_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1410_ = lean_box(0);
if (v_isShared_1409_ == 0)
{
lean_ctor_set_tag(v___x_1408_, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg___boxed(lean_object* v_f_1416_, lean_object* v_v_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1416_, v_v_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(uint8_t v_pu_1424_, lean_object* v_f_1425_, lean_object* v_v_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1425_, v_v_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___boxed(lean_object* v_pu_1433_, lean_object* v_f_1434_, lean_object* v_v_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
uint8_t v_pu_boxed_1441_; lean_object* v_res_1442_; 
v_pu_boxed_1441_ = lean_unbox(v_pu_1433_);
v_res_1442_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(v_pu_boxed_1441_, v_f_1434_, v_v_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t v_pu_1443_, lean_object* v_decl_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v_toSignature_1450_; lean_object* v_value_1451_; lean_object* v_params_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_toSignature_1450_ = lean_ctor_get(v_decl_1444_, 0);
lean_inc_ref(v_toSignature_1450_);
v_value_1451_ = lean_ctor_get(v_decl_1444_, 1);
lean_inc_ref(v_value_1451_);
lean_dec_ref(v_decl_1444_);
v_params_1452_ = lean_ctor_get(v_toSignature_1450_, 3);
lean_inc_ref(v_params_1452_);
lean_dec_ref(v_toSignature_1450_);
v___x_1453_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1443_, v_params_1452_, v_a_1446_);
lean_dec_ref(v_params_1452_);
lean_dec_ref(v___x_1453_);
v___x_1454_ = lean_box(v_pu_1443_);
v___x_1455_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_eraseCode___boxed), 7, 1);
lean_closure_set(v___x_1455_, 0, v___x_1454_);
v___x_1456_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v___x_1455_, v_value_1451_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl___boxed(lean_object* v_pu_1457_, lean_object* v_decl_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
uint8_t v_pu_boxed_1464_; lean_object* v_res_1465_; 
v_pu_boxed_1464_ = lean_unbox(v_pu_1457_);
v_res_1465_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_boxed_1464_, v_decl_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase(uint8_t v_pu_1466_, lean_object* v_decl_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_1466_, v_decl_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase___boxed(lean_object* v_pu_1474_, lean_object* v_decl_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_){
_start:
{
uint8_t v_pu_boxed_1481_; lean_object* v_res_1482_; 
v_pu_boxed_1481_ = lean_unbox(v_pu_1474_);
v_res_1482_ = l_Lean_Compiler_LCNF_Decl_erase(v_pu_boxed_1481_, v_decl_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_);
lean_dec(v_a_1479_);
lean_dec_ref(v_a_1478_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(lean_object* v_msg_1483_){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = l_Lean_instInhabitedExpr;
v___x_1485_ = lean_panic_fn_borrowed(v___x_1484_, v_msg_1483_);
return v___x_1485_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1489_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2));
v___x_1490_ = lean_unsigned_to_nat(20u);
v___x_1491_ = lean_unsigned_to_nat(215u);
v___x_1492_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1));
v___x_1493_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0));
v___x_1494_ = l_mkPanicMessageWithDecl(v___x_1493_, v___x_1492_, v___x_1491_, v___x_1490_, v___x_1489_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t v_pu_1495_, lean_object* v_s_1496_, uint8_t v_translator_1497_, lean_object* v_e_1498_){
_start:
{
uint8_t v___x_1499_; 
v___x_1499_ = l_Lean_Expr_hasFVar(v_e_1498_);
if (v___x_1499_ == 0)
{
return v_e_1498_;
}
else
{
switch(lean_obj_tag(v_e_1498_))
{
case 1:
{
lean_object* v_fvarId_1500_; lean_object* v___x_1501_; 
v_fvarId_1500_ = lean_ctor_get(v_e_1498_, 0);
v___x_1501_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1496_, v_fvarId_1500_);
if (lean_obj_tag(v___x_1501_) == 0)
{
return v_e_1498_;
}
else
{
lean_object* v_val_1502_; 
lean_dec_ref(v_e_1498_);
v_val_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_val_1502_);
lean_dec_ref(v___x_1501_);
switch(lean_obj_tag(v_val_1502_))
{
case 0:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_Compiler_LCNF_erasedExpr;
return v___x_1503_;
}
case 1:
{
if (v_translator_1497_ == 0)
{
lean_object* v_fvarId_1504_; lean_object* v___x_1505_; 
v_fvarId_1504_ = lean_ctor_get(v_val_1502_, 0);
lean_inc(v_fvarId_1504_);
lean_dec_ref(v_val_1502_);
v___x_1505_ = l_Lean_Expr_fvar___override(v_fvarId_1504_);
v_e_1498_ = v___x_1505_;
goto _start;
}
else
{
lean_object* v_fvarId_1507_; lean_object* v___x_1508_; 
v_fvarId_1507_ = lean_ctor_get(v_val_1502_, 0);
lean_inc(v_fvarId_1507_);
lean_dec_ref(v_val_1502_);
v___x_1508_ = l_Lean_Expr_fvar___override(v_fvarId_1507_);
return v___x_1508_;
}
}
default: 
{
if (v_translator_1497_ == 0)
{
lean_object* v_expr_1509_; 
v_expr_1509_ = lean_ctor_get(v_val_1502_, 0);
lean_inc_ref(v_expr_1509_);
lean_dec_ref(v_val_1502_);
v_e_1498_ = v_expr_1509_;
goto _start;
}
else
{
lean_object* v_expr_1511_; 
v_expr_1511_ = lean_ctor_get(v_val_1502_, 0);
lean_inc_ref(v_expr_1511_);
lean_dec_ref(v_val_1502_);
return v_expr_1511_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_1512_; lean_object* v_arg_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; uint8_t v___y_1517_; size_t v___x_1521_; size_t v___x_1522_; uint8_t v___x_1523_; 
v_fn_1512_ = lean_ctor_get(v_e_1498_, 0);
v_arg_1513_ = lean_ctor_get(v_e_1498_, 1);
lean_inc_ref(v_fn_1512_);
v___x_1514_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1495_, v_s_1496_, v_translator_1497_, v_fn_1512_);
lean_inc_ref(v_arg_1513_);
v___x_1515_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1495_, v_s_1496_, v_translator_1497_, v_arg_1513_);
v___x_1521_ = lean_ptr_addr(v_fn_1512_);
v___x_1522_ = lean_ptr_addr(v___x_1514_);
v___x_1523_ = lean_usize_dec_eq(v___x_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
v___y_1517_ = v___x_1523_;
goto v___jp_1516_;
}
else
{
size_t v___x_1524_; size_t v___x_1525_; uint8_t v___x_1526_; 
v___x_1524_ = lean_ptr_addr(v_arg_1513_);
v___x_1525_ = lean_ptr_addr(v___x_1515_);
v___x_1526_ = lean_usize_dec_eq(v___x_1524_, v___x_1525_);
v___y_1517_ = v___x_1526_;
goto v___jp_1516_;
}
v___jp_1516_:
{
if (v___y_1517_ == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec_ref(v_e_1498_);
v___x_1518_ = l_Lean_Expr_app___override(v___x_1514_, v___x_1515_);
v___x_1519_ = l_Lean_Expr_headBeta(v___x_1518_);
return v___x_1519_;
}
else
{
lean_object* v___x_1520_; 
lean_dec_ref(v___x_1515_);
lean_dec_ref(v___x_1514_);
v___x_1520_ = l_Lean_Expr_headBeta(v_e_1498_);
return v___x_1520_;
}
}
}
case 6:
{
lean_object* v_binderName_1527_; lean_object* v_binderType_1528_; lean_object* v_body_1529_; uint8_t v_binderInfo_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; uint8_t v___y_1534_; size_t v___x_1538_; size_t v___x_1539_; uint8_t v___x_1540_; 
v_binderName_1527_ = lean_ctor_get(v_e_1498_, 0);
v_binderType_1528_ = lean_ctor_get(v_e_1498_, 1);
v_body_1529_ = lean_ctor_get(v_e_1498_, 2);
v_binderInfo_1530_ = lean_ctor_get_uint8(v_e_1498_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1528_);
v___x_1531_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1495_, v_s_1496_, v_translator_1497_, v_binderType_1528_);
lean_inc_ref(v_body_1529_);
v___x_1532_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1495_, v_s_1496_, v_translator_1497_, v_body_1529_);
v___x_1538_ = lean_ptr_addr(v_binderType_1528_);
v___x_1539_ = lean_ptr_addr(v___x_1531_);
v___x_1540_ = lean_usize_dec_eq(v___x_1538_, v___x_1539_);
if (v___x_1540_ == 0)
{
v___y_1534_ = v___x_1540_;
goto v___jp_1533_;
}
else
{
size_t v___x_1541_; size_t v___x_1542_; uint8_t v___x_1543_; 
v___x_1541_ = lean_ptr_addr(v_body_1529_);
v___x_1542_ = lean_ptr_addr(v___x_1532_);
v___x_1543_ = lean_usize_dec_eq(v___x_1541_, v___x_1542_);
v___y_1534_ = v___x_1543_;
goto v___jp_1533_;
}
v___jp_1533_:
{
if (v___y_1534_ == 0)
{
lean_object* v___x_1535_; 
lean_inc(v_binderName_1527_);
lean_dec_ref(v_e_1498_);
v___x_1535_ = l_Lean_Expr_lam___override(v_binderName_1527_, v___x_1531_, v___x_1532_, v_binderInfo_1530_);
return v___x_1535_;
}
else
{
uint8_t v___x_1536_; 
v___x_1536_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1530_, v_binderInfo_1530_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; 
lean_inc(v_binderName_1527_);
lean_dec_ref(v_e_1498_);
v___x_1537_ = l_Lean_Expr_lam___override(v_binderName_1527_, v___x_1531_, v___x_1532_, v_binderInfo_1530_);
return v___x_1537_;
}
else
{
lean_dec_ref(v___x_1532_);
lean_dec_ref(v___x_1531_);
return v_e_1498_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1544_; lean_object* v_binderType_1545_; lean_object* v_body_1546_; uint8_t v_binderInfo_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___y_1551_; size_t v___x_1555_; size_t v___x_1556_; uint8_t v___x_1557_; 
v_binderName_1544_ = lean_ctor_get(v_e_1498_, 0);
v_binderType_1545_ = lean_ctor_get(v_e_1498_, 1);
v_body_1546_ = lean_ctor_get(v_e_1498_, 2);
v_binderInfo_1547_ = lean_ctor_get_uint8(v_e_1498_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1545_);
v___x_1548_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1495_, v_s_1496_, v_translator_1497_, v_binderType_1545_);
lean_inc_ref(v_body_1546_);
v___x_1549_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1495_, v_s_1496_, v_translator_1497_, v_body_1546_);
v___x_1555_ = lean_ptr_addr(v_binderType_1545_);
v___x_1556_ = lean_ptr_addr(v___x_1548_);
v___x_1557_ = lean_usize_dec_eq(v___x_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
v___y_1551_ = v___x_1557_;
goto v___jp_1550_;
}
else
{
size_t v___x_1558_; size_t v___x_1559_; uint8_t v___x_1560_; 
v___x_1558_ = lean_ptr_addr(v_body_1546_);
v___x_1559_ = lean_ptr_addr(v___x_1549_);
v___x_1560_ = lean_usize_dec_eq(v___x_1558_, v___x_1559_);
v___y_1551_ = v___x_1560_;
goto v___jp_1550_;
}
v___jp_1550_:
{
if (v___y_1551_ == 0)
{
lean_object* v___x_1552_; 
lean_inc(v_binderName_1544_);
lean_dec_ref(v_e_1498_);
v___x_1552_ = l_Lean_Expr_forallE___override(v_binderName_1544_, v___x_1548_, v___x_1549_, v_binderInfo_1547_);
return v___x_1552_;
}
else
{
uint8_t v___x_1553_; 
v___x_1553_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1547_, v_binderInfo_1547_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
lean_inc(v_binderName_1544_);
lean_dec_ref(v_e_1498_);
v___x_1554_ = l_Lean_Expr_forallE___override(v_binderName_1544_, v___x_1548_, v___x_1549_, v_binderInfo_1547_);
return v___x_1554_;
}
else
{
lean_dec_ref(v___x_1549_);
lean_dec_ref(v___x_1548_);
return v_e_1498_;
}
}
}
}
case 8:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
lean_dec_ref(v_e_1498_);
v___x_1561_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3, &l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3);
v___x_1562_ = l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(v___x_1561_);
return v___x_1562_;
}
case 10:
{
lean_object* v_data_1563_; lean_object* v_expr_1564_; lean_object* v___x_1565_; size_t v___x_1566_; size_t v___x_1567_; uint8_t v___x_1568_; 
v_data_1563_ = lean_ctor_get(v_e_1498_, 0);
v_expr_1564_ = lean_ctor_get(v_e_1498_, 1);
lean_inc_ref(v_expr_1564_);
v___x_1565_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1495_, v_s_1496_, v_translator_1497_, v_expr_1564_);
v___x_1566_ = lean_ptr_addr(v_expr_1564_);
v___x_1567_ = lean_ptr_addr(v___x_1565_);
v___x_1568_ = lean_usize_dec_eq(v___x_1566_, v___x_1567_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; 
lean_inc(v_data_1563_);
lean_dec_ref(v_e_1498_);
v___x_1569_ = l_Lean_Expr_mdata___override(v_data_1563_, v___x_1565_);
return v___x_1569_;
}
else
{
lean_dec_ref(v___x_1565_);
return v_e_1498_;
}
}
case 11:
{
lean_object* v_typeName_1570_; lean_object* v_idx_1571_; lean_object* v_struct_1572_; lean_object* v___x_1573_; size_t v___x_1574_; size_t v___x_1575_; uint8_t v___x_1576_; 
v_typeName_1570_ = lean_ctor_get(v_e_1498_, 0);
v_idx_1571_ = lean_ctor_get(v_e_1498_, 1);
v_struct_1572_ = lean_ctor_get(v_e_1498_, 2);
lean_inc_ref(v_struct_1572_);
v___x_1573_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1495_, v_s_1496_, v_translator_1497_, v_struct_1572_);
v___x_1574_ = lean_ptr_addr(v_struct_1572_);
v___x_1575_ = lean_ptr_addr(v___x_1573_);
v___x_1576_ = lean_usize_dec_eq(v___x_1574_, v___x_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; 
lean_inc(v_idx_1571_);
lean_inc(v_typeName_1570_);
lean_dec_ref(v_e_1498_);
v___x_1577_ = l_Lean_Expr_proj___override(v_typeName_1570_, v_idx_1571_, v___x_1573_);
return v___x_1577_;
}
else
{
lean_dec_ref(v___x_1573_);
return v_e_1498_;
}
}
default: 
{
return v_e_1498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(uint8_t v_pu_1578_, lean_object* v_s_1579_, uint8_t v_translator_1580_, lean_object* v_e_1581_){
_start:
{
if (lean_obj_tag(v_e_1581_) == 5)
{
lean_object* v_fn_1582_; lean_object* v_arg_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___y_1587_; size_t v___x_1589_; size_t v___x_1590_; uint8_t v___x_1591_; 
v_fn_1582_ = lean_ctor_get(v_e_1581_, 0);
v_arg_1583_ = lean_ctor_get(v_e_1581_, 1);
lean_inc_ref(v_fn_1582_);
v___x_1584_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1578_, v_s_1579_, v_translator_1580_, v_fn_1582_);
lean_inc_ref(v_arg_1583_);
v___x_1585_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1578_, v_s_1579_, v_translator_1580_, v_arg_1583_);
v___x_1589_ = lean_ptr_addr(v_fn_1582_);
v___x_1590_ = lean_ptr_addr(v___x_1584_);
v___x_1591_ = lean_usize_dec_eq(v___x_1589_, v___x_1590_);
if (v___x_1591_ == 0)
{
v___y_1587_ = v___x_1591_;
goto v___jp_1586_;
}
else
{
size_t v___x_1592_; size_t v___x_1593_; uint8_t v___x_1594_; 
v___x_1592_ = lean_ptr_addr(v_arg_1583_);
v___x_1593_ = lean_ptr_addr(v___x_1585_);
v___x_1594_ = lean_usize_dec_eq(v___x_1592_, v___x_1593_);
v___y_1587_ = v___x_1594_;
goto v___jp_1586_;
}
v___jp_1586_:
{
if (v___y_1587_ == 0)
{
lean_object* v___x_1588_; 
lean_dec_ref(v_e_1581_);
v___x_1588_ = l_Lean_Expr_app___override(v___x_1584_, v___x_1585_);
return v___x_1588_;
}
else
{
lean_dec_ref(v___x_1585_);
lean_dec_ref(v___x_1584_);
return v_e_1581_;
}
}
}
else
{
lean_object* v___x_1595_; 
v___x_1595_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1578_, v_s_1579_, v_translator_1580_, v_e_1581_);
return v___x_1595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(lean_object* v_pu_1596_, lean_object* v_s_1597_, lean_object* v_translator_1598_, lean_object* v_e_1599_){
_start:
{
uint8_t v_pu_boxed_1600_; uint8_t v_translator_boxed_1601_; lean_object* v_res_1602_; 
v_pu_boxed_1600_ = lean_unbox(v_pu_1596_);
v_translator_boxed_1601_ = lean_unbox(v_translator_1598_);
v_res_1602_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_boxed_1600_, v_s_1597_, v_translator_boxed_1601_, v_e_1599_);
lean_dec_ref(v_s_1597_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(lean_object* v_pu_1603_, lean_object* v_s_1604_, lean_object* v_translator_1605_, lean_object* v_e_1606_){
_start:
{
uint8_t v_pu_boxed_1607_; uint8_t v_translator_boxed_1608_; lean_object* v_res_1609_; 
v_pu_boxed_1607_ = lean_unbox(v_pu_1603_);
v_translator_boxed_1608_ = lean_unbox(v_translator_1605_);
v_res_1609_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_boxed_1607_, v_s_1604_, v_translator_boxed_1608_, v_e_1606_);
lean_dec_ref(v_s_1604_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(uint8_t v_pu_1610_, lean_object* v_s_1611_, lean_object* v_e_1612_, uint8_t v_translator_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1610_, v_s_1611_, v_translator_1613_, v_e_1612_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(lean_object* v_pu_1615_, lean_object* v_s_1616_, lean_object* v_e_1617_, lean_object* v_translator_1618_){
_start:
{
uint8_t v_pu_boxed_1619_; uint8_t v_translator_boxed_1620_; lean_object* v_res_1621_; 
v_pu_boxed_1619_ = lean_unbox(v_pu_1615_);
v_translator_boxed_1620_ = lean_unbox(v_translator_1618_);
v_res_1621_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(v_pu_boxed_1619_, v_s_1616_, v_e_1617_, v_translator_boxed_1620_);
lean_dec_ref(v_s_1616_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(lean_object* v_x_1622_){
_start:
{
if (lean_obj_tag(v_x_1622_) == 0)
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_unsigned_to_nat(0u);
return v___x_1623_;
}
else
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_unsigned_to_nat(1u);
return v___x_1624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___boxed(lean_object* v_x_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(v_x_1625_);
lean_dec(v_x_1625_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(lean_object* v_t_1627_, lean_object* v_k_1628_){
_start:
{
if (lean_obj_tag(v_t_1627_) == 0)
{
lean_object* v_fvarId_1629_; lean_object* v___x_1630_; 
v_fvarId_1629_ = lean_ctor_get(v_t_1627_, 0);
lean_inc(v_fvarId_1629_);
lean_dec_ref(v_t_1627_);
v___x_1630_ = lean_apply_1(v_k_1628_, v_fvarId_1629_);
return v___x_1630_;
}
else
{
return v_k_1628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(lean_object* v_motive_1631_, lean_object* v_ctorIdx_1632_, lean_object* v_t_1633_, lean_object* v_h_1634_, lean_object* v_k_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1633_, v_k_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___boxed(lean_object* v_motive_1637_, lean_object* v_ctorIdx_1638_, lean_object* v_t_1639_, lean_object* v_h_1640_, lean_object* v_k_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(v_motive_1637_, v_ctorIdx_1638_, v_t_1639_, v_h_1640_, v_k_1641_);
lean_dec(v_ctorIdx_1638_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim___redArg(lean_object* v_t_1643_, lean_object* v_fvar_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1643_, v_fvar_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim(lean_object* v_motive_1646_, lean_object* v_t_1647_, lean_object* v_h_1648_, lean_object* v_fvar_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1647_, v_fvar_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim___redArg(lean_object* v_t_1651_, lean_object* v_erased_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1651_, v_erased_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim(lean_object* v_motive_1654_, lean_object* v_t_1655_, lean_object* v_h_1656_, lean_object* v_erased_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1655_, v_erased_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object* v_s_1663_, lean_object* v_fvarId_1664_, uint8_t v_translator_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1663_, v_fvarId_1664_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v___x_1667_; 
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v_fvarId_1664_);
return v___x_1667_;
}
else
{
lean_object* v_val_1668_; 
lean_dec(v_fvarId_1664_);
v_val_1668_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_val_1668_);
lean_dec_ref(v___x_1666_);
if (lean_obj_tag(v_val_1668_) == 1)
{
if (v_translator_1665_ == 0)
{
lean_object* v_fvarId_1669_; 
v_fvarId_1669_ = lean_ctor_get(v_val_1668_, 0);
lean_inc(v_fvarId_1669_);
lean_dec_ref(v_val_1668_);
v_fvarId_1664_ = v_fvarId_1669_;
goto _start;
}
else
{
lean_object* v_fvarId_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
v_fvarId_1671_ = lean_ctor_get(v_val_1668_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_val_1668_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v_val_1668_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_fvarId_1671_);
lean_dec(v_val_1668_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
lean_ctor_set_tag(v___x_1673_, 0);
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_fvarId_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_object* v___x_1679_; 
lean_dec(v_val_1668_);
v___x_1679_ = lean_box(1);
return v___x_1679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg___boxed(lean_object* v_s_1680_, lean_object* v_fvarId_1681_, lean_object* v_translator_1682_){
_start:
{
uint8_t v_translator_boxed_1683_; lean_object* v_res_1684_; 
v_translator_boxed_1683_ = lean_unbox(v_translator_1682_);
v_res_1684_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1680_, v_fvarId_1681_, v_translator_boxed_1683_);
lean_dec_ref(v_s_1680_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp(uint8_t v_pu_1685_, lean_object* v_s_1686_, lean_object* v_fvarId_1687_, uint8_t v_translator_1688_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1686_, v_fvarId_1687_, v_translator_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___boxed(lean_object* v_pu_1690_, lean_object* v_s_1691_, lean_object* v_fvarId_1692_, lean_object* v_translator_1693_){
_start:
{
uint8_t v_pu_boxed_1694_; uint8_t v_translator_boxed_1695_; lean_object* v_res_1696_; 
v_pu_boxed_1694_ = lean_unbox(v_pu_1690_);
v_translator_boxed_1695_ = lean_unbox(v_translator_1693_);
v_res_1696_ = l_Lean_Compiler_LCNF_normFVarImp(v_pu_boxed_1694_, v_s_1691_, v_fvarId_1692_, v_translator_boxed_1695_);
lean_dec_ref(v_s_1691_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t v_pu_1697_, lean_object* v_s_1698_, lean_object* v_arg_1699_, uint8_t v_translator_1700_){
_start:
{
switch(lean_obj_tag(v_arg_1699_))
{
case 0:
{
return v_arg_1699_;
}
case 1:
{
lean_object* v_fvarId_1701_; lean_object* v___x_1702_; 
v_fvarId_1701_ = lean_ctor_get(v_arg_1699_, 0);
v___x_1702_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1698_, v_fvarId_1701_);
if (lean_obj_tag(v___x_1702_) == 0)
{
return v_arg_1699_;
}
else
{
lean_object* v_val_1703_; 
lean_dec_ref(v_arg_1699_);
v_val_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_val_1703_);
lean_dec_ref(v___x_1702_);
switch(lean_obj_tag(v_val_1703_))
{
case 0:
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_box(0);
return v___x_1704_;
}
case 1:
{
lean_object* v_fvarId_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1713_; 
v_fvarId_1705_ = lean_ctor_get(v_val_1703_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_val_1703_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1707_ = v_val_1703_;
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_fvarId_1705_);
lean_dec(v_val_1703_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1713_;
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
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_fvarId_1705_);
v___x_1710_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
if (v_translator_1700_ == 0)
{
v_arg_1699_ = v___x_1710_;
goto _start;
}
else
{
return v___x_1710_;
}
}
}
}
default: 
{
lean_object* v_expr_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
v_expr_1714_ = lean_ctor_get(v_val_1703_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_val_1703_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v_val_1703_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_expr_1714_);
lean_dec(v_val_1703_);
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
v_reuseFailAlloc_1720_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_expr_1714_);
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
}
default: 
{
lean_object* v_expr_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v_expr_1722_ = lean_ctor_get(v_arg_1699_, 0);
lean_inc_ref(v_expr_1722_);
v___x_1723_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1697_, v_s_1698_, v_translator_1700_, v_expr_1722_);
v___x_1724_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1697_, v_arg_1699_, v___x_1723_);
return v___x_1724_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp___boxed(lean_object* v_pu_1725_, lean_object* v_s_1726_, lean_object* v_arg_1727_, lean_object* v_translator_1728_){
_start:
{
uint8_t v_pu_boxed_1729_; uint8_t v_translator_boxed_1730_; lean_object* v_res_1731_; 
v_pu_boxed_1729_ = lean_unbox(v_pu_1725_);
v_translator_boxed_1730_ = lean_unbox(v_translator_1728_);
v_res_1731_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_boxed_1729_, v_s_1726_, v_arg_1727_, v_translator_boxed_1730_);
lean_dec_ref(v_s_1726_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(uint8_t v_pu_1732_, lean_object* v_s_1733_, uint8_t v_translator_1734_, lean_object* v_i_1735_, lean_object* v_as_1736_){
_start:
{
lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1737_ = lean_array_get_size(v_as_1736_);
v___x_1738_ = lean_nat_dec_lt(v_i_1735_, v___x_1737_);
if (v___x_1738_ == 0)
{
lean_dec(v_i_1735_);
return v_as_1736_;
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1740_; size_t v___x_1741_; size_t v___x_1742_; uint8_t v___x_1743_; 
v_a_1739_ = lean_array_fget_borrowed(v_as_1736_, v_i_1735_);
lean_inc(v_a_1739_);
v___x_1740_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1732_, v_s_1733_, v_a_1739_, v_translator_1734_);
v___x_1741_ = lean_ptr_addr(v_a_1739_);
v___x_1742_ = lean_ptr_addr(v___x_1740_);
v___x_1743_ = lean_usize_dec_eq(v___x_1741_, v___x_1742_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = lean_unsigned_to_nat(1u);
v___x_1745_ = lean_nat_add(v_i_1735_, v___x_1744_);
v___x_1746_ = lean_array_fset(v_as_1736_, v_i_1735_, v___x_1740_);
lean_dec(v_i_1735_);
v_i_1735_ = v___x_1745_;
v_as_1736_ = v___x_1746_;
goto _start;
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec(v___x_1740_);
v___x_1748_ = lean_unsigned_to_nat(1u);
v___x_1749_ = lean_nat_add(v_i_1735_, v___x_1748_);
lean_dec(v_i_1735_);
v_i_1735_ = v___x_1749_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0___boxed(lean_object* v_pu_1751_, lean_object* v_s_1752_, lean_object* v_translator_1753_, lean_object* v_i_1754_, lean_object* v_as_1755_){
_start:
{
uint8_t v_pu_boxed_1756_; uint8_t v_translator_boxed_1757_; lean_object* v_res_1758_; 
v_pu_boxed_1756_ = lean_unbox(v_pu_1751_);
v_translator_boxed_1757_ = lean_unbox(v_translator_1753_);
v_res_1758_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_boxed_1756_, v_s_1752_, v_translator_boxed_1757_, v_i_1754_, v_as_1755_);
lean_dec_ref(v_s_1752_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t v_pu_1759_, lean_object* v_s_1760_, lean_object* v_args_1761_, uint8_t v_translator_1762_){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = lean_unsigned_to_nat(0u);
v___x_1764_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_1759_, v_s_1760_, v_translator_1762_, v___x_1763_, v_args_1761_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp___boxed(lean_object* v_pu_1765_, lean_object* v_s_1766_, lean_object* v_args_1767_, lean_object* v_translator_1768_){
_start:
{
uint8_t v_pu_boxed_1769_; uint8_t v_translator_boxed_1770_; lean_object* v_res_1771_; 
v_pu_boxed_1769_ = lean_unbox(v_pu_1765_);
v_translator_boxed_1770_ = lean_unbox(v_translator_1768_);
v_res_1771_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_boxed_1769_, v_s_1766_, v_args_1767_, v_translator_boxed_1770_);
lean_dec_ref(v_s_1766_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t v_pu_1772_, lean_object* v_s_1773_, lean_object* v_e_1774_, uint8_t v_translator_1775_){
_start:
{
lean_object* v_fvarId_1777_; lean_object* v_args_1783_; 
switch(lean_obj_tag(v_e_1774_))
{
case 2:
{
lean_object* v_struct_1786_; lean_object* v___x_1787_; 
v_struct_1786_ = lean_ctor_get(v_e_1774_, 2);
lean_inc(v_struct_1786_);
v___x_1787_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1773_, v_struct_1786_, v_translator_1775_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_fvarId_1788_; lean_object* v___x_1789_; 
v_fvarId_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_fvarId_1788_);
lean_dec_ref(v___x_1787_);
v___x_1789_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1772_, v_e_1774_, v_fvarId_1788_);
return v___x_1789_;
}
else
{
lean_object* v___x_1790_; 
lean_dec_ref(v_e_1774_);
v___x_1790_ = lean_box(1);
return v___x_1790_;
}
}
case 3:
{
lean_object* v_args_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v_args_1791_ = lean_ctor_get(v_e_1774_, 2);
lean_inc_ref(v_args_1791_);
v___x_1792_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1772_, v_s_1773_, v_args_1791_, v_translator_1775_);
v___x_1793_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1772_, v_e_1774_, v___x_1792_);
return v___x_1793_;
}
case 4:
{
lean_object* v_fvarId_1794_; lean_object* v_args_1795_; lean_object* v___x_1796_; 
v_fvarId_1794_ = lean_ctor_get(v_e_1774_, 0);
v_args_1795_ = lean_ctor_get(v_e_1774_, 1);
lean_inc(v_fvarId_1794_);
v___x_1796_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1773_, v_fvarId_1794_, v_translator_1775_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_fvarId_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v_fvarId_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_fvarId_1797_);
lean_dec_ref(v___x_1796_);
lean_inc_ref(v_args_1795_);
v___x_1798_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1772_, v_s_1773_, v_args_1795_, v_translator_1775_);
v___x_1799_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_1772_, v_e_1774_, v_fvarId_1797_, v___x_1798_);
lean_dec_ref(v_e_1774_);
return v___x_1799_;
}
else
{
lean_object* v___x_1800_; 
lean_dec_ref(v_e_1774_);
v___x_1800_ = lean_box(1);
return v___x_1800_;
}
}
case 5:
{
lean_object* v_args_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v_args_1801_ = lean_ctor_get(v_e_1774_, 1);
lean_inc_ref(v_args_1801_);
v___x_1802_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1772_, v_s_1773_, v_args_1801_, v_translator_1775_);
v___x_1803_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1772_, v_e_1774_, v___x_1802_);
return v___x_1803_;
}
case 6:
{
lean_object* v_var_1804_; 
v_var_1804_ = lean_ctor_get(v_e_1774_, 1);
lean_inc(v_var_1804_);
v_fvarId_1777_ = v_var_1804_;
goto v___jp_1776_;
}
case 7:
{
lean_object* v_var_1805_; 
v_var_1805_ = lean_ctor_get(v_e_1774_, 1);
lean_inc(v_var_1805_);
v_fvarId_1777_ = v_var_1805_;
goto v___jp_1776_;
}
case 8:
{
lean_object* v_var_1806_; lean_object* v___x_1807_; 
v_var_1806_ = lean_ctor_get(v_e_1774_, 2);
lean_inc(v_var_1806_);
v___x_1807_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1773_, v_var_1806_, v_translator_1775_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_fvarId_1808_; lean_object* v___x_1809_; 
v_fvarId_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_fvarId_1808_);
lean_dec_ref(v___x_1807_);
v___x_1809_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1772_, v_e_1774_, v_fvarId_1808_);
return v___x_1809_;
}
else
{
lean_object* v___x_1810_; 
lean_dec_ref(v_e_1774_);
v___x_1810_ = lean_box(1);
return v___x_1810_;
}
}
case 9:
{
lean_object* v_args_1811_; 
v_args_1811_ = lean_ctor_get(v_e_1774_, 1);
lean_inc_ref(v_args_1811_);
v_args_1783_ = v_args_1811_;
goto v___jp_1782_;
}
case 10:
{
lean_object* v_args_1812_; 
v_args_1812_ = lean_ctor_get(v_e_1774_, 1);
lean_inc_ref(v_args_1812_);
v_args_1783_ = v_args_1812_;
goto v___jp_1782_;
}
case 11:
{
lean_object* v_n_1813_; lean_object* v_var_1814_; lean_object* v___x_1815_; 
v_n_1813_ = lean_ctor_get(v_e_1774_, 0);
lean_inc(v_n_1813_);
v_var_1814_ = lean_ctor_get(v_e_1774_, 1);
lean_inc(v_var_1814_);
v___x_1815_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1773_, v_var_1814_, v_translator_1775_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_fvarId_1816_; lean_object* v___x_1817_; 
v_fvarId_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_fvarId_1816_);
lean_dec_ref(v___x_1815_);
v___x_1817_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_1772_, v_e_1774_, v_n_1813_, v_fvarId_1816_);
lean_dec_ref(v_e_1774_);
return v___x_1817_;
}
else
{
lean_object* v___x_1818_; 
lean_dec(v_n_1813_);
lean_dec_ref(v_e_1774_);
v___x_1818_ = lean_box(1);
return v___x_1818_;
}
}
case 12:
{
lean_object* v_var_1819_; lean_object* v_i_1820_; uint8_t v_updateHeader_1821_; lean_object* v_args_1822_; lean_object* v___x_1823_; 
v_var_1819_ = lean_ctor_get(v_e_1774_, 0);
v_i_1820_ = lean_ctor_get(v_e_1774_, 1);
lean_inc_ref(v_i_1820_);
v_updateHeader_1821_ = lean_ctor_get_uint8(v_e_1774_, sizeof(void*)*3);
v_args_1822_ = lean_ctor_get(v_e_1774_, 2);
lean_inc(v_var_1819_);
v___x_1823_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1773_, v_var_1819_, v_translator_1775_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_fvarId_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v_fvarId_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_fvarId_1824_);
lean_dec_ref(v___x_1823_);
lean_inc_ref(v_args_1822_);
v___x_1825_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1772_, v_s_1773_, v_args_1822_, v_translator_1775_);
v___x_1826_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_1772_, v_e_1774_, v_fvarId_1824_, v_i_1820_, v_updateHeader_1821_, v___x_1825_);
return v___x_1826_;
}
else
{
lean_object* v___x_1827_; 
lean_dec_ref(v_i_1820_);
lean_dec_ref(v_e_1774_);
v___x_1827_ = lean_box(1);
return v___x_1827_;
}
}
case 13:
{
lean_object* v_ty_1828_; lean_object* v_fvarId_1829_; lean_object* v___x_1830_; 
v_ty_1828_ = lean_ctor_get(v_e_1774_, 0);
lean_inc_ref(v_ty_1828_);
v_fvarId_1829_ = lean_ctor_get(v_e_1774_, 1);
lean_inc(v_fvarId_1829_);
v___x_1830_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1773_, v_fvarId_1829_, v_translator_1775_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_fvarId_1831_; lean_object* v___x_1832_; 
v_fvarId_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_fvarId_1831_);
lean_dec_ref(v___x_1830_);
v___x_1832_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_1772_, v_e_1774_, v_ty_1828_, v_fvarId_1831_);
lean_dec_ref(v_e_1774_);
return v___x_1832_;
}
else
{
lean_object* v___x_1833_; 
lean_dec_ref(v_ty_1828_);
lean_dec_ref(v_e_1774_);
v___x_1833_ = lean_box(1);
return v___x_1833_;
}
}
case 14:
{
lean_object* v_fvarId_1834_; lean_object* v___x_1835_; 
v_fvarId_1834_ = lean_ctor_get(v_e_1774_, 0);
lean_inc(v_fvarId_1834_);
v___x_1835_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1773_, v_fvarId_1834_, v_translator_1775_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_fvarId_1836_; lean_object* v___x_1837_; 
v_fvarId_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_fvarId_1836_);
lean_dec_ref(v___x_1835_);
v___x_1837_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_1772_, v_e_1774_, v_fvarId_1836_);
return v___x_1837_;
}
else
{
lean_object* v___x_1838_; 
lean_dec_ref(v_e_1774_);
v___x_1838_ = lean_box(1);
return v___x_1838_;
}
}
case 15:
{
lean_object* v_fvarId_1839_; lean_object* v___x_1840_; 
v_fvarId_1839_ = lean_ctor_get(v_e_1774_, 0);
lean_inc(v_fvarId_1839_);
v___x_1840_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1773_, v_fvarId_1839_, v_translator_1775_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_fvarId_1841_; lean_object* v___x_1842_; 
v_fvarId_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_fvarId_1841_);
lean_dec_ref(v___x_1840_);
v___x_1842_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_1772_, v_e_1774_, v_fvarId_1841_);
return v___x_1842_;
}
else
{
lean_object* v___x_1843_; 
lean_dec_ref(v_e_1774_);
v___x_1843_ = lean_box(1);
return v___x_1843_;
}
}
default: 
{
return v_e_1774_;
}
}
v___jp_1776_:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1773_, v_fvarId_1777_, v_translator_1775_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_fvarId_1779_; lean_object* v___x_1780_; 
v_fvarId_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_fvarId_1779_);
lean_dec_ref(v___x_1778_);
v___x_1780_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1772_, v_e_1774_, v_fvarId_1779_);
return v___x_1780_;
}
else
{
lean_object* v___x_1781_; 
lean_dec(v_e_1774_);
v___x_1781_ = lean_box(1);
return v___x_1781_;
}
}
v___jp_1782_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1772_, v_s_1773_, v_args_1783_, v_translator_1775_);
v___x_1785_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1772_, v_e_1774_, v___x_1784_);
return v___x_1785_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp___boxed(lean_object* v_pu_1844_, lean_object* v_s_1845_, lean_object* v_e_1846_, lean_object* v_translator_1847_){
_start:
{
uint8_t v_pu_boxed_1848_; uint8_t v_translator_boxed_1849_; lean_object* v_res_1850_; 
v_pu_boxed_1848_ = lean_unbox(v_pu_1844_);
v_translator_boxed_1849_ = lean_unbox(v_translator_1847_);
v_res_1850_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_boxed_1848_, v_s_1845_, v_e_1846_, v_translator_boxed_1849_);
lean_dec_ref(v_s_1845_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___redArg(lean_object* v_inst_1851_, lean_object* v_inst_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_apply_2(v_inst_1851_, lean_box(0), v_inst_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(uint8_t v_pu_1854_, uint8_t v_t_1855_, lean_object* v_m_1856_, lean_object* v_n_1857_, lean_object* v_inst_1858_, lean_object* v_inst_1859_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = lean_apply_2(v_inst_1858_, lean_box(0), v_inst_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___boxed(lean_object* v_pu_1861_, lean_object* v_t_1862_, lean_object* v_m_1863_, lean_object* v_n_1864_, lean_object* v_inst_1865_, lean_object* v_inst_1866_){
_start:
{
uint8_t v_pu_boxed_1867_; uint8_t v_t_boxed_1868_; lean_object* v_res_1869_; 
v_pu_boxed_1867_ = lean_unbox(v_pu_1861_);
v_t_boxed_1868_ = lean_unbox(v_t_1862_);
v_res_1869_ = l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(v_pu_boxed_1867_, v_t_boxed_1868_, v_m_1863_, v_n_1864_, v_inst_1865_, v_inst_1866_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0(lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_f_1872_){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = lean_apply_1(v_inst_1870_, v_f_1872_);
v___x_1874_ = lean_apply_2(v_inst_1871_, lean_box(0), v___x_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg(lean_object* v_inst_1875_, lean_object* v_inst_1876_){
_start:
{
lean_object* v___f_1877_; 
v___f_1877_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1877_, 0, v_inst_1876_);
lean_closure_set(v___f_1877_, 1, v_inst_1875_);
return v___f_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(uint8_t v_pu_1878_, lean_object* v_m_1879_, lean_object* v_n_1880_, lean_object* v_inst_1881_, lean_object* v_inst_1882_){
_start:
{
lean_object* v___f_1883_; 
v___f_1883_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1883_, 0, v_inst_1882_);
lean_closure_set(v___f_1883_, 1, v_inst_1881_);
return v___f_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___boxed(lean_object* v_pu_1884_, lean_object* v_m_1885_, lean_object* v_n_1886_, lean_object* v_inst_1887_, lean_object* v_inst_1888_){
_start:
{
uint8_t v_pu_boxed_1889_; lean_object* v_res_1890_; 
v_pu_boxed_1889_ = lean_unbox(v_pu_1884_);
v_res_1890_ = l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(v_pu_boxed_1889_, v_m_1885_, v_n_1886_, v_inst_1887_, v_inst_1888_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___lam__0(lean_object* v___x_1891_, lean_object* v___x_1892_, lean_object* v_fvarId_1893_, lean_object* v_arg_1894_, lean_object* v_s_1895_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1891_, v___x_1892_, v_s_1895_, v_fvarId_1893_, v_arg_1894_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg(lean_object* v_inst_1899_, lean_object* v_fvarId_1900_, lean_object* v_arg_1901_){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___f_1904_; lean_object* v___x_1905_; 
v___x_1902_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1903_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1904_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1904_, 0, v___x_1902_);
lean_closure_set(v___f_1904_, 1, v___x_1903_);
lean_closure_set(v___f_1904_, 2, v_fvarId_1900_);
lean_closure_set(v___f_1904_, 3, v_arg_1901_);
v___x_1905_ = lean_apply_1(v_inst_1899_, v___f_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst(lean_object* v_m_1906_, uint8_t v_pu_1907_, lean_object* v_inst_1908_, lean_object* v_fvarId_1909_, lean_object* v_arg_1910_){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___f_1913_; lean_object* v___x_1914_; 
v___x_1911_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1912_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1913_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1913_, 0, v___x_1911_);
lean_closure_set(v___f_1913_, 1, v___x_1912_);
lean_closure_set(v___f_1913_, 2, v_fvarId_1909_);
lean_closure_set(v___f_1913_, 3, v_arg_1910_);
v___x_1914_ = lean_apply_1(v_inst_1908_, v___f_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___boxed(lean_object* v_m_1915_, lean_object* v_pu_1916_, lean_object* v_inst_1917_, lean_object* v_fvarId_1918_, lean_object* v_arg_1919_){
_start:
{
uint8_t v_pu_boxed_1920_; lean_object* v_res_1921_; 
v_pu_boxed_1920_ = lean_unbox(v_pu_1916_);
v_res_1921_ = l_Lean_Compiler_LCNF_addSubst(v_m_1915_, v_pu_boxed_1920_, v_inst_1917_, v_fvarId_1918_, v_arg_1919_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0(lean_object* v_fvarId_x27_1922_, lean_object* v___x_1923_, lean_object* v___x_1924_, lean_object* v_fvarId_1925_, lean_object* v_s_1926_){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1927_, 0, v_fvarId_x27_1922_);
v___x_1928_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1923_, v___x_1924_, v_s_1926_, v_fvarId_1925_, v___x_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg(lean_object* v_inst_1929_, lean_object* v_fvarId_1930_, lean_object* v_fvarId_x27_1931_){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___f_1934_; lean_object* v___x_1935_; 
v___x_1932_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1933_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1934_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1934_, 0, v_fvarId_x27_1931_);
lean_closure_set(v___f_1934_, 1, v___x_1932_);
lean_closure_set(v___f_1934_, 2, v___x_1933_);
lean_closure_set(v___f_1934_, 3, v_fvarId_1930_);
v___x_1935_ = lean_apply_1(v_inst_1929_, v___f_1934_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst(lean_object* v_m_1936_, uint8_t v_ph_1937_, lean_object* v_inst_1938_, lean_object* v_fvarId_1939_, lean_object* v_fvarId_x27_1940_){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___f_1943_; lean_object* v___x_1944_; 
v___x_1941_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1942_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1943_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1943_, 0, v_fvarId_x27_1940_);
lean_closure_set(v___f_1943_, 1, v___x_1941_);
lean_closure_set(v___f_1943_, 2, v___x_1942_);
lean_closure_set(v___f_1943_, 3, v_fvarId_1939_);
v___x_1944_ = lean_apply_1(v_inst_1938_, v___f_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___boxed(lean_object* v_m_1945_, lean_object* v_ph_1946_, lean_object* v_inst_1947_, lean_object* v_fvarId_1948_, lean_object* v_fvarId_x27_1949_){
_start:
{
uint8_t v_ph_boxed_1950_; lean_object* v_res_1951_; 
v_ph_boxed_1950_ = lean_unbox(v_ph_1946_);
v_res_1951_ = l_Lean_Compiler_LCNF_addFVarSubst(v_m_1945_, v_ph_boxed_1950_, v_inst_1947_, v_fvarId_1948_, v_fvarId_x27_1949_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(lean_object* v_fvarId_1952_, uint8_t v_t_1953_, lean_object* v_toPure_1954_, lean_object* v_____do__lift_1955_){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_____do__lift_1955_, v_fvarId_1952_, v_t_1953_);
v___x_1957_ = lean_apply_2(v_toPure_1954_, lean_box(0), v___x_1956_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed(lean_object* v_fvarId_1958_, lean_object* v_t_1959_, lean_object* v_toPure_1960_, lean_object* v_____do__lift_1961_){
_start:
{
uint8_t v_t_boxed_1962_; lean_object* v_res_1963_; 
v_t_boxed_1962_ = lean_unbox(v_t_1959_);
v_res_1963_ = l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(v_fvarId_1958_, v_t_boxed_1962_, v_toPure_1960_, v_____do__lift_1961_);
lean_dec_ref(v_____do__lift_1961_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg(uint8_t v_t_1964_, lean_object* v_inst_1965_, lean_object* v_inst_1966_, lean_object* v_fvarId_1967_){
_start:
{
lean_object* v_toApplicative_1968_; lean_object* v_toBind_1969_; lean_object* v_toPure_1970_; lean_object* v___x_1971_; lean_object* v___f_1972_; lean_object* v___x_1973_; 
v_toApplicative_1968_ = lean_ctor_get(v_inst_1966_, 0);
lean_inc_ref(v_toApplicative_1968_);
v_toBind_1969_ = lean_ctor_get(v_inst_1966_, 1);
lean_inc(v_toBind_1969_);
lean_dec_ref(v_inst_1966_);
v_toPure_1970_ = lean_ctor_get(v_toApplicative_1968_, 1);
lean_inc(v_toPure_1970_);
lean_dec_ref(v_toApplicative_1968_);
v___x_1971_ = lean_box(v_t_1964_);
v___f_1972_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1972_, 0, v_fvarId_1967_);
lean_closure_set(v___f_1972_, 1, v___x_1971_);
lean_closure_set(v___f_1972_, 2, v_toPure_1970_);
v___x_1973_ = lean_apply_4(v_toBind_1969_, lean_box(0), lean_box(0), v_inst_1965_, v___f_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___boxed(lean_object* v_t_1974_, lean_object* v_inst_1975_, lean_object* v_inst_1976_, lean_object* v_fvarId_1977_){
_start:
{
uint8_t v_t_boxed_1978_; lean_object* v_res_1979_; 
v_t_boxed_1978_ = lean_unbox(v_t_1974_);
v_res_1979_ = l_Lean_Compiler_LCNF_normFVar___redArg(v_t_boxed_1978_, v_inst_1975_, v_inst_1976_, v_fvarId_1977_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar(lean_object* v_m_1980_, uint8_t v_pu_1981_, uint8_t v_t_1982_, lean_object* v_inst_1983_, lean_object* v_inst_1984_, lean_object* v_fvarId_1985_){
_start:
{
lean_object* v_toApplicative_1986_; lean_object* v_toBind_1987_; lean_object* v_toPure_1988_; lean_object* v___x_1989_; lean_object* v___f_1990_; lean_object* v___x_1991_; 
v_toApplicative_1986_ = lean_ctor_get(v_inst_1984_, 0);
lean_inc_ref(v_toApplicative_1986_);
v_toBind_1987_ = lean_ctor_get(v_inst_1984_, 1);
lean_inc(v_toBind_1987_);
lean_dec_ref(v_inst_1984_);
v_toPure_1988_ = lean_ctor_get(v_toApplicative_1986_, 1);
lean_inc(v_toPure_1988_);
lean_dec_ref(v_toApplicative_1986_);
v___x_1989_ = lean_box(v_t_1982_);
v___f_1990_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1990_, 0, v_fvarId_1985_);
lean_closure_set(v___f_1990_, 1, v___x_1989_);
lean_closure_set(v___f_1990_, 2, v_toPure_1988_);
v___x_1991_ = lean_apply_4(v_toBind_1987_, lean_box(0), lean_box(0), v_inst_1983_, v___f_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___boxed(lean_object* v_m_1992_, lean_object* v_pu_1993_, lean_object* v_t_1994_, lean_object* v_inst_1995_, lean_object* v_inst_1996_, lean_object* v_fvarId_1997_){
_start:
{
uint8_t v_pu_boxed_1998_; uint8_t v_t_boxed_1999_; lean_object* v_res_2000_; 
v_pu_boxed_1998_ = lean_unbox(v_pu_1993_);
v_t_boxed_1999_ = lean_unbox(v_t_1994_);
v_res_2000_ = l_Lean_Compiler_LCNF_normFVar(v_m_1992_, v_pu_boxed_1998_, v_t_boxed_1999_, v_inst_1995_, v_inst_1996_, v_fvarId_1997_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(uint8_t v_pu_2001_, uint8_t v_t_2002_, lean_object* v_e_2003_, lean_object* v_toPure_2004_, lean_object* v_____do__lift_2005_){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2001_, v_____do__lift_2005_, v_t_2002_, v_e_2003_);
v___x_2007_ = lean_apply_2(v_toPure_2004_, lean_box(0), v___x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed(lean_object* v_pu_2008_, lean_object* v_t_2009_, lean_object* v_e_2010_, lean_object* v_toPure_2011_, lean_object* v_____do__lift_2012_){
_start:
{
uint8_t v_pu_boxed_2013_; uint8_t v_t_boxed_2014_; lean_object* v_res_2015_; 
v_pu_boxed_2013_ = lean_unbox(v_pu_2008_);
v_t_boxed_2014_ = lean_unbox(v_t_2009_);
v_res_2015_ = l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(v_pu_boxed_2013_, v_t_boxed_2014_, v_e_2010_, v_toPure_2011_, v_____do__lift_2012_);
lean_dec_ref(v_____do__lift_2012_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg(uint8_t v_pu_2016_, uint8_t v_t_2017_, lean_object* v_inst_2018_, lean_object* v_inst_2019_, lean_object* v_e_2020_){
_start:
{
lean_object* v_toApplicative_2021_; lean_object* v_toBind_2022_; lean_object* v_toPure_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___f_2026_; lean_object* v___x_2027_; 
v_toApplicative_2021_ = lean_ctor_get(v_inst_2019_, 0);
lean_inc_ref(v_toApplicative_2021_);
v_toBind_2022_ = lean_ctor_get(v_inst_2019_, 1);
lean_inc(v_toBind_2022_);
lean_dec_ref(v_inst_2019_);
v_toPure_2023_ = lean_ctor_get(v_toApplicative_2021_, 1);
lean_inc(v_toPure_2023_);
lean_dec_ref(v_toApplicative_2021_);
v___x_2024_ = lean_box(v_pu_2016_);
v___x_2025_ = lean_box(v_t_2017_);
v___f_2026_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2026_, 0, v___x_2024_);
lean_closure_set(v___f_2026_, 1, v___x_2025_);
lean_closure_set(v___f_2026_, 2, v_e_2020_);
lean_closure_set(v___f_2026_, 3, v_toPure_2023_);
v___x_2027_ = lean_apply_4(v_toBind_2022_, lean_box(0), lean_box(0), v_inst_2018_, v___f_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___boxed(lean_object* v_pu_2028_, lean_object* v_t_2029_, lean_object* v_inst_2030_, lean_object* v_inst_2031_, lean_object* v_e_2032_){
_start:
{
uint8_t v_pu_boxed_2033_; uint8_t v_t_boxed_2034_; lean_object* v_res_2035_; 
v_pu_boxed_2033_ = lean_unbox(v_pu_2028_);
v_t_boxed_2034_ = lean_unbox(v_t_2029_);
v_res_2035_ = l_Lean_Compiler_LCNF_normExpr___redArg(v_pu_boxed_2033_, v_t_boxed_2034_, v_inst_2030_, v_inst_2031_, v_e_2032_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr(lean_object* v_m_2036_, uint8_t v_pu_2037_, uint8_t v_t_2038_, lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_e_2041_){
_start:
{
lean_object* v_toApplicative_2042_; lean_object* v_toBind_2043_; lean_object* v_toPure_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___f_2047_; lean_object* v___x_2048_; 
v_toApplicative_2042_ = lean_ctor_get(v_inst_2040_, 0);
lean_inc_ref(v_toApplicative_2042_);
v_toBind_2043_ = lean_ctor_get(v_inst_2040_, 1);
lean_inc(v_toBind_2043_);
lean_dec_ref(v_inst_2040_);
v_toPure_2044_ = lean_ctor_get(v_toApplicative_2042_, 1);
lean_inc(v_toPure_2044_);
lean_dec_ref(v_toApplicative_2042_);
v___x_2045_ = lean_box(v_pu_2037_);
v___x_2046_ = lean_box(v_t_2038_);
v___f_2047_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2047_, 0, v___x_2045_);
lean_closure_set(v___f_2047_, 1, v___x_2046_);
lean_closure_set(v___f_2047_, 2, v_e_2041_);
lean_closure_set(v___f_2047_, 3, v_toPure_2044_);
v___x_2048_ = lean_apply_4(v_toBind_2043_, lean_box(0), lean_box(0), v_inst_2039_, v___f_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___boxed(lean_object* v_m_2049_, lean_object* v_pu_2050_, lean_object* v_t_2051_, lean_object* v_inst_2052_, lean_object* v_inst_2053_, lean_object* v_e_2054_){
_start:
{
uint8_t v_pu_boxed_2055_; uint8_t v_t_boxed_2056_; lean_object* v_res_2057_; 
v_pu_boxed_2055_ = lean_unbox(v_pu_2050_);
v_t_boxed_2056_ = lean_unbox(v_t_2051_);
v_res_2057_ = l_Lean_Compiler_LCNF_normExpr(v_m_2049_, v_pu_boxed_2055_, v_t_boxed_2056_, v_inst_2052_, v_inst_2053_, v_e_2054_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0(uint8_t v_pu_2058_, lean_object* v_arg_2059_, uint8_t v_t_2060_, lean_object* v_toPure_2061_, lean_object* v_____do__lift_2062_){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2058_, v_____do__lift_2062_, v_arg_2059_, v_t_2060_);
v___x_2064_ = lean_apply_2(v_toPure_2061_, lean_box(0), v___x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed(lean_object* v_pu_2065_, lean_object* v_arg_2066_, lean_object* v_t_2067_, lean_object* v_toPure_2068_, lean_object* v_____do__lift_2069_){
_start:
{
uint8_t v_pu_boxed_2070_; uint8_t v_t_boxed_2071_; lean_object* v_res_2072_; 
v_pu_boxed_2070_ = lean_unbox(v_pu_2065_);
v_t_boxed_2071_ = lean_unbox(v_t_2067_);
v_res_2072_ = l_Lean_Compiler_LCNF_normArg___redArg___lam__0(v_pu_boxed_2070_, v_arg_2066_, v_t_boxed_2071_, v_toPure_2068_, v_____do__lift_2069_);
lean_dec_ref(v_____do__lift_2069_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg(uint8_t v_pu_2073_, uint8_t v_t_2074_, lean_object* v_inst_2075_, lean_object* v_inst_2076_, lean_object* v_arg_2077_){
_start:
{
lean_object* v_toApplicative_2078_; lean_object* v_toBind_2079_; lean_object* v_toPure_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___f_2083_; lean_object* v___x_2084_; 
v_toApplicative_2078_ = lean_ctor_get(v_inst_2076_, 0);
lean_inc_ref(v_toApplicative_2078_);
v_toBind_2079_ = lean_ctor_get(v_inst_2076_, 1);
lean_inc(v_toBind_2079_);
lean_dec_ref(v_inst_2076_);
v_toPure_2080_ = lean_ctor_get(v_toApplicative_2078_, 1);
lean_inc(v_toPure_2080_);
lean_dec_ref(v_toApplicative_2078_);
v___x_2081_ = lean_box(v_pu_2073_);
v___x_2082_ = lean_box(v_t_2074_);
v___f_2083_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2083_, 0, v___x_2081_);
lean_closure_set(v___f_2083_, 1, v_arg_2077_);
lean_closure_set(v___f_2083_, 2, v___x_2082_);
lean_closure_set(v___f_2083_, 3, v_toPure_2080_);
v___x_2084_ = lean_apply_4(v_toBind_2079_, lean_box(0), lean_box(0), v_inst_2075_, v___f_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___boxed(lean_object* v_pu_2085_, lean_object* v_t_2086_, lean_object* v_inst_2087_, lean_object* v_inst_2088_, lean_object* v_arg_2089_){
_start:
{
uint8_t v_pu_boxed_2090_; uint8_t v_t_boxed_2091_; lean_object* v_res_2092_; 
v_pu_boxed_2090_ = lean_unbox(v_pu_2085_);
v_t_boxed_2091_ = lean_unbox(v_t_2086_);
v_res_2092_ = l_Lean_Compiler_LCNF_normArg___redArg(v_pu_boxed_2090_, v_t_boxed_2091_, v_inst_2087_, v_inst_2088_, v_arg_2089_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg(lean_object* v_m_2093_, uint8_t v_pu_2094_, uint8_t v_t_2095_, lean_object* v_inst_2096_, lean_object* v_inst_2097_, lean_object* v_arg_2098_){
_start:
{
lean_object* v_toApplicative_2099_; lean_object* v_toBind_2100_; lean_object* v_toPure_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___f_2104_; lean_object* v___x_2105_; 
v_toApplicative_2099_ = lean_ctor_get(v_inst_2097_, 0);
lean_inc_ref(v_toApplicative_2099_);
v_toBind_2100_ = lean_ctor_get(v_inst_2097_, 1);
lean_inc(v_toBind_2100_);
lean_dec_ref(v_inst_2097_);
v_toPure_2101_ = lean_ctor_get(v_toApplicative_2099_, 1);
lean_inc(v_toPure_2101_);
lean_dec_ref(v_toApplicative_2099_);
v___x_2102_ = lean_box(v_pu_2094_);
v___x_2103_ = lean_box(v_t_2095_);
v___f_2104_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2104_, 0, v___x_2102_);
lean_closure_set(v___f_2104_, 1, v_arg_2098_);
lean_closure_set(v___f_2104_, 2, v___x_2103_);
lean_closure_set(v___f_2104_, 3, v_toPure_2101_);
v___x_2105_ = lean_apply_4(v_toBind_2100_, lean_box(0), lean_box(0), v_inst_2096_, v___f_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___boxed(lean_object* v_m_2106_, lean_object* v_pu_2107_, lean_object* v_t_2108_, lean_object* v_inst_2109_, lean_object* v_inst_2110_, lean_object* v_arg_2111_){
_start:
{
uint8_t v_pu_boxed_2112_; uint8_t v_t_boxed_2113_; lean_object* v_res_2114_; 
v_pu_boxed_2112_ = lean_unbox(v_pu_2107_);
v_t_boxed_2113_ = lean_unbox(v_t_2108_);
v_res_2114_ = l_Lean_Compiler_LCNF_normArg(v_m_2106_, v_pu_boxed_2112_, v_t_boxed_2113_, v_inst_2109_, v_inst_2110_, v_arg_2111_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(uint8_t v_pu_2115_, lean_object* v_e_2116_, uint8_t v_t_2117_, lean_object* v_toPure_2118_, lean_object* v_____do__lift_2119_){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_2115_, v_____do__lift_2119_, v_e_2116_, v_t_2117_);
v___x_2121_ = lean_apply_2(v_toPure_2118_, lean_box(0), v___x_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed(lean_object* v_pu_2122_, lean_object* v_e_2123_, lean_object* v_t_2124_, lean_object* v_toPure_2125_, lean_object* v_____do__lift_2126_){
_start:
{
uint8_t v_pu_boxed_2127_; uint8_t v_t_boxed_2128_; lean_object* v_res_2129_; 
v_pu_boxed_2127_ = lean_unbox(v_pu_2122_);
v_t_boxed_2128_ = lean_unbox(v_t_2124_);
v_res_2129_ = l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(v_pu_boxed_2127_, v_e_2123_, v_t_boxed_2128_, v_toPure_2125_, v_____do__lift_2126_);
lean_dec_ref(v_____do__lift_2126_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg(uint8_t v_pu_2130_, uint8_t v_t_2131_, lean_object* v_inst_2132_, lean_object* v_inst_2133_, lean_object* v_e_2134_){
_start:
{
lean_object* v_toApplicative_2135_; lean_object* v_toBind_2136_; lean_object* v_toPure_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___f_2140_; lean_object* v___x_2141_; 
v_toApplicative_2135_ = lean_ctor_get(v_inst_2133_, 0);
lean_inc_ref(v_toApplicative_2135_);
v_toBind_2136_ = lean_ctor_get(v_inst_2133_, 1);
lean_inc(v_toBind_2136_);
lean_dec_ref(v_inst_2133_);
v_toPure_2137_ = lean_ctor_get(v_toApplicative_2135_, 1);
lean_inc(v_toPure_2137_);
lean_dec_ref(v_toApplicative_2135_);
v___x_2138_ = lean_box(v_pu_2130_);
v___x_2139_ = lean_box(v_t_2131_);
v___f_2140_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2140_, 0, v___x_2138_);
lean_closure_set(v___f_2140_, 1, v_e_2134_);
lean_closure_set(v___f_2140_, 2, v___x_2139_);
lean_closure_set(v___f_2140_, 3, v_toPure_2137_);
v___x_2141_ = lean_apply_4(v_toBind_2136_, lean_box(0), lean_box(0), v_inst_2132_, v___f_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___boxed(lean_object* v_pu_2142_, lean_object* v_t_2143_, lean_object* v_inst_2144_, lean_object* v_inst_2145_, lean_object* v_e_2146_){
_start:
{
uint8_t v_pu_boxed_2147_; uint8_t v_t_boxed_2148_; lean_object* v_res_2149_; 
v_pu_boxed_2147_ = lean_unbox(v_pu_2142_);
v_t_boxed_2148_ = lean_unbox(v_t_2143_);
v_res_2149_ = l_Lean_Compiler_LCNF_normLetValue___redArg(v_pu_boxed_2147_, v_t_boxed_2148_, v_inst_2144_, v_inst_2145_, v_e_2146_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue(lean_object* v_m_2150_, uint8_t v_pu_2151_, uint8_t v_t_2152_, lean_object* v_inst_2153_, lean_object* v_inst_2154_, lean_object* v_e_2155_){
_start:
{
lean_object* v_toApplicative_2156_; lean_object* v_toBind_2157_; lean_object* v_toPure_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___f_2161_; lean_object* v___x_2162_; 
v_toApplicative_2156_ = lean_ctor_get(v_inst_2154_, 0);
lean_inc_ref(v_toApplicative_2156_);
v_toBind_2157_ = lean_ctor_get(v_inst_2154_, 1);
lean_inc(v_toBind_2157_);
lean_dec_ref(v_inst_2154_);
v_toPure_2158_ = lean_ctor_get(v_toApplicative_2156_, 1);
lean_inc(v_toPure_2158_);
lean_dec_ref(v_toApplicative_2156_);
v___x_2159_ = lean_box(v_pu_2151_);
v___x_2160_ = lean_box(v_t_2152_);
v___f_2161_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2161_, 0, v___x_2159_);
lean_closure_set(v___f_2161_, 1, v_e_2155_);
lean_closure_set(v___f_2161_, 2, v___x_2160_);
lean_closure_set(v___f_2161_, 3, v_toPure_2158_);
v___x_2162_ = lean_apply_4(v_toBind_2157_, lean_box(0), lean_box(0), v_inst_2153_, v___f_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___boxed(lean_object* v_m_2163_, lean_object* v_pu_2164_, lean_object* v_t_2165_, lean_object* v_inst_2166_, lean_object* v_inst_2167_, lean_object* v_e_2168_){
_start:
{
uint8_t v_pu_boxed_2169_; uint8_t v_t_boxed_2170_; lean_object* v_res_2171_; 
v_pu_boxed_2169_ = lean_unbox(v_pu_2164_);
v_t_boxed_2170_ = lean_unbox(v_t_2165_);
v_res_2171_ = l_Lean_Compiler_LCNF_normLetValue(v_m_2163_, v_pu_boxed_2169_, v_t_boxed_2170_, v_inst_2166_, v_inst_2167_, v_e_2168_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore(uint8_t v_pu_2172_, lean_object* v_s_2173_, lean_object* v_e_2174_, uint8_t v_translator_2175_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2172_, v_s_2173_, v_translator_2175_, v_e_2174_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore___boxed(lean_object* v_pu_2177_, lean_object* v_s_2178_, lean_object* v_e_2179_, lean_object* v_translator_2180_){
_start:
{
uint8_t v_pu_boxed_2181_; uint8_t v_translator_boxed_2182_; lean_object* v_res_2183_; 
v_pu_boxed_2181_ = lean_unbox(v_pu_2177_);
v_translator_boxed_2182_ = lean_unbox(v_translator_2180_);
v_res_2183_ = l_Lean_Compiler_LCNF_normExprCore(v_pu_boxed_2181_, v_s_2178_, v_e_2179_, v_translator_boxed_2182_);
lean_dec_ref(v_s_2178_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(uint8_t v_pu_2184_, lean_object* v_args_2185_, uint8_t v_t_2186_, lean_object* v_toPure_2187_, lean_object* v_____do__lift_2188_){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_2184_, v_____do__lift_2188_, v_args_2185_, v_t_2186_);
v___x_2190_ = lean_apply_2(v_toPure_2187_, lean_box(0), v___x_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed(lean_object* v_pu_2191_, lean_object* v_args_2192_, lean_object* v_t_2193_, lean_object* v_toPure_2194_, lean_object* v_____do__lift_2195_){
_start:
{
uint8_t v_pu_boxed_2196_; uint8_t v_t_boxed_2197_; lean_object* v_res_2198_; 
v_pu_boxed_2196_ = lean_unbox(v_pu_2191_);
v_t_boxed_2197_ = lean_unbox(v_t_2193_);
v_res_2198_ = l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(v_pu_boxed_2196_, v_args_2192_, v_t_boxed_2197_, v_toPure_2194_, v_____do__lift_2195_);
lean_dec_ref(v_____do__lift_2195_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg(uint8_t v_pu_2199_, uint8_t v_t_2200_, lean_object* v_inst_2201_, lean_object* v_inst_2202_, lean_object* v_args_2203_){
_start:
{
lean_object* v_toApplicative_2204_; lean_object* v_toBind_2205_; lean_object* v_toPure_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___f_2209_; lean_object* v___x_2210_; 
v_toApplicative_2204_ = lean_ctor_get(v_inst_2202_, 0);
lean_inc_ref(v_toApplicative_2204_);
v_toBind_2205_ = lean_ctor_get(v_inst_2202_, 1);
lean_inc(v_toBind_2205_);
lean_dec_ref(v_inst_2202_);
v_toPure_2206_ = lean_ctor_get(v_toApplicative_2204_, 1);
lean_inc(v_toPure_2206_);
lean_dec_ref(v_toApplicative_2204_);
v___x_2207_ = lean_box(v_pu_2199_);
v___x_2208_ = lean_box(v_t_2200_);
v___f_2209_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2209_, 0, v___x_2207_);
lean_closure_set(v___f_2209_, 1, v_args_2203_);
lean_closure_set(v___f_2209_, 2, v___x_2208_);
lean_closure_set(v___f_2209_, 3, v_toPure_2206_);
v___x_2210_ = lean_apply_4(v_toBind_2205_, lean_box(0), lean_box(0), v_inst_2201_, v___f_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___boxed(lean_object* v_pu_2211_, lean_object* v_t_2212_, lean_object* v_inst_2213_, lean_object* v_inst_2214_, lean_object* v_args_2215_){
_start:
{
uint8_t v_pu_boxed_2216_; uint8_t v_t_boxed_2217_; lean_object* v_res_2218_; 
v_pu_boxed_2216_ = lean_unbox(v_pu_2211_);
v_t_boxed_2217_ = lean_unbox(v_t_2212_);
v_res_2218_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_boxed_2216_, v_t_boxed_2217_, v_inst_2213_, v_inst_2214_, v_args_2215_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs(lean_object* v_m_2219_, uint8_t v_pu_2220_, uint8_t v_t_2221_, lean_object* v_inst_2222_, lean_object* v_inst_2223_, lean_object* v_args_2224_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_2220_, v_t_2221_, v_inst_2222_, v_inst_2223_, v_args_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___boxed(lean_object* v_m_2226_, lean_object* v_pu_2227_, lean_object* v_t_2228_, lean_object* v_inst_2229_, lean_object* v_inst_2230_, lean_object* v_args_2231_){
_start:
{
uint8_t v_pu_boxed_2232_; uint8_t v_t_boxed_2233_; lean_object* v_res_2234_; 
v_pu_boxed_2232_ = lean_unbox(v_pu_2227_);
v_t_boxed_2233_ = lean_unbox(v_t_2228_);
v_res_2234_ = l_Lean_Compiler_LCNF_normArgs(v_m_2226_, v_pu_boxed_2232_, v_t_boxed_2233_, v_inst_2229_, v_inst_2230_, v_args_2231_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object* v_binderName_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v_lctx_2240_; lean_object* v_nextIdx_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2254_; 
v___x_2238_ = lean_st_ref_get(v_a_2236_);
v___x_2239_ = lean_st_ref_take(v_a_2236_);
v_lctx_2240_ = lean_ctor_get(v___x_2239_, 0);
v_nextIdx_2241_ = lean_ctor_get(v___x_2239_, 1);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2243_ = v___x_2239_;
v_isShared_2244_ = v_isSharedCheck_2254_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_nextIdx_2241_);
lean_inc(v_lctx_2240_);
lean_dec(v___x_2239_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2254_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2245_ = lean_unsigned_to_nat(1u);
v___x_2246_ = lean_nat_add(v_nextIdx_2241_, v___x_2245_);
lean_dec(v_nextIdx_2241_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 1, v___x_2246_);
v___x_2248_ = v___x_2243_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_lctx_2240_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2249_; lean_object* v_nextIdx_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2249_ = lean_st_ref_set(v_a_2236_, v___x_2248_);
v_nextIdx_2250_ = lean_ctor_get(v___x_2238_, 1);
lean_inc(v_nextIdx_2250_);
lean_dec(v___x_2238_);
v___x_2251_ = l_Lean_Name_num___override(v_binderName_2235_, v_nextIdx_2250_);
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
return v___x_2252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg___boxed(lean_object* v_binderName_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2255_, v_a_2256_);
lean_dec(v_a_2256_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object* v_binderName_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2259_, v_a_2261_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___boxed(lean_object* v_binderName_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_Compiler_LCNF_mkFreshBinderName(v_binderName_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_);
lean_dec(v_a_2270_);
lean_dec_ref(v_a_2269_);
lean_dec(v_a_2268_);
lean_dec_ref(v_a_2267_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(lean_object* v_binderName_2273_, lean_object* v_baseName_2274_, lean_object* v_a_2275_){
_start:
{
uint8_t v___x_2277_; 
v___x_2277_ = l_Lean_Name_isAnonymous(v_binderName_2273_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; 
lean_dec(v_baseName_2274_);
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v_binderName_2273_);
return v___x_2278_;
}
else
{
lean_object* v___x_2279_; 
lean_dec(v_binderName_2273_);
v___x_2279_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_baseName_2274_, v_a_2275_);
return v___x_2279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg___boxed(lean_object* v_binderName_2280_, lean_object* v_baseName_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2280_, v_baseName_2281_, v_a_2282_);
lean_dec(v_a_2282_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous(lean_object* v_binderName_2285_, lean_object* v_baseName_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2285_, v_baseName_2286_, v_a_2288_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___boxed(lean_object* v_binderName_2293_, lean_object* v_baseName_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_Compiler_LCNF_ensureNotAnonymous(v_binderName_2293_, v_baseName_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(lean_object* v___y_2301_){
_start:
{
lean_object* v___x_2303_; lean_object* v_ngen_2304_; lean_object* v_namePrefix_2305_; lean_object* v_idx_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2336_; 
v___x_2303_ = lean_st_ref_get(v___y_2301_);
v_ngen_2304_ = lean_ctor_get(v___x_2303_, 2);
lean_inc_ref(v_ngen_2304_);
lean_dec(v___x_2303_);
v_namePrefix_2305_ = lean_ctor_get(v_ngen_2304_, 0);
v_idx_2306_ = lean_ctor_get(v_ngen_2304_, 1);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_ngen_2304_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2308_ = v_ngen_2304_;
v_isShared_2309_ = v_isSharedCheck_2336_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_idx_2306_);
lean_inc(v_namePrefix_2305_);
lean_dec(v_ngen_2304_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2336_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2310_; lean_object* v_env_2311_; lean_object* v_nextMacroScope_2312_; lean_object* v_auxDeclNGen_2313_; lean_object* v_traceState_2314_; lean_object* v_cache_2315_; lean_object* v_messages_2316_; lean_object* v_infoState_2317_; lean_object* v_snapshotTasks_2318_; lean_object* v_newDecls_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2334_; 
v___x_2310_ = lean_st_ref_take(v___y_2301_);
v_env_2311_ = lean_ctor_get(v___x_2310_, 0);
v_nextMacroScope_2312_ = lean_ctor_get(v___x_2310_, 1);
v_auxDeclNGen_2313_ = lean_ctor_get(v___x_2310_, 3);
v_traceState_2314_ = lean_ctor_get(v___x_2310_, 4);
v_cache_2315_ = lean_ctor_get(v___x_2310_, 5);
v_messages_2316_ = lean_ctor_get(v___x_2310_, 6);
v_infoState_2317_ = lean_ctor_get(v___x_2310_, 7);
v_snapshotTasks_2318_ = lean_ctor_get(v___x_2310_, 8);
v_newDecls_2319_ = lean_ctor_get(v___x_2310_, 9);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2334_ == 0)
{
lean_object* v_unused_2335_; 
v_unused_2335_ = lean_ctor_get(v___x_2310_, 2);
lean_dec(v_unused_2335_);
v___x_2321_ = v___x_2310_;
v_isShared_2322_ = v_isSharedCheck_2334_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_newDecls_2319_);
lean_inc(v_snapshotTasks_2318_);
lean_inc(v_infoState_2317_);
lean_inc(v_messages_2316_);
lean_inc(v_cache_2315_);
lean_inc(v_traceState_2314_);
lean_inc(v_auxDeclNGen_2313_);
lean_inc(v_nextMacroScope_2312_);
lean_inc(v_env_2311_);
lean_dec(v___x_2310_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2334_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v_r_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2327_; 
lean_inc(v_idx_2306_);
lean_inc(v_namePrefix_2305_);
v_r_2323_ = l_Lean_Name_num___override(v_namePrefix_2305_, v_idx_2306_);
v___x_2324_ = lean_unsigned_to_nat(1u);
v___x_2325_ = lean_nat_add(v_idx_2306_, v___x_2324_);
lean_dec(v_idx_2306_);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 1, v___x_2325_);
v___x_2327_ = v___x_2308_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_namePrefix_2305_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2329_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 2, v___x_2327_);
v___x_2329_ = v___x_2321_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_env_2311_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_nextMacroScope_2312_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2332_, 3, v_auxDeclNGen_2313_);
lean_ctor_set(v_reuseFailAlloc_2332_, 4, v_traceState_2314_);
lean_ctor_set(v_reuseFailAlloc_2332_, 5, v_cache_2315_);
lean_ctor_set(v_reuseFailAlloc_2332_, 6, v_messages_2316_);
lean_ctor_set(v_reuseFailAlloc_2332_, 7, v_infoState_2317_);
lean_ctor_set(v_reuseFailAlloc_2332_, 8, v_snapshotTasks_2318_);
lean_ctor_set(v_reuseFailAlloc_2332_, 9, v_newDecls_2319_);
v___x_2329_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = lean_st_ref_set(v___y_2301_, v___x_2329_);
v___x_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2331_, 0, v_r_2323_);
return v___x_2331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg___boxed(lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2337_);
lean_dec(v___y_2337_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v___x_2345_; lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
v___x_2345_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2343_);
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0___boxed(lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t v_pu_2363_, lean_object* v_binderName_2364_, lean_object* v_type_2365_, uint8_t v_borrow_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2396_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref(v___x_2372_);
v___x_2374_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_2375_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2364_, v___x_2374_, v_a_2368_);
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2378_ = v___x_2375_;
v_isShared_2379_ = v_isSharedCheck_2396_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2375_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2396_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; lean_object* v_lctx_2381_; lean_object* v_nextIdx_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2395_; 
v___x_2380_ = lean_st_ref_take(v_a_2368_);
v_lctx_2381_ = lean_ctor_get(v___x_2380_, 0);
v_nextIdx_2382_ = lean_ctor_get(v___x_2380_, 1);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2384_ = v___x_2380_;
v_isShared_2385_ = v_isSharedCheck_2395_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_nextIdx_2382_);
lean_inc(v_lctx_2381_);
lean_dec(v___x_2380_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2395_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2389_; 
v___x_2386_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2386_, 0, v_a_2373_);
lean_ctor_set(v___x_2386_, 1, v_a_2376_);
lean_ctor_set(v___x_2386_, 2, v_type_2365_);
lean_ctor_set_uint8(v___x_2386_, sizeof(void*)*3, v_borrow_2366_);
lean_inc_ref(v___x_2386_);
v___x_2387_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2363_, v_lctx_2381_, v___x_2386_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v___x_2387_);
v___x_2389_ = v___x_2384_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2387_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_nextIdx_2382_);
v___x_2389_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2390_; lean_object* v___x_2392_; 
v___x_2390_ = lean_st_ref_set(v_a_2368_, v___x_2389_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2386_);
v___x_2392_ = v___x_2378_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2386_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec_ref(v_type_2365_);
lean_dec(v_binderName_2364_);
v_a_2397_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2372_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2372_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam___boxed(lean_object* v_pu_2405_, lean_object* v_binderName_2406_, lean_object* v_type_2407_, lean_object* v_borrow_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
uint8_t v_pu_boxed_2414_; uint8_t v_borrow_boxed_2415_; lean_object* v_res_2416_; 
v_pu_boxed_2414_ = lean_unbox(v_pu_2405_);
v_borrow_boxed_2415_ = lean_unbox(v_borrow_2408_);
v_res_2416_ = l_Lean_Compiler_LCNF_mkParam(v_pu_boxed_2414_, v_binderName_2406_, v_type_2407_, v_borrow_boxed_2415_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2420_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___boxed(lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t v_pu_2432_, lean_object* v_binderName_2433_, lean_object* v_type_2434_, lean_object* v_value_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2465_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_a_2442_);
lean_dec_ref(v___x_2441_);
v___x_2443_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2444_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2433_, v___x_2443_, v_a_2437_);
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2447_ = v___x_2444_;
v_isShared_2448_ = v_isSharedCheck_2465_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2465_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; lean_object* v_lctx_2450_; lean_object* v_nextIdx_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2464_; 
v___x_2449_ = lean_st_ref_take(v_a_2437_);
v_lctx_2450_ = lean_ctor_get(v___x_2449_, 0);
v_nextIdx_2451_ = lean_ctor_get(v___x_2449_, 1);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2453_ = v___x_2449_;
v_isShared_2454_ = v_isSharedCheck_2464_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_nextIdx_2451_);
lean_inc(v_lctx_2450_);
lean_dec(v___x_2449_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2464_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2458_; 
v___x_2455_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2455_, 0, v_a_2442_);
lean_ctor_set(v___x_2455_, 1, v_a_2445_);
lean_ctor_set(v___x_2455_, 2, v_type_2434_);
lean_ctor_set(v___x_2455_, 3, v_value_2435_);
lean_inc_ref(v___x_2455_);
v___x_2456_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2432_, v_lctx_2450_, v___x_2455_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2456_);
v___x_2458_ = v___x_2453_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2456_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v_nextIdx_2451_);
v___x_2458_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
lean_object* v___x_2459_; lean_object* v___x_2461_; 
v___x_2459_ = lean_st_ref_set(v_a_2437_, v___x_2458_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v___x_2455_);
v___x_2461_ = v___x_2447_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2455_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec(v_value_2435_);
lean_dec_ref(v_type_2434_);
lean_dec(v_binderName_2433_);
v_a_2466_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2441_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2441_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl___boxed(lean_object* v_pu_2474_, lean_object* v_binderName_2475_, lean_object* v_type_2476_, lean_object* v_value_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_){
_start:
{
uint8_t v_pu_boxed_2483_; lean_object* v_res_2484_; 
v_pu_boxed_2483_ = lean_unbox(v_pu_2474_);
v_res_2484_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_boxed_2483_, v_binderName_2475_, v_type_2476_, v_value_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_);
lean_dec(v_a_2481_);
lean_dec_ref(v_a_2480_);
lean_dec(v_a_2479_);
lean_dec_ref(v_a_2478_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t v_pu_2488_, lean_object* v_binderName_2489_, lean_object* v_type_2490_, lean_object* v_params_2491_, lean_object* v_value_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2522_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2499_);
lean_dec_ref(v___x_2498_);
v___x_2500_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFunDecl___closed__1));
v___x_2501_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2489_, v___x_2500_, v_a_2494_);
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2504_ = v___x_2501_;
v_isShared_2505_ = v_isSharedCheck_2522_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2501_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2522_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v_lctx_2507_; lean_object* v_nextIdx_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2521_; 
v___x_2506_ = lean_st_ref_take(v_a_2494_);
v_lctx_2507_ = lean_ctor_get(v___x_2506_, 0);
v_nextIdx_2508_ = lean_ctor_get(v___x_2506_, 1);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2510_ = v___x_2506_;
v_isShared_2511_ = v_isSharedCheck_2521_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_nextIdx_2508_);
lean_inc(v_lctx_2507_);
lean_dec(v___x_2506_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2521_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2515_; 
v___x_2512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2512_, 0, v_a_2499_);
lean_ctor_set(v___x_2512_, 1, v_a_2502_);
lean_ctor_set(v___x_2512_, 2, v_params_2491_);
lean_ctor_set(v___x_2512_, 3, v_type_2490_);
lean_ctor_set(v___x_2512_, 4, v_value_2492_);
lean_inc_ref(v___x_2512_);
v___x_2513_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2488_, v_lctx_2507_, v___x_2512_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 0, v___x_2513_);
v___x_2515_ = v___x_2510_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v_nextIdx_2508_);
v___x_2515_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2516_ = lean_st_ref_set(v_a_2494_, v___x_2515_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 0, v___x_2512_);
v___x_2518_ = v___x_2504_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2512_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec_ref(v_value_2492_);
lean_dec_ref(v_params_2491_);
lean_dec_ref(v_type_2490_);
lean_dec(v_binderName_2489_);
v_a_2523_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2498_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2498_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl___boxed(lean_object* v_pu_2531_, lean_object* v_binderName_2532_, lean_object* v_type_2533_, lean_object* v_params_2534_, lean_object* v_value_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
uint8_t v_pu_boxed_2541_; lean_object* v_res_2542_; 
v_pu_boxed_2541_ = lean_unbox(v_pu_2531_);
v_res_2542_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_boxed_2541_, v_binderName_2532_, v_type_2533_, v_params_2534_, v_value_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
lean_dec(v_a_2537_);
lean_dec_ref(v_a_2536_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(uint8_t v_pu_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v_a_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2549_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2550_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2549_, v_a_2545_);
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
lean_dec_ref(v___x_2550_);
v___x_2552_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2553_ = lean_box(1);
v___x_2554_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2543_, v_a_2551_, v___x_2552_, v___x_2553_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased___boxed(lean_object* v_pu_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
uint8_t v_pu_boxed_2561_; lean_object* v_res_2562_; 
v_pu_boxed_2561_ = lean_unbox(v_pu_2555_);
v_res_2562_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_boxed_2561_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t v_pu_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2580_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2580_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2580_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v_fvarId_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2578_; 
v_fvarId_2574_ = lean_ctor_get(v_a_2570_, 0);
lean_inc(v_fvarId_2574_);
v___x_2575_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2575_, 0, v_fvarId_2574_);
v___x_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2576_, 0, v_a_2570_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___x_2576_);
v___x_2578_ = v___x_2572_;
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
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
v_a_2581_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2569_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2569_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased___boxed(lean_object* v_pu_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_){
_start:
{
uint8_t v_pu_boxed_2595_; lean_object* v_res_2596_; 
v_pu_boxed_2595_ = lean_unbox(v_pu_2589_);
v_res_2596_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_boxed_2595_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_);
lean_dec(v_a_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t v_pu_2597_, lean_object* v_p_2598_, lean_object* v_type_2599_, lean_object* v_a_2600_){
_start:
{
lean_object* v_fvarId_2602_; lean_object* v_binderName_2603_; lean_object* v_type_2604_; uint8_t v_borrow_2605_; size_t v___x_2606_; size_t v___x_2607_; uint8_t v___x_2608_; 
v_fvarId_2602_ = lean_ctor_get(v_p_2598_, 0);
v_binderName_2603_ = lean_ctor_get(v_p_2598_, 1);
v_type_2604_ = lean_ctor_get(v_p_2598_, 2);
v_borrow_2605_ = lean_ctor_get_uint8(v_p_2598_, sizeof(void*)*3);
v___x_2606_ = lean_ptr_addr(v_type_2599_);
v___x_2607_ = lean_ptr_addr(v_type_2604_);
v___x_2608_ = lean_usize_dec_eq(v___x_2606_, v___x_2607_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2628_; 
lean_inc(v_binderName_2603_);
lean_inc(v_fvarId_2602_);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_p_2598_);
if (v_isSharedCheck_2628_ == 0)
{
lean_object* v_unused_2629_; lean_object* v_unused_2630_; lean_object* v_unused_2631_; 
v_unused_2629_ = lean_ctor_get(v_p_2598_, 2);
lean_dec(v_unused_2629_);
v_unused_2630_ = lean_ctor_get(v_p_2598_, 1);
lean_dec(v_unused_2630_);
v_unused_2631_ = lean_ctor_get(v_p_2598_, 0);
lean_dec(v_unused_2631_);
v___x_2610_ = v_p_2598_;
v_isShared_2611_ = v_isSharedCheck_2628_;
goto v_resetjp_2609_;
}
else
{
lean_dec(v_p_2598_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2628_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; lean_object* v_lctx_2613_; lean_object* v_nextIdx_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2627_; 
v___x_2612_ = lean_st_ref_take(v_a_2600_);
v_lctx_2613_ = lean_ctor_get(v___x_2612_, 0);
v_nextIdx_2614_ = lean_ctor_get(v___x_2612_, 1);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2616_ = v___x_2612_;
v_isShared_2617_ = v_isSharedCheck_2627_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_nextIdx_2614_);
lean_inc(v_lctx_2613_);
lean_dec(v___x_2612_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2627_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v_p_2619_; 
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 2, v_type_2599_);
v_p_2619_ = v___x_2610_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_fvarId_2602_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_binderName_2603_);
lean_ctor_set(v_reuseFailAlloc_2626_, 2, v_type_2599_);
lean_ctor_set_uint8(v_reuseFailAlloc_2626_, sizeof(void*)*3, v_borrow_2605_);
v_p_2619_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
lean_object* v___x_2620_; lean_object* v___x_2622_; 
lean_inc_ref(v_p_2619_);
v___x_2620_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2597_, v_lctx_2613_, v_p_2619_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2620_);
v___x_2622_ = v___x_2616_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v_nextIdx_2614_);
v___x_2622_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = lean_st_ref_set(v_a_2600_, v___x_2622_);
v___x_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2624_, 0, v_p_2619_);
return v___x_2624_;
}
}
}
}
}
else
{
lean_object* v___x_2632_; 
lean_dec_ref(v_type_2599_);
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v_p_2598_);
return v___x_2632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg___boxed(lean_object* v_pu_2633_, lean_object* v_p_2634_, lean_object* v_type_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
uint8_t v_pu_boxed_2638_; lean_object* v_res_2639_; 
v_pu_boxed_2638_ = lean_unbox(v_pu_2633_);
v_res_2639_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_boxed_2638_, v_p_2634_, v_type_2635_, v_a_2636_);
lean_dec(v_a_2636_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(uint8_t v_pu_2640_, lean_object* v_p_2641_, lean_object* v_type_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_2640_, v_p_2641_, v_type_2642_, v_a_2644_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(lean_object* v_pu_2649_, lean_object* v_p_2650_, lean_object* v_type_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_){
_start:
{
uint8_t v_pu_boxed_2657_; lean_object* v_res_2658_; 
v_pu_boxed_2657_ = lean_unbox(v_pu_2649_);
v_res_2658_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(v_pu_boxed_2657_, v_p_2650_, v_type_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t v_pu_2659_, lean_object* v_p_2660_, uint8_t v_borrow_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v_fvarId_2664_; lean_object* v_binderName_2665_; lean_object* v_type_2666_; uint8_t v_borrow_2667_; 
v_fvarId_2664_ = lean_ctor_get(v_p_2660_, 0);
v_binderName_2665_ = lean_ctor_get(v_p_2660_, 1);
v_type_2666_ = lean_ctor_get(v_p_2660_, 2);
v_borrow_2667_ = lean_ctor_get_uint8(v_p_2660_, sizeof(void*)*3);
if (v_borrow_2661_ == 0)
{
if (v_borrow_2667_ == 0)
{
lean_object* v___x_2683_; 
v___x_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2683_, 0, v_p_2660_);
return v___x_2683_;
}
else
{
lean_inc_ref(v_type_2666_);
lean_inc(v_binderName_2665_);
lean_inc(v_fvarId_2664_);
lean_dec_ref(v_p_2660_);
goto v___jp_2668_;
}
}
else
{
if (v_borrow_2667_ == 0)
{
lean_inc_ref(v_type_2666_);
lean_inc(v_binderName_2665_);
lean_inc(v_fvarId_2664_);
lean_dec_ref(v_p_2660_);
goto v___jp_2668_;
}
else
{
lean_object* v___x_2684_; 
v___x_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2684_, 0, v_p_2660_);
return v___x_2684_;
}
}
v___jp_2668_:
{
lean_object* v___x_2669_; lean_object* v_lctx_2670_; lean_object* v_nextIdx_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2682_; 
v___x_2669_ = lean_st_ref_take(v_a_2662_);
v_lctx_2670_ = lean_ctor_get(v___x_2669_, 0);
v_nextIdx_2671_ = lean_ctor_get(v___x_2669_, 1);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2673_ = v___x_2669_;
v_isShared_2674_ = v_isSharedCheck_2682_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_nextIdx_2671_);
lean_inc(v_lctx_2670_);
lean_dec(v___x_2669_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2682_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v_p_2675_; lean_object* v___x_2676_; lean_object* v___x_2678_; 
v_p_2675_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_p_2675_, 0, v_fvarId_2664_);
lean_ctor_set(v_p_2675_, 1, v_binderName_2665_);
lean_ctor_set(v_p_2675_, 2, v_type_2666_);
lean_ctor_set_uint8(v_p_2675_, sizeof(void*)*3, v_borrow_2661_);
lean_inc_ref(v_p_2675_);
v___x_2676_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2659_, v_lctx_2670_, v_p_2675_);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 0, v___x_2676_);
v___x_2678_ = v___x_2673_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2676_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v_nextIdx_2671_);
v___x_2678_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2679_ = lean_st_ref_set(v_a_2662_, v___x_2678_);
v___x_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2680_, 0, v_p_2675_);
return v___x_2680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg___boxed(lean_object* v_pu_2685_, lean_object* v_p_2686_, lean_object* v_borrow_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
uint8_t v_pu_boxed_2690_; uint8_t v_borrow_boxed_2691_; lean_object* v_res_2692_; 
v_pu_boxed_2690_ = lean_unbox(v_pu_2685_);
v_borrow_boxed_2691_ = lean_unbox(v_borrow_2687_);
v_res_2692_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_boxed_2690_, v_p_2686_, v_borrow_boxed_2691_, v_a_2688_);
lean_dec(v_a_2688_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(uint8_t v_pu_2693_, lean_object* v_p_2694_, uint8_t v_borrow_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_2693_, v_p_2694_, v_borrow_2695_, v_a_2697_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___boxed(lean_object* v_pu_2702_, lean_object* v_p_2703_, lean_object* v_borrow_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
uint8_t v_pu_boxed_2710_; uint8_t v_borrow_boxed_2711_; lean_object* v_res_2712_; 
v_pu_boxed_2710_ = lean_unbox(v_pu_2702_);
v_borrow_boxed_2711_ = lean_unbox(v_borrow_2704_);
v_res_2712_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(v_pu_boxed_2710_, v_p_2703_, v_borrow_boxed_2711_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t v_pu_2713_, lean_object* v_decl_2714_, lean_object* v_type_2715_, lean_object* v_value_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v_fvarId_2719_; lean_object* v_binderName_2720_; lean_object* v_type_2721_; lean_object* v_value_2722_; uint8_t v___y_2724_; size_t v___x_2750_; size_t v___x_2751_; uint8_t v___x_2752_; 
v_fvarId_2719_ = lean_ctor_get(v_decl_2714_, 0);
v_binderName_2720_ = lean_ctor_get(v_decl_2714_, 1);
v_type_2721_ = lean_ctor_get(v_decl_2714_, 2);
v_value_2722_ = lean_ctor_get(v_decl_2714_, 3);
v___x_2750_ = lean_ptr_addr(v_type_2715_);
v___x_2751_ = lean_ptr_addr(v_type_2721_);
v___x_2752_ = lean_usize_dec_eq(v___x_2750_, v___x_2751_);
if (v___x_2752_ == 0)
{
v___y_2724_ = v___x_2752_;
goto v___jp_2723_;
}
else
{
size_t v___x_2753_; size_t v___x_2754_; uint8_t v___x_2755_; 
v___x_2753_ = lean_ptr_addr(v_value_2716_);
v___x_2754_ = lean_ptr_addr(v_value_2722_);
v___x_2755_ = lean_usize_dec_eq(v___x_2753_, v___x_2754_);
v___y_2724_ = v___x_2755_;
goto v___jp_2723_;
}
v___jp_2723_:
{
if (v___y_2724_ == 0)
{
lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2744_; 
lean_inc(v_binderName_2720_);
lean_inc(v_fvarId_2719_);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_decl_2714_);
if (v_isSharedCheck_2744_ == 0)
{
lean_object* v_unused_2745_; lean_object* v_unused_2746_; lean_object* v_unused_2747_; lean_object* v_unused_2748_; 
v_unused_2745_ = lean_ctor_get(v_decl_2714_, 3);
lean_dec(v_unused_2745_);
v_unused_2746_ = lean_ctor_get(v_decl_2714_, 2);
lean_dec(v_unused_2746_);
v_unused_2747_ = lean_ctor_get(v_decl_2714_, 1);
lean_dec(v_unused_2747_);
v_unused_2748_ = lean_ctor_get(v_decl_2714_, 0);
lean_dec(v_unused_2748_);
v___x_2726_ = v_decl_2714_;
v_isShared_2727_ = v_isSharedCheck_2744_;
goto v_resetjp_2725_;
}
else
{
lean_dec(v_decl_2714_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2744_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2728_; lean_object* v_lctx_2729_; lean_object* v_nextIdx_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2743_; 
v___x_2728_ = lean_st_ref_take(v_a_2717_);
v_lctx_2729_ = lean_ctor_get(v___x_2728_, 0);
v_nextIdx_2730_ = lean_ctor_get(v___x_2728_, 1);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2732_ = v___x_2728_;
v_isShared_2733_ = v_isSharedCheck_2743_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_nextIdx_2730_);
lean_inc(v_lctx_2729_);
lean_dec(v___x_2728_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2743_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v_decl_2735_; 
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 3, v_value_2716_);
lean_ctor_set(v___x_2726_, 2, v_type_2715_);
v_decl_2735_ = v___x_2726_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_fvarId_2719_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_binderName_2720_);
lean_ctor_set(v_reuseFailAlloc_2742_, 2, v_type_2715_);
lean_ctor_set(v_reuseFailAlloc_2742_, 3, v_value_2716_);
v_decl_2735_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2736_; lean_object* v___x_2738_; 
lean_inc_ref(v_decl_2735_);
v___x_2736_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2713_, v_lctx_2729_, v_decl_2735_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v___x_2736_);
v___x_2738_ = v___x_2732_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_nextIdx_2730_);
v___x_2738_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = lean_st_ref_set(v_a_2717_, v___x_2738_);
v___x_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2740_, 0, v_decl_2735_);
return v___x_2740_;
}
}
}
}
}
else
{
lean_object* v___x_2749_; 
lean_dec(v_value_2716_);
lean_dec_ref(v_type_2715_);
v___x_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2749_, 0, v_decl_2714_);
return v___x_2749_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg___boxed(lean_object* v_pu_2756_, lean_object* v_decl_2757_, lean_object* v_type_2758_, lean_object* v_value_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_){
_start:
{
uint8_t v_pu_boxed_2762_; lean_object* v_res_2763_; 
v_pu_boxed_2762_ = lean_unbox(v_pu_2756_);
v_res_2763_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_boxed_2762_, v_decl_2757_, v_type_2758_, v_value_2759_, v_a_2760_);
lean_dec(v_a_2760_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(uint8_t v_pu_2764_, lean_object* v_decl_2765_, lean_object* v_type_2766_, lean_object* v_value_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2764_, v_decl_2765_, v_type_2766_, v_value_2767_, v_a_2769_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(lean_object* v_pu_2774_, lean_object* v_decl_2775_, lean_object* v_type_2776_, lean_object* v_value_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_){
_start:
{
uint8_t v_pu_boxed_2783_; lean_object* v_res_2784_; 
v_pu_boxed_2783_ = lean_unbox(v_pu_2774_);
v_res_2784_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(v_pu_boxed_2783_, v_decl_2775_, v_type_2776_, v_value_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_);
lean_dec(v_a_2781_);
lean_dec_ref(v_a_2780_);
lean_dec(v_a_2779_);
lean_dec_ref(v_a_2778_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t v_pu_2785_, lean_object* v_decl_2786_, lean_object* v_value_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v_type_2790_; lean_object* v___x_2791_; 
v_type_2790_ = lean_ctor_get(v_decl_2786_, 2);
lean_inc_ref(v_type_2790_);
v___x_2791_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2785_, v_decl_2786_, v_type_2790_, v_value_2787_, v_a_2788_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg___boxed(lean_object* v_pu_2792_, lean_object* v_decl_2793_, lean_object* v_value_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_){
_start:
{
uint8_t v_pu_boxed_2797_; lean_object* v_res_2798_; 
v_pu_boxed_2797_ = lean_unbox(v_pu_2792_);
v_res_2798_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_boxed_2797_, v_decl_2793_, v_value_2794_, v_a_2795_);
lean_dec(v_a_2795_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(uint8_t v_pu_2799_, lean_object* v_decl_2800_, lean_object* v_value_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_){
_start:
{
lean_object* v___x_2807_; 
v___x_2807_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_2799_, v_decl_2800_, v_value_2801_, v_a_2803_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___boxed(lean_object* v_pu_2808_, lean_object* v_decl_2809_, lean_object* v_value_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
uint8_t v_pu_boxed_2816_; lean_object* v_res_2817_; 
v_pu_boxed_2816_ = lean_unbox(v_pu_2808_);
v_res_2817_ = l_Lean_Compiler_LCNF_LetDecl_updateValue(v_pu_boxed_2816_, v_decl_2809_, v_value_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_);
lean_dec(v_a_2814_);
lean_dec_ref(v_a_2813_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t v_pu_2818_, lean_object* v_decl_2819_, lean_object* v_type_2820_, lean_object* v_params_2821_, lean_object* v_value_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v_fvarId_2825_; lean_object* v_binderName_2826_; lean_object* v_params_2827_; lean_object* v_type_2828_; lean_object* v_value_2829_; uint8_t v___y_2846_; size_t v___x_2851_; size_t v___x_2852_; uint8_t v___x_2853_; 
v_fvarId_2825_ = lean_ctor_get(v_decl_2819_, 0);
v_binderName_2826_ = lean_ctor_get(v_decl_2819_, 1);
v_params_2827_ = lean_ctor_get(v_decl_2819_, 2);
v_type_2828_ = lean_ctor_get(v_decl_2819_, 3);
v_value_2829_ = lean_ctor_get(v_decl_2819_, 4);
v___x_2851_ = lean_ptr_addr(v_type_2820_);
v___x_2852_ = lean_ptr_addr(v_type_2828_);
v___x_2853_ = lean_usize_dec_eq(v___x_2851_, v___x_2852_);
if (v___x_2853_ == 0)
{
v___y_2846_ = v___x_2853_;
goto v___jp_2845_;
}
else
{
size_t v___x_2854_; size_t v___x_2855_; uint8_t v___x_2856_; 
v___x_2854_ = lean_ptr_addr(v_params_2821_);
v___x_2855_ = lean_ptr_addr(v_params_2827_);
v___x_2856_ = lean_usize_dec_eq(v___x_2854_, v___x_2855_);
v___y_2846_ = v___x_2856_;
goto v___jp_2845_;
}
v___jp_2830_:
{
lean_object* v___x_2831_; lean_object* v_lctx_2832_; lean_object* v_nextIdx_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2844_; 
v___x_2831_ = lean_st_ref_take(v_a_2823_);
v_lctx_2832_ = lean_ctor_get(v___x_2831_, 0);
v_nextIdx_2833_ = lean_ctor_get(v___x_2831_, 1);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2835_ = v___x_2831_;
v_isShared_2836_ = v_isSharedCheck_2844_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_nextIdx_2833_);
lean_inc(v_lctx_2832_);
lean_dec(v___x_2831_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2844_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v_decl_2837_; lean_object* v___x_2838_; lean_object* v___x_2840_; 
v_decl_2837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_decl_2837_, 0, v_fvarId_2825_);
lean_ctor_set(v_decl_2837_, 1, v_binderName_2826_);
lean_ctor_set(v_decl_2837_, 2, v_params_2821_);
lean_ctor_set(v_decl_2837_, 3, v_type_2820_);
lean_ctor_set(v_decl_2837_, 4, v_value_2822_);
lean_inc_ref(v_decl_2837_);
v___x_2838_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2818_, v_lctx_2832_, v_decl_2837_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 0, v___x_2838_);
v___x_2840_ = v___x_2835_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2838_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_nextIdx_2833_);
v___x_2840_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = lean_st_ref_set(v_a_2823_, v___x_2840_);
v___x_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2842_, 0, v_decl_2837_);
return v___x_2842_;
}
}
}
v___jp_2845_:
{
if (v___y_2846_ == 0)
{
lean_inc(v_binderName_2826_);
lean_inc(v_fvarId_2825_);
lean_dec_ref(v_decl_2819_);
goto v___jp_2830_;
}
else
{
size_t v___x_2847_; size_t v___x_2848_; uint8_t v___x_2849_; 
v___x_2847_ = lean_ptr_addr(v_value_2822_);
v___x_2848_ = lean_ptr_addr(v_value_2829_);
v___x_2849_ = lean_usize_dec_eq(v___x_2847_, v___x_2848_);
if (v___x_2849_ == 0)
{
lean_inc(v_binderName_2826_);
lean_inc(v_fvarId_2825_);
lean_dec_ref(v_decl_2819_);
goto v___jp_2830_;
}
else
{
lean_object* v___x_2850_; 
lean_dec_ref(v_value_2822_);
lean_dec_ref(v_params_2821_);
lean_dec_ref(v_type_2820_);
v___x_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2850_, 0, v_decl_2819_);
return v___x_2850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg___boxed(lean_object* v_pu_2857_, lean_object* v_decl_2858_, lean_object* v_type_2859_, lean_object* v_params_2860_, lean_object* v_value_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
uint8_t v_pu_boxed_2864_; lean_object* v_res_2865_; 
v_pu_boxed_2864_ = lean_unbox(v_pu_2857_);
v_res_2865_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_boxed_2864_, v_decl_2858_, v_type_2859_, v_params_2860_, v_value_2861_, v_a_2862_);
lean_dec(v_a_2862_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(uint8_t v_pu_2866_, lean_object* v_decl_2867_, lean_object* v_type_2868_, lean_object* v_params_2869_, lean_object* v_value_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2866_, v_decl_2867_, v_type_2868_, v_params_2869_, v_value_2870_, v_a_2872_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(lean_object* v_pu_2877_, lean_object* v_decl_2878_, lean_object* v_type_2879_, lean_object* v_params_2880_, lean_object* v_value_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_){
_start:
{
uint8_t v_pu_boxed_2887_; lean_object* v_res_2888_; 
v_pu_boxed_2887_ = lean_unbox(v_pu_2877_);
v_res_2888_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(v_pu_boxed_2887_, v_decl_2878_, v_type_2879_, v_params_2880_, v_value_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_);
lean_dec(v_a_2885_);
lean_dec_ref(v_a_2884_);
lean_dec(v_a_2883_);
lean_dec_ref(v_a_2882_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(uint8_t v_pu_2889_, lean_object* v_decl_2890_, lean_object* v_type_2891_, lean_object* v_value_2892_, lean_object* v_a_2893_){
_start:
{
lean_object* v_params_2895_; lean_object* v___x_2896_; 
v_params_2895_ = lean_ctor_get(v_decl_2890_, 2);
lean_inc_ref(v_params_2895_);
v___x_2896_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2889_, v_decl_2890_, v_type_2891_, v_params_2895_, v_value_2892_, v_a_2893_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg___boxed(lean_object* v_pu_2897_, lean_object* v_decl_2898_, lean_object* v_type_2899_, lean_object* v_value_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_){
_start:
{
uint8_t v_pu_boxed_2903_; lean_object* v_res_2904_; 
v_pu_boxed_2903_ = lean_unbox(v_pu_2897_);
v_res_2904_ = l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(v_pu_boxed_2903_, v_decl_2898_, v_type_2899_, v_value_2900_, v_a_2901_);
lean_dec(v_a_2901_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27(uint8_t v_pu_2905_, lean_object* v_decl_2906_, lean_object* v_type_2907_, lean_object* v_value_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v_params_2914_; lean_object* v___x_2915_; 
v_params_2914_ = lean_ctor_get(v_decl_2906_, 2);
lean_inc_ref(v_params_2914_);
v___x_2915_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2905_, v_decl_2906_, v_type_2907_, v_params_2914_, v_value_2908_, v_a_2910_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___boxed(lean_object* v_pu_2916_, lean_object* v_decl_2917_, lean_object* v_type_2918_, lean_object* v_value_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_){
_start:
{
uint8_t v_pu_boxed_2925_; lean_object* v_res_2926_; 
v_pu_boxed_2925_ = lean_unbox(v_pu_2916_);
v_res_2926_ = l_Lean_Compiler_LCNF_FunDecl_update_x27(v_pu_boxed_2925_, v_decl_2917_, v_type_2918_, v_value_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
lean_dec(v_a_2923_);
lean_dec_ref(v_a_2922_);
lean_dec(v_a_2921_);
lean_dec_ref(v_a_2920_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(uint8_t v_pu_2927_, lean_object* v_decl_2928_, lean_object* v_value_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v_params_2932_; lean_object* v_type_2933_; lean_object* v___x_2934_; 
v_params_2932_ = lean_ctor_get(v_decl_2928_, 2);
lean_inc_ref(v_params_2932_);
v_type_2933_ = lean_ctor_get(v_decl_2928_, 3);
lean_inc_ref(v_type_2933_);
v___x_2934_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2927_, v_decl_2928_, v_type_2933_, v_params_2932_, v_value_2929_, v_a_2930_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg___boxed(lean_object* v_pu_2935_, lean_object* v_decl_2936_, lean_object* v_value_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_){
_start:
{
uint8_t v_pu_boxed_2940_; lean_object* v_res_2941_; 
v_pu_boxed_2940_ = lean_unbox(v_pu_2935_);
v_res_2941_ = l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(v_pu_boxed_2940_, v_decl_2936_, v_value_2937_, v_a_2938_);
lean_dec(v_a_2938_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue(uint8_t v_pu_2942_, lean_object* v_decl_2943_, lean_object* v_value_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v_params_2950_; lean_object* v_type_2951_; lean_object* v___x_2952_; 
v_params_2950_ = lean_ctor_get(v_decl_2943_, 2);
lean_inc_ref(v_params_2950_);
v_type_2951_ = lean_ctor_get(v_decl_2943_, 3);
lean_inc_ref(v_type_2951_);
v___x_2952_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2942_, v_decl_2943_, v_type_2951_, v_params_2950_, v_value_2944_, v_a_2946_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___boxed(lean_object* v_pu_2953_, lean_object* v_decl_2954_, lean_object* v_value_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_){
_start:
{
uint8_t v_pu_boxed_2961_; lean_object* v_res_2962_; 
v_pu_boxed_2961_ = lean_unbox(v_pu_2953_);
v_res_2962_ = l_Lean_Compiler_LCNF_FunDecl_updateValue(v_pu_boxed_2961_, v_decl_2954_, v_value_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
lean_dec(v_a_2959_);
lean_dec_ref(v_a_2958_);
lean_dec(v_a_2957_);
lean_dec_ref(v_a_2956_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0(uint8_t v_pu_2963_, lean_object* v_p_2964_, lean_object* v_inst_2965_, lean_object* v_____do__lift_2966_){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2967_ = lean_box(v_pu_2963_);
v___x_2968_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_2968_, 0, v___x_2967_);
lean_closure_set(v___x_2968_, 1, v_p_2964_);
lean_closure_set(v___x_2968_, 2, v_____do__lift_2966_);
v___x_2969_ = lean_apply_2(v_inst_2965_, lean_box(0), v___x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed(lean_object* v_pu_2970_, lean_object* v_p_2971_, lean_object* v_inst_2972_, lean_object* v_____do__lift_2973_){
_start:
{
uint8_t v_pu_boxed_2974_; lean_object* v_res_2975_; 
v_pu_boxed_2974_ = lean_unbox(v_pu_2970_);
v_res_2975_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__0(v_pu_boxed_2974_, v_p_2971_, v_inst_2972_, v_____do__lift_2973_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1(uint8_t v_pu_2976_, uint8_t v_t_2977_, lean_object* v_type_2978_, lean_object* v_toPure_2979_, lean_object* v_____do__lift_2980_){
_start:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2981_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2976_, v_____do__lift_2980_, v_t_2977_, v_type_2978_);
v___x_2982_ = lean_apply_2(v_toPure_2979_, lean_box(0), v___x_2981_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed(lean_object* v_pu_2983_, lean_object* v_t_2984_, lean_object* v_type_2985_, lean_object* v_toPure_2986_, lean_object* v_____do__lift_2987_){
_start:
{
uint8_t v_pu_boxed_2988_; uint8_t v_t_boxed_2989_; lean_object* v_res_2990_; 
v_pu_boxed_2988_ = lean_unbox(v_pu_2983_);
v_t_boxed_2989_ = lean_unbox(v_t_2984_);
v_res_2990_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__1(v_pu_boxed_2988_, v_t_boxed_2989_, v_type_2985_, v_toPure_2986_, v_____do__lift_2987_);
lean_dec_ref(v_____do__lift_2987_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg(uint8_t v_pu_2991_, uint8_t v_t_2992_, lean_object* v_inst_2993_, lean_object* v_inst_2994_, lean_object* v_inst_2995_, lean_object* v_p_2996_){
_start:
{
lean_object* v_toApplicative_2997_; lean_object* v_toBind_2998_; lean_object* v_type_2999_; lean_object* v_toPure_3000_; lean_object* v___x_3001_; lean_object* v___f_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___f_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v_toApplicative_2997_ = lean_ctor_get(v_inst_2994_, 0);
lean_inc_ref(v_toApplicative_2997_);
v_toBind_2998_ = lean_ctor_get(v_inst_2994_, 1);
lean_inc_n(v_toBind_2998_, 2);
lean_dec_ref(v_inst_2994_);
v_type_2999_ = lean_ctor_get(v_p_2996_, 2);
lean_inc_ref(v_type_2999_);
v_toPure_3000_ = lean_ctor_get(v_toApplicative_2997_, 1);
lean_inc(v_toPure_3000_);
lean_dec_ref(v_toApplicative_2997_);
v___x_3001_ = lean_box(v_pu_2991_);
v___f_3002_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3002_, 0, v___x_3001_);
lean_closure_set(v___f_3002_, 1, v_p_2996_);
lean_closure_set(v___f_3002_, 2, v_inst_2993_);
v___x_3003_ = lean_box(v_pu_2991_);
v___x_3004_ = lean_box(v_t_2992_);
v___f_3005_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3005_, 0, v___x_3003_);
lean_closure_set(v___f_3005_, 1, v___x_3004_);
lean_closure_set(v___f_3005_, 2, v_type_2999_);
lean_closure_set(v___f_3005_, 3, v_toPure_3000_);
v___x_3006_ = lean_apply_4(v_toBind_2998_, lean_box(0), lean_box(0), v_inst_2995_, v___f_3005_);
v___x_3007_ = lean_apply_4(v_toBind_2998_, lean_box(0), lean_box(0), v___x_3006_, v___f_3002_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___boxed(lean_object* v_pu_3008_, lean_object* v_t_3009_, lean_object* v_inst_3010_, lean_object* v_inst_3011_, lean_object* v_inst_3012_, lean_object* v_p_3013_){
_start:
{
uint8_t v_pu_boxed_3014_; uint8_t v_t_boxed_3015_; lean_object* v_res_3016_; 
v_pu_boxed_3014_ = lean_unbox(v_pu_3008_);
v_t_boxed_3015_ = lean_unbox(v_t_3009_);
v_res_3016_ = l_Lean_Compiler_LCNF_normParam___redArg(v_pu_boxed_3014_, v_t_boxed_3015_, v_inst_3010_, v_inst_3011_, v_inst_3012_, v_p_3013_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam(lean_object* v_m_3017_, uint8_t v_pu_3018_, uint8_t v_t_3019_, lean_object* v_inst_3020_, lean_object* v_inst_3021_, lean_object* v_inst_3022_, lean_object* v_p_3023_){
_start:
{
lean_object* v_toApplicative_3024_; lean_object* v_toBind_3025_; lean_object* v_type_3026_; lean_object* v_toPure_3027_; lean_object* v___x_3028_; lean_object* v___f_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___f_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v_toApplicative_3024_ = lean_ctor_get(v_inst_3021_, 0);
lean_inc_ref(v_toApplicative_3024_);
v_toBind_3025_ = lean_ctor_get(v_inst_3021_, 1);
lean_inc_n(v_toBind_3025_, 2);
lean_dec_ref(v_inst_3021_);
v_type_3026_ = lean_ctor_get(v_p_3023_, 2);
lean_inc_ref(v_type_3026_);
v_toPure_3027_ = lean_ctor_get(v_toApplicative_3024_, 1);
lean_inc(v_toPure_3027_);
lean_dec_ref(v_toApplicative_3024_);
v___x_3028_ = lean_box(v_pu_3018_);
v___f_3029_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3029_, 0, v___x_3028_);
lean_closure_set(v___f_3029_, 1, v_p_3023_);
lean_closure_set(v___f_3029_, 2, v_inst_3020_);
v___x_3030_ = lean_box(v_pu_3018_);
v___x_3031_ = lean_box(v_t_3019_);
v___f_3032_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3032_, 0, v___x_3030_);
lean_closure_set(v___f_3032_, 1, v___x_3031_);
lean_closure_set(v___f_3032_, 2, v_type_3026_);
lean_closure_set(v___f_3032_, 3, v_toPure_3027_);
v___x_3033_ = lean_apply_4(v_toBind_3025_, lean_box(0), lean_box(0), v_inst_3022_, v___f_3032_);
v___x_3034_ = lean_apply_4(v_toBind_3025_, lean_box(0), lean_box(0), v___x_3033_, v___f_3029_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___boxed(lean_object* v_m_3035_, lean_object* v_pu_3036_, lean_object* v_t_3037_, lean_object* v_inst_3038_, lean_object* v_inst_3039_, lean_object* v_inst_3040_, lean_object* v_p_3041_){
_start:
{
uint8_t v_pu_boxed_3042_; uint8_t v_t_boxed_3043_; lean_object* v_res_3044_; 
v_pu_boxed_3042_ = lean_unbox(v_pu_3036_);
v_t_boxed_3043_ = lean_unbox(v_t_3037_);
v_res_3044_ = l_Lean_Compiler_LCNF_normParam(v_m_3035_, v_pu_boxed_3042_, v_t_boxed_3043_, v_inst_3038_, v_inst_3039_, v_inst_3040_, v_p_3041_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg(uint8_t v_pu_3045_, uint8_t v_t_3046_, lean_object* v_inst_3047_, lean_object* v_inst_3048_, lean_object* v_inst_3049_, lean_object* v_ps_3050_){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3051_ = lean_box(v_pu_3045_);
v___x_3052_ = lean_box(v_t_3046_);
lean_inc_ref(v_inst_3048_);
v___x_3053_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___boxed), 7, 6);
lean_closure_set(v___x_3053_, 0, lean_box(0));
lean_closure_set(v___x_3053_, 1, v___x_3051_);
lean_closure_set(v___x_3053_, 2, v___x_3052_);
lean_closure_set(v___x_3053_, 3, v_inst_3047_);
lean_closure_set(v___x_3053_, 4, v_inst_3048_);
lean_closure_set(v___x_3053_, 5, v_inst_3049_);
v___x_3054_ = lean_unsigned_to_nat(0u);
v___x_3055_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_3048_, v___x_3053_, v___x_3054_, v_ps_3050_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg___boxed(lean_object* v_pu_3056_, lean_object* v_t_3057_, lean_object* v_inst_3058_, lean_object* v_inst_3059_, lean_object* v_inst_3060_, lean_object* v_ps_3061_){
_start:
{
uint8_t v_pu_boxed_3062_; uint8_t v_t_boxed_3063_; lean_object* v_res_3064_; 
v_pu_boxed_3062_ = lean_unbox(v_pu_3056_);
v_t_boxed_3063_ = lean_unbox(v_t_3057_);
v_res_3064_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_boxed_3062_, v_t_boxed_3063_, v_inst_3058_, v_inst_3059_, v_inst_3060_, v_ps_3061_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams(lean_object* v_m_3065_, uint8_t v_pu_3066_, uint8_t v_t_3067_, lean_object* v_inst_3068_, lean_object* v_inst_3069_, lean_object* v_inst_3070_, lean_object* v_ps_3071_){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_3066_, v_t_3067_, v_inst_3068_, v_inst_3069_, v_inst_3070_, v_ps_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___boxed(lean_object* v_m_3073_, lean_object* v_pu_3074_, lean_object* v_t_3075_, lean_object* v_inst_3076_, lean_object* v_inst_3077_, lean_object* v_inst_3078_, lean_object* v_ps_3079_){
_start:
{
uint8_t v_pu_boxed_3080_; uint8_t v_t_boxed_3081_; lean_object* v_res_3082_; 
v_pu_boxed_3080_ = lean_unbox(v_pu_3074_);
v_t_boxed_3081_ = lean_unbox(v_t_3075_);
v_res_3082_ = l_Lean_Compiler_LCNF_normParams(v_m_3073_, v_pu_boxed_3080_, v_t_boxed_3081_, v_inst_3076_, v_inst_3077_, v_inst_3078_, v_ps_3079_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(uint8_t v_pu_3083_, lean_object* v_decl_3084_, lean_object* v_____do__lift_3085_, lean_object* v_inst_3086_, lean_object* v_____do__lift_3087_){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3088_ = lean_box(v_pu_3083_);
v___x_3089_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_3089_, 0, v___x_3088_);
lean_closure_set(v___x_3089_, 1, v_decl_3084_);
lean_closure_set(v___x_3089_, 2, v_____do__lift_3085_);
lean_closure_set(v___x_3089_, 3, v_____do__lift_3087_);
v___x_3090_ = lean_apply_2(v_inst_3086_, lean_box(0), v___x_3089_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed(lean_object* v_pu_3091_, lean_object* v_decl_3092_, lean_object* v_____do__lift_3093_, lean_object* v_inst_3094_, lean_object* v_____do__lift_3095_){
_start:
{
uint8_t v_pu_boxed_3096_; lean_object* v_res_3097_; 
v_pu_boxed_3096_ = lean_unbox(v_pu_3091_);
v_res_3097_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(v_pu_boxed_3096_, v_decl_3092_, v_____do__lift_3093_, v_inst_3094_, v_____do__lift_3095_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(uint8_t v_pu_3098_, lean_object* v_value_3099_, uint8_t v_t_3100_, lean_object* v_toPure_3101_, lean_object* v_____do__lift_3102_){
_start:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3103_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3098_, v_____do__lift_3102_, v_value_3099_, v_t_3100_);
v___x_3104_ = lean_apply_2(v_toPure_3101_, lean_box(0), v___x_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed(lean_object* v_pu_3105_, lean_object* v_value_3106_, lean_object* v_t_3107_, lean_object* v_toPure_3108_, lean_object* v_____do__lift_3109_){
_start:
{
uint8_t v_pu_boxed_3110_; uint8_t v_t_boxed_3111_; lean_object* v_res_3112_; 
v_pu_boxed_3110_ = lean_unbox(v_pu_3105_);
v_t_boxed_3111_ = lean_unbox(v_t_3107_);
v_res_3112_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(v_pu_boxed_3110_, v_value_3106_, v_t_boxed_3111_, v_toPure_3108_, v_____do__lift_3109_);
lean_dec_ref(v_____do__lift_3109_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(uint8_t v_pu_3113_, lean_object* v_decl_3114_, lean_object* v_inst_3115_, lean_object* v_value_3116_, uint8_t v_t_3117_, lean_object* v_toPure_3118_, lean_object* v_toBind_3119_, lean_object* v_inst_3120_, lean_object* v_____do__lift_3121_){
_start:
{
lean_object* v___x_3122_; lean_object* v___f_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___f_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3122_ = lean_box(v_pu_3113_);
v___f_3123_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3123_, 0, v___x_3122_);
lean_closure_set(v___f_3123_, 1, v_decl_3114_);
lean_closure_set(v___f_3123_, 2, v_____do__lift_3121_);
lean_closure_set(v___f_3123_, 3, v_inst_3115_);
v___x_3124_ = lean_box(v_pu_3113_);
v___x_3125_ = lean_box(v_t_3117_);
v___f_3126_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3126_, 0, v___x_3124_);
lean_closure_set(v___f_3126_, 1, v_value_3116_);
lean_closure_set(v___f_3126_, 2, v___x_3125_);
lean_closure_set(v___f_3126_, 3, v_toPure_3118_);
lean_inc(v_toBind_3119_);
v___x_3127_ = lean_apply_4(v_toBind_3119_, lean_box(0), lean_box(0), v_inst_3120_, v___f_3126_);
v___x_3128_ = lean_apply_4(v_toBind_3119_, lean_box(0), lean_box(0), v___x_3127_, v___f_3123_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed(lean_object* v_pu_3129_, lean_object* v_decl_3130_, lean_object* v_inst_3131_, lean_object* v_value_3132_, lean_object* v_t_3133_, lean_object* v_toPure_3134_, lean_object* v_toBind_3135_, lean_object* v_inst_3136_, lean_object* v_____do__lift_3137_){
_start:
{
uint8_t v_pu_boxed_3138_; uint8_t v_t_boxed_3139_; lean_object* v_res_3140_; 
v_pu_boxed_3138_ = lean_unbox(v_pu_3129_);
v_t_boxed_3139_ = lean_unbox(v_t_3133_);
v_res_3140_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(v_pu_boxed_3138_, v_decl_3130_, v_inst_3131_, v_value_3132_, v_t_boxed_3139_, v_toPure_3134_, v_toBind_3135_, v_inst_3136_, v_____do__lift_3137_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg(uint8_t v_pu_3141_, uint8_t v_t_3142_, lean_object* v_inst_3143_, lean_object* v_inst_3144_, lean_object* v_inst_3145_, lean_object* v_decl_3146_){
_start:
{
lean_object* v_toApplicative_3147_; lean_object* v_toBind_3148_; lean_object* v_type_3149_; lean_object* v_value_3150_; lean_object* v_toPure_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___f_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___f_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v_toApplicative_3147_ = lean_ctor_get(v_inst_3144_, 0);
lean_inc_ref(v_toApplicative_3147_);
v_toBind_3148_ = lean_ctor_get(v_inst_3144_, 1);
lean_inc_n(v_toBind_3148_, 3);
lean_dec_ref(v_inst_3144_);
v_type_3149_ = lean_ctor_get(v_decl_3146_, 2);
lean_inc_ref(v_type_3149_);
v_value_3150_ = lean_ctor_get(v_decl_3146_, 3);
lean_inc(v_value_3150_);
v_toPure_3151_ = lean_ctor_get(v_toApplicative_3147_, 1);
lean_inc_n(v_toPure_3151_, 2);
lean_dec_ref(v_toApplicative_3147_);
v___x_3152_ = lean_box(v_pu_3141_);
v___x_3153_ = lean_box(v_t_3142_);
lean_inc(v_inst_3145_);
v___f_3154_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_3154_, 0, v___x_3152_);
lean_closure_set(v___f_3154_, 1, v_decl_3146_);
lean_closure_set(v___f_3154_, 2, v_inst_3143_);
lean_closure_set(v___f_3154_, 3, v_value_3150_);
lean_closure_set(v___f_3154_, 4, v___x_3153_);
lean_closure_set(v___f_3154_, 5, v_toPure_3151_);
lean_closure_set(v___f_3154_, 6, v_toBind_3148_);
lean_closure_set(v___f_3154_, 7, v_inst_3145_);
v___x_3155_ = lean_box(v_pu_3141_);
v___x_3156_ = lean_box(v_t_3142_);
v___f_3157_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3157_, 0, v___x_3155_);
lean_closure_set(v___f_3157_, 1, v___x_3156_);
lean_closure_set(v___f_3157_, 2, v_type_3149_);
lean_closure_set(v___f_3157_, 3, v_toPure_3151_);
v___x_3158_ = lean_apply_4(v_toBind_3148_, lean_box(0), lean_box(0), v_inst_3145_, v___f_3157_);
v___x_3159_ = lean_apply_4(v_toBind_3148_, lean_box(0), lean_box(0), v___x_3158_, v___f_3154_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___boxed(lean_object* v_pu_3160_, lean_object* v_t_3161_, lean_object* v_inst_3162_, lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_decl_3165_){
_start:
{
uint8_t v_pu_boxed_3166_; uint8_t v_t_boxed_3167_; lean_object* v_res_3168_; 
v_pu_boxed_3166_ = lean_unbox(v_pu_3160_);
v_t_boxed_3167_ = lean_unbox(v_t_3161_);
v_res_3168_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_boxed_3166_, v_t_boxed_3167_, v_inst_3162_, v_inst_3163_, v_inst_3164_, v_decl_3165_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl(lean_object* v_m_3169_, uint8_t v_pu_3170_, uint8_t v_t_3171_, lean_object* v_inst_3172_, lean_object* v_inst_3173_, lean_object* v_inst_3174_, lean_object* v_decl_3175_){
_start:
{
lean_object* v___x_3176_; 
v___x_3176_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_3170_, v_t_3171_, v_inst_3172_, v_inst_3173_, v_inst_3174_, v_decl_3175_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___boxed(lean_object* v_m_3177_, lean_object* v_pu_3178_, lean_object* v_t_3179_, lean_object* v_inst_3180_, lean_object* v_inst_3181_, lean_object* v_inst_3182_, lean_object* v_decl_3183_){
_start:
{
uint8_t v_pu_boxed_3184_; uint8_t v_t_boxed_3185_; lean_object* v_res_3186_; 
v_pu_boxed_3184_ = lean_unbox(v_pu_3178_);
v_t_boxed_3185_ = lean_unbox(v_t_3179_);
v_res_3186_ = l_Lean_Compiler_LCNF_normLetDecl(v_m_3177_, v_pu_boxed_3184_, v_t_boxed_3185_, v_inst_3180_, v_inst_3181_, v_inst_3182_, v_decl_3183_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(uint8_t v_pu_3187_, uint8_t v_t_3188_){
_start:
{
lean_object* v___x_3189_; lean_object* v_toApplicative_3190_; lean_object* v_toFunctor_3191_; lean_object* v_toSeq_3192_; lean_object* v_toSeqLeft_3193_; lean_object* v_toSeqRight_3194_; lean_object* v___f_3195_; lean_object* v___f_3196_; lean_object* v___f_3197_; lean_object* v___f_3198_; lean_object* v___x_3199_; lean_object* v___f_3200_; lean_object* v___f_3201_; lean_object* v___f_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v_toApplicative_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3234_; 
v___x_3189_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_3190_ = lean_ctor_get(v___x_3189_, 0);
v_toFunctor_3191_ = lean_ctor_get(v_toApplicative_3190_, 0);
v_toSeq_3192_ = lean_ctor_get(v_toApplicative_3190_, 2);
v_toSeqLeft_3193_ = lean_ctor_get(v_toApplicative_3190_, 3);
v_toSeqRight_3194_ = lean_ctor_get(v_toApplicative_3190_, 4);
v___f_3195_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_3196_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_3191_, 2);
v___f_3197_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3197_, 0, v_toFunctor_3191_);
v___f_3198_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3198_, 0, v_toFunctor_3191_);
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v___f_3197_);
lean_ctor_set(v___x_3199_, 1, v___f_3198_);
lean_inc(v_toSeqRight_3194_);
v___f_3200_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3200_, 0, v_toSeqRight_3194_);
lean_inc(v_toSeqLeft_3193_);
v___f_3201_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3201_, 0, v_toSeqLeft_3193_);
lean_inc(v_toSeq_3192_);
v___f_3202_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3202_, 0, v_toSeq_3192_);
v___x_3203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3199_);
lean_ctor_set(v___x_3203_, 1, v___f_3195_);
lean_ctor_set(v___x_3203_, 2, v___f_3202_);
lean_ctor_set(v___x_3203_, 3, v___f_3201_);
lean_ctor_set(v___x_3203_, 4, v___f_3200_);
v___x_3204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
lean_ctor_set(v___x_3204_, 1, v___f_3196_);
v___x_3205_ = l_StateRefT_x27_instMonad___redArg(v___x_3204_);
v_toApplicative_3206_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3234_ == 0)
{
lean_object* v_unused_3235_; 
v_unused_3235_ = lean_ctor_get(v___x_3205_, 1);
lean_dec(v_unused_3235_);
v___x_3208_ = v___x_3205_;
v_isShared_3209_ = v_isSharedCheck_3234_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_toApplicative_3206_);
lean_dec(v___x_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3234_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v_toFunctor_3210_; lean_object* v_toSeq_3211_; lean_object* v_toSeqLeft_3212_; lean_object* v_toSeqRight_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3232_; 
v_toFunctor_3210_ = lean_ctor_get(v_toApplicative_3206_, 0);
v_toSeq_3211_ = lean_ctor_get(v_toApplicative_3206_, 2);
v_toSeqLeft_3212_ = lean_ctor_get(v_toApplicative_3206_, 3);
v_toSeqRight_3213_ = lean_ctor_get(v_toApplicative_3206_, 4);
v_isSharedCheck_3232_ = !lean_is_exclusive(v_toApplicative_3206_);
if (v_isSharedCheck_3232_ == 0)
{
lean_object* v_unused_3233_; 
v_unused_3233_ = lean_ctor_get(v_toApplicative_3206_, 1);
lean_dec(v_unused_3233_);
v___x_3215_ = v_toApplicative_3206_;
v_isShared_3216_ = v_isSharedCheck_3232_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_toSeqRight_3213_);
lean_inc(v_toSeqLeft_3212_);
lean_inc(v_toSeq_3211_);
lean_inc(v_toFunctor_3210_);
lean_dec(v_toApplicative_3206_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3232_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___f_3217_; lean_object* v___f_3218_; lean_object* v___f_3219_; lean_object* v___f_3220_; lean_object* v___x_3221_; lean_object* v___f_3222_; lean_object* v___f_3223_; lean_object* v___f_3224_; lean_object* v___x_3226_; 
v___f_3217_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_3218_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_3210_);
v___f_3219_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3219_, 0, v_toFunctor_3210_);
v___f_3220_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3220_, 0, v_toFunctor_3210_);
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___f_3219_);
lean_ctor_set(v___x_3221_, 1, v___f_3220_);
v___f_3222_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3222_, 0, v_toSeqRight_3213_);
v___f_3223_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3223_, 0, v_toSeqLeft_3212_);
v___f_3224_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3224_, 0, v_toSeq_3211_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 4, v___f_3222_);
lean_ctor_set(v___x_3215_, 3, v___f_3223_);
lean_ctor_set(v___x_3215_, 2, v___f_3224_);
lean_ctor_set(v___x_3215_, 1, v___f_3217_);
lean_ctor_set(v___x_3215_, 0, v___x_3221_);
v___x_3226_ = v___x_3215_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3221_);
lean_ctor_set(v_reuseFailAlloc_3231_, 1, v___f_3217_);
lean_ctor_set(v_reuseFailAlloc_3231_, 2, v___f_3224_);
lean_ctor_set(v_reuseFailAlloc_3231_, 3, v___f_3223_);
lean_ctor_set(v_reuseFailAlloc_3231_, 4, v___f_3222_);
v___x_3226_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
lean_object* v___x_3228_; 
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 1, v___f_3218_);
lean_ctor_set(v___x_3208_, 0, v___x_3226_);
v___x_3228_ = v___x_3208_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3226_);
lean_ctor_set(v_reuseFailAlloc_3230_, 1, v___f_3218_);
v___x_3228_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
lean_object* v___x_3229_; 
v___x_3229_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_3229_, 0, lean_box(0));
lean_closure_set(v___x_3229_, 1, lean_box(0));
lean_closure_set(v___x_3229_, 2, v___x_3228_);
return v___x_3229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___boxed(lean_object* v_pu_3236_, lean_object* v_t_3237_){
_start:
{
uint8_t v_pu_boxed_3238_; uint8_t v_t_boxed_3239_; lean_object* v_res_3240_; 
v_pu_boxed_3238_ = lean_unbox(v_pu_3236_);
v_t_boxed_3239_ = lean_unbox(v_t_3237_);
v_res_3240_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(v_pu_boxed_3238_, v_t_boxed_3239_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg(uint8_t v_pu_3241_, lean_object* v_inst_3242_, lean_object* v_result_3243_, lean_object* v_x_3244_){
_start:
{
if (lean_obj_tag(v_result_3243_) == 0)
{
lean_object* v_fvarId_3245_; lean_object* v___x_3246_; 
lean_dec(v_inst_3242_);
v_fvarId_3245_ = lean_ctor_get(v_result_3243_, 0);
lean_inc(v_fvarId_3245_);
lean_dec_ref(v_result_3243_);
v___x_3246_ = lean_apply_1(v_x_3244_, v_fvarId_3245_);
return v___x_3246_;
}
else
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
lean_dec(v_x_3244_);
v___x_3247_ = lean_box(v_pu_3241_);
v___x_3248_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3248_, 0, v___x_3247_);
v___x_3249_ = lean_apply_2(v_inst_3242_, lean_box(0), v___x_3248_);
return v___x_3249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg___boxed(lean_object* v_pu_3250_, lean_object* v_inst_3251_, lean_object* v_result_3252_, lean_object* v_x_3253_){
_start:
{
uint8_t v_pu_boxed_3254_; lean_object* v_res_3255_; 
v_pu_boxed_3254_ = lean_unbox(v_pu_3250_);
v_res_3255_ = l_Lean_Compiler_LCNF_withNormFVarResult___redArg(v_pu_boxed_3254_, v_inst_3251_, v_result_3252_, v_x_3253_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult(lean_object* v_m_3256_, uint8_t v_pu_3257_, lean_object* v_inst_3258_, lean_object* v_inst_3259_, lean_object* v_result_3260_, lean_object* v_x_3261_){
_start:
{
if (lean_obj_tag(v_result_3260_) == 0)
{
lean_object* v_fvarId_3262_; lean_object* v___x_3263_; 
lean_dec(v_inst_3258_);
v_fvarId_3262_ = lean_ctor_get(v_result_3260_, 0);
lean_inc(v_fvarId_3262_);
lean_dec_ref(v_result_3260_);
v___x_3263_ = lean_apply_1(v_x_3261_, v_fvarId_3262_);
return v___x_3263_;
}
else
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
lean_dec(v_x_3261_);
v___x_3264_ = lean_box(v_pu_3257_);
v___x_3265_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3265_, 0, v___x_3264_);
v___x_3266_ = lean_apply_2(v_inst_3258_, lean_box(0), v___x_3265_);
return v___x_3266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___boxed(lean_object* v_m_3267_, lean_object* v_pu_3268_, lean_object* v_inst_3269_, lean_object* v_inst_3270_, lean_object* v_result_3271_, lean_object* v_x_3272_){
_start:
{
uint8_t v_pu_boxed_3273_; lean_object* v_res_3274_; 
v_pu_boxed_3273_ = lean_unbox(v_pu_3268_);
v_res_3274_ = l_Lean_Compiler_LCNF_withNormFVarResult(v_m_3267_, v_pu_boxed_3273_, v_inst_3269_, v_inst_3270_, v_result_3271_, v_x_3272_);
lean_dec_ref(v_inst_3270_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(uint8_t v_pu_3275_, uint8_t v_t_3276_, lean_object* v_args_3277_, lean_object* v___y_3278_){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_3275_, v___y_3278_, v_args_3277_, v_t_3276_);
v___x_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg___boxed(lean_object* v_pu_3282_, lean_object* v_t_3283_, lean_object* v_args_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
uint8_t v_pu_boxed_3287_; uint8_t v_t_boxed_3288_; lean_object* v_res_3289_; 
v_pu_boxed_3287_ = lean_unbox(v_pu_3282_);
v_t_boxed_3288_ = lean_unbox(v_t_3283_);
v_res_3289_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_boxed_3287_, v_t_boxed_3288_, v_args_3284_, v___y_3285_);
lean_dec_ref(v___y_3285_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(uint8_t v_pu_3290_, uint8_t v_t_3291_, lean_object* v_i_3292_, lean_object* v_as_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v___x_3297_; uint8_t v___x_3298_; 
v___x_3297_ = lean_array_get_size(v_as_3293_);
v___x_3298_ = lean_nat_dec_lt(v_i_3292_, v___x_3297_);
if (v___x_3298_ == 0)
{
lean_object* v___x_3299_; 
lean_dec(v_i_3292_);
v___x_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3299_, 0, v_as_3293_);
return v___x_3299_;
}
else
{
lean_object* v_a_3300_; lean_object* v_type_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v_a_3300_ = lean_array_fget_borrowed(v_as_3293_, v_i_3292_);
v_type_3301_ = lean_ctor_get(v_a_3300_, 2);
lean_inc_ref(v_type_3301_);
v___x_3302_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3290_, v___y_3294_, v_t_3291_, v_type_3301_);
lean_inc(v_a_3300_);
v___x_3303_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_3290_, v_a_3300_, v___x_3302_, v___y_3295_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; size_t v___x_3305_; size_t v___x_3306_; uint8_t v___x_3307_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_a_3304_);
lean_dec_ref(v___x_3303_);
v___x_3305_ = lean_ptr_addr(v_a_3300_);
v___x_3306_ = lean_ptr_addr(v_a_3304_);
v___x_3307_ = lean_usize_dec_eq(v___x_3305_, v___x_3306_);
if (v___x_3307_ == 0)
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3308_ = lean_unsigned_to_nat(1u);
v___x_3309_ = lean_nat_add(v_i_3292_, v___x_3308_);
v___x_3310_ = lean_array_fset(v_as_3293_, v_i_3292_, v_a_3304_);
lean_dec(v_i_3292_);
v_i_3292_ = v___x_3309_;
v_as_3293_ = v___x_3310_;
goto _start;
}
else
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
lean_dec(v_a_3304_);
v___x_3312_ = lean_unsigned_to_nat(1u);
v___x_3313_ = lean_nat_add(v_i_3292_, v___x_3312_);
lean_dec(v_i_3292_);
v_i_3292_ = v___x_3313_;
goto _start;
}
}
else
{
lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3322_; 
lean_dec_ref(v_as_3293_);
lean_dec(v_i_3292_);
v_a_3315_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3317_ = v___x_3303_;
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3303_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3320_; 
if (v_isShared_3318_ == 0)
{
v___x_3320_ = v___x_3317_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_a_3315_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg___boxed(lean_object* v_pu_3323_, lean_object* v_t_3324_, lean_object* v_i_3325_, lean_object* v_as_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
uint8_t v_pu_boxed_3330_; uint8_t v_t_boxed_3331_; lean_object* v_res_3332_; 
v_pu_boxed_3330_ = lean_unbox(v_pu_3323_);
v_t_boxed_3331_ = lean_unbox(v_t_3324_);
v_res_3332_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_boxed_3330_, v_t_boxed_3331_, v_i_3325_, v_as_3326_, v___y_3327_, v___y_3328_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(uint8_t v_pu_3333_, uint8_t v_t_3334_, lean_object* v_ps_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3342_ = lean_unsigned_to_nat(0u);
v___x_3343_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_3333_, v_t_3334_, v___x_3342_, v_ps_3335_, v___y_3336_, v___y_3338_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg___boxed(lean_object* v_pu_3344_, lean_object* v_t_3345_, lean_object* v_ps_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
uint8_t v_pu_boxed_3353_; uint8_t v_t_boxed_3354_; lean_object* v_res_3355_; 
v_pu_boxed_3353_ = lean_unbox(v_pu_3344_);
v_t_boxed_3354_ = lean_unbox(v_t_3345_);
v_res_3355_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_boxed_3353_, v_t_boxed_3354_, v_ps_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec_ref(v___y_3347_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(uint8_t v_pu_3356_, uint8_t v_t_3357_, lean_object* v_decl_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v_type_3362_; lean_object* v_value_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v_type_3362_ = lean_ctor_get(v_decl_3358_, 2);
v_value_3363_ = lean_ctor_get(v_decl_3358_, 3);
lean_inc_ref(v_type_3362_);
v___x_3364_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3356_, v___y_3359_, v_t_3357_, v_type_3362_);
lean_inc(v_value_3363_);
v___x_3365_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3356_, v___y_3359_, v_value_3363_, v_t_3357_);
v___x_3366_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_3356_, v_decl_3358_, v___x_3364_, v___x_3365_, v___y_3360_);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg___boxed(lean_object* v_pu_3367_, lean_object* v_t_3368_, lean_object* v_decl_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
uint8_t v_pu_boxed_3373_; uint8_t v_t_boxed_3374_; lean_object* v_res_3375_; 
v_pu_boxed_3373_ = lean_unbox(v_pu_3367_);
v_t_boxed_3374_ = lean_unbox(v_t_3368_);
v_res_3375_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_boxed_3373_, v_t_boxed_3374_, v_decl_3369_, v___y_3370_, v___y_3371_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(uint8_t v_pu_3376_, uint8_t v_t_3377_, lean_object* v_i_3378_, lean_object* v_as_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v___x_3386_; uint8_t v___x_3387_; 
v___x_3386_ = lean_array_get_size(v_as_3379_);
v___x_3387_ = lean_nat_dec_lt(v_i_3378_, v___x_3386_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; 
lean_dec(v_i_3378_);
v___x_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3388_, 0, v_as_3379_);
return v___x_3388_;
}
else
{
lean_object* v_a_3389_; lean_object* v_a_3391_; 
v_a_3389_ = lean_array_fget_borrowed(v_as_3379_, v_i_3378_);
switch(lean_obj_tag(v_a_3389_))
{
case 0:
{
lean_object* v_params_3402_; lean_object* v_code_3403_; lean_object* v___x_3404_; 
v_params_3402_ = lean_ctor_get(v_a_3389_, 1);
v_code_3403_ = lean_ctor_get(v_a_3389_, 2);
lean_inc_ref(v_params_3402_);
v___x_3404_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_3376_, v_t_3377_, v_params_3402_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3406_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3405_);
lean_dec_ref(v___x_3404_);
lean_inc_ref(v_code_3403_);
v___x_3406_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3376_, v_t_3377_, v_code_3403_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3408_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_a_3407_);
lean_dec_ref(v___x_3406_);
lean_inc_ref(v_a_3389_);
v___x_3408_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_3376_, v_a_3389_, v_a_3405_, v_a_3407_);
v_a_3391_ = v___x_3408_;
goto v___jp_3390_;
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
lean_dec(v_a_3405_);
lean_dec_ref(v_as_3379_);
lean_dec(v_i_3378_);
v_a_3409_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3406_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3406_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
lean_dec_ref(v_as_3379_);
lean_dec(v_i_3378_);
v_a_3417_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3404_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3404_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
case 1:
{
lean_object* v_code_3425_; lean_object* v___x_3426_; 
v_code_3425_ = lean_ctor_get(v_a_3389_, 1);
lean_inc_ref(v_code_3425_);
v___x_3426_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3376_, v_t_3377_, v_code_3425_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; lean_object* v___x_3428_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_a_3427_);
lean_dec_ref(v___x_3426_);
lean_inc_ref(v_a_3389_);
v___x_3428_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3389_, v_a_3427_);
v_a_3391_ = v___x_3428_;
goto v___jp_3390_;
}
else
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_dec_ref(v_as_3379_);
lean_dec(v_i_3378_);
v_a_3429_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3426_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3426_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
default: 
{
lean_object* v_code_3437_; lean_object* v___x_3438_; 
v_code_3437_ = lean_ctor_get(v_a_3389_, 0);
lean_inc_ref(v_code_3437_);
v___x_3438_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3376_, v_t_3377_, v_code_3437_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v___x_3440_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref(v___x_3438_);
lean_inc_ref(v_a_3389_);
v___x_3440_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3389_, v_a_3439_);
v_a_3391_ = v___x_3440_;
goto v___jp_3390_;
}
else
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3448_; 
lean_dec_ref(v_as_3379_);
lean_dec(v_i_3378_);
v_a_3441_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3443_ = v___x_3438_;
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3438_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3446_; 
if (v_isShared_3444_ == 0)
{
v___x_3446_ = v___x_3443_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_a_3441_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
}
v___jp_3390_:
{
size_t v___x_3392_; size_t v___x_3393_; uint8_t v___x_3394_; 
v___x_3392_ = lean_ptr_addr(v_a_3389_);
v___x_3393_ = lean_ptr_addr(v_a_3391_);
v___x_3394_ = lean_usize_dec_eq(v___x_3392_, v___x_3393_);
if (v___x_3394_ == 0)
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3395_ = lean_unsigned_to_nat(1u);
v___x_3396_ = lean_nat_add(v_i_3378_, v___x_3395_);
v___x_3397_ = lean_array_fset(v_as_3379_, v_i_3378_, v_a_3391_);
lean_dec(v_i_3378_);
v_i_3378_ = v___x_3396_;
v_as_3379_ = v___x_3397_;
goto _start;
}
else
{
lean_object* v___x_3399_; lean_object* v___x_3400_; 
lean_dec_ref(v_a_3391_);
v___x_3399_ = lean_unsigned_to_nat(1u);
v___x_3400_ = lean_nat_add(v_i_3378_, v___x_3399_);
lean_dec(v_i_3378_);
v_i_3378_ = v___x_3400_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp(uint8_t v_pu_3449_, uint8_t v_t_3450_, lean_object* v_code_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_){
_start:
{
switch(lean_obj_tag(v_code_3451_))
{
case 0:
{
lean_object* v_decl_3458_; lean_object* v_k_3459_; lean_object* v___x_3460_; 
v_decl_3458_ = lean_ctor_get(v_code_3451_, 0);
v_k_3459_ = lean_ctor_get(v_code_3451_, 1);
lean_inc_ref(v_decl_3458_);
v___x_3460_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_3449_, v_t_3450_, v_decl_3458_, v_a_3452_, v_a_3454_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3462_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref(v___x_3460_);
lean_inc_ref(v_k_3459_);
v___x_3462_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3449_, v_t_3450_, v_k_3459_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3490_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3465_ = v___x_3462_;
v_isShared_3466_ = v_isSharedCheck_3490_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3462_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3490_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
uint8_t v___y_3468_; size_t v___x_3484_; size_t v___x_3485_; uint8_t v___x_3486_; 
v___x_3484_ = lean_ptr_addr(v_k_3459_);
v___x_3485_ = lean_ptr_addr(v_a_3463_);
v___x_3486_ = lean_usize_dec_eq(v___x_3484_, v___x_3485_);
if (v___x_3486_ == 0)
{
v___y_3468_ = v___x_3486_;
goto v___jp_3467_;
}
else
{
size_t v___x_3487_; size_t v___x_3488_; uint8_t v___x_3489_; 
v___x_3487_ = lean_ptr_addr(v_decl_3458_);
v___x_3488_ = lean_ptr_addr(v_a_3461_);
v___x_3489_ = lean_usize_dec_eq(v___x_3487_, v___x_3488_);
v___y_3468_ = v___x_3489_;
goto v___jp_3467_;
}
v___jp_3467_:
{
if (v___y_3468_ == 0)
{
lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3478_; 
v_isSharedCheck_3478_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_3478_ == 0)
{
lean_object* v_unused_3479_; lean_object* v_unused_3480_; 
v_unused_3479_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_3479_);
v_unused_3480_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_3480_);
v___x_3470_ = v_code_3451_;
v_isShared_3471_ = v_isSharedCheck_3478_;
goto v_resetjp_3469_;
}
else
{
lean_dec(v_code_3451_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3478_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 1, v_a_3463_);
lean_ctor_set(v___x_3470_, 0, v_a_3461_);
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3461_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_a_3463_);
v___x_3473_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3475_; 
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v___x_3473_);
v___x_3475_ = v___x_3465_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3473_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
else
{
lean_object* v___x_3482_; 
lean_dec(v_a_3463_);
lean_dec(v_a_3461_);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v_code_3451_);
v___x_3482_ = v___x_3465_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_code_3451_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
}
else
{
lean_dec(v_a_3461_);
lean_dec_ref(v_code_3451_);
return v___x_3462_;
}
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_dec_ref(v_code_3451_);
v_a_3491_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3460_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3460_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
case 1:
{
lean_object* v_decl_3499_; lean_object* v_k_3500_; lean_object* v___x_3501_; 
v_decl_3499_ = lean_ctor_get(v_code_3451_, 0);
v_k_3500_ = lean_ctor_get(v_code_3451_, 1);
lean_inc_ref(v_decl_3499_);
v___x_3501_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3449_, v_t_3450_, v_decl_3499_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3503_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref(v___x_3501_);
lean_inc_ref(v_k_3500_);
v___x_3503_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3449_, v_t_3450_, v_k_3500_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3531_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3506_ = v___x_3503_;
v_isShared_3507_ = v_isSharedCheck_3531_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3503_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3531_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
uint8_t v___y_3509_; size_t v___x_3525_; size_t v___x_3526_; uint8_t v___x_3527_; 
v___x_3525_ = lean_ptr_addr(v_k_3500_);
v___x_3526_ = lean_ptr_addr(v_a_3504_);
v___x_3527_ = lean_usize_dec_eq(v___x_3525_, v___x_3526_);
if (v___x_3527_ == 0)
{
v___y_3509_ = v___x_3527_;
goto v___jp_3508_;
}
else
{
size_t v___x_3528_; size_t v___x_3529_; uint8_t v___x_3530_; 
v___x_3528_ = lean_ptr_addr(v_decl_3499_);
v___x_3529_ = lean_ptr_addr(v_a_3502_);
v___x_3530_ = lean_usize_dec_eq(v___x_3528_, v___x_3529_);
v___y_3509_ = v___x_3530_;
goto v___jp_3508_;
}
v___jp_3508_:
{
if (v___y_3509_ == 0)
{
lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3519_; 
v_isSharedCheck_3519_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_3519_ == 0)
{
lean_object* v_unused_3520_; lean_object* v_unused_3521_; 
v_unused_3520_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_3520_);
v_unused_3521_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_3521_);
v___x_3511_ = v_code_3451_;
v_isShared_3512_ = v_isSharedCheck_3519_;
goto v_resetjp_3510_;
}
else
{
lean_dec(v_code_3451_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3519_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 1, v_a_3504_);
lean_ctor_set(v___x_3511_, 0, v_a_3502_);
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3502_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v_a_3504_);
v___x_3514_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
lean_object* v___x_3516_; 
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 0, v___x_3514_);
v___x_3516_ = v___x_3506_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3514_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
else
{
lean_object* v___x_3523_; 
lean_dec(v_a_3504_);
lean_dec(v_a_3502_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 0, v_code_3451_);
v___x_3523_ = v___x_3506_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_code_3451_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
}
else
{
lean_dec(v_a_3502_);
lean_dec_ref(v_code_3451_);
return v___x_3503_;
}
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
lean_dec_ref(v_code_3451_);
v_a_3532_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3501_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3501_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
case 2:
{
lean_object* v_decl_3540_; lean_object* v_k_3541_; lean_object* v___x_3542_; 
v_decl_3540_ = lean_ctor_get(v_code_3451_, 0);
v_k_3541_ = lean_ctor_get(v_code_3451_, 1);
lean_inc_ref(v_decl_3540_);
v___x_3542_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3449_, v_t_3450_, v_decl_3540_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v_a_3543_; lean_object* v___x_3544_; 
v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
lean_inc(v_a_3543_);
lean_dec_ref(v___x_3542_);
lean_inc_ref(v_k_3541_);
v___x_3544_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3449_, v_t_3450_, v_k_3541_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3572_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3547_ = v___x_3544_;
v_isShared_3548_ = v_isSharedCheck_3572_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3544_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3572_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
uint8_t v___y_3550_; size_t v___x_3566_; size_t v___x_3567_; uint8_t v___x_3568_; 
v___x_3566_ = lean_ptr_addr(v_k_3541_);
v___x_3567_ = lean_ptr_addr(v_a_3545_);
v___x_3568_ = lean_usize_dec_eq(v___x_3566_, v___x_3567_);
if (v___x_3568_ == 0)
{
v___y_3550_ = v___x_3568_;
goto v___jp_3549_;
}
else
{
size_t v___x_3569_; size_t v___x_3570_; uint8_t v___x_3571_; 
v___x_3569_ = lean_ptr_addr(v_decl_3540_);
v___x_3570_ = lean_ptr_addr(v_a_3543_);
v___x_3571_ = lean_usize_dec_eq(v___x_3569_, v___x_3570_);
v___y_3550_ = v___x_3571_;
goto v___jp_3549_;
}
v___jp_3549_:
{
if (v___y_3550_ == 0)
{
lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3560_; 
v_isSharedCheck_3560_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_3560_ == 0)
{
lean_object* v_unused_3561_; lean_object* v_unused_3562_; 
v_unused_3561_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_3561_);
v_unused_3562_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_3562_);
v___x_3552_ = v_code_3451_;
v_isShared_3553_ = v_isSharedCheck_3560_;
goto v_resetjp_3551_;
}
else
{
lean_dec(v_code_3451_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3560_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3555_; 
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 1, v_a_3545_);
lean_ctor_set(v___x_3552_, 0, v_a_3543_);
v___x_3555_ = v___x_3552_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3543_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v_a_3545_);
v___x_3555_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
lean_object* v___x_3557_; 
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 0, v___x_3555_);
v___x_3557_ = v___x_3547_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v___x_3555_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
}
else
{
lean_object* v___x_3564_; 
lean_dec(v_a_3545_);
lean_dec(v_a_3543_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 0, v_code_3451_);
v___x_3564_ = v___x_3547_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_code_3451_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
}
else
{
lean_dec(v_a_3543_);
lean_dec_ref(v_code_3451_);
return v___x_3544_;
}
}
else
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3580_; 
lean_dec_ref(v_code_3451_);
v_a_3573_ = lean_ctor_get(v___x_3542_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3575_ = v___x_3542_;
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3542_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
if (v_isShared_3576_ == 0)
{
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3581_; lean_object* v_args_3582_; lean_object* v___x_3583_; 
v_fvarId_3581_ = lean_ctor_get(v_code_3451_, 0);
v_args_3582_ = lean_ctor_get(v_code_3451_, 1);
lean_inc(v_fvarId_3581_);
v___x_3583_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3452_, v_fvarId_3581_, v_t_3450_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_object* v_fvarId_3584_; lean_object* v___x_3585_; 
v_fvarId_3584_ = lean_ctor_get(v___x_3583_, 0);
lean_inc(v_fvarId_3584_);
lean_dec_ref(v___x_3583_);
lean_inc_ref(v_args_3582_);
v___x_3585_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_3449_, v_t_3450_, v_args_3582_, v_a_3452_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3611_; 
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3588_ = v___x_3585_;
v_isShared_3589_ = v_isSharedCheck_3611_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3585_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3611_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
uint8_t v___y_3591_; uint8_t v___x_3607_; 
v___x_3607_ = l_Lean_instBEqFVarId_beq(v_fvarId_3581_, v_fvarId_3584_);
if (v___x_3607_ == 0)
{
v___y_3591_ = v___x_3607_;
goto v___jp_3590_;
}
else
{
size_t v___x_3608_; size_t v___x_3609_; uint8_t v___x_3610_; 
v___x_3608_ = lean_ptr_addr(v_args_3582_);
v___x_3609_ = lean_ptr_addr(v_a_3586_);
v___x_3610_ = lean_usize_dec_eq(v___x_3608_, v___x_3609_);
v___y_3591_ = v___x_3610_;
goto v___jp_3590_;
}
v___jp_3590_:
{
if (v___y_3591_ == 0)
{
lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3601_; 
v_isSharedCheck_3601_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_3601_ == 0)
{
lean_object* v_unused_3602_; lean_object* v_unused_3603_; 
v_unused_3602_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_3602_);
v_unused_3603_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_3603_);
v___x_3593_ = v_code_3451_;
v_isShared_3594_ = v_isSharedCheck_3601_;
goto v_resetjp_3592_;
}
else
{
lean_dec(v_code_3451_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3601_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 1, v_a_3586_);
lean_ctor_set(v___x_3593_, 0, v_fvarId_3584_);
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_fvarId_3584_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v_a_3586_);
v___x_3596_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
lean_object* v___x_3598_; 
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 0, v___x_3596_);
v___x_3598_ = v___x_3588_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3596_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
}
else
{
lean_object* v___x_3605_; 
lean_dec(v_a_3586_);
lean_dec(v_fvarId_3584_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 0, v_code_3451_);
v___x_3605_ = v___x_3588_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_code_3451_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_dec(v_fvarId_3584_);
lean_dec_ref(v_code_3451_);
v_a_3612_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3585_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3585_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
else
{
lean_object* v___x_3620_; 
lean_dec_ref(v_code_3451_);
v___x_3620_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3449_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
return v___x_3620_;
}
}
case 4:
{
lean_object* v_cases_3621_; lean_object* v_typeName_3622_; lean_object* v_resultType_3623_; lean_object* v_discr_3624_; lean_object* v_alts_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3672_; 
v_cases_3621_ = lean_ctor_get(v_code_3451_, 0);
lean_inc_ref(v_cases_3621_);
v_typeName_3622_ = lean_ctor_get(v_cases_3621_, 0);
v_resultType_3623_ = lean_ctor_get(v_cases_3621_, 1);
v_discr_3624_ = lean_ctor_get(v_cases_3621_, 2);
v_alts_3625_ = lean_ctor_get(v_cases_3621_, 3);
v_isSharedCheck_3672_ = !lean_is_exclusive(v_cases_3621_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3627_ = v_cases_3621_;
v_isShared_3628_ = v_isSharedCheck_3672_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_alts_3625_);
lean_inc(v_discr_3624_);
lean_inc(v_resultType_3623_);
lean_inc(v_typeName_3622_);
lean_dec(v_cases_3621_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3672_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
lean_inc_ref(v_resultType_3623_);
v___x_3629_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3449_, v_a_3452_, v_t_3450_, v_resultType_3623_);
lean_inc(v_discr_3624_);
v___x_3630_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3452_, v_discr_3624_, v_t_3450_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_fvarId_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3670_; 
v_fvarId_3631_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3633_ = v___x_3630_;
v_isShared_3634_ = v_isSharedCheck_3670_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_fvarId_3631_);
lean_dec(v___x_3630_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3670_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3625_);
v___x_3636_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_3449_, v_t_3450_, v___x_3635_, v_alts_3625_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3661_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3639_ = v___x_3636_;
v_isShared_3640_ = v_isSharedCheck_3661_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3636_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3661_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
uint8_t v___y_3652_; size_t v___x_3655_; size_t v___x_3656_; uint8_t v___x_3657_; 
v___x_3655_ = lean_ptr_addr(v_alts_3625_);
lean_dec_ref(v_alts_3625_);
v___x_3656_ = lean_ptr_addr(v_a_3637_);
v___x_3657_ = lean_usize_dec_eq(v___x_3655_, v___x_3656_);
if (v___x_3657_ == 0)
{
lean_dec_ref(v_resultType_3623_);
v___y_3652_ = v___x_3657_;
goto v___jp_3651_;
}
else
{
size_t v___x_3658_; size_t v___x_3659_; uint8_t v___x_3660_; 
v___x_3658_ = lean_ptr_addr(v_resultType_3623_);
lean_dec_ref(v_resultType_3623_);
v___x_3659_ = lean_ptr_addr(v___x_3629_);
v___x_3660_ = lean_usize_dec_eq(v___x_3658_, v___x_3659_);
v___y_3652_ = v___x_3660_;
goto v___jp_3651_;
}
v___jp_3641_:
{
lean_object* v___x_3643_; 
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 3, v_a_3637_);
lean_ctor_set(v___x_3627_, 2, v_fvarId_3631_);
lean_ctor_set(v___x_3627_, 1, v___x_3629_);
v___x_3643_ = v___x_3627_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_typeName_3622_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v___x_3629_);
lean_ctor_set(v_reuseFailAlloc_3650_, 2, v_fvarId_3631_);
lean_ctor_set(v_reuseFailAlloc_3650_, 3, v_a_3637_);
v___x_3643_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
lean_object* v___x_3645_; 
if (v_isShared_3634_ == 0)
{
lean_ctor_set_tag(v___x_3633_, 4);
lean_ctor_set(v___x_3633_, 0, v___x_3643_);
v___x_3645_ = v___x_3633_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___x_3643_);
v___x_3645_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
lean_object* v___x_3647_; 
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 0, v___x_3645_);
v___x_3647_ = v___x_3639_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3645_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
v___jp_3651_:
{
if (v___y_3652_ == 0)
{
lean_dec(v_discr_3624_);
lean_dec_ref(v_code_3451_);
goto v___jp_3641_;
}
else
{
uint8_t v___x_3653_; 
v___x_3653_ = l_Lean_instBEqFVarId_beq(v_discr_3624_, v_fvarId_3631_);
lean_dec(v_discr_3624_);
if (v___x_3653_ == 0)
{
lean_dec_ref(v_code_3451_);
goto v___jp_3641_;
}
else
{
lean_object* v___x_3654_; 
lean_del_object(v___x_3639_);
lean_dec(v_a_3637_);
lean_del_object(v___x_3633_);
lean_dec(v_fvarId_3631_);
lean_dec_ref(v___x_3629_);
lean_del_object(v___x_3627_);
lean_dec(v_typeName_3622_);
v___x_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3654_, 0, v_code_3451_);
return v___x_3654_;
}
}
}
}
}
else
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3669_; 
lean_del_object(v___x_3633_);
lean_dec(v_fvarId_3631_);
lean_dec_ref(v___x_3629_);
lean_del_object(v___x_3627_);
lean_dec_ref(v_alts_3625_);
lean_dec(v_discr_3624_);
lean_dec_ref(v_resultType_3623_);
lean_dec(v_typeName_3622_);
lean_dec_ref(v_code_3451_);
v_a_3662_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3664_ = v___x_3636_;
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3636_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3667_; 
if (v_isShared_3665_ == 0)
{
v___x_3667_ = v___x_3664_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3662_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
}
}
else
{
lean_object* v___x_3671_; 
lean_dec_ref(v___x_3629_);
lean_del_object(v___x_3627_);
lean_dec_ref(v_alts_3625_);
lean_dec(v_discr_3624_);
lean_dec_ref(v_resultType_3623_);
lean_dec(v_typeName_3622_);
lean_dec_ref(v_code_3451_);
v___x_3671_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3449_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
return v___x_3671_;
}
}
}
case 5:
{
lean_object* v_fvarId_3673_; lean_object* v___x_3674_; 
v_fvarId_3673_ = lean_ctor_get(v_code_3451_, 0);
lean_inc(v_fvarId_3673_);
v___x_3674_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3452_, v_fvarId_3673_, v_t_3450_);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_object* v_fvarId_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3694_; 
v_fvarId_3675_ = lean_ctor_get(v___x_3674_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3677_ = v___x_3674_;
v_isShared_3678_ = v_isSharedCheck_3694_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_fvarId_3675_);
lean_dec(v___x_3674_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3694_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
uint8_t v___x_3679_; 
v___x_3679_ = l_Lean_instBEqFVarId_beq(v_fvarId_3673_, v_fvarId_3675_);
if (v___x_3679_ == 0)
{
lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3689_; 
v_isSharedCheck_3689_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; 
v_unused_3690_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_3690_);
v___x_3681_ = v_code_3451_;
v_isShared_3682_ = v_isSharedCheck_3689_;
goto v_resetjp_3680_;
}
else
{
lean_dec(v_code_3451_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3689_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 0, v_fvarId_3675_);
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_fvarId_3675_);
v___x_3684_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
lean_object* v___x_3686_; 
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 0, v___x_3684_);
v___x_3686_ = v___x_3677_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3684_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
else
{
lean_object* v___x_3692_; 
lean_dec(v_fvarId_3675_);
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 0, v_code_3451_);
v___x_3692_ = v___x_3677_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_code_3451_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
else
{
lean_object* v___x_3695_; 
lean_dec_ref(v_code_3451_);
v___x_3695_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3449_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
return v___x_3695_;
}
}
case 6:
{
lean_object* v_type_3696_; lean_object* v___x_3697_; size_t v___x_3698_; size_t v___x_3699_; uint8_t v___x_3700_; 
v_type_3696_ = lean_ctor_get(v_code_3451_, 0);
lean_inc_ref(v_type_3696_);
v___x_3697_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3449_, v_a_3452_, v_t_3450_, v_type_3696_);
v___x_3698_ = lean_ptr_addr(v_type_3696_);
v___x_3699_ = lean_ptr_addr(v___x_3697_);
v___x_3700_ = lean_usize_dec_eq(v___x_3698_, v___x_3699_);
if (v___x_3700_ == 0)
{
lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3708_; 
v_isSharedCheck_3708_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_3708_ == 0)
{
lean_object* v_unused_3709_; 
v_unused_3709_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_3709_);
v___x_3702_ = v_code_3451_;
v_isShared_3703_ = v_isSharedCheck_3708_;
goto v_resetjp_3701_;
}
else
{
lean_dec(v_code_3451_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3708_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 0, v___x_3697_);
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3697_);
v___x_3705_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
lean_object* v___x_3706_; 
v___x_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3705_);
return v___x_3706_;
}
}
}
else
{
lean_object* v___x_3710_; 
lean_dec_ref(v___x_3697_);
v___x_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3710_, 0, v_code_3451_);
return v___x_3710_;
}
}
case 7:
{
lean_object* v_fvarId_3711_; lean_object* v_i_3712_; lean_object* v_y_3713_; lean_object* v_k_3714_; lean_object* v___x_3715_; 
v_fvarId_3711_ = lean_ctor_get(v_code_3451_, 0);
v_i_3712_ = lean_ctor_get(v_code_3451_, 1);
v_y_3713_ = lean_ctor_get(v_code_3451_, 2);
v_k_3714_ = lean_ctor_get(v_code_3451_, 3);
lean_inc(v_fvarId_3711_);
v___x_3715_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3452_, v_fvarId_3711_, v_t_3450_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_fvarId_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v_fvarId_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_fvarId_3716_);
lean_dec_ref(v___x_3715_);
lean_inc(v_y_3713_);
v___x_3717_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_3449_, v_a_3452_, v_y_3713_, v_t_3450_);
lean_inc_ref(v_k_3714_);
v___x_3718_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3449_, v_t_3450_, v_k_3714_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3780_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3721_ = v___x_3718_;
v_isShared_3722_ = v_isSharedCheck_3780_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3718_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3780_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
uint8_t v___y_3724_; size_t v___x_3776_; size_t v___x_3777_; uint8_t v___x_3778_; 
v___x_3776_ = lean_ptr_addr(v_fvarId_3711_);
v___x_3777_ = lean_ptr_addr(v_fvarId_3716_);
v___x_3778_ = lean_usize_dec_eq(v___x_3776_, v___x_3777_);
if (v___x_3778_ == 0)
{
v___y_3724_ = v___x_3778_;
goto v___jp_3723_;
}
else
{
uint8_t v___x_3779_; 
v___x_3779_ = lean_nat_dec_eq(v_i_3712_, v_i_3712_);
v___y_3724_ = v___x_3779_;
goto v___jp_3723_;
}
v___jp_3723_:
{
if (v___y_3724_ == 0)
{
lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3734_; 
lean_inc(v_i_3712_);
v_isSharedCheck_3734_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_3734_ == 0)
{
lean_object* v_unused_3735_; lean_object* v_unused_3736_; lean_object* v_unused_3737_; lean_object* v_unused_3738_; 
v_unused_3735_ = lean_ctor_get(v_code_3451_, 3);
lean_dec(v_unused_3735_);
v_unused_3736_ = lean_ctor_get(v_code_3451_, 2);
lean_dec(v_unused_3736_);
v_unused_3737_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_3737_);
v_unused_3738_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_3738_);
v___x_3726_ = v_code_3451_;
v_isShared_3727_ = v_isSharedCheck_3734_;
goto v_resetjp_3725_;
}
else
{
lean_dec(v_code_3451_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3734_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
lean_ctor_set(v___x_3726_, 3, v_a_3719_);
lean_ctor_set(v___x_3726_, 2, v___x_3717_);
lean_ctor_set(v___x_3726_, 0, v_fvarId_3716_);
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_fvarId_3716_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_i_3712_);
lean_ctor_set(v_reuseFailAlloc_3733_, 2, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3733_, 3, v_a_3719_);
v___x_3729_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
lean_object* v___x_3731_; 
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v___x_3729_);
v___x_3731_ = v___x_3721_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3729_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
else
{
size_t v___x_3739_; size_t v___x_3740_; uint8_t v___x_3741_; 
v___x_3739_ = lean_ptr_addr(v_y_3713_);
v___x_3740_ = lean_ptr_addr(v___x_3717_);
v___x_3741_ = lean_usize_dec_eq(v___x_3739_, v___x_3740_);
if (v___x_3741_ == 0)
{
lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3751_; 
lean_inc(v_i_3712_);
v_isSharedCheck_3751_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_3751_ == 0)
{
lean_object* v_unused_3752_; lean_object* v_unused_3753_; lean_object* v_unused_3754_; lean_object* v_unused_3755_; 
v_unused_3752_ = lean_ctor_get(v_code_3451_, 3);
lean_dec(v_unused_3752_);
v_unused_3753_ = lean_ctor_get(v_code_3451_, 2);
lean_dec(v_unused_3753_);
v_unused_3754_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_3754_);
v_unused_3755_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_3755_);
v___x_3743_ = v_code_3451_;
v_isShared_3744_ = v_isSharedCheck_3751_;
goto v_resetjp_3742_;
}
else
{
lean_dec(v_code_3451_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3751_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 3, v_a_3719_);
lean_ctor_set(v___x_3743_, 2, v___x_3717_);
lean_ctor_set(v___x_3743_, 0, v_fvarId_3716_);
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_fvarId_3716_);
lean_ctor_set(v_reuseFailAlloc_3750_, 1, v_i_3712_);
lean_ctor_set(v_reuseFailAlloc_3750_, 2, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3750_, 3, v_a_3719_);
v___x_3746_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
lean_object* v___x_3748_; 
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v___x_3746_);
v___x_3748_ = v___x_3721_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v___x_3746_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
else
{
size_t v___x_3756_; size_t v___x_3757_; uint8_t v___x_3758_; 
v___x_3756_ = lean_ptr_addr(v_k_3714_);
v___x_3757_ = lean_ptr_addr(v_a_3719_);
v___x_3758_ = lean_usize_dec_eq(v___x_3756_, v___x_3757_);
if (v___x_3758_ == 0)
{
lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3768_; 
lean_inc(v_i_3712_);
v_isSharedCheck_3768_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_3768_ == 0)
{
lean_object* v_unused_3769_; lean_object* v_unused_3770_; lean_object* v_unused_3771_; lean_object* v_unused_3772_; 
v_unused_3769_ = lean_ctor_get(v_code_3451_, 3);
lean_dec(v_unused_3769_);
v_unused_3770_ = lean_ctor_get(v_code_3451_, 2);
lean_dec(v_unused_3770_);
v_unused_3771_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_3771_);
v_unused_3772_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_3772_);
v___x_3760_ = v_code_3451_;
v_isShared_3761_ = v_isSharedCheck_3768_;
goto v_resetjp_3759_;
}
else
{
lean_dec(v_code_3451_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3768_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3763_; 
if (v_isShared_3761_ == 0)
{
lean_ctor_set(v___x_3760_, 3, v_a_3719_);
lean_ctor_set(v___x_3760_, 2, v___x_3717_);
lean_ctor_set(v___x_3760_, 0, v_fvarId_3716_);
v___x_3763_ = v___x_3760_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_fvarId_3716_);
lean_ctor_set(v_reuseFailAlloc_3767_, 1, v_i_3712_);
lean_ctor_set(v_reuseFailAlloc_3767_, 2, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3767_, 3, v_a_3719_);
v___x_3763_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
lean_object* v___x_3765_; 
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v___x_3763_);
v___x_3765_ = v___x_3721_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v___x_3763_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
else
{
lean_object* v___x_3774_; 
lean_dec(v_a_3719_);
lean_dec(v___x_3717_);
lean_dec(v_fvarId_3716_);
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v_code_3451_);
v___x_3774_ = v___x_3721_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_code_3451_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3717_);
lean_dec(v_fvarId_3716_);
lean_dec_ref(v_code_3451_);
return v___x_3718_;
}
}
else
{
lean_object* v___x_3781_; 
lean_dec_ref(v_code_3451_);
v___x_3781_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3449_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
return v___x_3781_;
}
}
case 8:
{
lean_object* v_fvarId_3782_; lean_object* v_i_3783_; lean_object* v_y_3784_; lean_object* v_k_3785_; lean_object* v___x_3786_; 
v_fvarId_3782_ = lean_ctor_get(v_code_3451_, 0);
v_i_3783_ = lean_ctor_get(v_code_3451_, 1);
v_y_3784_ = lean_ctor_get(v_code_3451_, 2);
v_k_3785_ = lean_ctor_get(v_code_3451_, 3);
lean_inc(v_fvarId_3782_);
v___x_3786_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3452_, v_fvarId_3782_, v_t_3450_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_fvarId_3787_; lean_object* v___x_3788_; 
v_fvarId_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_fvarId_3787_);
lean_dec_ref(v___x_3786_);
lean_inc(v_y_3784_);
v___x_3788_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3452_, v_y_3784_, v_t_3450_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_fvarId_3789_; lean_object* v___x_3790_; 
v_fvarId_3789_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_fvarId_3789_);
lean_dec_ref(v___x_3788_);
lean_inc_ref(v_k_3785_);
v___x_3790_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3449_, v_t_3450_, v_k_3785_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3852_; 
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3793_ = v___x_3790_;
v_isShared_3794_ = v_isSharedCheck_3852_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3790_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3852_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
uint8_t v___y_3796_; size_t v___x_3848_; size_t v___x_3849_; uint8_t v___x_3850_; 
v___x_3848_ = lean_ptr_addr(v_fvarId_3782_);
v___x_3849_ = lean_ptr_addr(v_fvarId_3787_);
v___x_3850_ = lean_usize_dec_eq(v___x_3848_, v___x_3849_);
if (v___x_3850_ == 0)
{
v___y_3796_ = v___x_3850_;
goto v___jp_3795_;
}
else
{
uint8_t v___x_3851_; 
v___x_3851_ = lean_nat_dec_eq(v_i_3783_, v_i_3783_);
v___y_3796_ = v___x_3851_;
goto v___jp_3795_;
}
v___jp_3795_:
{
if (v___y_3796_ == 0)
{
lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3806_; 
lean_inc(v_i_3783_);
v_isSharedCheck_3806_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_3806_ == 0)
{
lean_object* v_unused_3807_; lean_object* v_unused_3808_; lean_object* v_unused_3809_; lean_object* v_unused_3810_; 
v_unused_3807_ = lean_ctor_get(v_code_3451_, 3);
lean_dec(v_unused_3807_);
v_unused_3808_ = lean_ctor_get(v_code_3451_, 2);
lean_dec(v_unused_3808_);
v_unused_3809_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_3809_);
v_unused_3810_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_3810_);
v___x_3798_ = v_code_3451_;
v_isShared_3799_ = v_isSharedCheck_3806_;
goto v_resetjp_3797_;
}
else
{
lean_dec(v_code_3451_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3806_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
if (v_isShared_3799_ == 0)
{
lean_ctor_set(v___x_3798_, 3, v_a_3791_);
lean_ctor_set(v___x_3798_, 2, v_fvarId_3789_);
lean_ctor_set(v___x_3798_, 0, v_fvarId_3787_);
v___x_3801_ = v___x_3798_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_fvarId_3787_);
lean_ctor_set(v_reuseFailAlloc_3805_, 1, v_i_3783_);
lean_ctor_set(v_reuseFailAlloc_3805_, 2, v_fvarId_3789_);
lean_ctor_set(v_reuseFailAlloc_3805_, 3, v_a_3791_);
v___x_3801_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
lean_object* v___x_3803_; 
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 0, v___x_3801_);
v___x_3803_ = v___x_3793_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3801_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
else
{
size_t v___x_3811_; size_t v___x_3812_; uint8_t v___x_3813_; 
v___x_3811_ = lean_ptr_addr(v_y_3784_);
v___x_3812_ = lean_ptr_addr(v_fvarId_3789_);
v___x_3813_ = lean_usize_dec_eq(v___x_3811_, v___x_3812_);
if (v___x_3813_ == 0)
{
lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3823_; 
lean_inc(v_i_3783_);
v_isSharedCheck_3823_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_3823_ == 0)
{
lean_object* v_unused_3824_; lean_object* v_unused_3825_; lean_object* v_unused_3826_; lean_object* v_unused_3827_; 
v_unused_3824_ = lean_ctor_get(v_code_3451_, 3);
lean_dec(v_unused_3824_);
v_unused_3825_ = lean_ctor_get(v_code_3451_, 2);
lean_dec(v_unused_3825_);
v_unused_3826_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_3826_);
v_unused_3827_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_3827_);
v___x_3815_ = v_code_3451_;
v_isShared_3816_ = v_isSharedCheck_3823_;
goto v_resetjp_3814_;
}
else
{
lean_dec(v_code_3451_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3823_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
lean_ctor_set(v___x_3815_, 3, v_a_3791_);
lean_ctor_set(v___x_3815_, 2, v_fvarId_3789_);
lean_ctor_set(v___x_3815_, 0, v_fvarId_3787_);
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_fvarId_3787_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v_i_3783_);
lean_ctor_set(v_reuseFailAlloc_3822_, 2, v_fvarId_3789_);
lean_ctor_set(v_reuseFailAlloc_3822_, 3, v_a_3791_);
v___x_3818_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
lean_object* v___x_3820_; 
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 0, v___x_3818_);
v___x_3820_ = v___x_3793_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v___x_3818_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
}
else
{
size_t v___x_3828_; size_t v___x_3829_; uint8_t v___x_3830_; 
v___x_3828_ = lean_ptr_addr(v_k_3785_);
v___x_3829_ = lean_ptr_addr(v_a_3791_);
v___x_3830_ = lean_usize_dec_eq(v___x_3828_, v___x_3829_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3840_; 
lean_inc(v_i_3783_);
v_isSharedCheck_3840_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_3840_ == 0)
{
lean_object* v_unused_3841_; lean_object* v_unused_3842_; lean_object* v_unused_3843_; lean_object* v_unused_3844_; 
v_unused_3841_ = lean_ctor_get(v_code_3451_, 3);
lean_dec(v_unused_3841_);
v_unused_3842_ = lean_ctor_get(v_code_3451_, 2);
lean_dec(v_unused_3842_);
v_unused_3843_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_3843_);
v_unused_3844_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_3844_);
v___x_3832_ = v_code_3451_;
v_isShared_3833_ = v_isSharedCheck_3840_;
goto v_resetjp_3831_;
}
else
{
lean_dec(v_code_3451_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3840_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3835_; 
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 3, v_a_3791_);
lean_ctor_set(v___x_3832_, 2, v_fvarId_3789_);
lean_ctor_set(v___x_3832_, 0, v_fvarId_3787_);
v___x_3835_ = v___x_3832_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_fvarId_3787_);
lean_ctor_set(v_reuseFailAlloc_3839_, 1, v_i_3783_);
lean_ctor_set(v_reuseFailAlloc_3839_, 2, v_fvarId_3789_);
lean_ctor_set(v_reuseFailAlloc_3839_, 3, v_a_3791_);
v___x_3835_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
lean_object* v___x_3837_; 
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 0, v___x_3835_);
v___x_3837_ = v___x_3793_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___x_3835_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
else
{
lean_object* v___x_3846_; 
lean_dec(v_a_3791_);
lean_dec(v_fvarId_3789_);
lean_dec(v_fvarId_3787_);
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 0, v_code_3451_);
v___x_3846_ = v___x_3793_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_code_3451_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_3789_);
lean_dec(v_fvarId_3787_);
lean_dec_ref(v_code_3451_);
return v___x_3790_;
}
}
else
{
lean_object* v___x_3853_; 
lean_dec(v_fvarId_3787_);
lean_dec_ref(v_code_3451_);
v___x_3853_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3449_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
return v___x_3853_;
}
}
else
{
lean_object* v___x_3854_; 
lean_dec_ref(v_code_3451_);
v___x_3854_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3449_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
return v___x_3854_;
}
}
case 9:
{
lean_object* v_fvarId_3855_; lean_object* v_i_3856_; lean_object* v_offset_3857_; lean_object* v_y_3858_; lean_object* v_ty_3859_; lean_object* v_k_3860_; lean_object* v___x_3861_; 
v_fvarId_3855_ = lean_ctor_get(v_code_3451_, 0);
v_i_3856_ = lean_ctor_get(v_code_3451_, 1);
v_offset_3857_ = lean_ctor_get(v_code_3451_, 2);
v_y_3858_ = lean_ctor_get(v_code_3451_, 3);
v_ty_3859_ = lean_ctor_get(v_code_3451_, 4);
v_k_3860_ = lean_ctor_get(v_code_3451_, 5);
lean_inc(v_fvarId_3855_);
v___x_3861_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3452_, v_fvarId_3855_, v_t_3450_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v_fvarId_3862_; lean_object* v___x_3863_; 
v_fvarId_3862_ = lean_ctor_get(v___x_3861_, 0);
lean_inc(v_fvarId_3862_);
lean_dec_ref(v___x_3861_);
lean_inc(v_y_3858_);
v___x_3863_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3452_, v_y_3858_, v_t_3450_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_fvarId_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v_fvarId_3864_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_fvarId_3864_);
lean_dec_ref(v___x_3863_);
lean_inc_ref(v_ty_3859_);
v___x_3865_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3449_, v_a_3452_, v_t_3450_, v_ty_3859_);
lean_inc_ref(v_k_3860_);
v___x_3866_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3449_, v_t_3450_, v_k_3860_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3970_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3869_ = v___x_3866_;
v_isShared_3870_ = v_isSharedCheck_3970_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3866_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3970_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
uint8_t v___y_3872_; size_t v___x_3966_; size_t v___x_3967_; uint8_t v___x_3968_; 
v___x_3966_ = lean_ptr_addr(v_fvarId_3855_);
v___x_3967_ = lean_ptr_addr(v_fvarId_3862_);
v___x_3968_ = lean_usize_dec_eq(v___x_3966_, v___x_3967_);
if (v___x_3968_ == 0)
{
v___y_3872_ = v___x_3968_;
goto v___jp_3871_;
}
else
{
uint8_t v___x_3969_; 
v___x_3969_ = lean_nat_dec_eq(v_i_3856_, v_i_3856_);
v___y_3872_ = v___x_3969_;
goto v___jp_3871_;
}
v___jp_3871_:
{
if (v___y_3872_ == 0)
{
lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3882_; 
lean_inc(v_offset_3857_);
lean_inc(v_i_3856_);
v_isSharedCheck_3882_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_3882_ == 0)
{
lean_object* v_unused_3883_; lean_object* v_unused_3884_; lean_object* v_unused_3885_; lean_object* v_unused_3886_; lean_object* v_unused_3887_; lean_object* v_unused_3888_; 
v_unused_3883_ = lean_ctor_get(v_code_3451_, 5);
lean_dec(v_unused_3883_);
v_unused_3884_ = lean_ctor_get(v_code_3451_, 4);
lean_dec(v_unused_3884_);
v_unused_3885_ = lean_ctor_get(v_code_3451_, 3);
lean_dec(v_unused_3885_);
v_unused_3886_ = lean_ctor_get(v_code_3451_, 2);
lean_dec(v_unused_3886_);
v_unused_3887_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_3887_);
v_unused_3888_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_3888_);
v___x_3874_ = v_code_3451_;
v_isShared_3875_ = v_isSharedCheck_3882_;
goto v_resetjp_3873_;
}
else
{
lean_dec(v_code_3451_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3882_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
lean_ctor_set(v___x_3874_, 5, v_a_3867_);
lean_ctor_set(v___x_3874_, 4, v___x_3865_);
lean_ctor_set(v___x_3874_, 3, v_fvarId_3864_);
lean_ctor_set(v___x_3874_, 0, v_fvarId_3862_);
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_fvarId_3862_);
lean_ctor_set(v_reuseFailAlloc_3881_, 1, v_i_3856_);
lean_ctor_set(v_reuseFailAlloc_3881_, 2, v_offset_3857_);
lean_ctor_set(v_reuseFailAlloc_3881_, 3, v_fvarId_3864_);
lean_ctor_set(v_reuseFailAlloc_3881_, 4, v___x_3865_);
lean_ctor_set(v_reuseFailAlloc_3881_, 5, v_a_3867_);
v___x_3877_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
lean_object* v___x_3879_; 
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 0, v___x_3877_);
v___x_3879_ = v___x_3869_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3877_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
else
{
uint8_t v___x_3889_; 
v___x_3889_ = lean_nat_dec_eq(v_offset_3857_, v_offset_3857_);
if (v___x_3889_ == 0)
{
lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3899_; 
lean_inc(v_offset_3857_);
lean_inc(v_i_3856_);
v_isSharedCheck_3899_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_3899_ == 0)
{
lean_object* v_unused_3900_; lean_object* v_unused_3901_; lean_object* v_unused_3902_; lean_object* v_unused_3903_; lean_object* v_unused_3904_; lean_object* v_unused_3905_; 
v_unused_3900_ = lean_ctor_get(v_code_3451_, 5);
lean_dec(v_unused_3900_);
v_unused_3901_ = lean_ctor_get(v_code_3451_, 4);
lean_dec(v_unused_3901_);
v_unused_3902_ = lean_ctor_get(v_code_3451_, 3);
lean_dec(v_unused_3902_);
v_unused_3903_ = lean_ctor_get(v_code_3451_, 2);
lean_dec(v_unused_3903_);
v_unused_3904_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_3904_);
v_unused_3905_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_3905_);
v___x_3891_ = v_code_3451_;
v_isShared_3892_ = v_isSharedCheck_3899_;
goto v_resetjp_3890_;
}
else
{
lean_dec(v_code_3451_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3899_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 5, v_a_3867_);
lean_ctor_set(v___x_3891_, 4, v___x_3865_);
lean_ctor_set(v___x_3891_, 3, v_fvarId_3864_);
lean_ctor_set(v___x_3891_, 0, v_fvarId_3862_);
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_fvarId_3862_);
lean_ctor_set(v_reuseFailAlloc_3898_, 1, v_i_3856_);
lean_ctor_set(v_reuseFailAlloc_3898_, 2, v_offset_3857_);
lean_ctor_set(v_reuseFailAlloc_3898_, 3, v_fvarId_3864_);
lean_ctor_set(v_reuseFailAlloc_3898_, 4, v___x_3865_);
lean_ctor_set(v_reuseFailAlloc_3898_, 5, v_a_3867_);
v___x_3894_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
lean_object* v___x_3896_; 
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 0, v___x_3894_);
v___x_3896_ = v___x_3869_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3894_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
}
else
{
size_t v___x_3906_; size_t v___x_3907_; uint8_t v___x_3908_; 
v___x_3906_ = lean_ptr_addr(v_y_3858_);
v___x_3907_ = lean_ptr_addr(v_fvarId_3864_);
v___x_3908_ = lean_usize_dec_eq(v___x_3906_, v___x_3907_);
if (v___x_3908_ == 0)
{
lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3918_; 
lean_inc(v_offset_3857_);
lean_inc(v_i_3856_);
v_isSharedCheck_3918_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_3918_ == 0)
{
lean_object* v_unused_3919_; lean_object* v_unused_3920_; lean_object* v_unused_3921_; lean_object* v_unused_3922_; lean_object* v_unused_3923_; lean_object* v_unused_3924_; 
v_unused_3919_ = lean_ctor_get(v_code_3451_, 5);
lean_dec(v_unused_3919_);
v_unused_3920_ = lean_ctor_get(v_code_3451_, 4);
lean_dec(v_unused_3920_);
v_unused_3921_ = lean_ctor_get(v_code_3451_, 3);
lean_dec(v_unused_3921_);
v_unused_3922_ = lean_ctor_get(v_code_3451_, 2);
lean_dec(v_unused_3922_);
v_unused_3923_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_3923_);
v_unused_3924_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_3924_);
v___x_3910_ = v_code_3451_;
v_isShared_3911_ = v_isSharedCheck_3918_;
goto v_resetjp_3909_;
}
else
{
lean_dec(v_code_3451_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3918_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 5, v_a_3867_);
lean_ctor_set(v___x_3910_, 4, v___x_3865_);
lean_ctor_set(v___x_3910_, 3, v_fvarId_3864_);
lean_ctor_set(v___x_3910_, 0, v_fvarId_3862_);
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_fvarId_3862_);
lean_ctor_set(v_reuseFailAlloc_3917_, 1, v_i_3856_);
lean_ctor_set(v_reuseFailAlloc_3917_, 2, v_offset_3857_);
lean_ctor_set(v_reuseFailAlloc_3917_, 3, v_fvarId_3864_);
lean_ctor_set(v_reuseFailAlloc_3917_, 4, v___x_3865_);
lean_ctor_set(v_reuseFailAlloc_3917_, 5, v_a_3867_);
v___x_3913_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
lean_object* v___x_3915_; 
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 0, v___x_3913_);
v___x_3915_ = v___x_3869_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3913_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
else
{
size_t v___x_3925_; size_t v___x_3926_; uint8_t v___x_3927_; 
v___x_3925_ = lean_ptr_addr(v_ty_3859_);
v___x_3926_ = lean_ptr_addr(v___x_3865_);
v___x_3927_ = lean_usize_dec_eq(v___x_3925_, v___x_3926_);
if (v___x_3927_ == 0)
{
lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3937_; 
lean_inc(v_offset_3857_);
lean_inc(v_i_3856_);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_3937_ == 0)
{
lean_object* v_unused_3938_; lean_object* v_unused_3939_; lean_object* v_unused_3940_; lean_object* v_unused_3941_; lean_object* v_unused_3942_; lean_object* v_unused_3943_; 
v_unused_3938_ = lean_ctor_get(v_code_3451_, 5);
lean_dec(v_unused_3938_);
v_unused_3939_ = lean_ctor_get(v_code_3451_, 4);
lean_dec(v_unused_3939_);
v_unused_3940_ = lean_ctor_get(v_code_3451_, 3);
lean_dec(v_unused_3940_);
v_unused_3941_ = lean_ctor_get(v_code_3451_, 2);
lean_dec(v_unused_3941_);
v_unused_3942_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_3942_);
v_unused_3943_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_3943_);
v___x_3929_ = v_code_3451_;
v_isShared_3930_ = v_isSharedCheck_3937_;
goto v_resetjp_3928_;
}
else
{
lean_dec(v_code_3451_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3937_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
lean_ctor_set(v___x_3929_, 5, v_a_3867_);
lean_ctor_set(v___x_3929_, 4, v___x_3865_);
lean_ctor_set(v___x_3929_, 3, v_fvarId_3864_);
lean_ctor_set(v___x_3929_, 0, v_fvarId_3862_);
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_fvarId_3862_);
lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_i_3856_);
lean_ctor_set(v_reuseFailAlloc_3936_, 2, v_offset_3857_);
lean_ctor_set(v_reuseFailAlloc_3936_, 3, v_fvarId_3864_);
lean_ctor_set(v_reuseFailAlloc_3936_, 4, v___x_3865_);
lean_ctor_set(v_reuseFailAlloc_3936_, 5, v_a_3867_);
v___x_3932_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
lean_object* v___x_3934_; 
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 0, v___x_3932_);
v___x_3934_ = v___x_3869_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
else
{
size_t v___x_3944_; size_t v___x_3945_; uint8_t v___x_3946_; 
v___x_3944_ = lean_ptr_addr(v_k_3860_);
v___x_3945_ = lean_ptr_addr(v_a_3867_);
v___x_3946_ = lean_usize_dec_eq(v___x_3944_, v___x_3945_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3956_; 
lean_inc(v_offset_3857_);
lean_inc(v_i_3856_);
v_isSharedCheck_3956_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_3956_ == 0)
{
lean_object* v_unused_3957_; lean_object* v_unused_3958_; lean_object* v_unused_3959_; lean_object* v_unused_3960_; lean_object* v_unused_3961_; lean_object* v_unused_3962_; 
v_unused_3957_ = lean_ctor_get(v_code_3451_, 5);
lean_dec(v_unused_3957_);
v_unused_3958_ = lean_ctor_get(v_code_3451_, 4);
lean_dec(v_unused_3958_);
v_unused_3959_ = lean_ctor_get(v_code_3451_, 3);
lean_dec(v_unused_3959_);
v_unused_3960_ = lean_ctor_get(v_code_3451_, 2);
lean_dec(v_unused_3960_);
v_unused_3961_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_3961_);
v_unused_3962_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_3962_);
v___x_3948_ = v_code_3451_;
v_isShared_3949_ = v_isSharedCheck_3956_;
goto v_resetjp_3947_;
}
else
{
lean_dec(v_code_3451_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3956_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 5, v_a_3867_);
lean_ctor_set(v___x_3948_, 4, v___x_3865_);
lean_ctor_set(v___x_3948_, 3, v_fvarId_3864_);
lean_ctor_set(v___x_3948_, 0, v_fvarId_3862_);
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_fvarId_3862_);
lean_ctor_set(v_reuseFailAlloc_3955_, 1, v_i_3856_);
lean_ctor_set(v_reuseFailAlloc_3955_, 2, v_offset_3857_);
lean_ctor_set(v_reuseFailAlloc_3955_, 3, v_fvarId_3864_);
lean_ctor_set(v_reuseFailAlloc_3955_, 4, v___x_3865_);
lean_ctor_set(v_reuseFailAlloc_3955_, 5, v_a_3867_);
v___x_3951_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
lean_object* v___x_3953_; 
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 0, v___x_3951_);
v___x_3953_ = v___x_3869_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v___x_3951_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
else
{
lean_object* v___x_3964_; 
lean_dec(v_a_3867_);
lean_dec_ref(v___x_3865_);
lean_dec(v_fvarId_3864_);
lean_dec(v_fvarId_3862_);
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 0, v_code_3451_);
v___x_3964_ = v___x_3869_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_code_3451_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3865_);
lean_dec(v_fvarId_3864_);
lean_dec(v_fvarId_3862_);
lean_dec_ref(v_code_3451_);
return v___x_3866_;
}
}
else
{
lean_object* v___x_3971_; 
lean_dec(v_fvarId_3862_);
lean_dec_ref(v_code_3451_);
v___x_3971_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3449_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
return v___x_3971_;
}
}
else
{
lean_object* v___x_3972_; 
lean_dec_ref(v_code_3451_);
v___x_3972_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3449_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
return v___x_3972_;
}
}
case 10:
{
lean_object* v_fvarId_3973_; lean_object* v_cidx_3974_; lean_object* v_k_3975_; lean_object* v___x_3976_; 
v_fvarId_3973_ = lean_ctor_get(v_code_3451_, 0);
v_cidx_3974_ = lean_ctor_get(v_code_3451_, 1);
v_k_3975_ = lean_ctor_get(v_code_3451_, 2);
lean_inc(v_fvarId_3973_);
v___x_3976_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3452_, v_fvarId_3973_, v_t_3450_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_fvarId_3977_; lean_object* v___x_3978_; 
v_fvarId_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_fvarId_3977_);
lean_dec_ref(v___x_3976_);
lean_inc_ref(v_k_3975_);
v___x_3978_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3449_, v_t_3450_, v_k_3975_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v_a_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_4021_; 
v_a_3979_ = lean_ctor_get(v___x_3978_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_3981_ = v___x_3978_;
v_isShared_3982_ = v_isSharedCheck_4021_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_a_3979_);
lean_dec(v___x_3978_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_4021_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
uint8_t v___y_3984_; size_t v___x_4017_; size_t v___x_4018_; uint8_t v___x_4019_; 
v___x_4017_ = lean_ptr_addr(v_fvarId_3973_);
v___x_4018_ = lean_ptr_addr(v_fvarId_3977_);
v___x_4019_ = lean_usize_dec_eq(v___x_4017_, v___x_4018_);
if (v___x_4019_ == 0)
{
v___y_3984_ = v___x_4019_;
goto v___jp_3983_;
}
else
{
uint8_t v___x_4020_; 
v___x_4020_ = lean_nat_dec_eq(v_cidx_3974_, v_cidx_3974_);
v___y_3984_ = v___x_4020_;
goto v___jp_3983_;
}
v___jp_3983_:
{
if (v___y_3984_ == 0)
{
lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3994_; 
lean_inc(v_cidx_3974_);
v_isSharedCheck_3994_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_3994_ == 0)
{
lean_object* v_unused_3995_; lean_object* v_unused_3996_; lean_object* v_unused_3997_; 
v_unused_3995_ = lean_ctor_get(v_code_3451_, 2);
lean_dec(v_unused_3995_);
v_unused_3996_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_3996_);
v_unused_3997_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_3997_);
v___x_3986_ = v_code_3451_;
v_isShared_3987_ = v_isSharedCheck_3994_;
goto v_resetjp_3985_;
}
else
{
lean_dec(v_code_3451_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3994_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 2, v_a_3979_);
lean_ctor_set(v___x_3986_, 0, v_fvarId_3977_);
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_fvarId_3977_);
lean_ctor_set(v_reuseFailAlloc_3993_, 1, v_cidx_3974_);
lean_ctor_set(v_reuseFailAlloc_3993_, 2, v_a_3979_);
v___x_3989_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
lean_object* v___x_3991_; 
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 0, v___x_3989_);
v___x_3991_ = v___x_3981_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3989_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
else
{
size_t v___x_3998_; size_t v___x_3999_; uint8_t v___x_4000_; 
v___x_3998_ = lean_ptr_addr(v_k_3975_);
v___x_3999_ = lean_ptr_addr(v_a_3979_);
v___x_4000_ = lean_usize_dec_eq(v___x_3998_, v___x_3999_);
if (v___x_4000_ == 0)
{
lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4010_; 
lean_inc(v_cidx_3974_);
v_isSharedCheck_4010_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_4010_ == 0)
{
lean_object* v_unused_4011_; lean_object* v_unused_4012_; lean_object* v_unused_4013_; 
v_unused_4011_ = lean_ctor_get(v_code_3451_, 2);
lean_dec(v_unused_4011_);
v_unused_4012_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_4012_);
v_unused_4013_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_4013_);
v___x_4002_ = v_code_3451_;
v_isShared_4003_ = v_isSharedCheck_4010_;
goto v_resetjp_4001_;
}
else
{
lean_dec(v_code_3451_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4010_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
lean_ctor_set(v___x_4002_, 2, v_a_3979_);
lean_ctor_set(v___x_4002_, 0, v_fvarId_3977_);
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_fvarId_3977_);
lean_ctor_set(v_reuseFailAlloc_4009_, 1, v_cidx_3974_);
lean_ctor_set(v_reuseFailAlloc_4009_, 2, v_a_3979_);
v___x_4005_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
lean_object* v___x_4007_; 
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 0, v___x_4005_);
v___x_4007_ = v___x_3981_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_4005_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
else
{
lean_object* v___x_4015_; 
lean_dec(v_a_3979_);
lean_dec(v_fvarId_3977_);
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 0, v_code_3451_);
v___x_4015_ = v___x_3981_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_code_3451_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_3977_);
lean_dec_ref(v_code_3451_);
return v___x_3978_;
}
}
else
{
lean_object* v___x_4022_; 
lean_dec_ref(v_code_3451_);
v___x_4022_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3449_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
return v___x_4022_;
}
}
case 11:
{
lean_object* v_fvarId_4023_; lean_object* v_n_4024_; uint8_t v_check_4025_; uint8_t v_persistent_4026_; lean_object* v_k_4027_; lean_object* v___x_4028_; 
v_fvarId_4023_ = lean_ctor_get(v_code_3451_, 0);
v_n_4024_ = lean_ctor_get(v_code_3451_, 1);
v_check_4025_ = lean_ctor_get_uint8(v_code_3451_, sizeof(void*)*3);
v_persistent_4026_ = lean_ctor_get_uint8(v_code_3451_, sizeof(void*)*3 + 1);
v_k_4027_ = lean_ctor_get(v_code_3451_, 2);
lean_inc(v_fvarId_4023_);
v___x_4028_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3452_, v_fvarId_4023_, v_t_3450_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_fvarId_4029_; lean_object* v___x_4030_; 
v_fvarId_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc(v_fvarId_4029_);
lean_dec_ref(v___x_4028_);
lean_inc_ref(v_k_4027_);
v___x_4030_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3449_, v_t_3450_, v_k_4027_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4073_; 
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4033_ = v___x_4030_;
v_isShared_4034_ = v_isSharedCheck_4073_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_4030_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4073_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
uint8_t v___y_4036_; size_t v___x_4069_; size_t v___x_4070_; uint8_t v___x_4071_; 
v___x_4069_ = lean_ptr_addr(v_fvarId_4023_);
v___x_4070_ = lean_ptr_addr(v_fvarId_4029_);
v___x_4071_ = lean_usize_dec_eq(v___x_4069_, v___x_4070_);
if (v___x_4071_ == 0)
{
v___y_4036_ = v___x_4071_;
goto v___jp_4035_;
}
else
{
uint8_t v___x_4072_; 
v___x_4072_ = lean_nat_dec_eq(v_n_4024_, v_n_4024_);
v___y_4036_ = v___x_4072_;
goto v___jp_4035_;
}
v___jp_4035_:
{
if (v___y_4036_ == 0)
{
lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4046_; 
lean_inc(v_n_4024_);
v_isSharedCheck_4046_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_4046_ == 0)
{
lean_object* v_unused_4047_; lean_object* v_unused_4048_; lean_object* v_unused_4049_; 
v_unused_4047_ = lean_ctor_get(v_code_3451_, 2);
lean_dec(v_unused_4047_);
v_unused_4048_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_4048_);
v_unused_4049_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_4049_);
v___x_4038_ = v_code_3451_;
v_isShared_4039_ = v_isSharedCheck_4046_;
goto v_resetjp_4037_;
}
else
{
lean_dec(v_code_3451_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4046_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4041_; 
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 2, v_a_4031_);
lean_ctor_set(v___x_4038_, 0, v_fvarId_4029_);
v___x_4041_ = v___x_4038_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_fvarId_4029_);
lean_ctor_set(v_reuseFailAlloc_4045_, 1, v_n_4024_);
lean_ctor_set(v_reuseFailAlloc_4045_, 2, v_a_4031_);
lean_ctor_set_uint8(v_reuseFailAlloc_4045_, sizeof(void*)*3, v_check_4025_);
lean_ctor_set_uint8(v_reuseFailAlloc_4045_, sizeof(void*)*3 + 1, v_persistent_4026_);
v___x_4041_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
lean_object* v___x_4043_; 
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 0, v___x_4041_);
v___x_4043_ = v___x_4033_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v___x_4041_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
else
{
size_t v___x_4050_; size_t v___x_4051_; uint8_t v___x_4052_; 
v___x_4050_ = lean_ptr_addr(v_k_4027_);
v___x_4051_ = lean_ptr_addr(v_a_4031_);
v___x_4052_ = lean_usize_dec_eq(v___x_4050_, v___x_4051_);
if (v___x_4052_ == 0)
{
lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4062_; 
lean_inc(v_n_4024_);
v_isSharedCheck_4062_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_4062_ == 0)
{
lean_object* v_unused_4063_; lean_object* v_unused_4064_; lean_object* v_unused_4065_; 
v_unused_4063_ = lean_ctor_get(v_code_3451_, 2);
lean_dec(v_unused_4063_);
v_unused_4064_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_4064_);
v_unused_4065_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_4065_);
v___x_4054_ = v_code_3451_;
v_isShared_4055_ = v_isSharedCheck_4062_;
goto v_resetjp_4053_;
}
else
{
lean_dec(v_code_3451_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4062_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
lean_ctor_set(v___x_4054_, 2, v_a_4031_);
lean_ctor_set(v___x_4054_, 0, v_fvarId_4029_);
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_fvarId_4029_);
lean_ctor_set(v_reuseFailAlloc_4061_, 1, v_n_4024_);
lean_ctor_set(v_reuseFailAlloc_4061_, 2, v_a_4031_);
lean_ctor_set_uint8(v_reuseFailAlloc_4061_, sizeof(void*)*3, v_check_4025_);
lean_ctor_set_uint8(v_reuseFailAlloc_4061_, sizeof(void*)*3 + 1, v_persistent_4026_);
v___x_4057_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
lean_object* v___x_4059_; 
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 0, v___x_4057_);
v___x_4059_ = v___x_4033_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4057_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
else
{
lean_object* v___x_4067_; 
lean_dec(v_a_4031_);
lean_dec(v_fvarId_4029_);
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 0, v_code_3451_);
v___x_4067_ = v___x_4033_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_code_3451_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4029_);
lean_dec_ref(v_code_3451_);
return v___x_4030_;
}
}
else
{
lean_object* v___x_4074_; 
lean_dec_ref(v_code_3451_);
v___x_4074_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3449_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
return v___x_4074_;
}
}
case 12:
{
lean_object* v_fvarId_4075_; lean_object* v_n_4076_; uint8_t v_check_4077_; uint8_t v_persistent_4078_; lean_object* v_k_4079_; lean_object* v___x_4080_; 
v_fvarId_4075_ = lean_ctor_get(v_code_3451_, 0);
v_n_4076_ = lean_ctor_get(v_code_3451_, 1);
v_check_4077_ = lean_ctor_get_uint8(v_code_3451_, sizeof(void*)*3);
v_persistent_4078_ = lean_ctor_get_uint8(v_code_3451_, sizeof(void*)*3 + 1);
v_k_4079_ = lean_ctor_get(v_code_3451_, 2);
lean_inc(v_fvarId_4075_);
v___x_4080_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3452_, v_fvarId_4075_, v_t_3450_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v_fvarId_4081_; lean_object* v___x_4082_; 
v_fvarId_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_fvarId_4081_);
lean_dec_ref(v___x_4080_);
lean_inc_ref(v_k_4079_);
v___x_4082_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3449_, v_t_3450_, v_k_4079_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4125_; 
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4085_ = v___x_4082_;
v_isShared_4086_ = v_isSharedCheck_4125_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4082_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4125_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
uint8_t v___y_4088_; size_t v___x_4121_; size_t v___x_4122_; uint8_t v___x_4123_; 
v___x_4121_ = lean_ptr_addr(v_fvarId_4075_);
v___x_4122_ = lean_ptr_addr(v_fvarId_4081_);
v___x_4123_ = lean_usize_dec_eq(v___x_4121_, v___x_4122_);
if (v___x_4123_ == 0)
{
v___y_4088_ = v___x_4123_;
goto v___jp_4087_;
}
else
{
uint8_t v___x_4124_; 
v___x_4124_ = lean_nat_dec_eq(v_n_4076_, v_n_4076_);
v___y_4088_ = v___x_4124_;
goto v___jp_4087_;
}
v___jp_4087_:
{
if (v___y_4088_ == 0)
{
lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4098_; 
lean_inc(v_n_4076_);
v_isSharedCheck_4098_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_4098_ == 0)
{
lean_object* v_unused_4099_; lean_object* v_unused_4100_; lean_object* v_unused_4101_; 
v_unused_4099_ = lean_ctor_get(v_code_3451_, 2);
lean_dec(v_unused_4099_);
v_unused_4100_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_4100_);
v_unused_4101_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_4101_);
v___x_4090_ = v_code_3451_;
v_isShared_4091_ = v_isSharedCheck_4098_;
goto v_resetjp_4089_;
}
else
{
lean_dec(v_code_3451_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4098_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v___x_4093_; 
if (v_isShared_4091_ == 0)
{
lean_ctor_set(v___x_4090_, 2, v_a_4083_);
lean_ctor_set(v___x_4090_, 0, v_fvarId_4081_);
v___x_4093_ = v___x_4090_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_fvarId_4081_);
lean_ctor_set(v_reuseFailAlloc_4097_, 1, v_n_4076_);
lean_ctor_set(v_reuseFailAlloc_4097_, 2, v_a_4083_);
lean_ctor_set_uint8(v_reuseFailAlloc_4097_, sizeof(void*)*3, v_check_4077_);
lean_ctor_set_uint8(v_reuseFailAlloc_4097_, sizeof(void*)*3 + 1, v_persistent_4078_);
v___x_4093_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
lean_object* v___x_4095_; 
if (v_isShared_4086_ == 0)
{
lean_ctor_set(v___x_4085_, 0, v___x_4093_);
v___x_4095_ = v___x_4085_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4093_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
else
{
size_t v___x_4102_; size_t v___x_4103_; uint8_t v___x_4104_; 
v___x_4102_ = lean_ptr_addr(v_k_4079_);
v___x_4103_ = lean_ptr_addr(v_a_4083_);
v___x_4104_ = lean_usize_dec_eq(v___x_4102_, v___x_4103_);
if (v___x_4104_ == 0)
{
lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4114_; 
lean_inc(v_n_4076_);
v_isSharedCheck_4114_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_4114_ == 0)
{
lean_object* v_unused_4115_; lean_object* v_unused_4116_; lean_object* v_unused_4117_; 
v_unused_4115_ = lean_ctor_get(v_code_3451_, 2);
lean_dec(v_unused_4115_);
v_unused_4116_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_4116_);
v_unused_4117_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_4117_);
v___x_4106_ = v_code_3451_;
v_isShared_4107_ = v_isSharedCheck_4114_;
goto v_resetjp_4105_;
}
else
{
lean_dec(v_code_3451_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4114_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 2, v_a_4083_);
lean_ctor_set(v___x_4106_, 0, v_fvarId_4081_);
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_fvarId_4081_);
lean_ctor_set(v_reuseFailAlloc_4113_, 1, v_n_4076_);
lean_ctor_set(v_reuseFailAlloc_4113_, 2, v_a_4083_);
lean_ctor_set_uint8(v_reuseFailAlloc_4113_, sizeof(void*)*3, v_check_4077_);
lean_ctor_set_uint8(v_reuseFailAlloc_4113_, sizeof(void*)*3 + 1, v_persistent_4078_);
v___x_4109_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
lean_object* v___x_4111_; 
if (v_isShared_4086_ == 0)
{
lean_ctor_set(v___x_4085_, 0, v___x_4109_);
v___x_4111_ = v___x_4085_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v___x_4109_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
}
}
else
{
lean_object* v___x_4119_; 
lean_dec(v_a_4083_);
lean_dec(v_fvarId_4081_);
if (v_isShared_4086_ == 0)
{
lean_ctor_set(v___x_4085_, 0, v_code_3451_);
v___x_4119_ = v___x_4085_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_code_3451_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4081_);
lean_dec_ref(v_code_3451_);
return v___x_4082_;
}
}
else
{
lean_object* v___x_4126_; 
lean_dec_ref(v_code_3451_);
v___x_4126_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3449_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
return v___x_4126_;
}
}
default: 
{
lean_object* v_fvarId_4127_; lean_object* v_k_4128_; lean_object* v___x_4129_; 
v_fvarId_4127_ = lean_ctor_get(v_code_3451_, 0);
v_k_4128_ = lean_ctor_get(v_code_3451_, 1);
lean_inc(v_fvarId_4127_);
v___x_4129_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3452_, v_fvarId_4127_, v_t_3450_);
if (lean_obj_tag(v___x_4129_) == 0)
{
lean_object* v_fvarId_4130_; lean_object* v___x_4131_; 
v_fvarId_4130_ = lean_ctor_get(v___x_4129_, 0);
lean_inc(v_fvarId_4130_);
lean_dec_ref(v___x_4129_);
lean_inc_ref(v_k_4128_);
v___x_4131_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3449_, v_t_3450_, v_k_4128_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
if (lean_obj_tag(v___x_4131_) == 0)
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4159_; 
v_a_4132_ = lean_ctor_get(v___x_4131_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4131_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4134_ = v___x_4131_;
v_isShared_4135_ = v_isSharedCheck_4159_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v___x_4131_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4159_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
uint8_t v___y_4137_; size_t v___x_4153_; size_t v___x_4154_; uint8_t v___x_4155_; 
v___x_4153_ = lean_ptr_addr(v_fvarId_4127_);
v___x_4154_ = lean_ptr_addr(v_fvarId_4130_);
v___x_4155_ = lean_usize_dec_eq(v___x_4153_, v___x_4154_);
if (v___x_4155_ == 0)
{
v___y_4137_ = v___x_4155_;
goto v___jp_4136_;
}
else
{
size_t v___x_4156_; size_t v___x_4157_; uint8_t v___x_4158_; 
v___x_4156_ = lean_ptr_addr(v_k_4128_);
v___x_4157_ = lean_ptr_addr(v_a_4132_);
v___x_4158_ = lean_usize_dec_eq(v___x_4156_, v___x_4157_);
v___y_4137_ = v___x_4158_;
goto v___jp_4136_;
}
v___jp_4136_:
{
if (v___y_4137_ == 0)
{
lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4147_; 
v_isSharedCheck_4147_ = !lean_is_exclusive(v_code_3451_);
if (v_isSharedCheck_4147_ == 0)
{
lean_object* v_unused_4148_; lean_object* v_unused_4149_; 
v_unused_4148_ = lean_ctor_get(v_code_3451_, 1);
lean_dec(v_unused_4148_);
v_unused_4149_ = lean_ctor_get(v_code_3451_, 0);
lean_dec(v_unused_4149_);
v___x_4139_ = v_code_3451_;
v_isShared_4140_ = v_isSharedCheck_4147_;
goto v_resetjp_4138_;
}
else
{
lean_dec(v_code_3451_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4147_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 1, v_a_4132_);
lean_ctor_set(v___x_4139_, 0, v_fvarId_4130_);
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_fvarId_4130_);
lean_ctor_set(v_reuseFailAlloc_4146_, 1, v_a_4132_);
v___x_4142_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
lean_object* v___x_4144_; 
if (v_isShared_4135_ == 0)
{
lean_ctor_set(v___x_4134_, 0, v___x_4142_);
v___x_4144_ = v___x_4134_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v___x_4142_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
}
else
{
lean_object* v___x_4151_; 
lean_dec(v_a_4132_);
lean_dec(v_fvarId_4130_);
if (v_isShared_4135_ == 0)
{
lean_ctor_set(v___x_4134_, 0, v_code_3451_);
v___x_4151_ = v___x_4134_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_code_3451_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_4130_);
lean_dec_ref(v_code_3451_);
return v___x_4131_;
}
}
else
{
lean_object* v___x_4160_; 
lean_dec_ref(v_code_3451_);
v___x_4160_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3449_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
return v___x_4160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t v_pu_4161_, uint8_t v_t_4162_, lean_object* v_decl_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_){
_start:
{
lean_object* v_params_4170_; lean_object* v_type_4171_; lean_object* v_value_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v_params_4170_ = lean_ctor_get(v_decl_4163_, 2);
v_type_4171_ = lean_ctor_get(v_decl_4163_, 3);
v_value_4172_ = lean_ctor_get(v_decl_4163_, 4);
lean_inc_ref(v_type_4171_);
v___x_4173_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4161_, v_a_4164_, v_t_4162_, v_type_4171_);
lean_inc_ref(v_params_4170_);
v___x_4174_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4161_, v_t_4162_, v_params_4170_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_object* v_a_4175_; lean_object* v___x_4176_; 
v_a_4175_ = lean_ctor_get(v___x_4174_, 0);
lean_inc(v_a_4175_);
lean_dec_ref(v___x_4174_);
lean_inc_ref(v_value_4172_);
v___x_4176_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4161_, v_t_4162_, v_value_4172_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_object* v_a_4177_; lean_object* v___x_4178_; 
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
lean_inc(v_a_4177_);
lean_dec_ref(v___x_4176_);
v___x_4178_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_4161_, v_decl_4163_, v___x_4173_, v_a_4175_, v_a_4177_, v_a_4166_);
return v___x_4178_;
}
else
{
lean_object* v_a_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4186_; 
lean_dec(v_a_4175_);
lean_dec_ref(v___x_4173_);
lean_dec_ref(v_decl_4163_);
v_a_4179_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4181_ = v___x_4176_;
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_a_4179_);
lean_dec(v___x_4176_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___x_4184_; 
if (v_isShared_4182_ == 0)
{
v___x_4184_ = v___x_4181_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_a_4179_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
}
else
{
lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4194_; 
lean_dec_ref(v___x_4173_);
lean_dec_ref(v_decl_4163_);
v_a_4187_ = lean_ctor_get(v___x_4174_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v___x_4174_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4189_ = v___x_4174_;
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4174_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
lean_object* v___x_4192_; 
if (v_isShared_4190_ == 0)
{
v___x_4192_ = v___x_4189_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4187_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp___boxed(lean_object* v_pu_4195_, lean_object* v_t_4196_, lean_object* v_decl_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_){
_start:
{
uint8_t v_pu_boxed_4204_; uint8_t v_t_boxed_4205_; lean_object* v_res_4206_; 
v_pu_boxed_4204_ = lean_unbox(v_pu_4195_);
v_t_boxed_4205_ = lean_unbox(v_t_4196_);
v_res_4206_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_boxed_4204_, v_t_boxed_4205_, v_decl_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_);
lean_dec(v_a_4202_);
lean_dec_ref(v_a_4201_);
lean_dec(v_a_4200_);
lean_dec_ref(v_a_4199_);
lean_dec_ref(v_a_4198_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4___boxed(lean_object* v_pu_4207_, lean_object* v_t_4208_, lean_object* v_i_4209_, lean_object* v_as_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
uint8_t v_pu_boxed_4217_; uint8_t v_t_boxed_4218_; lean_object* v_res_4219_; 
v_pu_boxed_4217_ = lean_unbox(v_pu_4207_);
v_t_boxed_4218_ = lean_unbox(v_t_4208_);
v_res_4219_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_boxed_4217_, v_t_boxed_4218_, v_i_4209_, v_as_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec_ref(v___y_4211_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp___boxed(lean_object* v_pu_4220_, lean_object* v_t_4221_, lean_object* v_code_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_){
_start:
{
uint8_t v_pu_boxed_4229_; uint8_t v_t_boxed_4230_; lean_object* v_res_4231_; 
v_pu_boxed_4229_ = lean_unbox(v_pu_4220_);
v_t_boxed_4230_ = lean_unbox(v_t_4221_);
v_res_4231_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_boxed_4229_, v_t_boxed_4230_, v_code_4222_, v_a_4223_, v_a_4224_, v_a_4225_, v_a_4226_, v_a_4227_);
lean_dec(v_a_4227_);
lean_dec_ref(v_a_4226_);
lean_dec(v_a_4225_);
lean_dec_ref(v_a_4224_);
lean_dec_ref(v_a_4223_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(uint8_t v_pu_4232_, uint8_t v_t_4233_, uint8_t v_pu_4234_, uint8_t v_t_4235_, lean_object* v_decl_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_){
_start:
{
lean_object* v___x_4243_; 
v___x_4243_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_4234_, v_t_4235_, v_decl_4236_, v___y_4237_, v___y_4239_);
return v___x_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___boxed(lean_object* v_pu_4244_, lean_object* v_t_4245_, lean_object* v_pu_4246_, lean_object* v_t_4247_, lean_object* v_decl_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_){
_start:
{
uint8_t v_pu_boxed_4255_; uint8_t v_t_boxed_4256_; uint8_t v_pu_boxed_4257_; uint8_t v_t_boxed_4258_; lean_object* v_res_4259_; 
v_pu_boxed_4255_ = lean_unbox(v_pu_4244_);
v_t_boxed_4256_ = lean_unbox(v_t_4245_);
v_pu_boxed_4257_ = lean_unbox(v_pu_4246_);
v_t_boxed_4258_ = lean_unbox(v_t_4247_);
v_res_4259_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(v_pu_boxed_4255_, v_t_boxed_4256_, v_pu_boxed_4257_, v_t_boxed_4258_, v_decl_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec_ref(v___y_4249_);
return v_res_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(uint8_t v_pu_4260_, uint8_t v_t_4261_, uint8_t v_pu_4262_, uint8_t v_t_4263_, lean_object* v_args_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_4262_, v_t_4263_, v_args_4264_, v___y_4265_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___boxed(lean_object* v_pu_4272_, lean_object* v_t_4273_, lean_object* v_pu_4274_, lean_object* v_t_4275_, lean_object* v_args_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_){
_start:
{
uint8_t v_pu_boxed_4283_; uint8_t v_t_boxed_4284_; uint8_t v_pu_boxed_4285_; uint8_t v_t_boxed_4286_; lean_object* v_res_4287_; 
v_pu_boxed_4283_ = lean_unbox(v_pu_4272_);
v_t_boxed_4284_ = lean_unbox(v_t_4273_);
v_pu_boxed_4285_ = lean_unbox(v_pu_4274_);
v_t_boxed_4286_ = lean_unbox(v_t_4275_);
v_res_4287_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(v_pu_boxed_4283_, v_t_boxed_4284_, v_pu_boxed_4285_, v_t_boxed_4286_, v_args_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec_ref(v___y_4277_);
return v_res_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(uint8_t v_pu_4288_, uint8_t v_t_4289_, uint8_t v_pu_4290_, uint8_t v_t_4291_, lean_object* v_ps_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4290_, v_t_4291_, v_ps_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___boxed(lean_object* v_pu_4300_, lean_object* v_t_4301_, lean_object* v_pu_4302_, lean_object* v_t_4303_, lean_object* v_ps_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
uint8_t v_pu_boxed_4311_; uint8_t v_t_boxed_4312_; uint8_t v_pu_boxed_4313_; uint8_t v_t_boxed_4314_; lean_object* v_res_4315_; 
v_pu_boxed_4311_ = lean_unbox(v_pu_4300_);
v_t_boxed_4312_ = lean_unbox(v_t_4301_);
v_pu_boxed_4313_ = lean_unbox(v_pu_4302_);
v_t_boxed_4314_ = lean_unbox(v_t_4303_);
v_res_4315_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(v_pu_boxed_4311_, v_t_boxed_4312_, v_pu_boxed_4313_, v_t_boxed_4314_, v_ps_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec_ref(v___y_4305_);
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(uint8_t v_pu_4316_, uint8_t v_t_4317_, lean_object* v_i_4318_, lean_object* v_as_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_){
_start:
{
lean_object* v___x_4326_; 
v___x_4326_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_4316_, v_t_4317_, v_i_4318_, v_as_4319_, v___y_4320_, v___y_4322_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___boxed(lean_object* v_pu_4327_, lean_object* v_t_4328_, lean_object* v_i_4329_, lean_object* v_as_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_){
_start:
{
uint8_t v_pu_boxed_4337_; uint8_t v_t_boxed_4338_; lean_object* v_res_4339_; 
v_pu_boxed_4337_ = lean_unbox(v_pu_4327_);
v_t_boxed_4338_ = lean_unbox(v_t_4328_);
v_res_4339_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(v_pu_boxed_4337_, v_t_boxed_4338_, v_i_4329_, v_as_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_);
lean_dec(v___y_4335_);
lean_dec_ref(v___y_4334_);
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
lean_dec_ref(v___y_4331_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(uint8_t v_pu_4340_, uint8_t v_t_4341_, lean_object* v_decl_4342_, lean_object* v_inst_4343_, lean_object* v_____do__lift_4344_){
_start:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; 
v___x_4345_ = lean_box(v_pu_4340_);
v___x_4346_ = lean_box(v_t_4341_);
v___x_4347_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDeclImp___boxed), 9, 4);
lean_closure_set(v___x_4347_, 0, v___x_4345_);
lean_closure_set(v___x_4347_, 1, v___x_4346_);
lean_closure_set(v___x_4347_, 2, v_decl_4342_);
lean_closure_set(v___x_4347_, 3, v_____do__lift_4344_);
v___x_4348_ = lean_apply_2(v_inst_4343_, lean_box(0), v___x_4347_);
return v___x_4348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed(lean_object* v_pu_4349_, lean_object* v_t_4350_, lean_object* v_decl_4351_, lean_object* v_inst_4352_, lean_object* v_____do__lift_4353_){
_start:
{
uint8_t v_pu_boxed_4354_; uint8_t v_t_boxed_4355_; lean_object* v_res_4356_; 
v_pu_boxed_4354_ = lean_unbox(v_pu_4349_);
v_t_boxed_4355_ = lean_unbox(v_t_4350_);
v_res_4356_ = l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(v_pu_boxed_4354_, v_t_boxed_4355_, v_decl_4351_, v_inst_4352_, v_____do__lift_4353_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg(uint8_t v_pu_4357_, uint8_t v_t_4358_, lean_object* v_inst_4359_, lean_object* v_inst_4360_, lean_object* v_inst_4361_, lean_object* v_decl_4362_){
_start:
{
lean_object* v_toBind_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___f_4366_; lean_object* v___x_4367_; 
v_toBind_4363_ = lean_ctor_get(v_inst_4360_, 1);
lean_inc(v_toBind_4363_);
lean_dec_ref(v_inst_4360_);
v___x_4364_ = lean_box(v_pu_4357_);
v___x_4365_ = lean_box(v_t_4358_);
v___f_4366_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4366_, 0, v___x_4364_);
lean_closure_set(v___f_4366_, 1, v___x_4365_);
lean_closure_set(v___f_4366_, 2, v_decl_4362_);
lean_closure_set(v___f_4366_, 3, v_inst_4359_);
v___x_4367_ = lean_apply_4(v_toBind_4363_, lean_box(0), lean_box(0), v_inst_4361_, v___f_4366_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___boxed(lean_object* v_pu_4368_, lean_object* v_t_4369_, lean_object* v_inst_4370_, lean_object* v_inst_4371_, lean_object* v_inst_4372_, lean_object* v_decl_4373_){
_start:
{
uint8_t v_pu_boxed_4374_; uint8_t v_t_boxed_4375_; lean_object* v_res_4376_; 
v_pu_boxed_4374_ = lean_unbox(v_pu_4368_);
v_t_boxed_4375_ = lean_unbox(v_t_4369_);
v_res_4376_ = l_Lean_Compiler_LCNF_normFunDecl___redArg(v_pu_boxed_4374_, v_t_boxed_4375_, v_inst_4370_, v_inst_4371_, v_inst_4372_, v_decl_4373_);
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl(lean_object* v_m_4377_, uint8_t v_pu_4378_, uint8_t v_t_4379_, lean_object* v_inst_4380_, lean_object* v_inst_4381_, lean_object* v_inst_4382_, lean_object* v_decl_4383_){
_start:
{
lean_object* v_toBind_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___f_4387_; lean_object* v___x_4388_; 
v_toBind_4384_ = lean_ctor_get(v_inst_4381_, 1);
lean_inc(v_toBind_4384_);
lean_dec_ref(v_inst_4381_);
v___x_4385_ = lean_box(v_pu_4378_);
v___x_4386_ = lean_box(v_t_4379_);
v___f_4387_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4387_, 0, v___x_4385_);
lean_closure_set(v___f_4387_, 1, v___x_4386_);
lean_closure_set(v___f_4387_, 2, v_decl_4383_);
lean_closure_set(v___f_4387_, 3, v_inst_4380_);
v___x_4388_ = lean_apply_4(v_toBind_4384_, lean_box(0), lean_box(0), v_inst_4382_, v___f_4387_);
return v___x_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___boxed(lean_object* v_m_4389_, lean_object* v_pu_4390_, lean_object* v_t_4391_, lean_object* v_inst_4392_, lean_object* v_inst_4393_, lean_object* v_inst_4394_, lean_object* v_decl_4395_){
_start:
{
uint8_t v_pu_boxed_4396_; uint8_t v_t_boxed_4397_; lean_object* v_res_4398_; 
v_pu_boxed_4396_ = lean_unbox(v_pu_4390_);
v_t_boxed_4397_ = lean_unbox(v_t_4391_);
v_res_4398_ = l_Lean_Compiler_LCNF_normFunDecl(v_m_4389_, v_pu_boxed_4396_, v_t_boxed_4397_, v_inst_4392_, v_inst_4393_, v_inst_4394_, v_decl_4395_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0(uint8_t v_pu_4399_, uint8_t v_t_4400_, lean_object* v_code_4401_, lean_object* v_inst_4402_, lean_object* v_____do__lift_4403_){
_start:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4404_ = lean_box(v_pu_4399_);
v___x_4405_ = lean_box(v_t_4400_);
v___x_4406_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCodeImp___boxed), 9, 4);
lean_closure_set(v___x_4406_, 0, v___x_4404_);
lean_closure_set(v___x_4406_, 1, v___x_4405_);
lean_closure_set(v___x_4406_, 2, v_code_4401_);
lean_closure_set(v___x_4406_, 3, v_____do__lift_4403_);
v___x_4407_ = lean_apply_2(v_inst_4402_, lean_box(0), v___x_4406_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed(lean_object* v_pu_4408_, lean_object* v_t_4409_, lean_object* v_code_4410_, lean_object* v_inst_4411_, lean_object* v_____do__lift_4412_){
_start:
{
uint8_t v_pu_boxed_4413_; uint8_t v_t_boxed_4414_; lean_object* v_res_4415_; 
v_pu_boxed_4413_ = lean_unbox(v_pu_4408_);
v_t_boxed_4414_ = lean_unbox(v_t_4409_);
v_res_4415_ = l_Lean_Compiler_LCNF_normCode___redArg___lam__0(v_pu_boxed_4413_, v_t_boxed_4414_, v_code_4410_, v_inst_4411_, v_____do__lift_4412_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg(uint8_t v_pu_4416_, uint8_t v_t_4417_, lean_object* v_inst_4418_, lean_object* v_inst_4419_, lean_object* v_inst_4420_, lean_object* v_code_4421_){
_start:
{
lean_object* v_toBind_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___f_4425_; lean_object* v___x_4426_; 
v_toBind_4422_ = lean_ctor_get(v_inst_4419_, 1);
lean_inc(v_toBind_4422_);
lean_dec_ref(v_inst_4419_);
v___x_4423_ = lean_box(v_pu_4416_);
v___x_4424_ = lean_box(v_t_4417_);
v___f_4425_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4425_, 0, v___x_4423_);
lean_closure_set(v___f_4425_, 1, v___x_4424_);
lean_closure_set(v___f_4425_, 2, v_code_4421_);
lean_closure_set(v___f_4425_, 3, v_inst_4418_);
v___x_4426_ = lean_apply_4(v_toBind_4422_, lean_box(0), lean_box(0), v_inst_4420_, v___f_4425_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___boxed(lean_object* v_pu_4427_, lean_object* v_t_4428_, lean_object* v_inst_4429_, lean_object* v_inst_4430_, lean_object* v_inst_4431_, lean_object* v_code_4432_){
_start:
{
uint8_t v_pu_boxed_4433_; uint8_t v_t_boxed_4434_; lean_object* v_res_4435_; 
v_pu_boxed_4433_ = lean_unbox(v_pu_4427_);
v_t_boxed_4434_ = lean_unbox(v_t_4428_);
v_res_4435_ = l_Lean_Compiler_LCNF_normCode___redArg(v_pu_boxed_4433_, v_t_boxed_4434_, v_inst_4429_, v_inst_4430_, v_inst_4431_, v_code_4432_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode(lean_object* v_m_4436_, uint8_t v_pu_4437_, uint8_t v_t_4438_, lean_object* v_inst_4439_, lean_object* v_inst_4440_, lean_object* v_inst_4441_, lean_object* v_code_4442_){
_start:
{
lean_object* v_toBind_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___f_4446_; lean_object* v___x_4447_; 
v_toBind_4443_ = lean_ctor_get(v_inst_4440_, 1);
lean_inc(v_toBind_4443_);
lean_dec_ref(v_inst_4440_);
v___x_4444_ = lean_box(v_pu_4437_);
v___x_4445_ = lean_box(v_t_4438_);
v___f_4446_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4446_, 0, v___x_4444_);
lean_closure_set(v___f_4446_, 1, v___x_4445_);
lean_closure_set(v___f_4446_, 2, v_code_4442_);
lean_closure_set(v___f_4446_, 3, v_inst_4439_);
v___x_4447_ = lean_apply_4(v_toBind_4443_, lean_box(0), lean_box(0), v_inst_4441_, v___f_4446_);
return v___x_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___boxed(lean_object* v_m_4448_, lean_object* v_pu_4449_, lean_object* v_t_4450_, lean_object* v_inst_4451_, lean_object* v_inst_4452_, lean_object* v_inst_4453_, lean_object* v_code_4454_){
_start:
{
uint8_t v_pu_boxed_4455_; uint8_t v_t_boxed_4456_; lean_object* v_res_4457_; 
v_pu_boxed_4455_ = lean_unbox(v_pu_4449_);
v_t_boxed_4456_ = lean_unbox(v_t_4450_);
v_res_4457_ = l_Lean_Compiler_LCNF_normCode(v_m_4448_, v_pu_boxed_4455_, v_t_boxed_4456_, v_inst_4451_, v_inst_4452_, v_inst_4453_, v_code_4454_);
return v_res_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t v_pu_4458_, lean_object* v_e_4459_, lean_object* v_s_4460_, uint8_t v_translator_4461_){
_start:
{
lean_object* v___x_4463_; lean_object* v___x_4464_; 
v___x_4463_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4458_, v_s_4460_, v_translator_4461_, v_e_4459_);
v___x_4464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4464_, 0, v___x_4463_);
return v___x_4464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg___boxed(lean_object* v_pu_4465_, lean_object* v_e_4466_, lean_object* v_s_4467_, lean_object* v_translator_4468_, lean_object* v_a_4469_){
_start:
{
uint8_t v_pu_boxed_4470_; uint8_t v_translator_boxed_4471_; lean_object* v_res_4472_; 
v_pu_boxed_4470_ = lean_unbox(v_pu_4465_);
v_translator_boxed_4471_ = lean_unbox(v_translator_4468_);
v_res_4472_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_boxed_4470_, v_e_4466_, v_s_4467_, v_translator_boxed_4471_);
lean_dec_ref(v_s_4467_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(uint8_t v_pu_4473_, lean_object* v_e_4474_, lean_object* v_s_4475_, uint8_t v_translator_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_){
_start:
{
lean_object* v___x_4482_; 
v___x_4482_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_4473_, v_e_4474_, v_s_4475_, v_translator_4476_);
return v___x_4482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___boxed(lean_object* v_pu_4483_, lean_object* v_e_4484_, lean_object* v_s_4485_, lean_object* v_translator_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_){
_start:
{
uint8_t v_pu_boxed_4492_; uint8_t v_translator_boxed_4493_; lean_object* v_res_4494_; 
v_pu_boxed_4492_ = lean_unbox(v_pu_4483_);
v_translator_boxed_4493_ = lean_unbox(v_translator_4486_);
v_res_4494_ = l_Lean_Compiler_LCNF_replaceExprFVars(v_pu_boxed_4492_, v_e_4484_, v_s_4485_, v_translator_boxed_4493_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_);
lean_dec(v_a_4490_);
lean_dec_ref(v_a_4489_);
lean_dec(v_a_4488_);
lean_dec_ref(v_a_4487_);
lean_dec_ref(v_s_4485_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t v_pu_4495_, lean_object* v_code_4496_, lean_object* v_s_4497_, uint8_t v_translator_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_){
_start:
{
lean_object* v___x_4504_; 
v___x_4504_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4495_, v_translator_4498_, v_code_4496_, v_s_4497_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_);
return v___x_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars___boxed(lean_object* v_pu_4505_, lean_object* v_code_4506_, lean_object* v_s_4507_, lean_object* v_translator_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_){
_start:
{
uint8_t v_pu_boxed_4514_; uint8_t v_translator_boxed_4515_; lean_object* v_res_4516_; 
v_pu_boxed_4514_ = lean_unbox(v_pu_4505_);
v_translator_boxed_4515_ = lean_unbox(v_translator_4508_);
v_res_4516_ = l_Lean_Compiler_LCNF_replaceFVars(v_pu_boxed_4514_, v_code_4506_, v_s_4507_, v_translator_boxed_4515_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_);
lean_dec(v_a_4512_);
lean_dec_ref(v_a_4511_);
lean_dec(v_a_4510_);
lean_dec_ref(v_a_4509_);
lean_dec_ref(v_s_4507_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg(lean_object* v_a_4520_){
_start:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4522_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1));
v___x_4523_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4522_, v_a_4520_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___boxed(lean_object* v_a_4524_, lean_object* v_a_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4524_);
lean_dec(v_a_4524_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName(lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_){
_start:
{
lean_object* v___x_4532_; 
v___x_4532_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4528_);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___boxed(lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_){
_start:
{
lean_object* v_res_4538_; 
v_res_4538_ = l_Lean_Compiler_LCNF_mkFreshJpName(v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_);
lean_dec(v_a_4536_);
lean_dec_ref(v_a_4535_);
lean_dec(v_a_4534_);
lean_dec_ref(v_a_4533_);
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t v_pu_4539_, lean_object* v_type_4540_, uint8_t v_borrow_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_){
_start:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v_a_4549_; lean_object* v___x_4550_; 
v___x_4547_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_4548_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4547_, v_a_4543_);
v_a_4549_ = lean_ctor_get(v___x_4548_, 0);
lean_inc(v_a_4549_);
lean_dec_ref(v___x_4548_);
v___x_4550_ = l_Lean_Compiler_LCNF_mkParam(v_pu_4539_, v_a_4549_, v_type_4540_, v_borrow_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_);
return v___x_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam___boxed(lean_object* v_pu_4551_, lean_object* v_type_4552_, lean_object* v_borrow_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_){
_start:
{
uint8_t v_pu_boxed_4559_; uint8_t v_borrow_boxed_4560_; lean_object* v_res_4561_; 
v_pu_boxed_4559_ = lean_unbox(v_pu_4551_);
v_borrow_boxed_4560_ = lean_unbox(v_borrow_4553_);
v_res_4561_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_boxed_4559_, v_type_4552_, v_borrow_boxed_4560_, v_a_4554_, v_a_4555_, v_a_4556_, v_a_4557_);
lean_dec(v_a_4557_);
lean_dec_ref(v_a_4556_);
lean_dec(v_a_4555_);
lean_dec_ref(v_a_4554_);
return v_res_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object* v_a_4562_){
_start:
{
lean_object* v_config_4564_; lean_object* v___x_4565_; 
v_config_4564_ = lean_ctor_get(v_a_4562_, 0);
lean_inc_ref(v_config_4564_);
v___x_4565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4565_, 0, v_config_4564_);
return v___x_4565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg___boxed(lean_object* v_a_4566_, lean_object* v_a_4567_){
_start:
{
lean_object* v_res_4568_; 
v_res_4568_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4566_);
lean_dec_ref(v_a_4566_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig(lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_){
_start:
{
lean_object* v___x_4574_; 
v___x_4574_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4569_);
return v___x_4574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___boxed(lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l_Lean_Compiler_LCNF_getConfig(v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_);
lean_dec(v_a_4578_);
lean_dec_ref(v_a_4577_);
lean_dec(v_a_4576_);
lean_dec_ref(v_a_4575_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object* v_x_4581_, lean_object* v_s_4582_, uint8_t v_phase_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_){
_start:
{
lean_object* v___x_4587_; lean_object* v_options_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
v___x_4587_ = lean_st_mk_ref(v_s_4582_);
v_options_4588_ = lean_ctor_get(v_a_4584_, 2);
v___x_4589_ = l_Lean_Compiler_LCNF_toConfigOptions(v_options_4588_);
v___x_4590_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4590_, 0, v___x_4589_);
lean_ctor_set_uint8(v___x_4590_, sizeof(void*)*1, v_phase_4583_);
lean_inc(v_a_4585_);
lean_inc_ref(v_a_4584_);
lean_inc(v___x_4587_);
v___x_4591_ = lean_apply_5(v_x_4581_, v___x_4590_, v___x_4587_, v_a_4584_, v_a_4585_, lean_box(0));
if (lean_obj_tag(v___x_4591_) == 0)
{
lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4600_; 
v_a_4592_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4594_ = v___x_4591_;
v_isShared_4595_ = v_isSharedCheck_4600_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v___x_4591_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4600_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v___x_4596_; lean_object* v___x_4598_; 
v___x_4596_ = lean_st_ref_get(v___x_4587_);
lean_dec(v___x_4587_);
lean_dec(v___x_4596_);
if (v_isShared_4595_ == 0)
{
v___x_4598_ = v___x_4594_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_a_4592_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
else
{
lean_dec(v___x_4587_);
return v___x_4591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg___boxed(lean_object* v_x_4601_, lean_object* v_s_4602_, lean_object* v_phase_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_){
_start:
{
uint8_t v_phase_boxed_4607_; lean_object* v_res_4608_; 
v_phase_boxed_4607_ = lean_unbox(v_phase_4603_);
v_res_4608_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4601_, v_s_4602_, v_phase_boxed_4607_, v_a_4604_, v_a_4605_);
lean_dec(v_a_4605_);
lean_dec_ref(v_a_4604_);
return v_res_4608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run(lean_object* v_00_u03b1_4609_, lean_object* v_x_4610_, lean_object* v_s_4611_, uint8_t v_phase_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_){
_start:
{
lean_object* v___x_4616_; 
v___x_4616_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4610_, v_s_4611_, v_phase_4612_, v_a_4613_, v_a_4614_);
return v___x_4616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___boxed(lean_object* v_00_u03b1_4617_, lean_object* v_x_4618_, lean_object* v_s_4619_, lean_object* v_phase_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_){
_start:
{
uint8_t v_phase_boxed_4624_; lean_object* v_res_4625_; 
v_phase_boxed_4624_ = lean_unbox(v_phase_4620_);
v_res_4625_ = l_Lean_Compiler_LCNF_CompilerM_run(v_00_u03b1_4617_, v_x_4618_, v_s_4619_, v_phase_boxed_4624_, v_a_4621_, v_a_4622_);
lean_dec(v_a_4622_);
lean_dec_ref(v_a_4621_);
return v_res_4625_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0(void){
_start:
{
lean_object* v___x_4626_; 
v___x_4626_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_4626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(lean_object* v_00_u03b1_4627_, lean_object* v_00_u03b2_4628_, lean_object* v_inst_4629_, lean_object* v_inst_4630_){
_start:
{
lean_object* v___x_4631_; 
v___x_4631_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(lean_object* v_00_u03b1_4632_, lean_object* v_00_u03b2_4633_, lean_object* v_inst_4634_, lean_object* v_inst_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(v_00_u03b1_4632_, v_00_u03b2_4633_, v_inst_4634_, v_inst_4635_);
lean_dec_ref(v_inst_4635_);
lean_dec_ref(v_inst_4634_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension(lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_){
_start:
{
lean_object* v___x_4641_; 
v___x_4641_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___boxed(lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_){
_start:
{
lean_object* v_res_4646_; 
v_res_4646_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension(v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
lean_dec_ref(v_a_4645_);
lean_dec_ref(v_a_4644_);
return v_res_4646_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; 
v___x_4650_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2));
v___x_4651_ = lean_unsigned_to_nat(14u);
v___x_4652_ = lean_unsigned_to_nat(177u);
v___x_4653_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1));
v___x_4654_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0));
v___x_4655_ = l_mkPanicMessageWithDecl(v___x_4654_, v___x_4653_, v___x_4652_, v___x_4651_, v___x_4650_);
return v___x_4655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(lean_object* v_inst_4656_, lean_object* v_inst_4657_, lean_object* v_snd_4658_, lean_object* v_inst_4659_, lean_object* v_s_4660_, lean_object* v_e_4661_){
_start:
{
lean_object* v_fst_4662_; lean_object* v_snd_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4678_; 
v_fst_4662_ = lean_ctor_get(v_s_4660_, 0);
v_snd_4663_ = lean_ctor_get(v_s_4660_, 1);
v_isSharedCheck_4678_ = !lean_is_exclusive(v_s_4660_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4665_ = v_s_4660_;
v_isShared_4666_ = v_isSharedCheck_4678_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_snd_4663_);
lean_inc(v_fst_4662_);
lean_dec(v_s_4660_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4678_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___x_4667_; lean_object* v___y_4669_; lean_object* v___x_4674_; 
lean_inc_n(v_e_4661_, 2);
v___x_4667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4667_, 0, v_e_4661_);
lean_ctor_set(v___x_4667_, 1, v_fst_4662_);
lean_inc_ref(v_inst_4657_);
lean_inc_ref(v_inst_4656_);
v___x_4674_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4656_, v_inst_4657_, v_snd_4658_, v_e_4661_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4675_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3);
v___x_4676_ = l_panic___redArg(v_inst_4659_, v___x_4675_);
v___y_4669_ = v___x_4676_;
goto v___jp_4668_;
}
else
{
lean_object* v_val_4677_; 
v_val_4677_ = lean_ctor_get(v___x_4674_, 0);
lean_inc(v_val_4677_);
lean_dec_ref(v___x_4674_);
v___y_4669_ = v_val_4677_;
goto v___jp_4668_;
}
v___jp_4668_:
{
lean_object* v___x_4670_; lean_object* v___x_4672_; 
v___x_4670_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4656_, v_inst_4657_, v_snd_4663_, v_e_4661_, v___y_4669_);
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 1, v___x_4670_);
lean_ctor_set(v___x_4665_, 0, v___x_4667_);
v___x_4672_ = v___x_4665_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v___x_4667_);
lean_ctor_set(v_reuseFailAlloc_4673_, 1, v___x_4670_);
v___x_4672_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
return v___x_4672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed(lean_object* v_inst_4679_, lean_object* v_inst_4680_, lean_object* v_snd_4681_, lean_object* v_inst_4682_, lean_object* v_s_4683_, lean_object* v_e_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(v_inst_4679_, v_inst_4680_, v_snd_4681_, v_inst_4682_, v_s_4683_, v_e_4684_);
lean_dec(v_inst_4682_);
lean_dec(v_snd_4681_);
return v_res_4685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(lean_object* v_inst_4688_, lean_object* v_inst_4689_, lean_object* v_inst_4690_, lean_object* v_oldState_4691_, lean_object* v_newState_4692_, lean_object* v_x_4693_, lean_object* v_s_4694_){
_start:
{
lean_object* v_fst_4695_; lean_object* v_snd_4696_; lean_object* v_fst_4697_; lean_object* v___f_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v_newEntries_4703_; lean_object* v___x_4704_; 
v_fst_4695_ = lean_ctor_get(v_newState_4692_, 0);
lean_inc_n(v_fst_4695_, 2);
v_snd_4696_ = lean_ctor_get(v_newState_4692_, 1);
lean_inc(v_snd_4696_);
lean_dec_ref(v_newState_4692_);
v_fst_4697_ = lean_ctor_get(v_oldState_4691_, 0);
v___f_4698_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_4698_, 0, v_inst_4688_);
lean_closure_set(v___f_4698_, 1, v_inst_4689_);
lean_closure_set(v___f_4698_, 2, v_snd_4696_);
lean_closure_set(v___f_4698_, 3, v_inst_4690_);
v___x_4699_ = l_List_lengthTR___redArg(v_fst_4695_);
v___x_4700_ = l_List_lengthTR___redArg(v_fst_4697_);
v___x_4701_ = lean_nat_sub(v___x_4699_, v___x_4700_);
lean_dec(v___x_4700_);
lean_dec(v___x_4699_);
v___x_4702_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0));
v_newEntries_4703_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_fst_4695_, v_fst_4695_, v___x_4701_, v___x_4702_);
lean_dec(v_fst_4695_);
v___x_4704_ = l_List_foldl___redArg(v___f_4698_, v_s_4694_, v_newEntries_4703_);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(lean_object* v_inst_4705_, lean_object* v_inst_4706_, lean_object* v_inst_4707_, lean_object* v_oldState_4708_, lean_object* v_newState_4709_, lean_object* v_x_4710_, lean_object* v_s_4711_){
_start:
{
lean_object* v_res_4712_; 
v_res_4712_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(v_inst_4705_, v_inst_4706_, v_inst_4707_, v_oldState_4708_, v_newState_4709_, v_x_4710_, v_s_4711_);
lean_dec(v_x_4710_);
lean_dec_ref(v_oldState_4708_);
return v_res_4712_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0(void){
_start:
{
lean_object* v___x_4713_; 
v___x_4713_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4713_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1(void){
_start:
{
lean_object* v___x_4714_; lean_object* v___x_4715_; 
v___x_4714_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0);
v___x_4715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4714_);
return v___x_4715_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2(void){
_start:
{
lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
v___x_4716_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1);
v___x_4717_ = lean_box(0);
v___x_4718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4718_, 0, v___x_4717_);
lean_ctor_set(v___x_4718_, 1, v___x_4716_);
return v___x_4718_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3(void){
_start:
{
lean_object* v___x_4719_; lean_object* v___x_4720_; 
v___x_4719_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2);
v___x_4720_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_4720_, 0, lean_box(0));
lean_closure_set(v___x_4720_, 1, lean_box(0));
lean_closure_set(v___x_4720_, 2, v___x_4719_);
return v___x_4720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object* v_inst_4721_, lean_object* v_inst_4722_, lean_object* v_inst_4723_){
_start:
{
lean_object* v___f_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; 
v___f_4725_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4725_, 0, v_inst_4721_);
lean_closure_set(v___f_4725_, 1, v_inst_4722_);
lean_closure_set(v___f_4725_, 2, v_inst_4723_);
v___x_4726_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3);
v___x_4727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4727_, 0, v___f_4725_);
v___x_4728_ = lean_box(0);
v___x_4729_ = l_Lean_registerEnvExtension___redArg(v___x_4726_, v___x_4727_, v___x_4728_);
if (lean_obj_tag(v___x_4729_) == 0)
{
lean_object* v_a_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4737_; 
v_a_4730_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4737_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4737_ == 0)
{
v___x_4732_ = v___x_4729_;
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_a_4730_);
lean_dec(v___x_4729_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___x_4735_; 
if (v_isShared_4733_ == 0)
{
v___x_4735_ = v___x_4732_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4730_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
return v___x_4735_;
}
}
}
else
{
lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4745_; 
v_a_4738_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4740_ = v___x_4729_;
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_a_4738_);
lean_dec(v___x_4729_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4743_; 
if (v_isShared_4741_ == 0)
{
v___x_4743_ = v___x_4740_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_a_4738_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
return v___x_4743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object* v_inst_4746_, lean_object* v_inst_4747_, lean_object* v_inst_4748_, lean_object* v_a_4749_){
_start:
{
lean_object* v_res_4750_; 
v_res_4750_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4746_, v_inst_4747_, v_inst_4748_);
return v_res_4750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object* v_00_u03b1_4751_, lean_object* v_00_u03b2_4752_, lean_object* v_inst_4753_, lean_object* v_inst_4754_, lean_object* v_inst_4755_){
_start:
{
lean_object* v___x_4757_; 
v___x_4757_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4753_, v_inst_4754_, v_inst_4755_);
return v___x_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object* v_00_u03b1_4758_, lean_object* v_00_u03b2_4759_, lean_object* v_inst_4760_, lean_object* v_inst_4761_, lean_object* v_inst_4762_, lean_object* v_a_4763_){
_start:
{
lean_object* v_res_4764_; 
v_res_4764_ = l_Lean_Compiler_LCNF_CacheExtension_register(v_00_u03b1_4758_, v_00_u03b2_4759_, v_inst_4760_, v_inst_4761_, v_inst_4762_);
return v_res_4764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object* v_a_4765_, lean_object* v_inst_4766_, lean_object* v_inst_4767_, lean_object* v_b_4768_, lean_object* v_x_4769_){
_start:
{
lean_object* v_fst_4770_; lean_object* v_snd_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4780_; 
v_fst_4770_ = lean_ctor_get(v_x_4769_, 0);
v_snd_4771_ = lean_ctor_get(v_x_4769_, 1);
v_isSharedCheck_4780_ = !lean_is_exclusive(v_x_4769_);
if (v_isSharedCheck_4780_ == 0)
{
v___x_4773_ = v_x_4769_;
v_isShared_4774_ = v_isSharedCheck_4780_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_snd_4771_);
lean_inc(v_fst_4770_);
lean_dec(v_x_4769_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4780_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4778_; 
lean_inc(v_a_4765_);
v___x_4775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4775_, 0, v_a_4765_);
lean_ctor_set(v___x_4775_, 1, v_fst_4770_);
v___x_4776_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4766_, v_inst_4767_, v_snd_4771_, v_a_4765_, v_b_4768_);
if (v_isShared_4774_ == 0)
{
lean_ctor_set(v___x_4773_, 1, v___x_4776_);
lean_ctor_set(v___x_4773_, 0, v___x_4775_);
v___x_4778_ = v___x_4773_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v___x_4775_);
lean_ctor_set(v_reuseFailAlloc_4779_, 1, v___x_4776_);
v___x_4778_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
return v___x_4778_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_4781_; 
v___x_4781_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4781_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___x_4782_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0);
v___x_4783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4783_, 0, v___x_4782_);
return v___x_4783_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2(void){
_start:
{
lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4784_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1);
v___x_4785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4785_, 0, v___x_4784_);
lean_ctor_set(v___x_4785_, 1, v___x_4784_);
return v___x_4785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object* v_inst_4786_, lean_object* v_inst_4787_, lean_object* v_ext_4788_, lean_object* v_a_4789_, lean_object* v_b_4790_, lean_object* v_a_4791_){
_start:
{
lean_object* v___x_4793_; lean_object* v_env_4794_; lean_object* v_nextMacroScope_4795_; lean_object* v_ngen_4796_; lean_object* v_auxDeclNGen_4797_; lean_object* v_traceState_4798_; lean_object* v_messages_4799_; lean_object* v_infoState_4800_; lean_object* v_snapshotTasks_4801_; lean_object* v_newDecls_4802_; lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4817_; 
v___x_4793_ = lean_st_ref_take(v_a_4791_);
v_env_4794_ = lean_ctor_get(v___x_4793_, 0);
v_nextMacroScope_4795_ = lean_ctor_get(v___x_4793_, 1);
v_ngen_4796_ = lean_ctor_get(v___x_4793_, 2);
v_auxDeclNGen_4797_ = lean_ctor_get(v___x_4793_, 3);
v_traceState_4798_ = lean_ctor_get(v___x_4793_, 4);
v_messages_4799_ = lean_ctor_get(v___x_4793_, 6);
v_infoState_4800_ = lean_ctor_get(v___x_4793_, 7);
v_snapshotTasks_4801_ = lean_ctor_get(v___x_4793_, 8);
v_newDecls_4802_ = lean_ctor_get(v___x_4793_, 9);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4817_ == 0)
{
lean_object* v_unused_4818_; 
v_unused_4818_ = lean_ctor_get(v___x_4793_, 5);
lean_dec(v_unused_4818_);
v___x_4804_ = v___x_4793_;
v_isShared_4805_ = v_isSharedCheck_4817_;
goto v_resetjp_4803_;
}
else
{
lean_inc(v_newDecls_4802_);
lean_inc(v_snapshotTasks_4801_);
lean_inc(v_infoState_4800_);
lean_inc(v_messages_4799_);
lean_inc(v_traceState_4798_);
lean_inc(v_auxDeclNGen_4797_);
lean_inc(v_ngen_4796_);
lean_inc(v_nextMacroScope_4795_);
lean_inc(v_env_4794_);
lean_dec(v___x_4793_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4817_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v_asyncMode_4806_; lean_object* v___f_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4812_; 
v_asyncMode_4806_ = lean_ctor_get(v_ext_4788_, 2);
lean_inc(v_asyncMode_4806_);
v___f_4807_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4807_, 0, v_a_4789_);
lean_closure_set(v___f_4807_, 1, v_inst_4786_);
lean_closure_set(v___f_4807_, 2, v_inst_4787_);
lean_closure_set(v___f_4807_, 3, v_b_4790_);
v___x_4808_ = lean_box(0);
v___x_4809_ = l_Lean_EnvExtension_modifyState___redArg(v_ext_4788_, v_env_4794_, v___f_4807_, v_asyncMode_4806_, v___x_4808_);
lean_dec(v_asyncMode_4806_);
v___x_4810_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2);
if (v_isShared_4805_ == 0)
{
lean_ctor_set(v___x_4804_, 5, v___x_4810_);
lean_ctor_set(v___x_4804_, 0, v___x_4809_);
v___x_4812_ = v___x_4804_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v___x_4809_);
lean_ctor_set(v_reuseFailAlloc_4816_, 1, v_nextMacroScope_4795_);
lean_ctor_set(v_reuseFailAlloc_4816_, 2, v_ngen_4796_);
lean_ctor_set(v_reuseFailAlloc_4816_, 3, v_auxDeclNGen_4797_);
lean_ctor_set(v_reuseFailAlloc_4816_, 4, v_traceState_4798_);
lean_ctor_set(v_reuseFailAlloc_4816_, 5, v___x_4810_);
lean_ctor_set(v_reuseFailAlloc_4816_, 6, v_messages_4799_);
lean_ctor_set(v_reuseFailAlloc_4816_, 7, v_infoState_4800_);
lean_ctor_set(v_reuseFailAlloc_4816_, 8, v_snapshotTasks_4801_);
lean_ctor_set(v_reuseFailAlloc_4816_, 9, v_newDecls_4802_);
v___x_4812_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4813_ = lean_st_ref_set(v_a_4791_, v___x_4812_);
v___x_4814_ = lean_box(0);
v___x_4815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4815_, 0, v___x_4814_);
return v___x_4815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object* v_inst_4819_, lean_object* v_inst_4820_, lean_object* v_ext_4821_, lean_object* v_a_4822_, lean_object* v_b_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_){
_start:
{
lean_object* v_res_4826_; 
v_res_4826_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4819_, v_inst_4820_, v_ext_4821_, v_a_4822_, v_b_4823_, v_a_4824_);
lean_dec(v_a_4824_);
return v_res_4826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object* v_00_u03b1_4827_, lean_object* v_00_u03b2_4828_, lean_object* v_inst_4829_, lean_object* v_inst_4830_, lean_object* v_inst_4831_, lean_object* v_ext_4832_, lean_object* v_a_4833_, lean_object* v_b_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_){
_start:
{
lean_object* v___x_4838_; 
v___x_4838_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4829_, v_inst_4830_, v_ext_4832_, v_a_4833_, v_b_4834_, v_a_4836_);
return v___x_4838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object* v_00_u03b1_4839_, lean_object* v_00_u03b2_4840_, lean_object* v_inst_4841_, lean_object* v_inst_4842_, lean_object* v_inst_4843_, lean_object* v_ext_4844_, lean_object* v_a_4845_, lean_object* v_b_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l_Lean_Compiler_LCNF_CacheExtension_insert(v_00_u03b1_4839_, v_00_u03b2_4840_, v_inst_4841_, v_inst_4842_, v_inst_4843_, v_ext_4844_, v_a_4845_, v_b_4846_, v_a_4847_, v_a_4848_);
lean_dec(v_a_4848_);
lean_dec_ref(v_a_4847_);
lean_dec(v_inst_4843_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(lean_object* v_inst_4851_, lean_object* v_inst_4852_, lean_object* v_ext_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_){
_start:
{
lean_object* v___x_4857_; lean_object* v_env_4858_; lean_object* v_asyncMode_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v_snd_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; 
v___x_4857_ = lean_st_ref_get(v_a_4855_);
v_env_4858_ = lean_ctor_get(v___x_4857_, 0);
lean_inc_ref(v_env_4858_);
lean_dec(v___x_4857_);
v_asyncMode_4859_ = lean_ctor_get(v_ext_4853_, 2);
v___x_4860_ = lean_box(0);
v___x_4861_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v_inst_4851_, v_inst_4852_);
v___x_4862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4862_, 0, v___x_4860_);
lean_ctor_set(v___x_4862_, 1, v___x_4861_);
v___x_4863_ = lean_box(0);
v___x_4864_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4862_, v_ext_4853_, v_env_4858_, v_asyncMode_4859_, v___x_4863_);
lean_dec_ref(v___x_4862_);
v_snd_4865_ = lean_ctor_get(v___x_4864_, 1);
lean_inc(v_snd_4865_);
lean_dec(v___x_4864_);
v___x_4866_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4851_, v_inst_4852_, v_snd_4865_, v_a_4854_);
lean_dec(v_snd_4865_);
v___x_4867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4867_, 0, v___x_4866_);
return v___x_4867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(lean_object* v_inst_4868_, lean_object* v_inst_4869_, lean_object* v_ext_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_){
_start:
{
lean_object* v_res_4874_; 
v_res_4874_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4868_, v_inst_4869_, v_ext_4870_, v_a_4871_, v_a_4872_);
lean_dec(v_a_4872_);
lean_dec_ref(v_ext_4870_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_object* v_00_u03b1_4875_, lean_object* v_00_u03b2_4876_, lean_object* v_inst_4877_, lean_object* v_inst_4878_, lean_object* v_inst_4879_, lean_object* v_ext_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_){
_start:
{
lean_object* v___x_4885_; 
v___x_4885_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4877_, v_inst_4878_, v_ext_4880_, v_a_4881_, v_a_4883_);
return v___x_4885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(lean_object* v_00_u03b1_4886_, lean_object* v_00_u03b2_4887_, lean_object* v_inst_4888_, lean_object* v_inst_4889_, lean_object* v_inst_4890_, lean_object* v_ext_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_){
_start:
{
lean_object* v_res_4896_; 
v_res_4896_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f(v_00_u03b1_4886_, v_00_u03b2_4887_, v_inst_4888_, v_inst_4889_, v_inst_4890_, v_ext_4891_, v_a_4892_, v_a_4893_, v_a_4894_);
lean_dec(v_a_4894_);
lean_dec_ref(v_a_4893_);
lean_dec_ref(v_ext_4891_);
lean_dec(v_inst_4890_);
return v_res_4896_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_LCtx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ConfigOptions(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_LCtx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ConfigOptions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_instInhabitedPhase_default = _init_l_Lean_Compiler_LCNF_instInhabitedPhase_default();
l_Lean_Compiler_LCNF_instInhabitedPhase = _init_l_Lean_Compiler_LCNF_instInhabitedPhase();
l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default = _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default();
lean_mark_persistent(l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default);
l_Lean_Compiler_LCNF_CompilerM_instInhabitedState = _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState();
lean_mark_persistent(l_Lean_Compiler_LCNF_CompilerM_instInhabitedState);
l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default = _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default();
lean_mark_persistent(l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default);
l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext = _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext();
lean_mark_persistent(l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext);
l_Lean_Compiler_LCNF_instMonadCompilerM = _init_l_Lean_Compiler_LCNF_instMonadCompilerM();
lean_mark_persistent(l_Lean_Compiler_LCNF_instMonadCompilerM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_LCtx(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ConfigOptions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_LCtx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ConfigOptions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_CompilerM(builtin);
}
#ifdef __cplusplus
}
#endif
