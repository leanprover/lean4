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
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(uint8_t, lean_object*, lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__4;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Compiler_LCNF_Phase_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_Compiler_LCNF_Phase_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___redArg(lean_object* v_base_23_){
_start:
{
lean_inc(v_base_23_);
return v_base_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___redArg___boxed(lean_object* v_base_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Compiler_LCNF_Phase_base_elim___redArg(v_base_24_);
lean_dec(v_base_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_base_29_){
_start:
{
lean_inc(v_base_29_);
return v_base_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_base_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_Compiler_LCNF_Phase_base_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_base_33_);
lean_dec(v_base_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(lean_object* v_mono_36_){
_start:
{
lean_inc(v_mono_36_);
return v_mono_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___redArg___boxed(lean_object* v_mono_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(v_mono_37_);
lean_dec(v_mono_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_mono_42_){
_start:
{
lean_inc(v_mono_42_);
return v_mono_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_mono_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_Compiler_LCNF_Phase_mono_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_mono_46_);
lean_dec(v_mono_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(lean_object* v_impure_49_){
_start:
{
lean_inc(v_impure_49_);
return v_impure_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___redArg___boxed(lean_object* v_impure_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(v_impure_50_);
lean_dec(v_impure_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_impure_55_){
_start:
{
lean_inc(v_impure_55_);
return v_impure_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_impure_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_Compiler_LCNF_Phase_impure_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_impure_59_);
lean_dec(v_impure_59_);
return v_res_61_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_instInhabitedPhase_default(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_instInhabitedPhase(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Phase_ofNat(lean_object* v_n_64_){
_start:
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = lean_nat_dec_le(v_n_64_, v___x_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(1u);
v___x_68_ = lean_nat_dec_le(v_n_64_, v___x_67_);
if (v___x_68_ == 0)
{
uint8_t v___x_69_; 
v___x_69_ = 2;
return v___x_69_;
}
else
{
uint8_t v___x_70_; 
v___x_70_ = 1;
return v___x_70_;
}
}
else
{
uint8_t v___x_71_; 
v___x_71_ = 0;
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ofNat___boxed(lean_object* v_n_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Lean_Compiler_LCNF_Phase_ofNat(v_n_72_);
lean_dec(v_n_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instDecidableEqPhase(uint8_t v_x_75_, uint8_t v_y_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_77_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_x_75_);
v___x_78_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_y_76_);
v___x_79_ = lean_nat_dec_eq(v___x_77_, v___x_78_);
lean_dec(v___x_78_);
lean_dec(v___x_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableEqPhase___boxed(lean_object* v_x_80_, lean_object* v_y_81_){
_start:
{
uint8_t v_x_13__boxed_82_; uint8_t v_y_14__boxed_83_; uint8_t v_res_84_; lean_object* v_r_85_; 
v_x_13__boxed_82_ = lean_unbox(v_x_80_);
v_y_14__boxed_83_ = lean_unbox(v_y_81_);
v_res_84_ = l_Lean_Compiler_LCNF_instDecidableEqPhase(v_x_13__boxed_82_, v_y_14__boxed_83_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t v_x_86_){
_start:
{
if (v_x_86_ == 2)
{
uint8_t v___x_87_; 
v___x_87_ = 1;
return v___x_87_;
}
else
{
uint8_t v___x_88_; 
v___x_88_ = 0;
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toPurity___boxed(lean_object* v_x_89_){
_start:
{
uint8_t v_x_23__boxed_90_; uint8_t v_res_91_; lean_object* v_r_92_; 
v_x_23__boxed_90_ = lean_unbox(v_x_89_);
v_res_91_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_x_23__boxed_90_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v_cellCount_93_; lean_object* v___x_94_; 
v_cellCount_93_ = lean_unsigned_to_nat(16u);
v___x_94_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_93_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v_cellCount_95_; lean_object* v___x_96_; 
v_cellCount_95_ = lean_unsigned_to_nat(16u);
v___x_96_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_95_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_97_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1);
v___x_98_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0);
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v___x_98_);
lean_ctor_set(v___x_100_, 2, v___x_97_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2);
v___x_102_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
lean_ctor_set(v___x_102_, 2, v___x_101_);
lean_ctor_set(v___x_102_, 3, v___x_101_);
lean_ctor_set(v___x_102_, 4, v___x_101_);
lean_ctor_set(v___x_102_, 5, v___x_101_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__4(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3);
v___x_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v___x_103_);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default(void){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__4, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__4_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__4);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState(void){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default;
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0(void){
_start:
{
lean_object* v___x_108_; uint8_t v___x_109_; lean_object* v___x_110_; 
v___x_108_ = l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default;
v___x_109_ = 0;
v___x_110_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_110_, 0, v___x_108_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*1, v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default(void){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext(void){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default;
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(lean_object* v_00_u03b1_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v___y_114_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object* v_00_u03b1_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(v_00_u03b1_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object* v_00_u03b1_129_, lean_object* v_00_u03b2_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; 
lean_inc(v___y_136_);
lean_inc_ref(v___y_135_);
lean_inc(v___y_134_);
lean_inc_ref(v___y_133_);
v___x_138_ = lean_apply_5(v___y_131_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, lean_box(0));
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_140_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_139_);
lean_dec_ref_known(v___x_138_, 1);
lean_inc(v___y_136_);
lean_inc_ref(v___y_135_);
lean_inc(v___y_134_);
lean_inc_ref(v___y_133_);
v___x_140_ = lean_apply_6(v___y_132_, v_a_139_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, lean_box(0));
return v___x_140_;
}
else
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
lean_dec_ref(v___y_132_);
v_a_141_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_138_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_138_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object* v_00_u03b1_149_, lean_object* v_00_u03b2_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(v_00_u03b1_149_, v_00_u03b2_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_158_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0(void){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_instMonadEIO(lean_box(0));
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0);
v___x_161_ = l_StateRefT_x27_instMonad___redArg(v___x_160_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM(void){
_start:
{
lean_object* v___x_166_; lean_object* v_toApplicative_167_; lean_object* v_toFunctor_168_; lean_object* v_toSeq_169_; lean_object* v_toSeqLeft_170_; lean_object* v_toSeqRight_171_; lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___f_174_; lean_object* v___f_175_; lean_object* v___x_176_; lean_object* v___f_177_; lean_object* v___f_178_; lean_object* v___f_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v_toApplicative_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_210_; 
v___x_166_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_167_ = lean_ctor_get(v___x_166_, 0);
v_toFunctor_168_ = lean_ctor_get(v_toApplicative_167_, 0);
v_toSeq_169_ = lean_ctor_get(v_toApplicative_167_, 2);
v_toSeqLeft_170_ = lean_ctor_get(v_toApplicative_167_, 3);
v_toSeqRight_171_ = lean_ctor_get(v_toApplicative_167_, 4);
v___f_172_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_173_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_168_, 2);
v___f_174_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_174_, 0, v_toFunctor_168_);
v___f_175_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_175_, 0, v_toFunctor_168_);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___f_174_);
lean_ctor_set(v___x_176_, 1, v___f_175_);
lean_inc(v_toSeqRight_171_);
v___f_177_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_177_, 0, v_toSeqRight_171_);
lean_inc(v_toSeqLeft_170_);
v___f_178_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_178_, 0, v_toSeqLeft_170_);
lean_inc(v_toSeq_169_);
v___f_179_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_179_, 0, v_toSeq_169_);
v___x_180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_180_, 0, v___x_176_);
lean_ctor_set(v___x_180_, 1, v___f_172_);
lean_ctor_set(v___x_180_, 2, v___f_179_);
lean_ctor_set(v___x_180_, 3, v___f_178_);
lean_ctor_set(v___x_180_, 4, v___f_177_);
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___f_173_);
v___x_182_ = l_StateRefT_x27_instMonad___redArg(v___x_181_);
v_toApplicative_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_210_ == 0)
{
lean_object* v_unused_211_; 
v_unused_211_ = lean_ctor_get(v___x_182_, 1);
lean_dec(v_unused_211_);
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_210_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_toApplicative_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_210_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v_toFunctor_187_; lean_object* v_toSeq_188_; lean_object* v_toSeqLeft_189_; lean_object* v_toSeqRight_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_208_; 
v_toFunctor_187_ = lean_ctor_get(v_toApplicative_183_, 0);
v_toSeq_188_ = lean_ctor_get(v_toApplicative_183_, 2);
v_toSeqLeft_189_ = lean_ctor_get(v_toApplicative_183_, 3);
v_toSeqRight_190_ = lean_ctor_get(v_toApplicative_183_, 4);
v_isSharedCheck_208_ = !lean_is_exclusive(v_toApplicative_183_);
if (v_isSharedCheck_208_ == 0)
{
lean_object* v_unused_209_; 
v_unused_209_ = lean_ctor_get(v_toApplicative_183_, 1);
lean_dec(v_unused_209_);
v___x_192_ = v_toApplicative_183_;
v_isShared_193_ = v_isSharedCheck_208_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_toSeqRight_190_);
lean_inc(v_toSeqLeft_189_);
lean_inc(v_toSeq_188_);
lean_inc(v_toFunctor_187_);
lean_dec(v_toApplicative_183_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_208_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___x_198_; lean_object* v___f_199_; lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___x_203_; 
v___f_194_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_195_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_187_);
v___f_196_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_196_, 0, v_toFunctor_187_);
v___f_197_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_197_, 0, v_toFunctor_187_);
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v___f_196_);
lean_ctor_set(v___x_198_, 1, v___f_197_);
v___f_199_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_199_, 0, v_toSeqRight_190_);
v___f_200_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_200_, 0, v_toSeqLeft_189_);
v___f_201_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_201_, 0, v_toSeq_188_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 4, v___f_199_);
lean_ctor_set(v___x_192_, 3, v___f_200_);
lean_ctor_set(v___x_192_, 2, v___f_201_);
lean_ctor_set(v___x_192_, 1, v___f_194_);
lean_ctor_set(v___x_192_, 0, v___x_198_);
v___x_203_ = v___x_192_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v___f_194_);
lean_ctor_set(v_reuseFailAlloc_207_, 2, v___f_201_);
lean_ctor_set(v_reuseFailAlloc_207_, 3, v___f_200_);
lean_ctor_set(v_reuseFailAlloc_207_, 4, v___f_199_);
v___x_203_ = v_reuseFailAlloc_207_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_205_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 1, v___f_195_);
lean_ctor_set(v___x_185_, 0, v___x_203_);
v___x_205_ = v___x_185_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v___f_195_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg(uint8_t v_phase_212_, lean_object* v_x_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_config_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_config_219_ = lean_ctor_get(v_a_214_, 0);
lean_inc_ref(v_config_219_);
v___x_220_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_220_, 0, v_config_219_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*1, v_phase_212_);
lean_inc(v_a_217_);
lean_inc_ref(v_a_216_);
lean_inc(v_a_215_);
v___x_221_ = lean_apply_5(v_x_213_, v___x_220_, v_a_215_, v_a_216_, v_a_217_, lean_box(0));
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg___boxed(lean_object* v_phase_222_, lean_object* v_x_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
uint8_t v_phase_boxed_229_; lean_object* v_res_230_; 
v_phase_boxed_229_ = lean_unbox(v_phase_222_);
v_res_230_ = l_Lean_Compiler_LCNF_withPhase___redArg(v_phase_boxed_229_, v_x_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase(lean_object* v_00_u03b1_231_, uint8_t v_phase_232_, lean_object* v_x_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_config_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_config_239_ = lean_ctor_get(v_a_234_, 0);
lean_inc_ref(v_config_239_);
v___x_240_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_240_, 0, v_config_239_);
lean_ctor_set_uint8(v___x_240_, sizeof(void*)*1, v_phase_232_);
lean_inc(v_a_237_);
lean_inc_ref(v_a_236_);
lean_inc(v_a_235_);
v___x_241_ = lean_apply_5(v_x_233_, v___x_240_, v_a_235_, v_a_236_, v_a_237_, lean_box(0));
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___boxed(lean_object* v_00_u03b1_242_, lean_object* v_phase_243_, lean_object* v_x_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
uint8_t v_phase_boxed_250_; lean_object* v_res_251_; 
v_phase_boxed_250_ = lean_unbox(v_phase_243_);
v_res_251_ = l_Lean_Compiler_LCNF_withPhase(v_00_u03b1_242_, v_phase_boxed_250_, v_x_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object* v_a_252_){
_start:
{
uint8_t v_phase_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_phase_254_ = lean_ctor_get_uint8(v_a_252_, sizeof(void*)*1);
v___x_255_ = lean_box(v_phase_254_);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg___boxed(lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_257_);
lean_dec_ref(v_a_257_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase(lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_260_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___boxed(lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Compiler_LCNF_getPhase(v_a_266_, v_a_267_, v_a_268_, v_a_269_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object* v_a_272_){
_start:
{
lean_object* v___x_274_; lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_285_; 
v___x_274_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_272_);
v_a_275_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_285_ == 0)
{
v___x_277_ = v___x_274_;
v_isShared_278_ = v_isSharedCheck_285_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_274_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_285_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
uint8_t v___x_279_; uint8_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_279_ = lean_unbox(v_a_275_);
lean_dec(v_a_275_);
v___x_280_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_279_);
v___x_281_ = lean_box(v___x_280_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_281_);
v___x_283_ = v___x_277_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg___boxed(lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_286_);
lean_dec_ref(v_a_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity(lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_289_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___boxed(lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Compiler_LCNF_getPurity(v_a_295_, v_a_296_, v_a_297_, v_a_298_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg(lean_object* v_a_301_){
_start:
{
lean_object* v___x_303_; lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_319_; 
v___x_303_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_301_);
v_a_304_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_319_ == 0)
{
v___x_306_ = v___x_303_;
v_isShared_307_ = v_isSharedCheck_319_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_303_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_319_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
uint8_t v___x_308_; 
v___x_308_ = lean_unbox(v_a_304_);
lean_dec(v_a_304_);
if (v___x_308_ == 0)
{
uint8_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_309_ = 1;
v___x_310_ = lean_box(v___x_309_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_310_);
v___x_312_ = v___x_306_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
else
{
uint8_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_314_ = 0;
v___x_315_ = lean_box(v___x_314_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_315_);
v___x_317_ = v___x_306_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg___boxed(lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_320_);
lean_dec_ref(v_a_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase(lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_323_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___boxed(lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Compiler_LCNF_inBasePhase(v_a_329_, v_a_330_, v_a_331_, v_a_332_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
return v_res_334_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0(void){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_335_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
lean_ctor_set(v___x_340_, 2, v___x_339_);
lean_ctor_set(v___x_340_, 3, v___x_339_);
lean_ctor_set(v___x_340_, 4, v___x_338_);
lean_ctor_set(v___x_340_, 5, v___x_338_);
lean_ctor_set(v___x_340_, 6, v___x_338_);
lean_ctor_set(v___x_340_, 7, v___x_338_);
lean_ctor_set(v___x_340_, 8, v___x_338_);
lean_ctor_set(v___x_340_, 9, v___x_338_);
lean_ctor_set(v___x_340_, 10, v___x_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(lean_object* v_msgData_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_347_ = lean_st_ref_get(v___y_345_);
v___x_348_ = lean_st_ref_get(v___y_343_);
v___x_349_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_342_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_372_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_372_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_372_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_372_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v_env_354_; lean_object* v_lctx_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_370_; 
v_env_354_ = lean_ctor_get(v___x_347_, 0);
lean_inc_ref(v_env_354_);
lean_dec(v___x_347_);
v_lctx_355_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v___x_348_, 1);
lean_dec(v_unused_371_);
v___x_357_ = v___x_348_;
v_isShared_358_ = v_isSharedCheck_370_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_lctx_355_);
lean_dec(v___x_348_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_370_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v_options_359_; uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v_options_359_ = lean_ctor_get(v___y_344_, 2);
v___x_360_ = lean_unbox(v_a_350_);
lean_dec(v_a_350_);
v___x_361_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_355_, v___x_360_);
lean_dec_ref(v_lctx_355_);
v___x_362_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_359_);
v___x_363_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_363_, 0, v_env_354_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
lean_ctor_set(v___x_363_, 2, v___x_361_);
lean_ctor_set(v___x_363_, 3, v_options_359_);
if (v_isShared_358_ == 0)
{
lean_ctor_set_tag(v___x_357_, 3);
lean_ctor_set(v___x_357_, 1, v_msgData_341_);
lean_ctor_set(v___x_357_, 0, v___x_363_);
v___x_365_ = v___x_357_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_msgData_341_);
v___x_365_ = v_reuseFailAlloc_369_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_367_; 
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_365_);
v___x_367_ = v___x_352_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec(v___x_348_);
lean_dec(v___x_347_);
lean_dec_ref(v_msgData_341_);
v_a_373_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_349_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_349_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed(lean_object* v_msgData_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(v_msgData_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(lean_object* v_msg_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_options_396_; lean_object* v_ref_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_options_396_ = lean_ctor_get(v___y_393_, 2);
v_ref_397_ = lean_ctor_get(v___y_393_, 5);
v___x_398_ = lean_st_ref_get(v___y_394_);
v___x_399_ = lean_st_ref_get(v___y_392_);
v___x_400_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_391_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_423_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_423_ == 0)
{
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_423_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_423_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_env_405_; lean_object* v_lctx_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_421_; 
v_env_405_ = lean_ctor_get(v___x_398_, 0);
lean_inc_ref(v_env_405_);
lean_dec(v___x_398_);
v_lctx_406_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v___x_399_, 1);
lean_dec(v_unused_422_);
v___x_408_ = v___x_399_;
v_isShared_409_ = v_isSharedCheck_421_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_lctx_406_);
lean_dec(v___x_399_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_421_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
uint8_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_410_ = lean_unbox(v_a_401_);
lean_dec(v_a_401_);
v___x_411_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_406_, v___x_410_);
lean_dec_ref(v_lctx_406_);
v___x_412_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_396_);
v___x_413_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_413_, 0, v_env_405_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
lean_ctor_set(v___x_413_, 2, v___x_411_);
lean_ctor_set(v___x_413_, 3, v_options_396_);
if (v_isShared_409_ == 0)
{
lean_ctor_set_tag(v___x_408_, 3);
lean_ctor_set(v___x_408_, 1, v_msg_390_);
lean_ctor_set(v___x_408_, 0, v___x_413_);
v___x_415_ = v___x_408_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_msg_390_);
v___x_415_ = v_reuseFailAlloc_420_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_416_; lean_object* v___x_418_; 
lean_inc(v_ref_397_);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v_ref_397_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 1);
lean_ctor_set(v___x_403_, 0, v___x_416_);
v___x_418_ = v___x_403_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec(v___x_399_);
lean_dec(v___x_398_);
lean_dec_ref(v_msg_390_);
v_a_424_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_400_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_400_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg___boxed(lean_object* v_msg_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(lean_object* v_00_u03b1_439_, lean_object* v_msg_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___boxed(lean_object* v_00_u03b1_447_, lean_object* v_msg_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(v_00_u03b1_447_, v_msg_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_m_455_, lean_object* v_query_456_, lean_object* v_x_457_, lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
lean_object* v_zero_460_; uint8_t v_isZero_461_; 
v_zero_460_ = lean_unsigned_to_nat(0u);
v_isZero_461_ = lean_nat_dec_eq(v_x_458_, v_zero_460_);
if (v_isZero_461_ == 1)
{
lean_dec(v_x_459_);
lean_dec(v_x_458_);
if (lean_obj_tag(v_x_457_) == 0)
{
lean_object* v___x_462_; 
v___x_462_ = lean_box(2);
return v___x_462_;
}
else
{
lean_object* v_val_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
v_val_463_ = lean_ctor_get(v_x_457_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v_x_457_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v_x_457_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_val_463_);
lean_dec(v_x_457_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_val_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
else
{
lean_object* v_keyArray_471_; lean_object* v_valueArray_472_; lean_object* v___x_473_; uint8_t v_isSome_474_; 
v_keyArray_471_ = lean_ctor_get(v_m_455_, 1);
v_valueArray_472_ = lean_ctor_get(v_m_455_, 2);
v___x_473_ = lean_array_fget_borrowed(v_keyArray_471_, v_x_459_);
v_isSome_474_ = lean_noption_is_some(v___x_473_);
if (v_isSome_474_ == 0)
{
lean_dec(v_x_458_);
if (lean_obj_tag(v_x_457_) == 0)
{
lean_object* v___x_475_; 
v___x_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_475_, 0, v_x_459_);
return v___x_475_;
}
else
{
lean_object* v_val_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec(v_x_459_);
v_val_476_ = lean_ctor_get(v_x_457_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v_x_457_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v_x_457_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_val_476_);
lean_dec(v_x_457_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_val_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
else
{
lean_object* v_one_484_; lean_object* v_n_485_; lean_object* v___y_487_; 
v_one_484_ = lean_unsigned_to_nat(1u);
v_n_485_ = lean_nat_sub(v_x_458_, v_one_484_);
lean_dec(v_x_458_);
if (v_isSome_474_ == 0)
{
goto v___jp_493_;
}
else
{
lean_object* v___x_495_; uint8_t v_isSome_496_; 
v___x_495_ = lean_array_fget_borrowed(v_valueArray_472_, v_x_459_);
v_isSome_496_ = lean_noption_is_some(v___x_495_);
if (v_isSome_496_ == 0)
{
goto v___jp_493_;
}
else
{
lean_object* v_val_497_; uint8_t v___x_498_; 
lean_inc(v___x_473_);
v_val_497_ = lean_noption_get(v___x_473_);
v___x_498_ = l_Lean_instBEqFVarId_beq(v_val_497_, v_query_456_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
lean_dec(v_val_497_);
v___x_499_ = lean_array_get_size(v_keyArray_471_);
v___x_500_ = lean_nat_add(v_x_459_, v_one_484_);
lean_dec(v_x_459_);
v___x_501_ = lean_nat_dec_lt(v___x_500_, v___x_499_);
if (v___x_501_ == 0)
{
lean_dec(v___x_500_);
v_x_458_ = v_n_485_;
v_x_459_ = v_zero_460_;
goto _start;
}
else
{
v_x_458_ = v_n_485_;
v_x_459_ = v___x_500_;
goto _start;
}
}
else
{
lean_object* v_val_504_; lean_object* v___x_505_; 
lean_dec(v_n_485_);
lean_dec(v_x_457_);
lean_inc(v___x_495_);
v_val_504_ = lean_noption_get(v___x_495_);
v___x_505_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_505_, 0, v_x_459_);
lean_ctor_set(v___x_505_, 1, v_val_497_);
lean_ctor_set(v___x_505_, 2, v_val_504_);
return v___x_505_;
}
}
}
v___jp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_488_ = lean_array_get_size(v_keyArray_471_);
v___x_489_ = lean_nat_add(v_x_459_, v_one_484_);
lean_dec(v_x_459_);
v___x_490_ = lean_nat_dec_lt(v___x_489_, v___x_488_);
if (v___x_490_ == 0)
{
lean_dec(v___x_489_);
v_x_457_ = v___y_487_;
v_x_458_ = v_n_485_;
v_x_459_ = v_zero_460_;
goto _start;
}
else
{
v_x_457_ = v___y_487_;
v_x_458_ = v_n_485_;
v_x_459_ = v___x_489_;
goto _start;
}
}
v___jp_493_:
{
if (lean_obj_tag(v_x_457_) == 0)
{
lean_object* v___x_494_; 
lean_inc(v_x_459_);
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v_x_459_);
v___y_487_ = v___x_494_;
goto v___jp_486_;
}
else
{
v___y_487_ = v_x_457_;
goto v___jp_486_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_m_506_, lean_object* v_query_507_, lean_object* v_x_508_, lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2_spec__3___redArg(v_m_506_, v_query_507_, v_x_508_, v_x_509_, v_x_510_);
lean_dec(v_query_507_);
lean_dec_ref(v_m_506_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2___redArg(lean_object* v_m_512_, lean_object* v_query_513_){
_start:
{
lean_object* v_keyArray_514_; lean_object* v___x_515_; uint64_t v___x_516_; uint64_t v___x_517_; uint64_t v___x_518_; uint64_t v_fold_519_; uint64_t v___x_520_; uint64_t v___x_521_; uint64_t v___x_522_; size_t v___x_523_; size_t v___x_524_; size_t v___x_525_; size_t v___x_526_; size_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_keyArray_514_ = lean_ctor_get(v_m_512_, 1);
v___x_515_ = lean_array_get_size(v_keyArray_514_);
v___x_516_ = l_Lean_instHashableFVarId_hash(v_query_513_);
v___x_517_ = 32ULL;
v___x_518_ = lean_uint64_shift_right(v___x_516_, v___x_517_);
v_fold_519_ = lean_uint64_xor(v___x_516_, v___x_518_);
v___x_520_ = 16ULL;
v___x_521_ = lean_uint64_shift_right(v_fold_519_, v___x_520_);
v___x_522_ = lean_uint64_xor(v_fold_519_, v___x_521_);
v___x_523_ = lean_uint64_to_usize(v___x_522_);
v___x_524_ = lean_usize_of_nat(v___x_515_);
v___x_525_ = ((size_t)1ULL);
v___x_526_ = lean_usize_sub(v___x_524_, v___x_525_);
v___x_527_ = lean_usize_land(v___x_523_, v___x_526_);
v___x_528_ = lean_usize_to_nat(v___x_527_);
v___x_529_ = lean_box(0);
v___x_530_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2_spec__3___redArg(v_m_512_, v_query_513_, v___x_529_, v___x_515_, v___x_528_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_531_, lean_object* v_query_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2___redArg(v_m_531_, v_query_532_);
lean_dec(v_query_532_);
lean_dec_ref(v_m_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(lean_object* v_m_534_, lean_object* v_query_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2___redArg(v_m_534_, v_query_535_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_index_537_; lean_object* v_key_538_; lean_object* v_value_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
v_index_537_ = lean_ctor_get(v___x_536_, 0);
v_key_538_ = lean_ctor_get(v___x_536_, 1);
v_value_539_ = lean_ctor_get(v___x_536_, 2);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_536_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_value_539_);
lean_inc(v_key_538_);
lean_inc(v_index_537_);
lean_dec(v___x_536_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_index_537_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_key_538_);
lean_ctor_set(v_reuseFailAlloc_545_, 2, v_value_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
else
{
lean_object* v___x_547_; 
lean_dec(v___x_536_);
v___x_547_ = lean_box(1);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg___boxed(lean_object* v_m_548_, lean_object* v_query_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_m_548_, v_query_549_);
lean_dec(v_query_549_);
lean_dec_ref(v_m_548_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object* v_m_551_, lean_object* v_a_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_m_551_, v_a_552_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_value_554_; lean_object* v___x_555_; 
v_value_554_ = lean_ctor_get(v___x_553_, 2);
lean_inc(v_value_554_);
lean_dec_ref_known(v___x_553_, 3);
v___x_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_555_, 0, v_value_554_);
return v___x_555_;
}
else
{
lean_object* v___x_556_; 
v___x_556_ = lean_box(0);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg___boxed(lean_object* v_m_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_557_, v_a_558_);
lean_dec(v_a_558_);
lean_dec_ref(v_m_557_);
return v_res_559_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getType___closed__1(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = ((lean_object*)(l_Lean_Compiler_LCNF_getType___closed__0));
v___x_562_ = l_Lean_stringToMessageData(v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType(lean_object* v_fvarId_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_st_ref_get(v_a_565_);
v___x_570_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_564_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_621_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_621_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_621_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_621_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___y_576_; lean_object* v_lctx_587_; lean_object* v___y_589_; lean_object* v___y_604_; uint8_t v___x_618_; 
v_lctx_587_ = lean_ctor_get(v___x_569_, 0);
lean_inc_ref(v_lctx_587_);
lean_dec(v___x_569_);
v___x_618_ = lean_unbox(v_a_571_);
if (v___x_618_ == 0)
{
lean_object* v_letDeclsPure_619_; 
v_letDeclsPure_619_ = lean_ctor_get(v_lctx_587_, 2);
lean_inc_ref(v_letDeclsPure_619_);
v___y_604_ = v_letDeclsPure_619_;
goto v___jp_603_;
}
else
{
lean_object* v_letDeclsImpure_620_; 
v_letDeclsImpure_620_ = lean_ctor_get(v_lctx_587_, 3);
lean_inc_ref(v_letDeclsImpure_620_);
v___y_604_ = v_letDeclsImpure_620_;
goto v___jp_603_;
}
v___jp_575_:
{
lean_object* v___x_577_; 
v___x_577_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_576_, v_fvarId_563_);
lean_dec_ref(v___y_576_);
if (lean_obj_tag(v___x_577_) == 1)
{
lean_object* v_val_578_; lean_object* v_type_579_; lean_object* v___x_581_; 
lean_dec(v_fvarId_563_);
v_val_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_val_578_);
lean_dec_ref_known(v___x_577_, 1);
v_type_579_ = lean_ctor_get(v_val_578_, 3);
lean_inc_ref(v_type_579_);
lean_dec(v_val_578_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v_type_579_);
v___x_581_ = v___x_573_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_type_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
lean_dec(v___x_577_);
lean_del_object(v___x_573_);
v___x_583_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_584_ = l_Lean_MessageData_ofName(v_fvarId_563_);
v___x_585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_583_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_585_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
return v___x_586_;
}
}
v___jp_588_:
{
lean_object* v___x_590_; 
v___x_590_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_589_, v_fvarId_563_);
lean_dec_ref(v___y_589_);
if (lean_obj_tag(v___x_590_) == 1)
{
lean_object* v_val_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_599_; 
lean_dec_ref(v_lctx_587_);
lean_del_object(v___x_573_);
lean_dec(v_a_571_);
lean_dec(v_fvarId_563_);
v_val_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_599_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_val_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v_type_595_; lean_object* v___x_597_; 
v_type_595_ = lean_ctor_get(v_val_591_, 2);
lean_inc_ref(v_type_595_);
lean_dec(v_val_591_);
if (v_isShared_594_ == 0)
{
lean_ctor_set_tag(v___x_593_, 0);
lean_ctor_set(v___x_593_, 0, v_type_595_);
v___x_597_ = v___x_593_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_type_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
else
{
uint8_t v___x_600_; 
lean_dec(v___x_590_);
v___x_600_ = lean_unbox(v_a_571_);
lean_dec(v_a_571_);
if (v___x_600_ == 0)
{
lean_object* v_funDeclsPure_601_; 
v_funDeclsPure_601_ = lean_ctor_get(v_lctx_587_, 4);
lean_inc_ref(v_funDeclsPure_601_);
lean_dec_ref(v_lctx_587_);
v___y_576_ = v_funDeclsPure_601_;
goto v___jp_575_;
}
else
{
lean_object* v_funDeclsImpure_602_; 
v_funDeclsImpure_602_ = lean_ctor_get(v_lctx_587_, 5);
lean_inc_ref(v_funDeclsImpure_602_);
lean_dec_ref(v_lctx_587_);
v___y_576_ = v_funDeclsImpure_602_;
goto v___jp_575_;
}
}
}
v___jp_603_:
{
lean_object* v___x_605_; 
v___x_605_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_604_, v_fvarId_563_);
lean_dec_ref(v___y_604_);
if (lean_obj_tag(v___x_605_) == 1)
{
lean_object* v_val_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v_lctx_587_);
lean_del_object(v___x_573_);
lean_dec(v_a_571_);
lean_dec(v_fvarId_563_);
v_val_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_614_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_614_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_val_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_614_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v_type_610_; lean_object* v___x_612_; 
v_type_610_ = lean_ctor_get(v_val_606_, 2);
lean_inc_ref(v_type_610_);
lean_dec(v_val_606_);
if (v_isShared_609_ == 0)
{
lean_ctor_set_tag(v___x_608_, 0);
lean_ctor_set(v___x_608_, 0, v_type_610_);
v___x_612_ = v___x_608_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_type_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
else
{
uint8_t v___x_615_; 
lean_dec(v___x_605_);
v___x_615_ = lean_unbox(v_a_571_);
if (v___x_615_ == 0)
{
lean_object* v_paramsPure_616_; 
v_paramsPure_616_ = lean_ctor_get(v_lctx_587_, 0);
lean_inc_ref(v_paramsPure_616_);
v___y_589_ = v_paramsPure_616_;
goto v___jp_588_;
}
else
{
lean_object* v_paramsImpure_617_; 
v_paramsImpure_617_ = lean_ctor_get(v_lctx_587_, 1);
lean_inc_ref(v_paramsImpure_617_);
v___y_589_ = v_paramsImpure_617_;
goto v___jp_588_;
}
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec(v___x_569_);
lean_dec(v_fvarId_563_);
v_a_622_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_570_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_570_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType___boxed(lean_object* v_fvarId_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_Compiler_LCNF_getType(v_fvarId_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(lean_object* v_00_u03b2_637_, lean_object* v_m_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_638_, v_a_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___boxed(lean_object* v_00_u03b2_641_, lean_object* v_m_642_, lean_object* v_a_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(v_00_u03b2_641_, v_m_642_, v_a_643_);
lean_dec(v_a_643_);
lean_dec_ref(v_m_642_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(lean_object* v_00_u03b2_645_, lean_object* v_m_646_, lean_object* v_query_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_m_646_, v_query_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_649_, lean_object* v_m_650_, lean_object* v_query_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(v_00_u03b2_649_, v_m_650_, v_query_651_);
lean_dec(v_query_651_);
lean_dec_ref(v_m_650_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_653_, lean_object* v_m_654_, lean_object* v_query_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2___redArg(v_m_654_, v_query_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_657_, lean_object* v_m_658_, lean_object* v_query_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2(v_00_u03b2_657_, v_m_658_, v_query_659_);
lean_dec(v_query_659_);
lean_dec_ref(v_m_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_661_, lean_object* v_m_662_, lean_object* v_query_663_, lean_object* v_x_664_, lean_object* v_x_665_, lean_object* v_x_666_, lean_object* v_x_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2_spec__3___redArg(v_m_662_, v_query_663_, v_x_664_, v_x_665_, v_x_666_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_669_, lean_object* v_m_670_, lean_object* v_query_671_, lean_object* v_x_672_, lean_object* v_x_673_, lean_object* v_x_674_, lean_object* v_x_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0_spec__2_spec__3(v_00_u03b2_669_, v_m_670_, v_query_671_, v_x_672_, v_x_673_, v_x_674_, v_x_675_);
lean_dec(v_query_671_);
lean_dec_ref(v_m_670_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object* v_fvarId_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_st_ref_get(v_a_679_);
v___x_684_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_678_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_735_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_735_ == 0)
{
v___x_687_ = v___x_684_;
v_isShared_688_ = v_isSharedCheck_735_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_735_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___y_690_; lean_object* v_lctx_701_; lean_object* v___y_703_; lean_object* v___y_718_; uint8_t v___x_732_; 
v_lctx_701_ = lean_ctor_get(v___x_683_, 0);
lean_inc_ref(v_lctx_701_);
lean_dec(v___x_683_);
v___x_732_ = lean_unbox(v_a_685_);
if (v___x_732_ == 0)
{
lean_object* v_letDeclsPure_733_; 
v_letDeclsPure_733_ = lean_ctor_get(v_lctx_701_, 2);
lean_inc_ref(v_letDeclsPure_733_);
v___y_718_ = v_letDeclsPure_733_;
goto v___jp_717_;
}
else
{
lean_object* v_letDeclsImpure_734_; 
v_letDeclsImpure_734_ = lean_ctor_get(v_lctx_701_, 3);
lean_inc_ref(v_letDeclsImpure_734_);
v___y_718_ = v_letDeclsImpure_734_;
goto v___jp_717_;
}
v___jp_689_:
{
lean_object* v___x_691_; 
v___x_691_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_690_, v_fvarId_677_);
lean_dec_ref(v___y_690_);
if (lean_obj_tag(v___x_691_) == 1)
{
lean_object* v_val_692_; lean_object* v_binderName_693_; lean_object* v___x_695_; 
lean_dec(v_fvarId_677_);
v_val_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_val_692_);
lean_dec_ref_known(v___x_691_, 1);
v_binderName_693_ = lean_ctor_get(v_val_692_, 1);
lean_inc(v_binderName_693_);
lean_dec(v_val_692_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v_binderName_693_);
v___x_695_ = v___x_687_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_binderName_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
lean_dec(v___x_691_);
lean_del_object(v___x_687_);
v___x_697_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_698_ = l_Lean_MessageData_ofName(v_fvarId_677_);
v___x_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_699_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
return v___x_700_;
}
}
v___jp_702_:
{
lean_object* v___x_704_; 
v___x_704_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_703_, v_fvarId_677_);
lean_dec_ref(v___y_703_);
if (lean_obj_tag(v___x_704_) == 1)
{
lean_object* v_val_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_713_; 
lean_dec_ref(v_lctx_701_);
lean_del_object(v___x_687_);
lean_dec(v_a_685_);
lean_dec(v_fvarId_677_);
v_val_705_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_713_ == 0)
{
v___x_707_ = v___x_704_;
v_isShared_708_ = v_isSharedCheck_713_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_val_705_);
lean_dec(v___x_704_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_713_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v_binderName_709_; lean_object* v___x_711_; 
v_binderName_709_ = lean_ctor_get(v_val_705_, 1);
lean_inc(v_binderName_709_);
lean_dec(v_val_705_);
if (v_isShared_708_ == 0)
{
lean_ctor_set_tag(v___x_707_, 0);
lean_ctor_set(v___x_707_, 0, v_binderName_709_);
v___x_711_ = v___x_707_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_binderName_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
else
{
uint8_t v___x_714_; 
lean_dec(v___x_704_);
v___x_714_ = lean_unbox(v_a_685_);
lean_dec(v_a_685_);
if (v___x_714_ == 0)
{
lean_object* v_funDeclsPure_715_; 
v_funDeclsPure_715_ = lean_ctor_get(v_lctx_701_, 4);
lean_inc_ref(v_funDeclsPure_715_);
lean_dec_ref(v_lctx_701_);
v___y_690_ = v_funDeclsPure_715_;
goto v___jp_689_;
}
else
{
lean_object* v_funDeclsImpure_716_; 
v_funDeclsImpure_716_ = lean_ctor_get(v_lctx_701_, 5);
lean_inc_ref(v_funDeclsImpure_716_);
lean_dec_ref(v_lctx_701_);
v___y_690_ = v_funDeclsImpure_716_;
goto v___jp_689_;
}
}
}
v___jp_717_:
{
lean_object* v___x_719_; 
v___x_719_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_718_, v_fvarId_677_);
lean_dec_ref(v___y_718_);
if (lean_obj_tag(v___x_719_) == 1)
{
lean_object* v_val_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_728_; 
lean_dec_ref(v_lctx_701_);
lean_del_object(v___x_687_);
lean_dec(v_a_685_);
lean_dec(v_fvarId_677_);
v_val_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_728_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_val_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v_binderName_724_; lean_object* v___x_726_; 
v_binderName_724_ = lean_ctor_get(v_val_720_, 1);
lean_inc(v_binderName_724_);
lean_dec(v_val_720_);
if (v_isShared_723_ == 0)
{
lean_ctor_set_tag(v___x_722_, 0);
lean_ctor_set(v___x_722_, 0, v_binderName_724_);
v___x_726_ = v___x_722_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_binderName_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
else
{
uint8_t v___x_729_; 
lean_dec(v___x_719_);
v___x_729_ = lean_unbox(v_a_685_);
if (v___x_729_ == 0)
{
lean_object* v_paramsPure_730_; 
v_paramsPure_730_ = lean_ctor_get(v_lctx_701_, 0);
lean_inc_ref(v_paramsPure_730_);
v___y_703_ = v_paramsPure_730_;
goto v___jp_702_;
}
else
{
lean_object* v_paramsImpure_731_; 
v_paramsImpure_731_ = lean_ctor_get(v_lctx_701_, 1);
lean_inc_ref(v_paramsImpure_731_);
v___y_703_ = v_paramsImpure_731_;
goto v___jp_702_;
}
}
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec(v___x_683_);
lean_dec(v_fvarId_677_);
v_a_736_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_684_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_684_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName___boxed(lean_object* v_fvarId_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t v_pu_751_, lean_object* v_fvarId_752_, lean_object* v_a_753_){
_start:
{
lean_object* v___x_755_; lean_object* v___y_757_; 
v___x_755_ = lean_st_ref_get(v_a_753_);
if (v_pu_751_ == 0)
{
lean_object* v_lctx_760_; lean_object* v_paramsPure_761_; 
v_lctx_760_ = lean_ctor_get(v___x_755_, 0);
lean_inc_ref(v_lctx_760_);
lean_dec(v___x_755_);
v_paramsPure_761_ = lean_ctor_get(v_lctx_760_, 0);
lean_inc_ref(v_paramsPure_761_);
lean_dec_ref(v_lctx_760_);
v___y_757_ = v_paramsPure_761_;
goto v___jp_756_;
}
else
{
lean_object* v_lctx_762_; lean_object* v_paramsImpure_763_; 
v_lctx_762_ = lean_ctor_get(v___x_755_, 0);
lean_inc_ref(v_lctx_762_);
lean_dec(v___x_755_);
v_paramsImpure_763_ = lean_ctor_get(v_lctx_762_, 1);
lean_inc_ref(v_paramsImpure_763_);
lean_dec_ref(v_lctx_762_);
v___y_757_ = v_paramsImpure_763_;
goto v___jp_756_;
}
v___jp_756_:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_757_, v_fvarId_752_);
lean_dec_ref(v___y_757_);
v___x_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
return v___x_759_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg___boxed(lean_object* v_pu_764_, lean_object* v_fvarId_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
uint8_t v_pu_boxed_768_; lean_object* v_res_769_; 
v_pu_boxed_768_ = lean_unbox(v_pu_764_);
v_res_769_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_boxed_768_, v_fvarId_765_, v_a_766_);
lean_dec(v_a_766_);
lean_dec(v_fvarId_765_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f(uint8_t v_pu_770_, lean_object* v_fvarId_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_770_, v_fvarId_771_, v_a_773_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___boxed(lean_object* v_pu_778_, lean_object* v_fvarId_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
uint8_t v_pu_boxed_785_; lean_object* v_res_786_; 
v_pu_boxed_785_ = lean_unbox(v_pu_778_);
v_res_786_ = l_Lean_Compiler_LCNF_findParam_x3f(v_pu_boxed_785_, v_fvarId_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
lean_dec(v_fvarId_779_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t v_pu_787_, lean_object* v_fvarId_788_, lean_object* v_a_789_){
_start:
{
lean_object* v___x_791_; lean_object* v___y_793_; 
v___x_791_ = lean_st_ref_get(v_a_789_);
if (v_pu_787_ == 0)
{
lean_object* v_lctx_796_; lean_object* v_letDeclsPure_797_; 
v_lctx_796_ = lean_ctor_get(v___x_791_, 0);
lean_inc_ref(v_lctx_796_);
lean_dec(v___x_791_);
v_letDeclsPure_797_ = lean_ctor_get(v_lctx_796_, 2);
lean_inc_ref(v_letDeclsPure_797_);
lean_dec_ref(v_lctx_796_);
v___y_793_ = v_letDeclsPure_797_;
goto v___jp_792_;
}
else
{
lean_object* v_lctx_798_; lean_object* v_letDeclsImpure_799_; 
v_lctx_798_ = lean_ctor_get(v___x_791_, 0);
lean_inc_ref(v_lctx_798_);
lean_dec(v___x_791_);
v_letDeclsImpure_799_ = lean_ctor_get(v_lctx_798_, 3);
lean_inc_ref(v_letDeclsImpure_799_);
lean_dec_ref(v_lctx_798_);
v___y_793_ = v_letDeclsImpure_799_;
goto v___jp_792_;
}
v___jp_792_:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_793_, v_fvarId_788_);
lean_dec_ref(v___y_793_);
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg___boxed(lean_object* v_pu_800_, lean_object* v_fvarId_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
uint8_t v_pu_boxed_804_; lean_object* v_res_805_; 
v_pu_boxed_804_ = lean_unbox(v_pu_800_);
v_res_805_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_boxed_804_, v_fvarId_801_, v_a_802_);
lean_dec(v_a_802_);
lean_dec(v_fvarId_801_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(uint8_t v_pu_806_, lean_object* v_fvarId_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_806_, v_fvarId_807_, v_a_809_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___boxed(lean_object* v_pu_814_, lean_object* v_fvarId_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
uint8_t v_pu_boxed_821_; lean_object* v_res_822_; 
v_pu_boxed_821_ = lean_unbox(v_pu_814_);
v_res_822_ = l_Lean_Compiler_LCNF_findLetDecl_x3f(v_pu_boxed_821_, v_fvarId_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_fvarId_815_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t v_pu_823_, lean_object* v_fvarId_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___x_827_; lean_object* v___y_829_; 
v___x_827_ = lean_st_ref_get(v_a_825_);
if (v_pu_823_ == 0)
{
lean_object* v_lctx_832_; lean_object* v_funDeclsPure_833_; 
v_lctx_832_ = lean_ctor_get(v___x_827_, 0);
lean_inc_ref(v_lctx_832_);
lean_dec(v___x_827_);
v_funDeclsPure_833_ = lean_ctor_get(v_lctx_832_, 4);
lean_inc_ref(v_funDeclsPure_833_);
lean_dec_ref(v_lctx_832_);
v___y_829_ = v_funDeclsPure_833_;
goto v___jp_828_;
}
else
{
lean_object* v_lctx_834_; lean_object* v_funDeclsImpure_835_; 
v_lctx_834_ = lean_ctor_get(v___x_827_, 0);
lean_inc_ref(v_lctx_834_);
lean_dec(v___x_827_);
v_funDeclsImpure_835_ = lean_ctor_get(v_lctx_834_, 5);
lean_inc_ref(v_funDeclsImpure_835_);
lean_dec_ref(v_lctx_834_);
v___y_829_ = v_funDeclsImpure_835_;
goto v___jp_828_;
}
v___jp_828_:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_829_, v_fvarId_824_);
lean_dec_ref(v___y_829_);
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg___boxed(lean_object* v_pu_836_, lean_object* v_fvarId_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
uint8_t v_pu_boxed_840_; lean_object* v_res_841_; 
v_pu_boxed_840_ = lean_unbox(v_pu_836_);
v_res_841_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_boxed_840_, v_fvarId_837_, v_a_838_);
lean_dec(v_a_838_);
lean_dec(v_fvarId_837_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(uint8_t v_pu_842_, lean_object* v_fvarId_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_842_, v_fvarId_843_, v_a_845_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___boxed(lean_object* v_pu_850_, lean_object* v_fvarId_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
uint8_t v_pu_boxed_857_; lean_object* v_res_858_; 
v_pu_boxed_857_ = lean_unbox(v_pu_850_);
v_res_858_ = l_Lean_Compiler_LCNF_findFunDecl_x3f(v_pu_boxed_857_, v_fvarId_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_fvarId_851_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t v_pu_859_, lean_object* v_fvarId_860_, lean_object* v_a_861_){
_start:
{
lean_object* v___x_863_; lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_884_; 
v___x_863_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_859_, v_fvarId_860_, v_a_861_);
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_884_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_884_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_884_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
if (lean_obj_tag(v_a_864_) == 1)
{
lean_object* v_val_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_879_; 
v_val_868_ = lean_ctor_get(v_a_864_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v_a_864_);
if (v_isSharedCheck_879_ == 0)
{
v___x_870_ = v_a_864_;
v_isShared_871_ = v_isSharedCheck_879_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_val_868_);
lean_dec(v_a_864_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_879_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v_value_872_; lean_object* v___x_874_; 
v_value_872_ = lean_ctor_get(v_val_868_, 3);
lean_inc(v_value_872_);
lean_dec(v_val_868_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v_value_872_);
v___x_874_ = v___x_870_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_value_872_);
v___x_874_ = v_reuseFailAlloc_878_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_876_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_874_);
v___x_876_ = v___x_866_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
lean_object* v___x_880_; lean_object* v___x_882_; 
lean_dec(v_a_864_);
v___x_880_ = lean_box(0);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_880_);
v___x_882_ = v___x_866_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg___boxed(lean_object* v_pu_885_, lean_object* v_fvarId_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
uint8_t v_pu_boxed_889_; lean_object* v_res_890_; 
v_pu_boxed_889_ = lean_unbox(v_pu_885_);
v_res_890_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_boxed_889_, v_fvarId_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec(v_fvarId_886_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f(uint8_t v_pu_891_, lean_object* v_fvarId_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_891_, v_fvarId_892_, v_a_894_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___boxed(lean_object* v_pu_899_, lean_object* v_fvarId_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
uint8_t v_pu_boxed_906_; lean_object* v_res_907_; 
v_pu_boxed_906_ = lean_unbox(v_pu_899_);
v_res_907_ = l_Lean_Compiler_LCNF_findLetValue_x3f(v_pu_boxed_906_, v_fvarId_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_fvarId_900_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg(lean_object* v_fvarId_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
uint8_t v___x_912_; lean_object* v___x_913_; 
v___x_912_ = 0;
v___x_913_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_912_, v_fvarId_908_, v_a_909_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_957_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_957_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_957_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_957_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
if (lean_obj_tag(v_a_914_) == 1)
{
lean_object* v_val_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_956_; 
v_val_924_ = lean_ctor_get(v_a_914_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v_a_914_);
if (v_isSharedCheck_956_ == 0)
{
v___x_926_ = v_a_914_;
v_isShared_927_ = v_isSharedCheck_956_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_val_924_);
lean_dec(v_a_914_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_956_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
if (lean_obj_tag(v_val_924_) == 3)
{
lean_object* v_declName_928_; lean_object* v___x_929_; lean_object* v_env_930_; uint8_t v___x_931_; lean_object* v___x_932_; 
lean_del_object(v___x_916_);
v_declName_928_ = lean_ctor_get(v_val_924_, 0);
lean_inc(v_declName_928_);
lean_dec_ref_known(v_val_924_, 3);
v___x_929_ = lean_st_ref_get(v_a_910_);
v_env_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc_ref(v_env_930_);
lean_dec(v___x_929_);
v___x_931_ = 0;
v___x_932_ = l_Lean_Environment_find_x3f(v_env_930_, v_declName_928_, v___x_931_);
if (lean_obj_tag(v___x_932_) == 1)
{
lean_object* v_val_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_951_; 
lean_del_object(v___x_926_);
v_val_933_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_951_ == 0)
{
v___x_935_ = v___x_932_;
v_isShared_936_ = v_isSharedCheck_951_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_val_933_);
lean_dec(v___x_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_951_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
if (lean_obj_tag(v_val_933_) == 6)
{
lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_945_; 
lean_del_object(v___x_935_);
v_isSharedCheck_945_ = !lean_is_exclusive(v_val_933_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; 
v_unused_946_ = lean_ctor_get(v_val_933_, 0);
lean_dec(v_unused_946_);
v___x_938_ = v_val_933_;
v_isShared_939_ = v_isSharedCheck_945_;
goto v_resetjp_937_;
}
else
{
lean_dec(v_val_933_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_945_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
uint8_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_940_ = 1;
v___x_941_ = lean_box(v___x_940_);
if (v_isShared_939_ == 0)
{
lean_ctor_set_tag(v___x_938_, 0);
lean_ctor_set(v___x_938_, 0, v___x_941_);
v___x_943_ = v___x_938_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
else
{
lean_object* v___x_947_; lean_object* v___x_949_; 
lean_dec(v_val_933_);
v___x_947_ = lean_box(v___x_931_);
if (v_isShared_936_ == 0)
{
lean_ctor_set_tag(v___x_935_, 0);
lean_ctor_set(v___x_935_, 0, v___x_947_);
v___x_949_ = v___x_935_;
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
}
}
else
{
lean_object* v___x_952_; lean_object* v___x_954_; 
lean_dec(v___x_932_);
v___x_952_ = lean_box(v___x_931_);
if (v_isShared_927_ == 0)
{
lean_ctor_set_tag(v___x_926_, 0);
lean_ctor_set(v___x_926_, 0, v___x_952_);
v___x_954_ = v___x_926_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
else
{
lean_del_object(v___x_926_);
lean_dec(v_val_924_);
goto v___jp_918_;
}
}
}
else
{
lean_dec(v_a_914_);
goto v___jp_918_;
}
v___jp_918_:
{
uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_919_ = 0;
v___x_920_ = lean_box(v___x_919_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_920_);
v___x_922_ = v___x_916_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
v_a_958_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_913_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_913_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg___boxed(lean_object* v_fvarId_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_966_, v_a_967_, v_a_968_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
lean_dec(v_fvarId_966_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp(lean_object* v_fvarId_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_971_, v_a_973_, v_a_975_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___boxed(lean_object* v_fvarId_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_Compiler_LCNF_isConstructorApp(v_fvarId_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_fvarId_978_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(lean_object* v_arg_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
if (lean_obj_tag(v_arg_985_) == 1)
{
lean_object* v_fvarId_989_; lean_object* v___x_990_; 
v_fvarId_989_ = lean_ctor_get(v_arg_985_, 0);
v___x_990_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_989_, v_a_986_, v_a_987_);
return v___x_990_;
}
else
{
uint8_t v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_991_ = 0;
v___x_992_ = lean_box(v___x_991_);
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg___boxed(lean_object* v_arg_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_994_, v_a_995_, v_a_996_);
lean_dec(v_a_996_);
lean_dec(v_a_995_);
lean_dec(v_arg_994_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp(uint8_t v_pu_999_, lean_object* v_arg_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_1000_, v_a_1002_, v_a_1004_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___boxed(lean_object* v_pu_1007_, lean_object* v_arg_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
uint8_t v_pu_boxed_1014_; lean_object* v_res_1015_; 
v_pu_boxed_1014_ = lean_unbox(v_pu_1007_);
v_res_1015_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp(v_pu_boxed_1014_, v_arg_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_arg_1008_);
return v_res_1015_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getParam___closed__1(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParam___closed__0));
v___x_1018_ = l_Lean_stringToMessageData(v___x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam(uint8_t v_pu_1019_, lean_object* v_fvarId_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v___x_1026_; lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1039_; 
v___x_1026_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_1019_, v_fvarId_1020_, v_a_1022_);
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1039_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1039_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
if (lean_obj_tag(v_a_1027_) == 1)
{
lean_object* v_val_1031_; lean_object* v___x_1033_; 
lean_dec(v_fvarId_1020_);
v_val_1031_ = lean_ctor_get(v_a_1027_, 0);
lean_inc(v_val_1031_);
lean_dec_ref_known(v_a_1027_, 1);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v_val_1031_);
v___x_1033_ = v___x_1029_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_val_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
else
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_del_object(v___x_1029_);
lean_dec(v_a_1027_);
v___x_1035_ = lean_obj_once(&l_Lean_Compiler_LCNF_getParam___closed__1, &l_Lean_Compiler_LCNF_getParam___closed__1_once, _init_l_Lean_Compiler_LCNF_getParam___closed__1);
v___x_1036_ = l_Lean_MessageData_ofName(v_fvarId_1020_);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_1037_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam___boxed(lean_object* v_pu_1040_, lean_object* v_fvarId_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
uint8_t v_pu_boxed_1047_; lean_object* v_res_1048_; 
v_pu_boxed_1047_ = lean_unbox(v_pu_1040_);
v_res_1048_ = l_Lean_Compiler_LCNF_getParam(v_pu_boxed_1047_, v_fvarId_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
return v_res_1048_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = ((lean_object*)(l_Lean_Compiler_LCNF_getLetDecl___closed__0));
v___x_1051_ = l_Lean_stringToMessageData(v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl(uint8_t v_pu_1052_, lean_object* v_fvarId_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v___x_1059_; lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1072_; 
v___x_1059_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_1052_, v_fvarId_1053_, v_a_1055_);
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1062_ = v___x_1059_;
v_isShared_1063_ = v_isSharedCheck_1072_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1072_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
if (lean_obj_tag(v_a_1060_) == 1)
{
lean_object* v_val_1064_; lean_object* v___x_1066_; 
lean_dec(v_fvarId_1053_);
v_val_1064_ = lean_ctor_get(v_a_1060_, 0);
lean_inc(v_val_1064_);
lean_dec_ref_known(v_a_1060_, 1);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v_val_1064_);
v___x_1066_ = v___x_1062_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_val_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
else
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_del_object(v___x_1062_);
lean_dec(v_a_1060_);
v___x_1068_ = lean_obj_once(&l_Lean_Compiler_LCNF_getLetDecl___closed__1, &l_Lean_Compiler_LCNF_getLetDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1);
v___x_1069_ = l_Lean_MessageData_ofName(v_fvarId_1053_);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_1070_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
return v___x_1071_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl___boxed(lean_object* v_pu_1073_, lean_object* v_fvarId_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
uint8_t v_pu_boxed_1080_; lean_object* v_res_1081_; 
v_pu_boxed_1080_ = lean_unbox(v_pu_1073_);
v_res_1081_ = l_Lean_Compiler_LCNF_getLetDecl(v_pu_boxed_1080_, v_fvarId_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
return v_res_1081_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = ((lean_object*)(l_Lean_Compiler_LCNF_getFunDecl___closed__0));
v___x_1084_ = l_Lean_stringToMessageData(v___x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t v_pu_1085_, lean_object* v_fvarId_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v___x_1092_; lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1105_; 
v___x_1092_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_1085_, v_fvarId_1086_, v_a_1088_);
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1105_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1105_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
if (lean_obj_tag(v_a_1093_) == 1)
{
lean_object* v_val_1097_; lean_object* v___x_1099_; 
lean_dec(v_fvarId_1086_);
v_val_1097_ = lean_ctor_get(v_a_1093_, 0);
lean_inc(v_val_1097_);
lean_dec_ref_known(v_a_1093_, 1);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v_val_1097_);
v___x_1099_ = v___x_1095_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_val_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
else
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_del_object(v___x_1095_);
lean_dec(v_a_1093_);
v___x_1101_ = lean_obj_once(&l_Lean_Compiler_LCNF_getFunDecl___closed__1, &l_Lean_Compiler_LCNF_getFunDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1);
v___x_1102_ = l_Lean_MessageData_ofName(v_fvarId_1086_);
v___x_1103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_1103_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
return v___x_1104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl___boxed(lean_object* v_pu_1106_, lean_object* v_fvarId_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
uint8_t v_pu_boxed_1113_; lean_object* v_res_1114_; 
v_pu_boxed_1113_ = lean_unbox(v_pu_1106_);
v_res_1114_ = l_Lean_Compiler_LCNF_getFunDecl(v_pu_boxed_1113_, v_fvarId_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg(lean_object* v_f_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v___x_1118_; lean_object* v_lctx_1119_; lean_object* v_nextIdx_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1131_; 
v___x_1118_ = lean_st_ref_take(v_a_1116_);
v_lctx_1119_ = lean_ctor_get(v___x_1118_, 0);
v_nextIdx_1120_ = lean_ctor_get(v___x_1118_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1122_ = v___x_1118_;
v_isShared_1123_ = v_isSharedCheck_1131_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_nextIdx_1120_);
lean_inc(v_lctx_1119_);
lean_dec(v___x_1118_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1131_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1124_ = lean_apply_1(v_f_1115_, v_lctx_1119_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1124_);
v___x_1126_ = v___x_1122_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_nextIdx_1120_);
v___x_1126_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = lean_st_ref_put(v_a_1116_, v___x_1126_);
v___x_1128_ = lean_box(0);
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
return v___x_1129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg___boxed(lean_object* v_f_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_Compiler_LCNF_modifyLCtx___redArg(v_f_1132_, v_a_1133_);
lean_dec(v_a_1133_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx(lean_object* v_f_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v___x_1142_; lean_object* v_lctx_1143_; lean_object* v_nextIdx_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1155_; 
v___x_1142_ = lean_st_ref_take(v_a_1138_);
v_lctx_1143_ = lean_ctor_get(v___x_1142_, 0);
v_nextIdx_1144_ = lean_ctor_get(v___x_1142_, 1);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1146_ = v___x_1142_;
v_isShared_1147_ = v_isSharedCheck_1155_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_nextIdx_1144_);
lean_inc(v_lctx_1143_);
lean_dec(v___x_1142_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1155_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1148_ = lean_apply_1(v_f_1136_, v_lctx_1143_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1148_);
v___x_1150_ = v___x_1146_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_nextIdx_1144_);
v___x_1150_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = lean_st_ref_put(v_a_1138_, v___x_1150_);
v___x_1152_ = lean_box(0);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
return v___x_1153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___boxed(lean_object* v_f_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_Compiler_LCNF_modifyLCtx(v_f_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t v_pu_1163_, lean_object* v_decl_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v___x_1167_; lean_object* v_lctx_1168_; lean_object* v_nextIdx_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1180_; 
v___x_1167_ = lean_st_ref_take(v_a_1165_);
v_lctx_1168_ = lean_ctor_get(v___x_1167_, 0);
v_nextIdx_1169_ = lean_ctor_get(v___x_1167_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1171_ = v___x_1167_;
v_isShared_1172_ = v_isSharedCheck_1180_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_nextIdx_1169_);
lean_inc(v_lctx_1168_);
lean_dec(v___x_1167_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1180_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1173_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_1163_, v_lctx_1168_, v_decl_1164_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1173_);
v___x_1175_ = v___x_1171_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_nextIdx_1169_);
v___x_1175_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1176_ = lean_st_ref_put(v_a_1165_, v___x_1175_);
v___x_1177_ = lean_box(0);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg___boxed(lean_object* v_pu_1181_, lean_object* v_decl_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
uint8_t v_pu_boxed_1185_; lean_object* v_res_1186_; 
v_pu_boxed_1185_ = lean_unbox(v_pu_1181_);
v_res_1186_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_boxed_1185_, v_decl_1182_, v_a_1183_);
lean_dec(v_a_1183_);
lean_dec_ref(v_decl_1182_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(uint8_t v_pu_1187_, lean_object* v_decl_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1187_, v_decl_1188_, v_a_1190_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___boxed(lean_object* v_pu_1195_, lean_object* v_decl_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
uint8_t v_pu_boxed_1202_; lean_object* v_res_1203_; 
v_pu_boxed_1202_ = lean_unbox(v_pu_1195_);
v_res_1203_ = l_Lean_Compiler_LCNF_eraseLetDecl(v_pu_boxed_1202_, v_decl_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec(v_a_1198_);
lean_dec_ref(v_a_1197_);
lean_dec_ref(v_decl_1196_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t v_pu_1204_, lean_object* v_decl_1205_, uint8_t v_recursive_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v___x_1209_; lean_object* v_lctx_1210_; lean_object* v_nextIdx_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1222_; 
v___x_1209_ = lean_st_ref_take(v_a_1207_);
v_lctx_1210_ = lean_ctor_get(v___x_1209_, 0);
v_nextIdx_1211_ = lean_ctor_get(v___x_1209_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1213_ = v___x_1209_;
v_isShared_1214_ = v_isSharedCheck_1222_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_nextIdx_1211_);
lean_inc(v_lctx_1210_);
lean_dec(v___x_1209_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1222_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1215_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_1204_, v_lctx_1210_, v_decl_1205_, v_recursive_1206_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1215_);
v___x_1217_ = v___x_1213_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_nextIdx_1211_);
v___x_1217_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = lean_st_ref_put(v_a_1207_, v___x_1217_);
v___x_1219_ = lean_box(0);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg___boxed(lean_object* v_pu_1223_, lean_object* v_decl_1224_, lean_object* v_recursive_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
uint8_t v_pu_boxed_1228_; uint8_t v_recursive_boxed_1229_; lean_object* v_res_1230_; 
v_pu_boxed_1228_ = lean_unbox(v_pu_1223_);
v_recursive_boxed_1229_ = lean_unbox(v_recursive_1225_);
v_res_1230_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_boxed_1228_, v_decl_1224_, v_recursive_boxed_1229_, v_a_1226_);
lean_dec(v_a_1226_);
lean_dec_ref(v_decl_1224_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(uint8_t v_pu_1231_, lean_object* v_decl_1232_, uint8_t v_recursive_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1231_, v_decl_1232_, v_recursive_1233_, v_a_1235_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___boxed(lean_object* v_pu_1240_, lean_object* v_decl_1241_, lean_object* v_recursive_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
uint8_t v_pu_boxed_1248_; uint8_t v_recursive_boxed_1249_; lean_object* v_res_1250_; 
v_pu_boxed_1248_ = lean_unbox(v_pu_1240_);
v_recursive_boxed_1249_ = lean_unbox(v_recursive_1242_);
v_res_1250_ = l_Lean_Compiler_LCNF_eraseFunDecl(v_pu_boxed_1248_, v_decl_1241_, v_recursive_boxed_1249_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec_ref(v_decl_1241_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t v_pu_1251_, lean_object* v_code_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v___x_1255_; lean_object* v_lctx_1256_; lean_object* v_nextIdx_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1268_; 
v___x_1255_ = lean_st_ref_take(v_a_1253_);
v_lctx_1256_ = lean_ctor_get(v___x_1255_, 0);
v_nextIdx_1257_ = lean_ctor_get(v___x_1255_, 1);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1259_ = v___x_1255_;
v_isShared_1260_ = v_isSharedCheck_1268_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_nextIdx_1257_);
lean_inc(v_lctx_1256_);
lean_dec(v___x_1255_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1268_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_1251_, v_code_1252_, v_lctx_1256_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1261_);
v___x_1263_ = v___x_1259_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_nextIdx_1257_);
v___x_1263_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = lean_st_ref_put(v_a_1253_, v___x_1263_);
v___x_1265_ = lean_box(0);
v___x_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg___boxed(lean_object* v_pu_1269_, lean_object* v_code_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
uint8_t v_pu_boxed_1273_; lean_object* v_res_1274_; 
v_pu_boxed_1273_ = lean_unbox(v_pu_1269_);
v_res_1274_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_boxed_1273_, v_code_1270_, v_a_1271_);
lean_dec(v_a_1271_);
lean_dec_ref(v_code_1270_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode(uint8_t v_pu_1275_, lean_object* v_code_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_1275_, v_code_1276_, v_a_1278_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___boxed(lean_object* v_pu_1283_, lean_object* v_code_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
uint8_t v_pu_boxed_1290_; lean_object* v_res_1291_; 
v_pu_boxed_1290_ = lean_unbox(v_pu_1283_);
v_res_1291_ = l_Lean_Compiler_LCNF_eraseCode(v_pu_boxed_1290_, v_code_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec_ref(v_code_1284_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t v_pu_1292_, lean_object* v_param_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v___x_1296_; lean_object* v_lctx_1297_; lean_object* v_nextIdx_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1309_; 
v___x_1296_ = lean_st_ref_take(v_a_1294_);
v_lctx_1297_ = lean_ctor_get(v___x_1296_, 0);
v_nextIdx_1298_ = lean_ctor_get(v___x_1296_, 1);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1300_ = v___x_1296_;
v_isShared_1301_ = v_isSharedCheck_1309_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_nextIdx_1298_);
lean_inc(v_lctx_1297_);
lean_dec(v___x_1296_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1309_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1302_ = l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_1292_, v_lctx_1297_, v_param_1293_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1302_);
v___x_1304_ = v___x_1300_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1302_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_nextIdx_1298_);
v___x_1304_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1305_ = lean_st_ref_put(v_a_1294_, v___x_1304_);
v___x_1306_ = lean_box(0);
v___x_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
return v___x_1307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg___boxed(lean_object* v_pu_1310_, lean_object* v_param_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_){
_start:
{
uint8_t v_pu_boxed_1314_; lean_object* v_res_1315_; 
v_pu_boxed_1314_ = lean_unbox(v_pu_1310_);
v_res_1315_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_boxed_1314_, v_param_1311_, v_a_1312_);
lean_dec(v_a_1312_);
lean_dec_ref(v_param_1311_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam(uint8_t v_pu_1316_, lean_object* v_param_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_1316_, v_param_1317_, v_a_1319_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___boxed(lean_object* v_pu_1324_, lean_object* v_param_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
uint8_t v_pu_boxed_1331_; lean_object* v_res_1332_; 
v_pu_boxed_1331_ = lean_unbox(v_pu_1324_);
v_res_1332_ = l_Lean_Compiler_LCNF_eraseParam(v_pu_boxed_1331_, v_param_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec_ref(v_param_1325_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t v_pu_1333_, lean_object* v_params_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v___x_1337_; lean_object* v_lctx_1338_; lean_object* v_nextIdx_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1350_; 
v___x_1337_ = lean_st_ref_take(v_a_1335_);
v_lctx_1338_ = lean_ctor_get(v___x_1337_, 0);
v_nextIdx_1339_ = lean_ctor_get(v___x_1337_, 1);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1341_ = v___x_1337_;
v_isShared_1342_ = v_isSharedCheck_1350_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_nextIdx_1339_);
lean_inc(v_lctx_1338_);
lean_dec(v___x_1337_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1350_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1343_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_1333_, v_lctx_1338_, v_params_1334_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v___x_1343_);
v___x_1345_ = v___x_1341_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_nextIdx_1339_);
v___x_1345_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1346_ = lean_st_ref_put(v_a_1335_, v___x_1345_);
v___x_1347_ = lean_box(0);
v___x_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
return v___x_1348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg___boxed(lean_object* v_pu_1351_, lean_object* v_params_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
uint8_t v_pu_boxed_1355_; lean_object* v_res_1356_; 
v_pu_boxed_1355_ = lean_unbox(v_pu_1351_);
v_res_1356_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_boxed_1355_, v_params_1352_, v_a_1353_);
lean_dec(v_a_1353_);
lean_dec_ref(v_params_1352_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams(uint8_t v_pu_1357_, lean_object* v_params_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1357_, v_params_1358_, v_a_1360_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___boxed(lean_object* v_pu_1365_, lean_object* v_params_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
uint8_t v_pu_boxed_1372_; lean_object* v_res_1373_; 
v_pu_boxed_1372_ = lean_unbox(v_pu_1365_);
v_res_1373_ = l_Lean_Compiler_LCNF_eraseParams(v_pu_boxed_1372_, v_params_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec_ref(v_params_1366_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t v_pu_1374_, lean_object* v_decl_1375_, lean_object* v_a_1376_){
_start:
{
switch(lean_obj_tag(v_decl_1375_))
{
case 0:
{
lean_object* v_decl_1378_; lean_object* v___x_1379_; 
v_decl_1378_ = lean_ctor_get(v_decl_1375_, 0);
v___x_1379_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1374_, v_decl_1378_, v_a_1376_);
return v___x_1379_;
}
case 1:
{
lean_object* v_decl_1380_; uint8_t v___x_1381_; lean_object* v___x_1382_; 
v_decl_1380_ = lean_ctor_get(v_decl_1375_, 0);
v___x_1381_ = 1;
v___x_1382_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1374_, v_decl_1380_, v___x_1381_, v_a_1376_);
return v___x_1382_;
}
case 2:
{
lean_object* v_decl_1383_; uint8_t v___x_1384_; lean_object* v___x_1385_; 
v_decl_1383_ = lean_ctor_get(v_decl_1375_, 0);
v___x_1384_ = 1;
v___x_1385_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1374_, v_decl_1383_, v___x_1384_, v_a_1376_);
return v___x_1385_;
}
default: 
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_box(0);
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg___boxed(lean_object* v_pu_1388_, lean_object* v_decl_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
uint8_t v_pu_boxed_1392_; lean_object* v_res_1393_; 
v_pu_boxed_1392_ = lean_unbox(v_pu_1388_);
v_res_1393_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_boxed_1392_, v_decl_1389_, v_a_1390_);
lean_dec(v_a_1390_);
lean_dec_ref(v_decl_1389_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl(uint8_t v_pu_1394_, lean_object* v_decl_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1394_, v_decl_1395_, v_a_1397_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___boxed(lean_object* v_pu_1402_, lean_object* v_decl_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
uint8_t v_pu_boxed_1409_; lean_object* v_res_1410_; 
v_pu_boxed_1409_ = lean_unbox(v_pu_1402_);
v_res_1410_ = l_Lean_Compiler_LCNF_eraseCodeDecl(v_pu_boxed_1409_, v_decl_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
lean_dec_ref(v_decl_1403_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(uint8_t v_pu_1411_, lean_object* v_as_1412_, size_t v_i_1413_, size_t v_stop_1414_, lean_object* v_b_1415_, lean_object* v___y_1416_){
_start:
{
uint8_t v___x_1418_; 
v___x_1418_ = lean_usize_dec_eq(v_i_1413_, v_stop_1414_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = lean_array_uget_borrowed(v_as_1412_, v_i_1413_);
v___x_1420_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1411_, v___x_1419_, v___y_1416_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; size_t v___x_1422_; size_t v___x_1423_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1422_ = ((size_t)1ULL);
v___x_1423_ = lean_usize_add(v_i_1413_, v___x_1422_);
v_i_1413_ = v___x_1423_;
v_b_1415_ = v_a_1421_;
goto _start;
}
else
{
return v___x_1420_;
}
}
else
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v_b_1415_);
return v___x_1425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg___boxed(lean_object* v_pu_1426_, lean_object* v_as_1427_, lean_object* v_i_1428_, lean_object* v_stop_1429_, lean_object* v_b_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
uint8_t v_pu_boxed_1433_; size_t v_i_boxed_1434_; size_t v_stop_boxed_1435_; lean_object* v_res_1436_; 
v_pu_boxed_1433_ = lean_unbox(v_pu_1426_);
v_i_boxed_1434_ = lean_unbox_usize(v_i_1428_);
lean_dec(v_i_1428_);
v_stop_boxed_1435_ = lean_unbox_usize(v_stop_1429_);
lean_dec(v_stop_1429_);
v_res_1436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_boxed_1433_, v_as_1427_, v_i_boxed_1434_, v_stop_boxed_1435_, v_b_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v_as_1427_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls(uint8_t v_pu_1437_, lean_object* v_decls_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1444_ = lean_unsigned_to_nat(0u);
v___x_1445_ = lean_array_get_size(v_decls_1438_);
v___x_1446_ = lean_box(0);
v___x_1447_ = lean_nat_dec_lt(v___x_1444_, v___x_1445_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1446_);
return v___x_1448_;
}
else
{
uint8_t v___x_1449_; 
v___x_1449_ = lean_nat_dec_le(v___x_1445_, v___x_1445_);
if (v___x_1449_ == 0)
{
if (v___x_1447_ == 0)
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1446_);
return v___x_1450_;
}
else
{
size_t v___x_1451_; size_t v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = ((size_t)0ULL);
v___x_1452_ = lean_usize_of_nat(v___x_1445_);
v___x_1453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1437_, v_decls_1438_, v___x_1451_, v___x_1452_, v___x_1446_, v_a_1440_);
return v___x_1453_;
}
}
else
{
size_t v___x_1454_; size_t v___x_1455_; lean_object* v___x_1456_; 
v___x_1454_ = ((size_t)0ULL);
v___x_1455_ = lean_usize_of_nat(v___x_1445_);
v___x_1456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1437_, v_decls_1438_, v___x_1454_, v___x_1455_, v___x_1446_, v_a_1440_);
return v___x_1456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls___boxed(lean_object* v_pu_1457_, lean_object* v_decls_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
uint8_t v_pu_boxed_1464_; lean_object* v_res_1465_; 
v_pu_boxed_1464_ = lean_unbox(v_pu_1457_);
v_res_1465_ = l_Lean_Compiler_LCNF_eraseCodeDecls(v_pu_boxed_1464_, v_decls_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
lean_dec_ref(v_decls_1458_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(uint8_t v_pu_1466_, lean_object* v_as_1467_, size_t v_i_1468_, size_t v_stop_1469_, lean_object* v_b_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1466_, v_as_1467_, v_i_1468_, v_stop_1469_, v_b_1470_, v___y_1472_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___boxed(lean_object* v_pu_1477_, lean_object* v_as_1478_, lean_object* v_i_1479_, lean_object* v_stop_1480_, lean_object* v_b_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
uint8_t v_pu_boxed_1487_; size_t v_i_boxed_1488_; size_t v_stop_boxed_1489_; lean_object* v_res_1490_; 
v_pu_boxed_1487_ = lean_unbox(v_pu_1477_);
v_i_boxed_1488_ = lean_unbox_usize(v_i_1479_);
lean_dec(v_i_1479_);
v_stop_boxed_1489_ = lean_unbox_usize(v_stop_1480_);
lean_dec(v_stop_1480_);
v_res_1490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(v_pu_boxed_1487_, v_as_1478_, v_i_boxed_1488_, v_stop_boxed_1489_, v_b_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec_ref(v_as_1478_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(lean_object* v_f_1491_, lean_object* v_v_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
if (lean_obj_tag(v_v_1492_) == 0)
{
lean_object* v_code_1498_; lean_object* v___x_1499_; 
v_code_1498_ = lean_ctor_get(v_v_1492_, 0);
lean_inc_ref(v_code_1498_);
lean_dec_ref_known(v_v_1492_, 1);
lean_inc(v___y_1496_);
lean_inc_ref(v___y_1495_);
lean_inc(v___y_1494_);
lean_inc_ref(v___y_1493_);
v___x_1499_ = lean_apply_6(v_f_1491_, v_code_1498_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, lean_box(0));
return v___x_1499_;
}
else
{
lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1507_; 
lean_dec_ref(v_f_1491_);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_v_1492_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; 
v_unused_1508_ = lean_ctor_get(v_v_1492_, 0);
lean_dec(v_unused_1508_);
v___x_1501_ = v_v_1492_;
v_isShared_1502_ = v_isSharedCheck_1507_;
goto v_resetjp_1500_;
}
else
{
lean_dec(v_v_1492_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1507_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1503_ = lean_box(0);
if (v_isShared_1502_ == 0)
{
lean_ctor_set_tag(v___x_1501_, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1503_);
v___x_1505_ = v___x_1501_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg___boxed(lean_object* v_f_1509_, lean_object* v_v_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1509_, v_v_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(uint8_t v_pu_1517_, lean_object* v_f_1518_, lean_object* v_v_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1518_, v_v_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___boxed(lean_object* v_pu_1526_, lean_object* v_f_1527_, lean_object* v_v_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
uint8_t v_pu_boxed_1534_; lean_object* v_res_1535_; 
v_pu_boxed_1534_ = lean_unbox(v_pu_1526_);
v_res_1535_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(v_pu_boxed_1534_, v_f_1527_, v_v_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t v_pu_1536_, lean_object* v_decl_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v_toSignature_1543_; lean_object* v_value_1544_; lean_object* v_params_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_toSignature_1543_ = lean_ctor_get(v_decl_1537_, 0);
lean_inc_ref(v_toSignature_1543_);
v_value_1544_ = lean_ctor_get(v_decl_1537_, 1);
lean_inc_ref(v_value_1544_);
lean_dec_ref(v_decl_1537_);
v_params_1545_ = lean_ctor_get(v_toSignature_1543_, 3);
lean_inc_ref(v_params_1545_);
lean_dec_ref(v_toSignature_1543_);
v___x_1546_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1536_, v_params_1545_, v_a_1539_);
lean_dec_ref(v_params_1545_);
lean_dec_ref(v___x_1546_);
v___x_1547_ = lean_box(v_pu_1536_);
v___x_1548_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_eraseCode___boxed), 7, 1);
lean_closure_set(v___x_1548_, 0, v___x_1547_);
v___x_1549_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v___x_1548_, v_value_1544_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl___boxed(lean_object* v_pu_1550_, lean_object* v_decl_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
uint8_t v_pu_boxed_1557_; lean_object* v_res_1558_; 
v_pu_boxed_1557_ = lean_unbox(v_pu_1550_);
v_res_1558_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_boxed_1557_, v_decl_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase(uint8_t v_pu_1559_, lean_object* v_decl_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_1559_, v_decl_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase___boxed(lean_object* v_pu_1567_, lean_object* v_decl_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_){
_start:
{
uint8_t v_pu_boxed_1574_; lean_object* v_res_1575_; 
v_pu_boxed_1574_ = lean_unbox(v_pu_1567_);
v_res_1575_ = l_Lean_Compiler_LCNF_Decl_erase(v_pu_boxed_1574_, v_decl_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
lean_dec(v_a_1570_);
lean_dec_ref(v_a_1569_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(lean_object* v_msg_1576_){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = l_Lean_instInhabitedExpr;
v___x_1578_ = lean_panic_fn_borrowed(v___x_1577_, v_msg_1576_);
return v___x_1578_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1582_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2));
v___x_1583_ = lean_unsigned_to_nat(20u);
v___x_1584_ = lean_unsigned_to_nat(215u);
v___x_1585_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1));
v___x_1586_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0));
v___x_1587_ = l_mkPanicMessageWithDecl(v___x_1586_, v___x_1585_, v___x_1584_, v___x_1583_, v___x_1582_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t v_pu_1588_, lean_object* v_s_1589_, uint8_t v_translator_1590_, lean_object* v_e_1591_){
_start:
{
uint8_t v___x_1592_; 
v___x_1592_ = l_Lean_Expr_hasFVar(v_e_1591_);
if (v___x_1592_ == 0)
{
return v_e_1591_;
}
else
{
switch(lean_obj_tag(v_e_1591_))
{
case 1:
{
lean_object* v_fvarId_1593_; lean_object* v___x_1594_; 
v_fvarId_1593_ = lean_ctor_get(v_e_1591_, 0);
v___x_1594_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1589_, v_fvarId_1593_);
if (lean_obj_tag(v___x_1594_) == 0)
{
return v_e_1591_;
}
else
{
lean_object* v_val_1595_; 
lean_dec_ref_known(v_e_1591_, 1);
v_val_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_val_1595_);
lean_dec_ref_known(v___x_1594_, 1);
switch(lean_obj_tag(v_val_1595_))
{
case 0:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_Compiler_LCNF_erasedExpr;
return v___x_1596_;
}
case 1:
{
if (v_translator_1590_ == 0)
{
lean_object* v_fvarId_1597_; lean_object* v___x_1598_; 
v_fvarId_1597_ = lean_ctor_get(v_val_1595_, 0);
lean_inc(v_fvarId_1597_);
lean_dec_ref_known(v_val_1595_, 1);
v___x_1598_ = l_Lean_Expr_fvar___override(v_fvarId_1597_);
v_e_1591_ = v___x_1598_;
goto _start;
}
else
{
lean_object* v_fvarId_1600_; lean_object* v___x_1601_; 
v_fvarId_1600_ = lean_ctor_get(v_val_1595_, 0);
lean_inc(v_fvarId_1600_);
lean_dec_ref_known(v_val_1595_, 1);
v___x_1601_ = l_Lean_Expr_fvar___override(v_fvarId_1600_);
return v___x_1601_;
}
}
default: 
{
if (v_translator_1590_ == 0)
{
lean_object* v_expr_1602_; 
v_expr_1602_ = lean_ctor_get(v_val_1595_, 0);
lean_inc_ref(v_expr_1602_);
lean_dec_ref_known(v_val_1595_, 1);
v_e_1591_ = v_expr_1602_;
goto _start;
}
else
{
lean_object* v_expr_1604_; 
v_expr_1604_ = lean_ctor_get(v_val_1595_, 0);
lean_inc_ref(v_expr_1604_);
lean_dec_ref_known(v_val_1595_, 1);
return v_expr_1604_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_1605_; lean_object* v_arg_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___y_1610_; size_t v___x_1614_; size_t v___x_1615_; uint8_t v___x_1616_; 
v_fn_1605_ = lean_ctor_get(v_e_1591_, 0);
v_arg_1606_ = lean_ctor_get(v_e_1591_, 1);
lean_inc_ref(v_fn_1605_);
v___x_1607_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1588_, v_s_1589_, v_translator_1590_, v_fn_1605_);
lean_inc_ref(v_arg_1606_);
v___x_1608_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1588_, v_s_1589_, v_translator_1590_, v_arg_1606_);
v___x_1614_ = lean_ptr_addr(v_fn_1605_);
v___x_1615_ = lean_ptr_addr(v___x_1607_);
v___x_1616_ = lean_usize_dec_eq(v___x_1614_, v___x_1615_);
if (v___x_1616_ == 0)
{
v___y_1610_ = v___x_1616_;
goto v___jp_1609_;
}
else
{
size_t v___x_1617_; size_t v___x_1618_; uint8_t v___x_1619_; 
v___x_1617_ = lean_ptr_addr(v_arg_1606_);
v___x_1618_ = lean_ptr_addr(v___x_1608_);
v___x_1619_ = lean_usize_dec_eq(v___x_1617_, v___x_1618_);
v___y_1610_ = v___x_1619_;
goto v___jp_1609_;
}
v___jp_1609_:
{
if (v___y_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_dec_ref_known(v_e_1591_, 2);
v___x_1611_ = l_Lean_Expr_app___override(v___x_1607_, v___x_1608_);
v___x_1612_ = l_Lean_Expr_headBeta(v___x_1611_);
return v___x_1612_;
}
else
{
lean_object* v___x_1613_; 
lean_dec_ref(v___x_1608_);
lean_dec_ref(v___x_1607_);
v___x_1613_ = l_Lean_Expr_headBeta(v_e_1591_);
return v___x_1613_;
}
}
}
case 6:
{
lean_object* v_binderName_1620_; lean_object* v_binderType_1621_; lean_object* v_body_1622_; uint8_t v_binderInfo_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___y_1627_; size_t v___x_1631_; size_t v___x_1632_; uint8_t v___x_1633_; 
v_binderName_1620_ = lean_ctor_get(v_e_1591_, 0);
v_binderType_1621_ = lean_ctor_get(v_e_1591_, 1);
v_body_1622_ = lean_ctor_get(v_e_1591_, 2);
v_binderInfo_1623_ = lean_ctor_get_uint8(v_e_1591_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1621_);
v___x_1624_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1588_, v_s_1589_, v_translator_1590_, v_binderType_1621_);
lean_inc_ref(v_body_1622_);
v___x_1625_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1588_, v_s_1589_, v_translator_1590_, v_body_1622_);
v___x_1631_ = lean_ptr_addr(v_binderType_1621_);
v___x_1632_ = lean_ptr_addr(v___x_1624_);
v___x_1633_ = lean_usize_dec_eq(v___x_1631_, v___x_1632_);
if (v___x_1633_ == 0)
{
v___y_1627_ = v___x_1633_;
goto v___jp_1626_;
}
else
{
size_t v___x_1634_; size_t v___x_1635_; uint8_t v___x_1636_; 
v___x_1634_ = lean_ptr_addr(v_body_1622_);
v___x_1635_ = lean_ptr_addr(v___x_1625_);
v___x_1636_ = lean_usize_dec_eq(v___x_1634_, v___x_1635_);
v___y_1627_ = v___x_1636_;
goto v___jp_1626_;
}
v___jp_1626_:
{
if (v___y_1627_ == 0)
{
lean_object* v___x_1628_; 
lean_inc(v_binderName_1620_);
lean_dec_ref_known(v_e_1591_, 3);
v___x_1628_ = l_Lean_Expr_lam___override(v_binderName_1620_, v___x_1624_, v___x_1625_, v_binderInfo_1623_);
return v___x_1628_;
}
else
{
uint8_t v___x_1629_; 
v___x_1629_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1623_, v_binderInfo_1623_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; 
lean_inc(v_binderName_1620_);
lean_dec_ref_known(v_e_1591_, 3);
v___x_1630_ = l_Lean_Expr_lam___override(v_binderName_1620_, v___x_1624_, v___x_1625_, v_binderInfo_1623_);
return v___x_1630_;
}
else
{
lean_dec_ref(v___x_1625_);
lean_dec_ref(v___x_1624_);
return v_e_1591_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1637_; lean_object* v_binderType_1638_; lean_object* v_body_1639_; uint8_t v_binderInfo_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___y_1644_; size_t v___x_1648_; size_t v___x_1649_; uint8_t v___x_1650_; 
v_binderName_1637_ = lean_ctor_get(v_e_1591_, 0);
v_binderType_1638_ = lean_ctor_get(v_e_1591_, 1);
v_body_1639_ = lean_ctor_get(v_e_1591_, 2);
v_binderInfo_1640_ = lean_ctor_get_uint8(v_e_1591_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1638_);
v___x_1641_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1588_, v_s_1589_, v_translator_1590_, v_binderType_1638_);
lean_inc_ref(v_body_1639_);
v___x_1642_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1588_, v_s_1589_, v_translator_1590_, v_body_1639_);
v___x_1648_ = lean_ptr_addr(v_binderType_1638_);
v___x_1649_ = lean_ptr_addr(v___x_1641_);
v___x_1650_ = lean_usize_dec_eq(v___x_1648_, v___x_1649_);
if (v___x_1650_ == 0)
{
v___y_1644_ = v___x_1650_;
goto v___jp_1643_;
}
else
{
size_t v___x_1651_; size_t v___x_1652_; uint8_t v___x_1653_; 
v___x_1651_ = lean_ptr_addr(v_body_1639_);
v___x_1652_ = lean_ptr_addr(v___x_1642_);
v___x_1653_ = lean_usize_dec_eq(v___x_1651_, v___x_1652_);
v___y_1644_ = v___x_1653_;
goto v___jp_1643_;
}
v___jp_1643_:
{
if (v___y_1644_ == 0)
{
lean_object* v___x_1645_; 
lean_inc(v_binderName_1637_);
lean_dec_ref_known(v_e_1591_, 3);
v___x_1645_ = l_Lean_Expr_forallE___override(v_binderName_1637_, v___x_1641_, v___x_1642_, v_binderInfo_1640_);
return v___x_1645_;
}
else
{
uint8_t v___x_1646_; 
v___x_1646_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1640_, v_binderInfo_1640_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; 
lean_inc(v_binderName_1637_);
lean_dec_ref_known(v_e_1591_, 3);
v___x_1647_ = l_Lean_Expr_forallE___override(v_binderName_1637_, v___x_1641_, v___x_1642_, v_binderInfo_1640_);
return v___x_1647_;
}
else
{
lean_dec_ref(v___x_1642_);
lean_dec_ref(v___x_1641_);
return v_e_1591_;
}
}
}
}
case 8:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_dec_ref_known(v_e_1591_, 4);
v___x_1654_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3, &l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3);
v___x_1655_ = l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(v___x_1654_);
return v___x_1655_;
}
case 10:
{
lean_object* v_data_1656_; lean_object* v_expr_1657_; lean_object* v___x_1658_; size_t v___x_1659_; size_t v___x_1660_; uint8_t v___x_1661_; 
v_data_1656_ = lean_ctor_get(v_e_1591_, 0);
v_expr_1657_ = lean_ctor_get(v_e_1591_, 1);
lean_inc_ref(v_expr_1657_);
v___x_1658_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1588_, v_s_1589_, v_translator_1590_, v_expr_1657_);
v___x_1659_ = lean_ptr_addr(v_expr_1657_);
v___x_1660_ = lean_ptr_addr(v___x_1658_);
v___x_1661_ = lean_usize_dec_eq(v___x_1659_, v___x_1660_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; 
lean_inc(v_data_1656_);
lean_dec_ref_known(v_e_1591_, 2);
v___x_1662_ = l_Lean_Expr_mdata___override(v_data_1656_, v___x_1658_);
return v___x_1662_;
}
else
{
lean_dec_ref(v___x_1658_);
return v_e_1591_;
}
}
case 11:
{
lean_object* v_typeName_1663_; lean_object* v_idx_1664_; lean_object* v_struct_1665_; lean_object* v___x_1666_; size_t v___x_1667_; size_t v___x_1668_; uint8_t v___x_1669_; 
v_typeName_1663_ = lean_ctor_get(v_e_1591_, 0);
v_idx_1664_ = lean_ctor_get(v_e_1591_, 1);
v_struct_1665_ = lean_ctor_get(v_e_1591_, 2);
lean_inc_ref(v_struct_1665_);
v___x_1666_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1588_, v_s_1589_, v_translator_1590_, v_struct_1665_);
v___x_1667_ = lean_ptr_addr(v_struct_1665_);
v___x_1668_ = lean_ptr_addr(v___x_1666_);
v___x_1669_ = lean_usize_dec_eq(v___x_1667_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; 
lean_inc(v_idx_1664_);
lean_inc(v_typeName_1663_);
lean_dec_ref_known(v_e_1591_, 3);
v___x_1670_ = l_Lean_Expr_proj___override(v_typeName_1663_, v_idx_1664_, v___x_1666_);
return v___x_1670_;
}
else
{
lean_dec_ref(v___x_1666_);
return v_e_1591_;
}
}
default: 
{
return v_e_1591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(uint8_t v_pu_1671_, lean_object* v_s_1672_, uint8_t v_translator_1673_, lean_object* v_e_1674_){
_start:
{
if (lean_obj_tag(v_e_1674_) == 5)
{
lean_object* v_fn_1675_; lean_object* v_arg_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; uint8_t v___y_1680_; size_t v___x_1682_; size_t v___x_1683_; uint8_t v___x_1684_; 
v_fn_1675_ = lean_ctor_get(v_e_1674_, 0);
v_arg_1676_ = lean_ctor_get(v_e_1674_, 1);
lean_inc_ref(v_fn_1675_);
v___x_1677_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1671_, v_s_1672_, v_translator_1673_, v_fn_1675_);
lean_inc_ref(v_arg_1676_);
v___x_1678_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1671_, v_s_1672_, v_translator_1673_, v_arg_1676_);
v___x_1682_ = lean_ptr_addr(v_fn_1675_);
v___x_1683_ = lean_ptr_addr(v___x_1677_);
v___x_1684_ = lean_usize_dec_eq(v___x_1682_, v___x_1683_);
if (v___x_1684_ == 0)
{
v___y_1680_ = v___x_1684_;
goto v___jp_1679_;
}
else
{
size_t v___x_1685_; size_t v___x_1686_; uint8_t v___x_1687_; 
v___x_1685_ = lean_ptr_addr(v_arg_1676_);
v___x_1686_ = lean_ptr_addr(v___x_1678_);
v___x_1687_ = lean_usize_dec_eq(v___x_1685_, v___x_1686_);
v___y_1680_ = v___x_1687_;
goto v___jp_1679_;
}
v___jp_1679_:
{
if (v___y_1680_ == 0)
{
lean_object* v___x_1681_; 
lean_dec_ref_known(v_e_1674_, 2);
v___x_1681_ = l_Lean_Expr_app___override(v___x_1677_, v___x_1678_);
return v___x_1681_;
}
else
{
lean_dec_ref(v___x_1678_);
lean_dec_ref(v___x_1677_);
return v_e_1674_;
}
}
}
else
{
lean_object* v___x_1688_; 
v___x_1688_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1671_, v_s_1672_, v_translator_1673_, v_e_1674_);
return v___x_1688_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(lean_object* v_pu_1689_, lean_object* v_s_1690_, lean_object* v_translator_1691_, lean_object* v_e_1692_){
_start:
{
uint8_t v_pu_boxed_1693_; uint8_t v_translator_boxed_1694_; lean_object* v_res_1695_; 
v_pu_boxed_1693_ = lean_unbox(v_pu_1689_);
v_translator_boxed_1694_ = lean_unbox(v_translator_1691_);
v_res_1695_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_boxed_1693_, v_s_1690_, v_translator_boxed_1694_, v_e_1692_);
lean_dec_ref(v_s_1690_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(lean_object* v_pu_1696_, lean_object* v_s_1697_, lean_object* v_translator_1698_, lean_object* v_e_1699_){
_start:
{
uint8_t v_pu_boxed_1700_; uint8_t v_translator_boxed_1701_; lean_object* v_res_1702_; 
v_pu_boxed_1700_ = lean_unbox(v_pu_1696_);
v_translator_boxed_1701_ = lean_unbox(v_translator_1698_);
v_res_1702_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_boxed_1700_, v_s_1697_, v_translator_boxed_1701_, v_e_1699_);
lean_dec_ref(v_s_1697_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(uint8_t v_pu_1703_, lean_object* v_s_1704_, lean_object* v_e_1705_, uint8_t v_translator_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1703_, v_s_1704_, v_translator_1706_, v_e_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(lean_object* v_pu_1708_, lean_object* v_s_1709_, lean_object* v_e_1710_, lean_object* v_translator_1711_){
_start:
{
uint8_t v_pu_boxed_1712_; uint8_t v_translator_boxed_1713_; lean_object* v_res_1714_; 
v_pu_boxed_1712_ = lean_unbox(v_pu_1708_);
v_translator_boxed_1713_ = lean_unbox(v_translator_1711_);
v_res_1714_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(v_pu_boxed_1712_, v_s_1709_, v_e_1710_, v_translator_boxed_1713_);
lean_dec_ref(v_s_1709_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(lean_object* v_x_1715_){
_start:
{
if (lean_obj_tag(v_x_1715_) == 0)
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_unsigned_to_nat(0u);
return v___x_1716_;
}
else
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_unsigned_to_nat(1u);
return v___x_1717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___boxed(lean_object* v_x_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(v_x_1718_);
lean_dec(v_x_1718_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(lean_object* v_t_1720_, lean_object* v_k_1721_){
_start:
{
if (lean_obj_tag(v_t_1720_) == 0)
{
lean_object* v_fvarId_1722_; lean_object* v___x_1723_; 
v_fvarId_1722_ = lean_ctor_get(v_t_1720_, 0);
lean_inc(v_fvarId_1722_);
lean_dec_ref_known(v_t_1720_, 1);
v___x_1723_ = lean_apply_1(v_k_1721_, v_fvarId_1722_);
return v___x_1723_;
}
else
{
return v_k_1721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(lean_object* v_motive_1724_, lean_object* v_ctorIdx_1725_, lean_object* v_t_1726_, lean_object* v_h_1727_, lean_object* v_k_1728_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1726_, v_k_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___boxed(lean_object* v_motive_1730_, lean_object* v_ctorIdx_1731_, lean_object* v_t_1732_, lean_object* v_h_1733_, lean_object* v_k_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(v_motive_1730_, v_ctorIdx_1731_, v_t_1732_, v_h_1733_, v_k_1734_);
lean_dec(v_ctorIdx_1731_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim___redArg(lean_object* v_t_1736_, lean_object* v_fvar_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1736_, v_fvar_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim(lean_object* v_motive_1739_, lean_object* v_t_1740_, lean_object* v_h_1741_, lean_object* v_fvar_1742_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1740_, v_fvar_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim___redArg(lean_object* v_t_1744_, lean_object* v_erased_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1744_, v_erased_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim(lean_object* v_motive_1747_, lean_object* v_t_1748_, lean_object* v_h_1749_, lean_object* v_erased_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1748_, v_erased_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object* v_s_1756_, lean_object* v_fvarId_1757_, uint8_t v_translator_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1756_, v_fvarId_1757_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v___x_1760_; 
v___x_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1760_, 0, v_fvarId_1757_);
return v___x_1760_;
}
else
{
lean_object* v_val_1761_; 
lean_dec(v_fvarId_1757_);
v_val_1761_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_val_1761_);
lean_dec_ref_known(v___x_1759_, 1);
if (lean_obj_tag(v_val_1761_) == 1)
{
if (v_translator_1758_ == 0)
{
lean_object* v_fvarId_1762_; 
v_fvarId_1762_ = lean_ctor_get(v_val_1761_, 0);
lean_inc(v_fvarId_1762_);
lean_dec_ref_known(v_val_1761_, 1);
v_fvarId_1757_ = v_fvarId_1762_;
goto _start;
}
else
{
lean_object* v_fvarId_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
v_fvarId_1764_ = lean_ctor_get(v_val_1761_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_val_1761_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v_val_1761_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_fvarId_1764_);
lean_dec(v_val_1761_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
lean_ctor_set_tag(v___x_1766_, 0);
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_fvarId_1764_);
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
else
{
lean_object* v___x_1772_; 
lean_dec(v_val_1761_);
v___x_1772_ = lean_box(1);
return v___x_1772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg___boxed(lean_object* v_s_1773_, lean_object* v_fvarId_1774_, lean_object* v_translator_1775_){
_start:
{
uint8_t v_translator_boxed_1776_; lean_object* v_res_1777_; 
v_translator_boxed_1776_ = lean_unbox(v_translator_1775_);
v_res_1777_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1773_, v_fvarId_1774_, v_translator_boxed_1776_);
lean_dec_ref(v_s_1773_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp(uint8_t v_pu_1778_, lean_object* v_s_1779_, lean_object* v_fvarId_1780_, uint8_t v_translator_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1779_, v_fvarId_1780_, v_translator_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___boxed(lean_object* v_pu_1783_, lean_object* v_s_1784_, lean_object* v_fvarId_1785_, lean_object* v_translator_1786_){
_start:
{
uint8_t v_pu_boxed_1787_; uint8_t v_translator_boxed_1788_; lean_object* v_res_1789_; 
v_pu_boxed_1787_ = lean_unbox(v_pu_1783_);
v_translator_boxed_1788_ = lean_unbox(v_translator_1786_);
v_res_1789_ = l_Lean_Compiler_LCNF_normFVarImp(v_pu_boxed_1787_, v_s_1784_, v_fvarId_1785_, v_translator_boxed_1788_);
lean_dec_ref(v_s_1784_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t v_pu_1790_, lean_object* v_s_1791_, lean_object* v_arg_1792_, uint8_t v_translator_1793_){
_start:
{
switch(lean_obj_tag(v_arg_1792_))
{
case 0:
{
return v_arg_1792_;
}
case 1:
{
lean_object* v_fvarId_1794_; lean_object* v___x_1795_; 
v_fvarId_1794_ = lean_ctor_get(v_arg_1792_, 0);
v___x_1795_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1791_, v_fvarId_1794_);
if (lean_obj_tag(v___x_1795_) == 0)
{
return v_arg_1792_;
}
else
{
lean_object* v_val_1796_; 
lean_dec_ref_known(v_arg_1792_, 1);
v_val_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_val_1796_);
lean_dec_ref_known(v___x_1795_, 1);
switch(lean_obj_tag(v_val_1796_))
{
case 0:
{
lean_object* v___x_1797_; 
v___x_1797_ = lean_box(0);
return v___x_1797_;
}
case 1:
{
lean_object* v_fvarId_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1806_; 
v_fvarId_1798_ = lean_ctor_get(v_val_1796_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_val_1796_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1800_ = v_val_1796_;
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_fvarId_1798_);
lean_dec(v_val_1796_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_fvarId_1798_);
v___x_1803_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
if (v_translator_1793_ == 0)
{
v_arg_1792_ = v___x_1803_;
goto _start;
}
else
{
return v___x_1803_;
}
}
}
}
default: 
{
lean_object* v_expr_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
v_expr_1807_ = lean_ctor_get(v_val_1796_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_val_1796_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v_val_1796_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_expr_1807_);
lean_dec(v_val_1796_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_expr_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
}
}
default: 
{
lean_object* v_expr_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v_expr_1815_ = lean_ctor_get(v_arg_1792_, 0);
lean_inc_ref(v_expr_1815_);
v___x_1816_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1790_, v_s_1791_, v_translator_1793_, v_expr_1815_);
v___x_1817_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1790_, v_arg_1792_, v___x_1816_);
return v___x_1817_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp___boxed(lean_object* v_pu_1818_, lean_object* v_s_1819_, lean_object* v_arg_1820_, lean_object* v_translator_1821_){
_start:
{
uint8_t v_pu_boxed_1822_; uint8_t v_translator_boxed_1823_; lean_object* v_res_1824_; 
v_pu_boxed_1822_ = lean_unbox(v_pu_1818_);
v_translator_boxed_1823_ = lean_unbox(v_translator_1821_);
v_res_1824_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_boxed_1822_, v_s_1819_, v_arg_1820_, v_translator_boxed_1823_);
lean_dec_ref(v_s_1819_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(uint8_t v_pu_1825_, lean_object* v_s_1826_, uint8_t v_translator_1827_, lean_object* v_i_1828_, lean_object* v_as_1829_){
_start:
{
lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1830_ = lean_array_get_size(v_as_1829_);
v___x_1831_ = lean_nat_dec_lt(v_i_1828_, v___x_1830_);
if (v___x_1831_ == 0)
{
lean_dec(v_i_1828_);
return v_as_1829_;
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1833_; size_t v___x_1834_; size_t v___x_1835_; uint8_t v___x_1836_; 
v_a_1832_ = lean_array_fget_borrowed(v_as_1829_, v_i_1828_);
lean_inc(v_a_1832_);
v___x_1833_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1825_, v_s_1826_, v_a_1832_, v_translator_1827_);
v___x_1834_ = lean_ptr_addr(v_a_1832_);
v___x_1835_ = lean_ptr_addr(v___x_1833_);
v___x_1836_ = lean_usize_dec_eq(v___x_1834_, v___x_1835_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = lean_unsigned_to_nat(1u);
v___x_1838_ = lean_nat_add(v_i_1828_, v___x_1837_);
v___x_1839_ = lean_array_fset(v_as_1829_, v_i_1828_, v___x_1833_);
lean_dec(v_i_1828_);
v_i_1828_ = v___x_1838_;
v_as_1829_ = v___x_1839_;
goto _start;
}
else
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_dec(v___x_1833_);
v___x_1841_ = lean_unsigned_to_nat(1u);
v___x_1842_ = lean_nat_add(v_i_1828_, v___x_1841_);
lean_dec(v_i_1828_);
v_i_1828_ = v___x_1842_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0___boxed(lean_object* v_pu_1844_, lean_object* v_s_1845_, lean_object* v_translator_1846_, lean_object* v_i_1847_, lean_object* v_as_1848_){
_start:
{
uint8_t v_pu_boxed_1849_; uint8_t v_translator_boxed_1850_; lean_object* v_res_1851_; 
v_pu_boxed_1849_ = lean_unbox(v_pu_1844_);
v_translator_boxed_1850_ = lean_unbox(v_translator_1846_);
v_res_1851_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_boxed_1849_, v_s_1845_, v_translator_boxed_1850_, v_i_1847_, v_as_1848_);
lean_dec_ref(v_s_1845_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t v_pu_1852_, lean_object* v_s_1853_, lean_object* v_args_1854_, uint8_t v_translator_1855_){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = lean_unsigned_to_nat(0u);
v___x_1857_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_1852_, v_s_1853_, v_translator_1855_, v___x_1856_, v_args_1854_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp___boxed(lean_object* v_pu_1858_, lean_object* v_s_1859_, lean_object* v_args_1860_, lean_object* v_translator_1861_){
_start:
{
uint8_t v_pu_boxed_1862_; uint8_t v_translator_boxed_1863_; lean_object* v_res_1864_; 
v_pu_boxed_1862_ = lean_unbox(v_pu_1858_);
v_translator_boxed_1863_ = lean_unbox(v_translator_1861_);
v_res_1864_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_boxed_1862_, v_s_1859_, v_args_1860_, v_translator_boxed_1863_);
lean_dec_ref(v_s_1859_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t v_pu_1865_, lean_object* v_s_1866_, lean_object* v_e_1867_, uint8_t v_translator_1868_){
_start:
{
lean_object* v_fvarId_1870_; lean_object* v_args_1876_; 
switch(lean_obj_tag(v_e_1867_))
{
case 2:
{
lean_object* v_struct_1879_; lean_object* v___x_1880_; 
v_struct_1879_ = lean_ctor_get(v_e_1867_, 2);
lean_inc(v_struct_1879_);
v___x_1880_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1866_, v_struct_1879_, v_translator_1868_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_fvarId_1881_; lean_object* v___x_1882_; 
v_fvarId_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_fvarId_1881_);
lean_dec_ref_known(v___x_1880_, 1);
v___x_1882_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1865_, v_e_1867_, v_fvarId_1881_);
return v___x_1882_;
}
else
{
lean_object* v___x_1883_; 
lean_dec_ref_known(v_e_1867_, 3);
v___x_1883_ = lean_box(1);
return v___x_1883_;
}
}
case 3:
{
lean_object* v_args_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v_args_1884_ = lean_ctor_get(v_e_1867_, 2);
lean_inc_ref(v_args_1884_);
v___x_1885_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1865_, v_s_1866_, v_args_1884_, v_translator_1868_);
v___x_1886_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1865_, v_e_1867_, v___x_1885_);
return v___x_1886_;
}
case 4:
{
lean_object* v_fvarId_1887_; lean_object* v_args_1888_; lean_object* v___x_1889_; 
v_fvarId_1887_ = lean_ctor_get(v_e_1867_, 0);
v_args_1888_ = lean_ctor_get(v_e_1867_, 1);
lean_inc(v_fvarId_1887_);
v___x_1889_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1866_, v_fvarId_1887_, v_translator_1868_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_fvarId_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v_fvarId_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_fvarId_1890_);
lean_dec_ref_known(v___x_1889_, 1);
lean_inc_ref(v_args_1888_);
v___x_1891_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1865_, v_s_1866_, v_args_1888_, v_translator_1868_);
v___x_1892_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_1865_, v_e_1867_, v_fvarId_1890_, v___x_1891_);
lean_dec_ref_known(v_e_1867_, 2);
return v___x_1892_;
}
else
{
lean_object* v___x_1893_; 
lean_dec_ref_known(v_e_1867_, 2);
v___x_1893_ = lean_box(1);
return v___x_1893_;
}
}
case 5:
{
lean_object* v_args_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v_args_1894_ = lean_ctor_get(v_e_1867_, 1);
lean_inc_ref(v_args_1894_);
v___x_1895_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1865_, v_s_1866_, v_args_1894_, v_translator_1868_);
v___x_1896_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1865_, v_e_1867_, v___x_1895_);
return v___x_1896_;
}
case 6:
{
lean_object* v_var_1897_; 
v_var_1897_ = lean_ctor_get(v_e_1867_, 1);
lean_inc(v_var_1897_);
v_fvarId_1870_ = v_var_1897_;
goto v___jp_1869_;
}
case 7:
{
lean_object* v_var_1898_; 
v_var_1898_ = lean_ctor_get(v_e_1867_, 1);
lean_inc(v_var_1898_);
v_fvarId_1870_ = v_var_1898_;
goto v___jp_1869_;
}
case 8:
{
lean_object* v_var_1899_; lean_object* v___x_1900_; 
v_var_1899_ = lean_ctor_get(v_e_1867_, 2);
lean_inc(v_var_1899_);
v___x_1900_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1866_, v_var_1899_, v_translator_1868_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_fvarId_1901_; lean_object* v___x_1902_; 
v_fvarId_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_fvarId_1901_);
lean_dec_ref_known(v___x_1900_, 1);
v___x_1902_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1865_, v_e_1867_, v_fvarId_1901_);
return v___x_1902_;
}
else
{
lean_object* v___x_1903_; 
lean_dec_ref_known(v_e_1867_, 3);
v___x_1903_ = lean_box(1);
return v___x_1903_;
}
}
case 9:
{
lean_object* v_args_1904_; 
v_args_1904_ = lean_ctor_get(v_e_1867_, 1);
lean_inc_ref(v_args_1904_);
v_args_1876_ = v_args_1904_;
goto v___jp_1875_;
}
case 10:
{
lean_object* v_args_1905_; 
v_args_1905_ = lean_ctor_get(v_e_1867_, 1);
lean_inc_ref(v_args_1905_);
v_args_1876_ = v_args_1905_;
goto v___jp_1875_;
}
case 11:
{
lean_object* v_n_1906_; lean_object* v_var_1907_; lean_object* v___x_1908_; 
v_n_1906_ = lean_ctor_get(v_e_1867_, 0);
lean_inc(v_n_1906_);
v_var_1907_ = lean_ctor_get(v_e_1867_, 1);
lean_inc(v_var_1907_);
v___x_1908_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1866_, v_var_1907_, v_translator_1868_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_fvarId_1909_; lean_object* v___x_1910_; 
v_fvarId_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_fvarId_1909_);
lean_dec_ref_known(v___x_1908_, 1);
v___x_1910_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_1865_, v_e_1867_, v_n_1906_, v_fvarId_1909_);
lean_dec_ref_known(v_e_1867_, 2);
return v___x_1910_;
}
else
{
lean_object* v___x_1911_; 
lean_dec_ref_known(v_e_1867_, 2);
lean_dec(v_n_1906_);
v___x_1911_ = lean_box(1);
return v___x_1911_;
}
}
case 12:
{
lean_object* v_var_1912_; lean_object* v_i_1913_; uint8_t v_updateHeader_1914_; lean_object* v_args_1915_; lean_object* v___x_1916_; 
v_var_1912_ = lean_ctor_get(v_e_1867_, 0);
v_i_1913_ = lean_ctor_get(v_e_1867_, 1);
lean_inc_ref(v_i_1913_);
v_updateHeader_1914_ = lean_ctor_get_uint8(v_e_1867_, sizeof(void*)*3);
v_args_1915_ = lean_ctor_get(v_e_1867_, 2);
lean_inc(v_var_1912_);
v___x_1916_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1866_, v_var_1912_, v_translator_1868_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_fvarId_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v_fvarId_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_fvarId_1917_);
lean_dec_ref_known(v___x_1916_, 1);
lean_inc_ref(v_args_1915_);
v___x_1918_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1865_, v_s_1866_, v_args_1915_, v_translator_1868_);
v___x_1919_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_1865_, v_e_1867_, v_fvarId_1917_, v_i_1913_, v_updateHeader_1914_, v___x_1918_);
return v___x_1919_;
}
else
{
lean_object* v___x_1920_; 
lean_dec_ref(v_i_1913_);
lean_dec_ref_known(v_e_1867_, 3);
v___x_1920_ = lean_box(1);
return v___x_1920_;
}
}
case 13:
{
lean_object* v_ty_1921_; lean_object* v_fvarId_1922_; lean_object* v___x_1923_; 
v_ty_1921_ = lean_ctor_get(v_e_1867_, 0);
lean_inc_ref(v_ty_1921_);
v_fvarId_1922_ = lean_ctor_get(v_e_1867_, 1);
lean_inc(v_fvarId_1922_);
v___x_1923_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1866_, v_fvarId_1922_, v_translator_1868_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_fvarId_1924_; lean_object* v___x_1925_; 
v_fvarId_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_fvarId_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v___x_1925_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_1865_, v_e_1867_, v_ty_1921_, v_fvarId_1924_);
lean_dec_ref_known(v_e_1867_, 2);
return v___x_1925_;
}
else
{
lean_object* v___x_1926_; 
lean_dec_ref_known(v_e_1867_, 2);
lean_dec_ref(v_ty_1921_);
v___x_1926_ = lean_box(1);
return v___x_1926_;
}
}
case 14:
{
lean_object* v_fvarId_1927_; lean_object* v___x_1928_; 
v_fvarId_1927_ = lean_ctor_get(v_e_1867_, 0);
lean_inc(v_fvarId_1927_);
v___x_1928_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1866_, v_fvarId_1927_, v_translator_1868_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_fvarId_1929_; lean_object* v___x_1930_; 
v_fvarId_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_fvarId_1929_);
lean_dec_ref_known(v___x_1928_, 1);
v___x_1930_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_1865_, v_e_1867_, v_fvarId_1929_);
return v___x_1930_;
}
else
{
lean_object* v___x_1931_; 
lean_dec_ref_known(v_e_1867_, 1);
v___x_1931_ = lean_box(1);
return v___x_1931_;
}
}
case 15:
{
lean_object* v_fvarId_1932_; lean_object* v___x_1933_; 
v_fvarId_1932_ = lean_ctor_get(v_e_1867_, 0);
lean_inc(v_fvarId_1932_);
v___x_1933_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1866_, v_fvarId_1932_, v_translator_1868_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_fvarId_1934_; lean_object* v___x_1935_; 
v_fvarId_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_fvarId_1934_);
lean_dec_ref_known(v___x_1933_, 1);
v___x_1935_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_1865_, v_e_1867_, v_fvarId_1934_);
return v___x_1935_;
}
else
{
lean_object* v___x_1936_; 
lean_dec_ref_known(v_e_1867_, 1);
v___x_1936_ = lean_box(1);
return v___x_1936_;
}
}
default: 
{
return v_e_1867_;
}
}
v___jp_1869_:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1866_, v_fvarId_1870_, v_translator_1868_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_fvarId_1872_; lean_object* v___x_1873_; 
v_fvarId_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_fvarId_1872_);
lean_dec_ref_known(v___x_1871_, 1);
v___x_1873_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1865_, v_e_1867_, v_fvarId_1872_);
return v___x_1873_;
}
else
{
lean_object* v___x_1874_; 
lean_dec(v_e_1867_);
v___x_1874_ = lean_box(1);
return v___x_1874_;
}
}
v___jp_1875_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1865_, v_s_1866_, v_args_1876_, v_translator_1868_);
v___x_1878_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1865_, v_e_1867_, v___x_1877_);
return v___x_1878_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp___boxed(lean_object* v_pu_1937_, lean_object* v_s_1938_, lean_object* v_e_1939_, lean_object* v_translator_1940_){
_start:
{
uint8_t v_pu_boxed_1941_; uint8_t v_translator_boxed_1942_; lean_object* v_res_1943_; 
v_pu_boxed_1941_ = lean_unbox(v_pu_1937_);
v_translator_boxed_1942_ = lean_unbox(v_translator_1940_);
v_res_1943_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_boxed_1941_, v_s_1938_, v_e_1939_, v_translator_boxed_1942_);
lean_dec_ref(v_s_1938_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___redArg(lean_object* v_inst_1944_, lean_object* v_inst_1945_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = lean_apply_2(v_inst_1944_, lean_box(0), v_inst_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(uint8_t v_pu_1947_, uint8_t v_t_1948_, lean_object* v_m_1949_, lean_object* v_n_1950_, lean_object* v_inst_1951_, lean_object* v_inst_1952_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = lean_apply_2(v_inst_1951_, lean_box(0), v_inst_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___boxed(lean_object* v_pu_1954_, lean_object* v_t_1955_, lean_object* v_m_1956_, lean_object* v_n_1957_, lean_object* v_inst_1958_, lean_object* v_inst_1959_){
_start:
{
uint8_t v_pu_boxed_1960_; uint8_t v_t_boxed_1961_; lean_object* v_res_1962_; 
v_pu_boxed_1960_ = lean_unbox(v_pu_1954_);
v_t_boxed_1961_ = lean_unbox(v_t_1955_);
v_res_1962_ = l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(v_pu_boxed_1960_, v_t_boxed_1961_, v_m_1956_, v_n_1957_, v_inst_1958_, v_inst_1959_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0(lean_object* v_inst_1963_, lean_object* v_inst_1964_, lean_object* v_f_1965_){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = lean_apply_1(v_inst_1963_, v_f_1965_);
v___x_1967_ = lean_apply_2(v_inst_1964_, lean_box(0), v___x_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg(lean_object* v_inst_1968_, lean_object* v_inst_1969_){
_start:
{
lean_object* v___f_1970_; 
v___f_1970_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1970_, 0, v_inst_1969_);
lean_closure_set(v___f_1970_, 1, v_inst_1968_);
return v___f_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(uint8_t v_pu_1971_, lean_object* v_m_1972_, lean_object* v_n_1973_, lean_object* v_inst_1974_, lean_object* v_inst_1975_){
_start:
{
lean_object* v___f_1976_; 
v___f_1976_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1976_, 0, v_inst_1975_);
lean_closure_set(v___f_1976_, 1, v_inst_1974_);
return v___f_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___boxed(lean_object* v_pu_1977_, lean_object* v_m_1978_, lean_object* v_n_1979_, lean_object* v_inst_1980_, lean_object* v_inst_1981_){
_start:
{
uint8_t v_pu_boxed_1982_; lean_object* v_res_1983_; 
v_pu_boxed_1982_ = lean_unbox(v_pu_1977_);
v_res_1983_ = l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(v_pu_boxed_1982_, v_m_1978_, v_n_1979_, v_inst_1980_, v_inst_1981_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___lam__0(lean_object* v___x_1984_, lean_object* v___x_1985_, lean_object* v_fvarId_1986_, lean_object* v_arg_1987_, lean_object* v_s_1988_){
_start:
{
lean_object* v___y_1990_; lean_object* v_i_1991_; lean_object* v___y_2007_; lean_object* v_i_2008_; lean_object* v___y_2014_; lean_object* v___x_2023_; 
lean_inc(v_fvarId_1986_);
lean_inc_ref(v___x_1985_);
lean_inc_ref(v___x_1984_);
v___x_2023_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_1984_, v___x_1985_, v_s_1988_, v_fvarId_1986_);
switch(lean_obj_tag(v___x_2023_))
{
case 0:
{
lean_object* v_index_2024_; lean_object* v_size_2025_; lean_object* v___x_2026_; 
lean_dec_ref(v___x_1985_);
lean_dec_ref(v___x_1984_);
v_index_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_index_2024_);
lean_dec_ref_known(v___x_2023_, 3);
v_size_2025_ = lean_ctor_get(v_s_1988_, 0);
lean_inc(v_size_2025_);
v___x_2026_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_1988_, v_size_2025_, v_index_2024_, v_fvarId_1986_, v_arg_1987_);
lean_dec(v_index_2024_);
return v___x_2026_;
}
case 1:
{
lean_object* v_index_2027_; lean_object* v_size_2028_; lean_object* v_keyArray_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v_index_2027_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_index_2027_);
lean_dec_ref_known(v___x_2023_, 1);
v_size_2028_ = lean_ctor_get(v_s_1988_, 0);
v_keyArray_2029_ = lean_ctor_get(v_s_1988_, 1);
v___x_2030_ = lean_unsigned_to_nat(1u);
v___x_2031_ = lean_nat_add(v_size_2028_, v___x_2030_);
v___x_2032_ = lean_array_get_size(v_keyArray_2029_);
v___x_2033_ = lean_nat_dec_lt(v___x_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_dec(v___x_2031_);
lean_dec(v_index_2027_);
goto v___jp_1996_;
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2034_ = lean_unsigned_to_nat(4u);
v___x_2035_ = lean_nat_mul(v___x_2031_, v___x_2034_);
v___x_2036_ = lean_unsigned_to_nat(3u);
v___x_2037_ = lean_nat_mul(v___x_2032_, v___x_2036_);
v___x_2038_ = lean_nat_dec_le(v___x_2035_, v___x_2037_);
lean_dec(v___x_2037_);
lean_dec(v___x_2035_);
if (v___x_2038_ == 0)
{
lean_dec(v___x_2031_);
lean_dec(v_index_2027_);
goto v___jp_1996_;
}
else
{
lean_object* v___x_2039_; 
lean_dec_ref(v___x_1985_);
lean_dec_ref(v___x_1984_);
v___x_2039_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_1988_, v___x_2031_, v_index_2027_, v_fvarId_1986_, v_arg_1987_);
lean_dec(v_index_2027_);
return v___x_2039_;
}
}
}
default: 
{
lean_object* v_size_2040_; lean_object* v_keyArray_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; 
v_size_2040_ = lean_ctor_get(v_s_1988_, 0);
v_keyArray_2041_ = lean_ctor_get(v_s_1988_, 1);
v___x_2042_ = lean_unsigned_to_nat(1u);
v___x_2043_ = lean_nat_add(v_size_2040_, v___x_2042_);
v___x_2044_ = lean_array_get_size(v_keyArray_2041_);
v___x_2045_ = lean_nat_dec_lt(v___x_2043_, v___x_2044_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; 
lean_dec(v___x_2043_);
lean_inc_ref(v___x_1985_);
lean_inc_ref(v___x_1984_);
v___x_2046_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_1984_, v___x_1985_, v_s_1988_);
v___y_2014_ = v___x_2046_;
goto v___jp_2013_;
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
v___x_2047_ = lean_unsigned_to_nat(4u);
v___x_2048_ = lean_nat_mul(v___x_2043_, v___x_2047_);
lean_dec(v___x_2043_);
v___x_2049_ = lean_unsigned_to_nat(3u);
v___x_2050_ = lean_nat_mul(v___x_2044_, v___x_2049_);
v___x_2051_ = lean_nat_dec_le(v___x_2048_, v___x_2050_);
lean_dec(v___x_2050_);
lean_dec(v___x_2048_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; 
lean_inc_ref(v___x_1985_);
lean_inc_ref(v___x_1984_);
v___x_2052_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_1984_, v___x_1985_, v_s_1988_);
v___y_2014_ = v___x_2052_;
goto v___jp_2013_;
}
else
{
v___y_2014_ = v_s_1988_;
goto v___jp_2013_;
}
}
}
}
v___jp_1989_:
{
lean_object* v_size_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v_size_1992_ = lean_ctor_get(v___y_1990_, 0);
v___x_1993_ = lean_unsigned_to_nat(1u);
v___x_1994_ = lean_nat_add(v_size_1992_, v___x_1993_);
v___x_1995_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1990_, v___x_1994_, v_i_1991_, v_fvarId_1986_, v_arg_1987_);
lean_dec(v_i_1991_);
return v___x_1995_;
}
v___jp_1996_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
lean_inc_ref(v___x_1985_);
lean_inc_ref(v___x_1984_);
v___x_1997_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_1984_, v___x_1985_, v_s_1988_);
lean_inc(v_fvarId_1986_);
v___x_1998_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_1984_, v___x_1985_, v___x_1997_, v_fvarId_1986_);
switch(lean_obj_tag(v___x_1998_))
{
case 0:
{
lean_object* v_index_1999_; lean_object* v_size_2000_; lean_object* v___x_2001_; 
v_index_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_index_1999_);
lean_dec_ref_known(v___x_1998_, 3);
v_size_2000_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_size_2000_);
v___x_2001_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1997_, v_size_2000_, v_index_1999_, v_fvarId_1986_, v_arg_1987_);
lean_dec(v_index_1999_);
return v___x_2001_;
}
case 1:
{
lean_object* v_index_2002_; 
v_index_2002_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_index_2002_);
lean_dec_ref_known(v___x_1998_, 1);
v___y_1990_ = v___x_1997_;
v_i_1991_ = v_index_2002_;
goto v___jp_1989_;
}
default: 
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = lean_unsigned_to_nat(0u);
v___x_2004_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1997_, v___x_2003_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_index_2005_; 
v_index_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_index_2005_);
lean_dec_ref_known(v___x_2004_, 1);
v___y_1990_ = v___x_1997_;
v_i_1991_ = v_index_2005_;
goto v___jp_1989_;
}
else
{
lean_dec(v_arg_1987_);
lean_dec(v_fvarId_1986_);
return v___x_1997_;
}
}
}
}
v___jp_2006_:
{
lean_object* v_size_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_size_2009_ = lean_ctor_get(v___y_2007_, 0);
v___x_2010_ = lean_unsigned_to_nat(1u);
v___x_2011_ = lean_nat_add(v_size_2009_, v___x_2010_);
v___x_2012_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2007_, v___x_2011_, v_i_2008_, v_fvarId_1986_, v_arg_1987_);
lean_dec(v_i_2008_);
return v___x_2012_;
}
v___jp_2013_:
{
lean_object* v___x_2015_; 
lean_inc(v_fvarId_1986_);
v___x_2015_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_1984_, v___x_1985_, v___y_2014_, v_fvarId_1986_);
switch(lean_obj_tag(v___x_2015_))
{
case 0:
{
lean_object* v_index_2016_; lean_object* v_size_2017_; lean_object* v___x_2018_; 
v_index_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_index_2016_);
lean_dec_ref_known(v___x_2015_, 3);
v_size_2017_ = lean_ctor_get(v___y_2014_, 0);
lean_inc(v_size_2017_);
v___x_2018_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2014_, v_size_2017_, v_index_2016_, v_fvarId_1986_, v_arg_1987_);
lean_dec(v_index_2016_);
return v___x_2018_;
}
case 1:
{
lean_object* v_index_2019_; 
v_index_2019_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_index_2019_);
lean_dec_ref_known(v___x_2015_, 1);
v___y_2007_ = v___y_2014_;
v_i_2008_ = v_index_2019_;
goto v___jp_2006_;
}
default: 
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_unsigned_to_nat(0u);
v___x_2021_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2014_, v___x_2020_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_index_2022_; 
v_index_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_index_2022_);
lean_dec_ref_known(v___x_2021_, 1);
v___y_2007_ = v___y_2014_;
v_i_2008_ = v_index_2022_;
goto v___jp_2006_;
}
else
{
lean_dec(v_arg_1987_);
lean_dec(v_fvarId_1986_);
return v___y_2014_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg(lean_object* v_inst_2055_, lean_object* v_fvarId_2056_, lean_object* v_arg_2057_){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___f_2060_; lean_object* v___x_2061_; 
v___x_2058_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_2059_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_2060_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2060_, 0, v___x_2058_);
lean_closure_set(v___f_2060_, 1, v___x_2059_);
lean_closure_set(v___f_2060_, 2, v_fvarId_2056_);
lean_closure_set(v___f_2060_, 3, v_arg_2057_);
v___x_2061_ = lean_apply_1(v_inst_2055_, v___f_2060_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst(lean_object* v_m_2062_, uint8_t v_pu_2063_, lean_object* v_inst_2064_, lean_object* v_fvarId_2065_, lean_object* v_arg_2066_){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___f_2069_; lean_object* v___x_2070_; 
v___x_2067_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_2068_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_2069_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2069_, 0, v___x_2067_);
lean_closure_set(v___f_2069_, 1, v___x_2068_);
lean_closure_set(v___f_2069_, 2, v_fvarId_2065_);
lean_closure_set(v___f_2069_, 3, v_arg_2066_);
v___x_2070_ = lean_apply_1(v_inst_2064_, v___f_2069_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___boxed(lean_object* v_m_2071_, lean_object* v_pu_2072_, lean_object* v_inst_2073_, lean_object* v_fvarId_2074_, lean_object* v_arg_2075_){
_start:
{
uint8_t v_pu_boxed_2076_; lean_object* v_res_2077_; 
v_pu_boxed_2076_ = lean_unbox(v_pu_2072_);
v_res_2077_ = l_Lean_Compiler_LCNF_addSubst(v_m_2071_, v_pu_boxed_2076_, v_inst_2073_, v_fvarId_2074_, v_arg_2075_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0(lean_object* v_fvarId_x27_2078_, lean_object* v___x_2079_, lean_object* v___x_2080_, lean_object* v_fvarId_2081_, lean_object* v_s_2082_){
_start:
{
lean_object* v___x_2083_; lean_object* v___y_2085_; lean_object* v_i_2086_; lean_object* v___y_2092_; lean_object* v___y_2102_; lean_object* v_i_2103_; lean_object* v___x_2118_; 
v___x_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2083_, 0, v_fvarId_x27_2078_);
lean_inc(v_fvarId_2081_);
lean_inc_ref(v___x_2080_);
lean_inc_ref(v___x_2079_);
v___x_2118_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2079_, v___x_2080_, v_s_2082_, v_fvarId_2081_);
switch(lean_obj_tag(v___x_2118_))
{
case 0:
{
lean_object* v_index_2119_; lean_object* v_size_2120_; lean_object* v___x_2121_; 
lean_dec_ref(v___x_2080_);
lean_dec_ref(v___x_2079_);
v_index_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_index_2119_);
lean_dec_ref_known(v___x_2118_, 3);
v_size_2120_ = lean_ctor_get(v_s_2082_, 0);
lean_inc(v_size_2120_);
v___x_2121_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_2082_, v_size_2120_, v_index_2119_, v_fvarId_2081_, v___x_2083_);
lean_dec(v_index_2119_);
return v___x_2121_;
}
case 1:
{
lean_object* v_index_2122_; lean_object* v_size_2123_; lean_object* v_keyArray_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; 
v_index_2122_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_index_2122_);
lean_dec_ref_known(v___x_2118_, 1);
v_size_2123_ = lean_ctor_get(v_s_2082_, 0);
v_keyArray_2124_ = lean_ctor_get(v_s_2082_, 1);
v___x_2125_ = lean_unsigned_to_nat(1u);
v___x_2126_ = lean_nat_add(v_size_2123_, v___x_2125_);
v___x_2127_ = lean_array_get_size(v_keyArray_2124_);
v___x_2128_ = lean_nat_dec_lt(v___x_2126_, v___x_2127_);
if (v___x_2128_ == 0)
{
lean_dec(v___x_2126_);
lean_dec(v_index_2122_);
goto v___jp_2108_;
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2129_ = lean_unsigned_to_nat(4u);
v___x_2130_ = lean_nat_mul(v___x_2126_, v___x_2129_);
v___x_2131_ = lean_unsigned_to_nat(3u);
v___x_2132_ = lean_nat_mul(v___x_2127_, v___x_2131_);
v___x_2133_ = lean_nat_dec_le(v___x_2130_, v___x_2132_);
lean_dec(v___x_2132_);
lean_dec(v___x_2130_);
if (v___x_2133_ == 0)
{
lean_dec(v___x_2126_);
lean_dec(v_index_2122_);
goto v___jp_2108_;
}
else
{
lean_object* v___x_2134_; 
lean_dec_ref(v___x_2080_);
lean_dec_ref(v___x_2079_);
v___x_2134_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_2082_, v___x_2126_, v_index_2122_, v_fvarId_2081_, v___x_2083_);
lean_dec(v_index_2122_);
return v___x_2134_;
}
}
}
default: 
{
lean_object* v_size_2135_; lean_object* v_keyArray_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v_size_2135_ = lean_ctor_get(v_s_2082_, 0);
v_keyArray_2136_ = lean_ctor_get(v_s_2082_, 1);
v___x_2137_ = lean_unsigned_to_nat(1u);
v___x_2138_ = lean_nat_add(v_size_2135_, v___x_2137_);
v___x_2139_ = lean_array_get_size(v_keyArray_2136_);
v___x_2140_ = lean_nat_dec_lt(v___x_2138_, v___x_2139_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; 
lean_dec(v___x_2138_);
lean_inc_ref(v___x_2080_);
lean_inc_ref(v___x_2079_);
v___x_2141_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2079_, v___x_2080_, v_s_2082_);
v___y_2092_ = v___x_2141_;
goto v___jp_2091_;
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v___x_2142_ = lean_unsigned_to_nat(4u);
v___x_2143_ = lean_nat_mul(v___x_2138_, v___x_2142_);
lean_dec(v___x_2138_);
v___x_2144_ = lean_unsigned_to_nat(3u);
v___x_2145_ = lean_nat_mul(v___x_2139_, v___x_2144_);
v___x_2146_ = lean_nat_dec_le(v___x_2143_, v___x_2145_);
lean_dec(v___x_2145_);
lean_dec(v___x_2143_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; 
lean_inc_ref(v___x_2080_);
lean_inc_ref(v___x_2079_);
v___x_2147_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2079_, v___x_2080_, v_s_2082_);
v___y_2092_ = v___x_2147_;
goto v___jp_2091_;
}
else
{
v___y_2092_ = v_s_2082_;
goto v___jp_2091_;
}
}
}
}
v___jp_2084_:
{
lean_object* v_size_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v_size_2087_ = lean_ctor_get(v___y_2085_, 0);
v___x_2088_ = lean_unsigned_to_nat(1u);
v___x_2089_ = lean_nat_add(v_size_2087_, v___x_2088_);
v___x_2090_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2085_, v___x_2089_, v_i_2086_, v_fvarId_2081_, v___x_2083_);
lean_dec(v_i_2086_);
return v___x_2090_;
}
v___jp_2091_:
{
lean_object* v___x_2093_; 
lean_inc(v_fvarId_2081_);
v___x_2093_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2079_, v___x_2080_, v___y_2092_, v_fvarId_2081_);
switch(lean_obj_tag(v___x_2093_))
{
case 0:
{
lean_object* v_index_2094_; lean_object* v_size_2095_; lean_object* v___x_2096_; 
v_index_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_index_2094_);
lean_dec_ref_known(v___x_2093_, 3);
v_size_2095_ = lean_ctor_get(v___y_2092_, 0);
lean_inc(v_size_2095_);
v___x_2096_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2092_, v_size_2095_, v_index_2094_, v_fvarId_2081_, v___x_2083_);
lean_dec(v_index_2094_);
return v___x_2096_;
}
case 1:
{
lean_object* v_index_2097_; 
v_index_2097_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_index_2097_);
lean_dec_ref_known(v___x_2093_, 1);
v___y_2085_ = v___y_2092_;
v_i_2086_ = v_index_2097_;
goto v___jp_2084_;
}
default: 
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_unsigned_to_nat(0u);
v___x_2099_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2092_, v___x_2098_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_index_2100_; 
v_index_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_index_2100_);
lean_dec_ref_known(v___x_2099_, 1);
v___y_2085_ = v___y_2092_;
v_i_2086_ = v_index_2100_;
goto v___jp_2084_;
}
else
{
lean_dec_ref_known(v___x_2083_, 1);
lean_dec(v_fvarId_2081_);
return v___y_2092_;
}
}
}
}
v___jp_2101_:
{
lean_object* v_size_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v_size_2104_ = lean_ctor_get(v___y_2102_, 0);
v___x_2105_ = lean_unsigned_to_nat(1u);
v___x_2106_ = lean_nat_add(v_size_2104_, v___x_2105_);
v___x_2107_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2102_, v___x_2106_, v_i_2103_, v_fvarId_2081_, v___x_2083_);
lean_dec(v_i_2103_);
return v___x_2107_;
}
v___jp_2108_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
lean_inc_ref(v___x_2080_);
lean_inc_ref(v___x_2079_);
v___x_2109_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2079_, v___x_2080_, v_s_2082_);
lean_inc(v_fvarId_2081_);
v___x_2110_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2079_, v___x_2080_, v___x_2109_, v_fvarId_2081_);
switch(lean_obj_tag(v___x_2110_))
{
case 0:
{
lean_object* v_index_2111_; lean_object* v_size_2112_; lean_object* v___x_2113_; 
v_index_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_index_2111_);
lean_dec_ref_known(v___x_2110_, 3);
v_size_2112_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_size_2112_);
v___x_2113_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2109_, v_size_2112_, v_index_2111_, v_fvarId_2081_, v___x_2083_);
lean_dec(v_index_2111_);
return v___x_2113_;
}
case 1:
{
lean_object* v_index_2114_; 
v_index_2114_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_index_2114_);
lean_dec_ref_known(v___x_2110_, 1);
v___y_2102_ = v___x_2109_;
v_i_2103_ = v_index_2114_;
goto v___jp_2101_;
}
default: 
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = lean_unsigned_to_nat(0u);
v___x_2116_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2109_, v___x_2115_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_index_2117_; 
v_index_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_index_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v___y_2102_ = v___x_2109_;
v_i_2103_ = v_index_2117_;
goto v___jp_2101_;
}
else
{
lean_dec_ref_known(v___x_2083_, 1);
lean_dec(v_fvarId_2081_);
return v___x_2109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg(lean_object* v_inst_2148_, lean_object* v_fvarId_2149_, lean_object* v_fvarId_x27_2150_){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___f_2153_; lean_object* v___x_2154_; 
v___x_2151_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_2152_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_2153_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2153_, 0, v_fvarId_x27_2150_);
lean_closure_set(v___f_2153_, 1, v___x_2151_);
lean_closure_set(v___f_2153_, 2, v___x_2152_);
lean_closure_set(v___f_2153_, 3, v_fvarId_2149_);
v___x_2154_ = lean_apply_1(v_inst_2148_, v___f_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst(lean_object* v_m_2155_, uint8_t v_ph_2156_, lean_object* v_inst_2157_, lean_object* v_fvarId_2158_, lean_object* v_fvarId_x27_2159_){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___f_2162_; lean_object* v___x_2163_; 
v___x_2160_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_2161_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_2162_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2162_, 0, v_fvarId_x27_2159_);
lean_closure_set(v___f_2162_, 1, v___x_2160_);
lean_closure_set(v___f_2162_, 2, v___x_2161_);
lean_closure_set(v___f_2162_, 3, v_fvarId_2158_);
v___x_2163_ = lean_apply_1(v_inst_2157_, v___f_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___boxed(lean_object* v_m_2164_, lean_object* v_ph_2165_, lean_object* v_inst_2166_, lean_object* v_fvarId_2167_, lean_object* v_fvarId_x27_2168_){
_start:
{
uint8_t v_ph_boxed_2169_; lean_object* v_res_2170_; 
v_ph_boxed_2169_ = lean_unbox(v_ph_2165_);
v_res_2170_ = l_Lean_Compiler_LCNF_addFVarSubst(v_m_2164_, v_ph_boxed_2169_, v_inst_2166_, v_fvarId_2167_, v_fvarId_x27_2168_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(lean_object* v_fvarId_2171_, uint8_t v_t_2172_, lean_object* v_toPure_2173_, lean_object* v_____do__lift_2174_){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_____do__lift_2174_, v_fvarId_2171_, v_t_2172_);
v___x_2176_ = lean_apply_2(v_toPure_2173_, lean_box(0), v___x_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed(lean_object* v_fvarId_2177_, lean_object* v_t_2178_, lean_object* v_toPure_2179_, lean_object* v_____do__lift_2180_){
_start:
{
uint8_t v_t_boxed_2181_; lean_object* v_res_2182_; 
v_t_boxed_2181_ = lean_unbox(v_t_2178_);
v_res_2182_ = l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(v_fvarId_2177_, v_t_boxed_2181_, v_toPure_2179_, v_____do__lift_2180_);
lean_dec_ref(v_____do__lift_2180_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg(uint8_t v_t_2183_, lean_object* v_inst_2184_, lean_object* v_inst_2185_, lean_object* v_fvarId_2186_){
_start:
{
lean_object* v_toApplicative_2187_; lean_object* v_toBind_2188_; lean_object* v_toPure_2189_; lean_object* v___x_2190_; lean_object* v___f_2191_; lean_object* v___x_2192_; 
v_toApplicative_2187_ = lean_ctor_get(v_inst_2185_, 0);
lean_inc_ref(v_toApplicative_2187_);
v_toBind_2188_ = lean_ctor_get(v_inst_2185_, 1);
lean_inc(v_toBind_2188_);
lean_dec_ref(v_inst_2185_);
v_toPure_2189_ = lean_ctor_get(v_toApplicative_2187_, 1);
lean_inc(v_toPure_2189_);
lean_dec_ref(v_toApplicative_2187_);
v___x_2190_ = lean_box(v_t_2183_);
v___f_2191_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2191_, 0, v_fvarId_2186_);
lean_closure_set(v___f_2191_, 1, v___x_2190_);
lean_closure_set(v___f_2191_, 2, v_toPure_2189_);
v___x_2192_ = lean_apply_4(v_toBind_2188_, lean_box(0), lean_box(0), v_inst_2184_, v___f_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___boxed(lean_object* v_t_2193_, lean_object* v_inst_2194_, lean_object* v_inst_2195_, lean_object* v_fvarId_2196_){
_start:
{
uint8_t v_t_boxed_2197_; lean_object* v_res_2198_; 
v_t_boxed_2197_ = lean_unbox(v_t_2193_);
v_res_2198_ = l_Lean_Compiler_LCNF_normFVar___redArg(v_t_boxed_2197_, v_inst_2194_, v_inst_2195_, v_fvarId_2196_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar(lean_object* v_m_2199_, uint8_t v_pu_2200_, uint8_t v_t_2201_, lean_object* v_inst_2202_, lean_object* v_inst_2203_, lean_object* v_fvarId_2204_){
_start:
{
lean_object* v_toApplicative_2205_; lean_object* v_toBind_2206_; lean_object* v_toPure_2207_; lean_object* v___x_2208_; lean_object* v___f_2209_; lean_object* v___x_2210_; 
v_toApplicative_2205_ = lean_ctor_get(v_inst_2203_, 0);
lean_inc_ref(v_toApplicative_2205_);
v_toBind_2206_ = lean_ctor_get(v_inst_2203_, 1);
lean_inc(v_toBind_2206_);
lean_dec_ref(v_inst_2203_);
v_toPure_2207_ = lean_ctor_get(v_toApplicative_2205_, 1);
lean_inc(v_toPure_2207_);
lean_dec_ref(v_toApplicative_2205_);
v___x_2208_ = lean_box(v_t_2201_);
v___f_2209_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2209_, 0, v_fvarId_2204_);
lean_closure_set(v___f_2209_, 1, v___x_2208_);
lean_closure_set(v___f_2209_, 2, v_toPure_2207_);
v___x_2210_ = lean_apply_4(v_toBind_2206_, lean_box(0), lean_box(0), v_inst_2202_, v___f_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___boxed(lean_object* v_m_2211_, lean_object* v_pu_2212_, lean_object* v_t_2213_, lean_object* v_inst_2214_, lean_object* v_inst_2215_, lean_object* v_fvarId_2216_){
_start:
{
uint8_t v_pu_boxed_2217_; uint8_t v_t_boxed_2218_; lean_object* v_res_2219_; 
v_pu_boxed_2217_ = lean_unbox(v_pu_2212_);
v_t_boxed_2218_ = lean_unbox(v_t_2213_);
v_res_2219_ = l_Lean_Compiler_LCNF_normFVar(v_m_2211_, v_pu_boxed_2217_, v_t_boxed_2218_, v_inst_2214_, v_inst_2215_, v_fvarId_2216_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(uint8_t v_pu_2220_, uint8_t v_t_2221_, lean_object* v_e_2222_, lean_object* v_toPure_2223_, lean_object* v_____do__lift_2224_){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2220_, v_____do__lift_2224_, v_t_2221_, v_e_2222_);
v___x_2226_ = lean_apply_2(v_toPure_2223_, lean_box(0), v___x_2225_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed(lean_object* v_pu_2227_, lean_object* v_t_2228_, lean_object* v_e_2229_, lean_object* v_toPure_2230_, lean_object* v_____do__lift_2231_){
_start:
{
uint8_t v_pu_boxed_2232_; uint8_t v_t_boxed_2233_; lean_object* v_res_2234_; 
v_pu_boxed_2232_ = lean_unbox(v_pu_2227_);
v_t_boxed_2233_ = lean_unbox(v_t_2228_);
v_res_2234_ = l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(v_pu_boxed_2232_, v_t_boxed_2233_, v_e_2229_, v_toPure_2230_, v_____do__lift_2231_);
lean_dec_ref(v_____do__lift_2231_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg(uint8_t v_pu_2235_, uint8_t v_t_2236_, lean_object* v_inst_2237_, lean_object* v_inst_2238_, lean_object* v_e_2239_){
_start:
{
lean_object* v_toApplicative_2240_; lean_object* v_toBind_2241_; lean_object* v_toPure_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___f_2245_; lean_object* v___x_2246_; 
v_toApplicative_2240_ = lean_ctor_get(v_inst_2238_, 0);
lean_inc_ref(v_toApplicative_2240_);
v_toBind_2241_ = lean_ctor_get(v_inst_2238_, 1);
lean_inc(v_toBind_2241_);
lean_dec_ref(v_inst_2238_);
v_toPure_2242_ = lean_ctor_get(v_toApplicative_2240_, 1);
lean_inc(v_toPure_2242_);
lean_dec_ref(v_toApplicative_2240_);
v___x_2243_ = lean_box(v_pu_2235_);
v___x_2244_ = lean_box(v_t_2236_);
v___f_2245_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2245_, 0, v___x_2243_);
lean_closure_set(v___f_2245_, 1, v___x_2244_);
lean_closure_set(v___f_2245_, 2, v_e_2239_);
lean_closure_set(v___f_2245_, 3, v_toPure_2242_);
v___x_2246_ = lean_apply_4(v_toBind_2241_, lean_box(0), lean_box(0), v_inst_2237_, v___f_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___boxed(lean_object* v_pu_2247_, lean_object* v_t_2248_, lean_object* v_inst_2249_, lean_object* v_inst_2250_, lean_object* v_e_2251_){
_start:
{
uint8_t v_pu_boxed_2252_; uint8_t v_t_boxed_2253_; lean_object* v_res_2254_; 
v_pu_boxed_2252_ = lean_unbox(v_pu_2247_);
v_t_boxed_2253_ = lean_unbox(v_t_2248_);
v_res_2254_ = l_Lean_Compiler_LCNF_normExpr___redArg(v_pu_boxed_2252_, v_t_boxed_2253_, v_inst_2249_, v_inst_2250_, v_e_2251_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr(lean_object* v_m_2255_, uint8_t v_pu_2256_, uint8_t v_t_2257_, lean_object* v_inst_2258_, lean_object* v_inst_2259_, lean_object* v_e_2260_){
_start:
{
lean_object* v_toApplicative_2261_; lean_object* v_toBind_2262_; lean_object* v_toPure_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___f_2266_; lean_object* v___x_2267_; 
v_toApplicative_2261_ = lean_ctor_get(v_inst_2259_, 0);
lean_inc_ref(v_toApplicative_2261_);
v_toBind_2262_ = lean_ctor_get(v_inst_2259_, 1);
lean_inc(v_toBind_2262_);
lean_dec_ref(v_inst_2259_);
v_toPure_2263_ = lean_ctor_get(v_toApplicative_2261_, 1);
lean_inc(v_toPure_2263_);
lean_dec_ref(v_toApplicative_2261_);
v___x_2264_ = lean_box(v_pu_2256_);
v___x_2265_ = lean_box(v_t_2257_);
v___f_2266_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2266_, 0, v___x_2264_);
lean_closure_set(v___f_2266_, 1, v___x_2265_);
lean_closure_set(v___f_2266_, 2, v_e_2260_);
lean_closure_set(v___f_2266_, 3, v_toPure_2263_);
v___x_2267_ = lean_apply_4(v_toBind_2262_, lean_box(0), lean_box(0), v_inst_2258_, v___f_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___boxed(lean_object* v_m_2268_, lean_object* v_pu_2269_, lean_object* v_t_2270_, lean_object* v_inst_2271_, lean_object* v_inst_2272_, lean_object* v_e_2273_){
_start:
{
uint8_t v_pu_boxed_2274_; uint8_t v_t_boxed_2275_; lean_object* v_res_2276_; 
v_pu_boxed_2274_ = lean_unbox(v_pu_2269_);
v_t_boxed_2275_ = lean_unbox(v_t_2270_);
v_res_2276_ = l_Lean_Compiler_LCNF_normExpr(v_m_2268_, v_pu_boxed_2274_, v_t_boxed_2275_, v_inst_2271_, v_inst_2272_, v_e_2273_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0(uint8_t v_pu_2277_, lean_object* v_arg_2278_, uint8_t v_t_2279_, lean_object* v_toPure_2280_, lean_object* v_____do__lift_2281_){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2277_, v_____do__lift_2281_, v_arg_2278_, v_t_2279_);
v___x_2283_ = lean_apply_2(v_toPure_2280_, lean_box(0), v___x_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed(lean_object* v_pu_2284_, lean_object* v_arg_2285_, lean_object* v_t_2286_, lean_object* v_toPure_2287_, lean_object* v_____do__lift_2288_){
_start:
{
uint8_t v_pu_boxed_2289_; uint8_t v_t_boxed_2290_; lean_object* v_res_2291_; 
v_pu_boxed_2289_ = lean_unbox(v_pu_2284_);
v_t_boxed_2290_ = lean_unbox(v_t_2286_);
v_res_2291_ = l_Lean_Compiler_LCNF_normArg___redArg___lam__0(v_pu_boxed_2289_, v_arg_2285_, v_t_boxed_2290_, v_toPure_2287_, v_____do__lift_2288_);
lean_dec_ref(v_____do__lift_2288_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg(uint8_t v_pu_2292_, uint8_t v_t_2293_, lean_object* v_inst_2294_, lean_object* v_inst_2295_, lean_object* v_arg_2296_){
_start:
{
lean_object* v_toApplicative_2297_; lean_object* v_toBind_2298_; lean_object* v_toPure_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___f_2302_; lean_object* v___x_2303_; 
v_toApplicative_2297_ = lean_ctor_get(v_inst_2295_, 0);
lean_inc_ref(v_toApplicative_2297_);
v_toBind_2298_ = lean_ctor_get(v_inst_2295_, 1);
lean_inc(v_toBind_2298_);
lean_dec_ref(v_inst_2295_);
v_toPure_2299_ = lean_ctor_get(v_toApplicative_2297_, 1);
lean_inc(v_toPure_2299_);
lean_dec_ref(v_toApplicative_2297_);
v___x_2300_ = lean_box(v_pu_2292_);
v___x_2301_ = lean_box(v_t_2293_);
v___f_2302_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2302_, 0, v___x_2300_);
lean_closure_set(v___f_2302_, 1, v_arg_2296_);
lean_closure_set(v___f_2302_, 2, v___x_2301_);
lean_closure_set(v___f_2302_, 3, v_toPure_2299_);
v___x_2303_ = lean_apply_4(v_toBind_2298_, lean_box(0), lean_box(0), v_inst_2294_, v___f_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___boxed(lean_object* v_pu_2304_, lean_object* v_t_2305_, lean_object* v_inst_2306_, lean_object* v_inst_2307_, lean_object* v_arg_2308_){
_start:
{
uint8_t v_pu_boxed_2309_; uint8_t v_t_boxed_2310_; lean_object* v_res_2311_; 
v_pu_boxed_2309_ = lean_unbox(v_pu_2304_);
v_t_boxed_2310_ = lean_unbox(v_t_2305_);
v_res_2311_ = l_Lean_Compiler_LCNF_normArg___redArg(v_pu_boxed_2309_, v_t_boxed_2310_, v_inst_2306_, v_inst_2307_, v_arg_2308_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg(lean_object* v_m_2312_, uint8_t v_pu_2313_, uint8_t v_t_2314_, lean_object* v_inst_2315_, lean_object* v_inst_2316_, lean_object* v_arg_2317_){
_start:
{
lean_object* v_toApplicative_2318_; lean_object* v_toBind_2319_; lean_object* v_toPure_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___f_2323_; lean_object* v___x_2324_; 
v_toApplicative_2318_ = lean_ctor_get(v_inst_2316_, 0);
lean_inc_ref(v_toApplicative_2318_);
v_toBind_2319_ = lean_ctor_get(v_inst_2316_, 1);
lean_inc(v_toBind_2319_);
lean_dec_ref(v_inst_2316_);
v_toPure_2320_ = lean_ctor_get(v_toApplicative_2318_, 1);
lean_inc(v_toPure_2320_);
lean_dec_ref(v_toApplicative_2318_);
v___x_2321_ = lean_box(v_pu_2313_);
v___x_2322_ = lean_box(v_t_2314_);
v___f_2323_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2323_, 0, v___x_2321_);
lean_closure_set(v___f_2323_, 1, v_arg_2317_);
lean_closure_set(v___f_2323_, 2, v___x_2322_);
lean_closure_set(v___f_2323_, 3, v_toPure_2320_);
v___x_2324_ = lean_apply_4(v_toBind_2319_, lean_box(0), lean_box(0), v_inst_2315_, v___f_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___boxed(lean_object* v_m_2325_, lean_object* v_pu_2326_, lean_object* v_t_2327_, lean_object* v_inst_2328_, lean_object* v_inst_2329_, lean_object* v_arg_2330_){
_start:
{
uint8_t v_pu_boxed_2331_; uint8_t v_t_boxed_2332_; lean_object* v_res_2333_; 
v_pu_boxed_2331_ = lean_unbox(v_pu_2326_);
v_t_boxed_2332_ = lean_unbox(v_t_2327_);
v_res_2333_ = l_Lean_Compiler_LCNF_normArg(v_m_2325_, v_pu_boxed_2331_, v_t_boxed_2332_, v_inst_2328_, v_inst_2329_, v_arg_2330_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(uint8_t v_pu_2334_, lean_object* v_e_2335_, uint8_t v_t_2336_, lean_object* v_toPure_2337_, lean_object* v_____do__lift_2338_){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_2334_, v_____do__lift_2338_, v_e_2335_, v_t_2336_);
v___x_2340_ = lean_apply_2(v_toPure_2337_, lean_box(0), v___x_2339_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed(lean_object* v_pu_2341_, lean_object* v_e_2342_, lean_object* v_t_2343_, lean_object* v_toPure_2344_, lean_object* v_____do__lift_2345_){
_start:
{
uint8_t v_pu_boxed_2346_; uint8_t v_t_boxed_2347_; lean_object* v_res_2348_; 
v_pu_boxed_2346_ = lean_unbox(v_pu_2341_);
v_t_boxed_2347_ = lean_unbox(v_t_2343_);
v_res_2348_ = l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(v_pu_boxed_2346_, v_e_2342_, v_t_boxed_2347_, v_toPure_2344_, v_____do__lift_2345_);
lean_dec_ref(v_____do__lift_2345_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg(uint8_t v_pu_2349_, uint8_t v_t_2350_, lean_object* v_inst_2351_, lean_object* v_inst_2352_, lean_object* v_e_2353_){
_start:
{
lean_object* v_toApplicative_2354_; lean_object* v_toBind_2355_; lean_object* v_toPure_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___f_2359_; lean_object* v___x_2360_; 
v_toApplicative_2354_ = lean_ctor_get(v_inst_2352_, 0);
lean_inc_ref(v_toApplicative_2354_);
v_toBind_2355_ = lean_ctor_get(v_inst_2352_, 1);
lean_inc(v_toBind_2355_);
lean_dec_ref(v_inst_2352_);
v_toPure_2356_ = lean_ctor_get(v_toApplicative_2354_, 1);
lean_inc(v_toPure_2356_);
lean_dec_ref(v_toApplicative_2354_);
v___x_2357_ = lean_box(v_pu_2349_);
v___x_2358_ = lean_box(v_t_2350_);
v___f_2359_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2359_, 0, v___x_2357_);
lean_closure_set(v___f_2359_, 1, v_e_2353_);
lean_closure_set(v___f_2359_, 2, v___x_2358_);
lean_closure_set(v___f_2359_, 3, v_toPure_2356_);
v___x_2360_ = lean_apply_4(v_toBind_2355_, lean_box(0), lean_box(0), v_inst_2351_, v___f_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___boxed(lean_object* v_pu_2361_, lean_object* v_t_2362_, lean_object* v_inst_2363_, lean_object* v_inst_2364_, lean_object* v_e_2365_){
_start:
{
uint8_t v_pu_boxed_2366_; uint8_t v_t_boxed_2367_; lean_object* v_res_2368_; 
v_pu_boxed_2366_ = lean_unbox(v_pu_2361_);
v_t_boxed_2367_ = lean_unbox(v_t_2362_);
v_res_2368_ = l_Lean_Compiler_LCNF_normLetValue___redArg(v_pu_boxed_2366_, v_t_boxed_2367_, v_inst_2363_, v_inst_2364_, v_e_2365_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue(lean_object* v_m_2369_, uint8_t v_pu_2370_, uint8_t v_t_2371_, lean_object* v_inst_2372_, lean_object* v_inst_2373_, lean_object* v_e_2374_){
_start:
{
lean_object* v_toApplicative_2375_; lean_object* v_toBind_2376_; lean_object* v_toPure_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___f_2380_; lean_object* v___x_2381_; 
v_toApplicative_2375_ = lean_ctor_get(v_inst_2373_, 0);
lean_inc_ref(v_toApplicative_2375_);
v_toBind_2376_ = lean_ctor_get(v_inst_2373_, 1);
lean_inc(v_toBind_2376_);
lean_dec_ref(v_inst_2373_);
v_toPure_2377_ = lean_ctor_get(v_toApplicative_2375_, 1);
lean_inc(v_toPure_2377_);
lean_dec_ref(v_toApplicative_2375_);
v___x_2378_ = lean_box(v_pu_2370_);
v___x_2379_ = lean_box(v_t_2371_);
v___f_2380_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2380_, 0, v___x_2378_);
lean_closure_set(v___f_2380_, 1, v_e_2374_);
lean_closure_set(v___f_2380_, 2, v___x_2379_);
lean_closure_set(v___f_2380_, 3, v_toPure_2377_);
v___x_2381_ = lean_apply_4(v_toBind_2376_, lean_box(0), lean_box(0), v_inst_2372_, v___f_2380_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___boxed(lean_object* v_m_2382_, lean_object* v_pu_2383_, lean_object* v_t_2384_, lean_object* v_inst_2385_, lean_object* v_inst_2386_, lean_object* v_e_2387_){
_start:
{
uint8_t v_pu_boxed_2388_; uint8_t v_t_boxed_2389_; lean_object* v_res_2390_; 
v_pu_boxed_2388_ = lean_unbox(v_pu_2383_);
v_t_boxed_2389_ = lean_unbox(v_t_2384_);
v_res_2390_ = l_Lean_Compiler_LCNF_normLetValue(v_m_2382_, v_pu_boxed_2388_, v_t_boxed_2389_, v_inst_2385_, v_inst_2386_, v_e_2387_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore(uint8_t v_pu_2391_, lean_object* v_s_2392_, lean_object* v_e_2393_, uint8_t v_translator_2394_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2391_, v_s_2392_, v_translator_2394_, v_e_2393_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore___boxed(lean_object* v_pu_2396_, lean_object* v_s_2397_, lean_object* v_e_2398_, lean_object* v_translator_2399_){
_start:
{
uint8_t v_pu_boxed_2400_; uint8_t v_translator_boxed_2401_; lean_object* v_res_2402_; 
v_pu_boxed_2400_ = lean_unbox(v_pu_2396_);
v_translator_boxed_2401_ = lean_unbox(v_translator_2399_);
v_res_2402_ = l_Lean_Compiler_LCNF_normExprCore(v_pu_boxed_2400_, v_s_2397_, v_e_2398_, v_translator_boxed_2401_);
lean_dec_ref(v_s_2397_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(uint8_t v_pu_2403_, lean_object* v_args_2404_, uint8_t v_t_2405_, lean_object* v_toPure_2406_, lean_object* v_____do__lift_2407_){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_2403_, v_____do__lift_2407_, v_args_2404_, v_t_2405_);
v___x_2409_ = lean_apply_2(v_toPure_2406_, lean_box(0), v___x_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed(lean_object* v_pu_2410_, lean_object* v_args_2411_, lean_object* v_t_2412_, lean_object* v_toPure_2413_, lean_object* v_____do__lift_2414_){
_start:
{
uint8_t v_pu_boxed_2415_; uint8_t v_t_boxed_2416_; lean_object* v_res_2417_; 
v_pu_boxed_2415_ = lean_unbox(v_pu_2410_);
v_t_boxed_2416_ = lean_unbox(v_t_2412_);
v_res_2417_ = l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(v_pu_boxed_2415_, v_args_2411_, v_t_boxed_2416_, v_toPure_2413_, v_____do__lift_2414_);
lean_dec_ref(v_____do__lift_2414_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg(uint8_t v_pu_2418_, uint8_t v_t_2419_, lean_object* v_inst_2420_, lean_object* v_inst_2421_, lean_object* v_args_2422_){
_start:
{
lean_object* v_toApplicative_2423_; lean_object* v_toBind_2424_; lean_object* v_toPure_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___f_2428_; lean_object* v___x_2429_; 
v_toApplicative_2423_ = lean_ctor_get(v_inst_2421_, 0);
lean_inc_ref(v_toApplicative_2423_);
v_toBind_2424_ = lean_ctor_get(v_inst_2421_, 1);
lean_inc(v_toBind_2424_);
lean_dec_ref(v_inst_2421_);
v_toPure_2425_ = lean_ctor_get(v_toApplicative_2423_, 1);
lean_inc(v_toPure_2425_);
lean_dec_ref(v_toApplicative_2423_);
v___x_2426_ = lean_box(v_pu_2418_);
v___x_2427_ = lean_box(v_t_2419_);
v___f_2428_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2428_, 0, v___x_2426_);
lean_closure_set(v___f_2428_, 1, v_args_2422_);
lean_closure_set(v___f_2428_, 2, v___x_2427_);
lean_closure_set(v___f_2428_, 3, v_toPure_2425_);
v___x_2429_ = lean_apply_4(v_toBind_2424_, lean_box(0), lean_box(0), v_inst_2420_, v___f_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___boxed(lean_object* v_pu_2430_, lean_object* v_t_2431_, lean_object* v_inst_2432_, lean_object* v_inst_2433_, lean_object* v_args_2434_){
_start:
{
uint8_t v_pu_boxed_2435_; uint8_t v_t_boxed_2436_; lean_object* v_res_2437_; 
v_pu_boxed_2435_ = lean_unbox(v_pu_2430_);
v_t_boxed_2436_ = lean_unbox(v_t_2431_);
v_res_2437_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_boxed_2435_, v_t_boxed_2436_, v_inst_2432_, v_inst_2433_, v_args_2434_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs(lean_object* v_m_2438_, uint8_t v_pu_2439_, uint8_t v_t_2440_, lean_object* v_inst_2441_, lean_object* v_inst_2442_, lean_object* v_args_2443_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_2439_, v_t_2440_, v_inst_2441_, v_inst_2442_, v_args_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___boxed(lean_object* v_m_2445_, lean_object* v_pu_2446_, lean_object* v_t_2447_, lean_object* v_inst_2448_, lean_object* v_inst_2449_, lean_object* v_args_2450_){
_start:
{
uint8_t v_pu_boxed_2451_; uint8_t v_t_boxed_2452_; lean_object* v_res_2453_; 
v_pu_boxed_2451_ = lean_unbox(v_pu_2446_);
v_t_boxed_2452_ = lean_unbox(v_t_2447_);
v_res_2453_ = l_Lean_Compiler_LCNF_normArgs(v_m_2445_, v_pu_boxed_2451_, v_t_boxed_2452_, v_inst_2448_, v_inst_2449_, v_args_2450_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object* v_binderName_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v_lctx_2459_; lean_object* v_nextIdx_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2473_; 
v___x_2457_ = lean_st_ref_get(v_a_2455_);
v___x_2458_ = lean_st_ref_take(v_a_2455_);
v_lctx_2459_ = lean_ctor_get(v___x_2458_, 0);
v_nextIdx_2460_ = lean_ctor_get(v___x_2458_, 1);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2462_ = v___x_2458_;
v_isShared_2463_ = v_isSharedCheck_2473_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_nextIdx_2460_);
lean_inc(v_lctx_2459_);
lean_dec(v___x_2458_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2473_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2467_; 
v___x_2464_ = lean_unsigned_to_nat(1u);
v___x_2465_ = lean_nat_add(v_nextIdx_2460_, v___x_2464_);
lean_dec(v_nextIdx_2460_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 1, v___x_2465_);
v___x_2467_ = v___x_2462_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_lctx_2459_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v___x_2465_);
v___x_2467_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
lean_object* v___x_2468_; lean_object* v_nextIdx_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2468_ = lean_st_ref_put(v_a_2455_, v___x_2467_);
v_nextIdx_2469_ = lean_ctor_get(v___x_2457_, 1);
lean_inc(v_nextIdx_2469_);
lean_dec(v___x_2457_);
v___x_2470_ = l_Lean_Name_num___override(v_binderName_2454_, v_nextIdx_2469_);
v___x_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
return v___x_2471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg___boxed(lean_object* v_binderName_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2474_, v_a_2475_);
lean_dec(v_a_2475_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object* v_binderName_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2478_, v_a_2480_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___boxed(lean_object* v_binderName_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_Compiler_LCNF_mkFreshBinderName(v_binderName_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(lean_object* v_binderName_2492_, lean_object* v_baseName_2493_, lean_object* v_a_2494_){
_start:
{
uint8_t v___x_2496_; 
v___x_2496_ = l_Lean_Name_isAnonymous(v_binderName_2492_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; 
lean_dec(v_baseName_2493_);
v___x_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2497_, 0, v_binderName_2492_);
return v___x_2497_;
}
else
{
lean_object* v___x_2498_; 
lean_dec(v_binderName_2492_);
v___x_2498_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_baseName_2493_, v_a_2494_);
return v___x_2498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg___boxed(lean_object* v_binderName_2499_, lean_object* v_baseName_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2499_, v_baseName_2500_, v_a_2501_);
lean_dec(v_a_2501_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous(lean_object* v_binderName_2504_, lean_object* v_baseName_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2504_, v_baseName_2505_, v_a_2507_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___boxed(lean_object* v_binderName_2512_, lean_object* v_baseName_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_Compiler_LCNF_ensureNotAnonymous(v_binderName_2512_, v_baseName_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(lean_object* v___y_2520_){
_start:
{
lean_object* v___x_2522_; lean_object* v_ngen_2523_; lean_object* v_namePrefix_2524_; lean_object* v_idx_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2554_; 
v___x_2522_ = lean_st_ref_get(v___y_2520_);
v_ngen_2523_ = lean_ctor_get(v___x_2522_, 2);
lean_inc_ref(v_ngen_2523_);
lean_dec(v___x_2522_);
v_namePrefix_2524_ = lean_ctor_get(v_ngen_2523_, 0);
v_idx_2525_ = lean_ctor_get(v_ngen_2523_, 1);
v_isSharedCheck_2554_ = !lean_is_exclusive(v_ngen_2523_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2527_ = v_ngen_2523_;
v_isShared_2528_ = v_isSharedCheck_2554_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_idx_2525_);
lean_inc(v_namePrefix_2524_);
lean_dec(v_ngen_2523_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2554_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; lean_object* v_env_2530_; lean_object* v_nextMacroScope_2531_; lean_object* v_auxDeclNGen_2532_; lean_object* v_traceState_2533_; lean_object* v_cache_2534_; lean_object* v_messages_2535_; lean_object* v_infoState_2536_; lean_object* v_snapshotTasks_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2552_; 
v___x_2529_ = lean_st_ref_take(v___y_2520_);
v_env_2530_ = lean_ctor_get(v___x_2529_, 0);
v_nextMacroScope_2531_ = lean_ctor_get(v___x_2529_, 1);
v_auxDeclNGen_2532_ = lean_ctor_get(v___x_2529_, 3);
v_traceState_2533_ = lean_ctor_get(v___x_2529_, 4);
v_cache_2534_ = lean_ctor_get(v___x_2529_, 5);
v_messages_2535_ = lean_ctor_get(v___x_2529_, 6);
v_infoState_2536_ = lean_ctor_get(v___x_2529_, 7);
v_snapshotTasks_2537_ = lean_ctor_get(v___x_2529_, 8);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2552_ == 0)
{
lean_object* v_unused_2553_; 
v_unused_2553_ = lean_ctor_get(v___x_2529_, 2);
lean_dec(v_unused_2553_);
v___x_2539_ = v___x_2529_;
v_isShared_2540_ = v_isSharedCheck_2552_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_snapshotTasks_2537_);
lean_inc(v_infoState_2536_);
lean_inc(v_messages_2535_);
lean_inc(v_cache_2534_);
lean_inc(v_traceState_2533_);
lean_inc(v_auxDeclNGen_2532_);
lean_inc(v_nextMacroScope_2531_);
lean_inc(v_env_2530_);
lean_dec(v___x_2529_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2552_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v_r_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
lean_inc(v_idx_2525_);
lean_inc(v_namePrefix_2524_);
v_r_2541_ = l_Lean_Name_num___override(v_namePrefix_2524_, v_idx_2525_);
v___x_2542_ = lean_unsigned_to_nat(1u);
v___x_2543_ = lean_nat_add(v_idx_2525_, v___x_2542_);
lean_dec(v_idx_2525_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 1, v___x_2543_);
v___x_2545_ = v___x_2527_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_namePrefix_2524_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v___x_2543_);
v___x_2545_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2547_; 
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 2, v___x_2545_);
v___x_2547_ = v___x_2539_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_env_2530_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_nextMacroScope_2531_);
lean_ctor_set(v_reuseFailAlloc_2550_, 2, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2550_, 3, v_auxDeclNGen_2532_);
lean_ctor_set(v_reuseFailAlloc_2550_, 4, v_traceState_2533_);
lean_ctor_set(v_reuseFailAlloc_2550_, 5, v_cache_2534_);
lean_ctor_set(v_reuseFailAlloc_2550_, 6, v_messages_2535_);
lean_ctor_set(v_reuseFailAlloc_2550_, 7, v_infoState_2536_);
lean_ctor_set(v_reuseFailAlloc_2550_, 8, v_snapshotTasks_2537_);
v___x_2547_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = lean_st_ref_put(v___y_2520_, v___x_2547_);
v___x_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2549_, 0, v_r_2541_);
return v___x_2549_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg___boxed(lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2555_);
lean_dec(v___y_2555_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v___x_2563_; lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
v___x_2563_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2561_);
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2563_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2563_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0___boxed(lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t v_pu_2581_, lean_object* v_binderName_2582_, lean_object* v_type_2583_, uint8_t v_borrow_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2614_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref_known(v___x_2590_, 1);
v___x_2592_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_2593_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2582_, v___x_2592_, v_a_2586_);
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2614_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2614_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2598_; lean_object* v_lctx_2599_; lean_object* v_nextIdx_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2613_; 
v___x_2598_ = lean_st_ref_take(v_a_2586_);
v_lctx_2599_ = lean_ctor_get(v___x_2598_, 0);
v_nextIdx_2600_ = lean_ctor_get(v___x_2598_, 1);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2602_ = v___x_2598_;
v_isShared_2603_ = v_isSharedCheck_2613_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_nextIdx_2600_);
lean_inc(v_lctx_2599_);
lean_dec(v___x_2598_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2613_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2607_; 
v___x_2604_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2604_, 0, v_a_2591_);
lean_ctor_set(v___x_2604_, 1, v_a_2594_);
lean_ctor_set(v___x_2604_, 2, v_type_2583_);
lean_ctor_set_uint8(v___x_2604_, sizeof(void*)*3, v_borrow_2584_);
lean_inc_ref(v___x_2604_);
v___x_2605_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2581_, v_lctx_2599_, v___x_2604_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 0, v___x_2605_);
v___x_2607_ = v___x_2602_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2605_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_nextIdx_2600_);
v___x_2607_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
lean_object* v___x_2608_; lean_object* v___x_2610_; 
v___x_2608_ = lean_st_ref_put(v_a_2586_, v___x_2607_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v___x_2604_);
v___x_2610_ = v___x_2596_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2604_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec_ref(v_type_2583_);
lean_dec(v_binderName_2582_);
v_a_2615_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2590_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2590_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam___boxed(lean_object* v_pu_2623_, lean_object* v_binderName_2624_, lean_object* v_type_2625_, lean_object* v_borrow_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
uint8_t v_pu_boxed_2632_; uint8_t v_borrow_boxed_2633_; lean_object* v_res_2634_; 
v_pu_boxed_2632_ = lean_unbox(v_pu_2623_);
v_borrow_boxed_2633_ = lean_unbox(v_borrow_2626_);
v_res_2634_ = l_Lean_Compiler_LCNF_mkParam(v_pu_boxed_2632_, v_binderName_2624_, v_type_2625_, v_borrow_boxed_2633_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2638_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___boxed(lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t v_pu_2650_, lean_object* v_binderName_2651_, lean_object* v_type_2652_, lean_object* v_value_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2683_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
v___x_2661_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2662_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2651_, v___x_2661_, v_a_2655_);
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2665_ = v___x_2662_;
v_isShared_2666_ = v_isSharedCheck_2683_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2662_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2683_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; lean_object* v_lctx_2668_; lean_object* v_nextIdx_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2682_; 
v___x_2667_ = lean_st_ref_take(v_a_2655_);
v_lctx_2668_ = lean_ctor_get(v___x_2667_, 0);
v_nextIdx_2669_ = lean_ctor_get(v___x_2667_, 1);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2671_ = v___x_2667_;
v_isShared_2672_ = v_isSharedCheck_2682_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_nextIdx_2669_);
lean_inc(v_lctx_2668_);
lean_dec(v___x_2667_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2682_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2673_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2673_, 0, v_a_2660_);
lean_ctor_set(v___x_2673_, 1, v_a_2663_);
lean_ctor_set(v___x_2673_, 2, v_type_2652_);
lean_ctor_set(v___x_2673_, 3, v_value_2653_);
lean_inc_ref(v___x_2673_);
v___x_2674_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2650_, v_lctx_2668_, v___x_2673_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 0, v___x_2674_);
v___x_2676_ = v___x_2671_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2674_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v_nextIdx_2669_);
v___x_2676_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2677_; lean_object* v___x_2679_; 
v___x_2677_ = lean_st_ref_put(v_a_2655_, v___x_2676_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v___x_2673_);
v___x_2679_ = v___x_2665_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2673_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec(v_value_2653_);
lean_dec_ref(v_type_2652_);
lean_dec(v_binderName_2651_);
v_a_2684_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2659_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2659_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl___boxed(lean_object* v_pu_2692_, lean_object* v_binderName_2693_, lean_object* v_type_2694_, lean_object* v_value_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_){
_start:
{
uint8_t v_pu_boxed_2701_; lean_object* v_res_2702_; 
v_pu_boxed_2701_ = lean_unbox(v_pu_2692_);
v_res_2702_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_boxed_2701_, v_binderName_2693_, v_type_2694_, v_value_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t v_pu_2706_, lean_object* v_binderName_2707_, lean_object* v_type_2708_, lean_object* v_params_2709_, lean_object* v_value_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2740_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2716_, 1);
v___x_2718_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFunDecl___closed__1));
v___x_2719_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2707_, v___x_2718_, v_a_2712_);
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2722_ = v___x_2719_;
v_isShared_2723_ = v_isSharedCheck_2740_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2719_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2740_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2724_; lean_object* v_lctx_2725_; lean_object* v_nextIdx_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2739_; 
v___x_2724_ = lean_st_ref_take(v_a_2712_);
v_lctx_2725_ = lean_ctor_get(v___x_2724_, 0);
v_nextIdx_2726_ = lean_ctor_get(v___x_2724_, 1);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2728_ = v___x_2724_;
v_isShared_2729_ = v_isSharedCheck_2739_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_nextIdx_2726_);
lean_inc(v_lctx_2725_);
lean_dec(v___x_2724_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2739_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2730_, 0, v_a_2717_);
lean_ctor_set(v___x_2730_, 1, v_a_2720_);
lean_ctor_set(v___x_2730_, 2, v_params_2709_);
lean_ctor_set(v___x_2730_, 3, v_type_2708_);
lean_ctor_set(v___x_2730_, 4, v_value_2710_);
lean_inc_ref(v___x_2730_);
v___x_2731_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2706_, v_lctx_2725_, v___x_2730_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v___x_2731_);
v___x_2733_ = v___x_2728_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v___x_2731_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_nextIdx_2726_);
v___x_2733_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
lean_object* v___x_2734_; lean_object* v___x_2736_; 
v___x_2734_ = lean_st_ref_put(v_a_2712_, v___x_2733_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v___x_2730_);
v___x_2736_ = v___x_2722_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2730_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec_ref(v_value_2710_);
lean_dec_ref(v_params_2709_);
lean_dec_ref(v_type_2708_);
lean_dec(v_binderName_2707_);
v_a_2741_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2716_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2716_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl___boxed(lean_object* v_pu_2749_, lean_object* v_binderName_2750_, lean_object* v_type_2751_, lean_object* v_params_2752_, lean_object* v_value_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
uint8_t v_pu_boxed_2759_; lean_object* v_res_2760_; 
v_pu_boxed_2759_ = lean_unbox(v_pu_2749_);
v_res_2760_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_boxed_2759_, v_binderName_2750_, v_type_2751_, v_params_2752_, v_value_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_);
lean_dec(v_a_2757_);
lean_dec_ref(v_a_2756_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(uint8_t v_pu_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v_a_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2767_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2768_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2767_, v_a_2763_);
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2769_);
lean_dec_ref(v___x_2768_);
v___x_2770_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2771_ = lean_box(1);
v___x_2772_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2761_, v_a_2769_, v___x_2770_, v___x_2771_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased___boxed(lean_object* v_pu_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
uint8_t v_pu_boxed_2779_; lean_object* v_res_2780_; 
v_pu_boxed_2779_ = lean_unbox(v_pu_2773_);
v_res_2780_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_boxed_2779_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
lean_dec(v_a_2777_);
lean_dec_ref(v_a_2776_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t v_pu_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v___x_2787_; 
v___x_2787_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
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
lean_object* v_fvarId_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2796_; 
v_fvarId_2792_ = lean_ctor_get(v_a_2788_, 0);
lean_inc(v_fvarId_2792_);
v___x_2793_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2793_, 0, v_fvarId_2792_);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v_a_2788_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v___x_2794_);
v___x_2796_ = v___x_2790_;
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
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased___boxed(lean_object* v_pu_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_){
_start:
{
uint8_t v_pu_boxed_2813_; lean_object* v_res_2814_; 
v_pu_boxed_2813_ = lean_unbox(v_pu_2807_);
v_res_2814_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_boxed_2813_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_);
lean_dec(v_a_2811_);
lean_dec_ref(v_a_2810_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t v_pu_2815_, lean_object* v_p_2816_, lean_object* v_type_2817_, lean_object* v_a_2818_){
_start:
{
lean_object* v_fvarId_2820_; lean_object* v_binderName_2821_; lean_object* v_type_2822_; uint8_t v_borrow_2823_; size_t v___x_2824_; size_t v___x_2825_; uint8_t v___x_2826_; 
v_fvarId_2820_ = lean_ctor_get(v_p_2816_, 0);
v_binderName_2821_ = lean_ctor_get(v_p_2816_, 1);
v_type_2822_ = lean_ctor_get(v_p_2816_, 2);
v_borrow_2823_ = lean_ctor_get_uint8(v_p_2816_, sizeof(void*)*3);
v___x_2824_ = lean_ptr_addr(v_type_2817_);
v___x_2825_ = lean_ptr_addr(v_type_2822_);
v___x_2826_ = lean_usize_dec_eq(v___x_2824_, v___x_2825_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2846_; 
lean_inc(v_binderName_2821_);
lean_inc(v_fvarId_2820_);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_p_2816_);
if (v_isSharedCheck_2846_ == 0)
{
lean_object* v_unused_2847_; lean_object* v_unused_2848_; lean_object* v_unused_2849_; 
v_unused_2847_ = lean_ctor_get(v_p_2816_, 2);
lean_dec(v_unused_2847_);
v_unused_2848_ = lean_ctor_get(v_p_2816_, 1);
lean_dec(v_unused_2848_);
v_unused_2849_ = lean_ctor_get(v_p_2816_, 0);
lean_dec(v_unused_2849_);
v___x_2828_ = v_p_2816_;
v_isShared_2829_ = v_isSharedCheck_2846_;
goto v_resetjp_2827_;
}
else
{
lean_dec(v_p_2816_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2846_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2830_; lean_object* v_lctx_2831_; lean_object* v_nextIdx_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2845_; 
v___x_2830_ = lean_st_ref_take(v_a_2818_);
v_lctx_2831_ = lean_ctor_get(v___x_2830_, 0);
v_nextIdx_2832_ = lean_ctor_get(v___x_2830_, 1);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2834_ = v___x_2830_;
v_isShared_2835_ = v_isSharedCheck_2845_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_nextIdx_2832_);
lean_inc(v_lctx_2831_);
lean_dec(v___x_2830_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2845_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v_p_2837_; 
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 2, v_type_2817_);
v_p_2837_ = v___x_2828_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_fvarId_2820_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v_binderName_2821_);
lean_ctor_set(v_reuseFailAlloc_2844_, 2, v_type_2817_);
lean_ctor_set_uint8(v_reuseFailAlloc_2844_, sizeof(void*)*3, v_borrow_2823_);
v_p_2837_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
lean_object* v___x_2838_; lean_object* v___x_2840_; 
lean_inc_ref(v_p_2837_);
v___x_2838_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2815_, v_lctx_2831_, v_p_2837_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2838_);
v___x_2840_ = v___x_2834_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2838_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_nextIdx_2832_);
v___x_2840_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = lean_st_ref_put(v_a_2818_, v___x_2840_);
v___x_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2842_, 0, v_p_2837_);
return v___x_2842_;
}
}
}
}
}
else
{
lean_object* v___x_2850_; 
lean_dec_ref(v_type_2817_);
v___x_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2850_, 0, v_p_2816_);
return v___x_2850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg___boxed(lean_object* v_pu_2851_, lean_object* v_p_2852_, lean_object* v_type_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_){
_start:
{
uint8_t v_pu_boxed_2856_; lean_object* v_res_2857_; 
v_pu_boxed_2856_ = lean_unbox(v_pu_2851_);
v_res_2857_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_boxed_2856_, v_p_2852_, v_type_2853_, v_a_2854_);
lean_dec(v_a_2854_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(uint8_t v_pu_2858_, lean_object* v_p_2859_, lean_object* v_type_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_){
_start:
{
lean_object* v___x_2866_; 
v___x_2866_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_2858_, v_p_2859_, v_type_2860_, v_a_2862_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(lean_object* v_pu_2867_, lean_object* v_p_2868_, lean_object* v_type_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
uint8_t v_pu_boxed_2875_; lean_object* v_res_2876_; 
v_pu_boxed_2875_ = lean_unbox(v_pu_2867_);
v_res_2876_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(v_pu_boxed_2875_, v_p_2868_, v_type_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
lean_dec(v_a_2873_);
lean_dec_ref(v_a_2872_);
lean_dec(v_a_2871_);
lean_dec_ref(v_a_2870_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t v_pu_2877_, lean_object* v_p_2878_, uint8_t v_borrow_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v_fvarId_2882_; lean_object* v_binderName_2883_; lean_object* v_type_2884_; uint8_t v_borrow_2885_; 
v_fvarId_2882_ = lean_ctor_get(v_p_2878_, 0);
v_binderName_2883_ = lean_ctor_get(v_p_2878_, 1);
v_type_2884_ = lean_ctor_get(v_p_2878_, 2);
v_borrow_2885_ = lean_ctor_get_uint8(v_p_2878_, sizeof(void*)*3);
if (v_borrow_2879_ == 0)
{
if (v_borrow_2885_ == 0)
{
lean_object* v___x_2901_; 
v___x_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2901_, 0, v_p_2878_);
return v___x_2901_;
}
else
{
lean_inc_ref(v_type_2884_);
lean_inc(v_binderName_2883_);
lean_inc(v_fvarId_2882_);
lean_dec_ref(v_p_2878_);
goto v___jp_2886_;
}
}
else
{
if (v_borrow_2885_ == 0)
{
lean_inc_ref(v_type_2884_);
lean_inc(v_binderName_2883_);
lean_inc(v_fvarId_2882_);
lean_dec_ref(v_p_2878_);
goto v___jp_2886_;
}
else
{
lean_object* v___x_2902_; 
v___x_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2902_, 0, v_p_2878_);
return v___x_2902_;
}
}
v___jp_2886_:
{
lean_object* v___x_2887_; lean_object* v_lctx_2888_; lean_object* v_nextIdx_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2900_; 
v___x_2887_ = lean_st_ref_take(v_a_2880_);
v_lctx_2888_ = lean_ctor_get(v___x_2887_, 0);
v_nextIdx_2889_ = lean_ctor_get(v___x_2887_, 1);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2891_ = v___x_2887_;
v_isShared_2892_ = v_isSharedCheck_2900_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_nextIdx_2889_);
lean_inc(v_lctx_2888_);
lean_dec(v___x_2887_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2900_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v_p_2893_; lean_object* v___x_2894_; lean_object* v___x_2896_; 
v_p_2893_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_p_2893_, 0, v_fvarId_2882_);
lean_ctor_set(v_p_2893_, 1, v_binderName_2883_);
lean_ctor_set(v_p_2893_, 2, v_type_2884_);
lean_ctor_set_uint8(v_p_2893_, sizeof(void*)*3, v_borrow_2879_);
lean_inc_ref(v_p_2893_);
v___x_2894_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2877_, v_lctx_2888_, v_p_2893_);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 0, v___x_2894_);
v___x_2896_ = v___x_2891_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_nextIdx_2889_);
v___x_2896_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2897_ = lean_st_ref_put(v_a_2880_, v___x_2896_);
v___x_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2898_, 0, v_p_2893_);
return v___x_2898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg___boxed(lean_object* v_pu_2903_, lean_object* v_p_2904_, lean_object* v_borrow_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
uint8_t v_pu_boxed_2908_; uint8_t v_borrow_boxed_2909_; lean_object* v_res_2910_; 
v_pu_boxed_2908_ = lean_unbox(v_pu_2903_);
v_borrow_boxed_2909_ = lean_unbox(v_borrow_2905_);
v_res_2910_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_boxed_2908_, v_p_2904_, v_borrow_boxed_2909_, v_a_2906_);
lean_dec(v_a_2906_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(uint8_t v_pu_2911_, lean_object* v_p_2912_, uint8_t v_borrow_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v___x_2919_; 
v___x_2919_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_2911_, v_p_2912_, v_borrow_2913_, v_a_2915_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___boxed(lean_object* v_pu_2920_, lean_object* v_p_2921_, lean_object* v_borrow_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_){
_start:
{
uint8_t v_pu_boxed_2928_; uint8_t v_borrow_boxed_2929_; lean_object* v_res_2930_; 
v_pu_boxed_2928_ = lean_unbox(v_pu_2920_);
v_borrow_boxed_2929_ = lean_unbox(v_borrow_2922_);
v_res_2930_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(v_pu_boxed_2928_, v_p_2921_, v_borrow_boxed_2929_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec(v_a_2926_);
lean_dec_ref(v_a_2925_);
lean_dec(v_a_2924_);
lean_dec_ref(v_a_2923_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t v_pu_2931_, lean_object* v_decl_2932_, lean_object* v_type_2933_, lean_object* v_value_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_fvarId_2937_; lean_object* v_binderName_2938_; lean_object* v_type_2939_; lean_object* v_value_2940_; uint8_t v___y_2942_; size_t v___x_2968_; size_t v___x_2969_; uint8_t v___x_2970_; 
v_fvarId_2937_ = lean_ctor_get(v_decl_2932_, 0);
v_binderName_2938_ = lean_ctor_get(v_decl_2932_, 1);
v_type_2939_ = lean_ctor_get(v_decl_2932_, 2);
v_value_2940_ = lean_ctor_get(v_decl_2932_, 3);
v___x_2968_ = lean_ptr_addr(v_type_2933_);
v___x_2969_ = lean_ptr_addr(v_type_2939_);
v___x_2970_ = lean_usize_dec_eq(v___x_2968_, v___x_2969_);
if (v___x_2970_ == 0)
{
v___y_2942_ = v___x_2970_;
goto v___jp_2941_;
}
else
{
size_t v___x_2971_; size_t v___x_2972_; uint8_t v___x_2973_; 
v___x_2971_ = lean_ptr_addr(v_value_2934_);
v___x_2972_ = lean_ptr_addr(v_value_2940_);
v___x_2973_ = lean_usize_dec_eq(v___x_2971_, v___x_2972_);
v___y_2942_ = v___x_2973_;
goto v___jp_2941_;
}
v___jp_2941_:
{
if (v___y_2942_ == 0)
{
lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2962_; 
lean_inc(v_binderName_2938_);
lean_inc(v_fvarId_2937_);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_decl_2932_);
if (v_isSharedCheck_2962_ == 0)
{
lean_object* v_unused_2963_; lean_object* v_unused_2964_; lean_object* v_unused_2965_; lean_object* v_unused_2966_; 
v_unused_2963_ = lean_ctor_get(v_decl_2932_, 3);
lean_dec(v_unused_2963_);
v_unused_2964_ = lean_ctor_get(v_decl_2932_, 2);
lean_dec(v_unused_2964_);
v_unused_2965_ = lean_ctor_get(v_decl_2932_, 1);
lean_dec(v_unused_2965_);
v_unused_2966_ = lean_ctor_get(v_decl_2932_, 0);
lean_dec(v_unused_2966_);
v___x_2944_ = v_decl_2932_;
v_isShared_2945_ = v_isSharedCheck_2962_;
goto v_resetjp_2943_;
}
else
{
lean_dec(v_decl_2932_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2962_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; lean_object* v_lctx_2947_; lean_object* v_nextIdx_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2961_; 
v___x_2946_ = lean_st_ref_take(v_a_2935_);
v_lctx_2947_ = lean_ctor_get(v___x_2946_, 0);
v_nextIdx_2948_ = lean_ctor_get(v___x_2946_, 1);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2950_ = v___x_2946_;
v_isShared_2951_ = v_isSharedCheck_2961_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_nextIdx_2948_);
lean_inc(v_lctx_2947_);
lean_dec(v___x_2946_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2961_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v_decl_2953_; 
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 3, v_value_2934_);
lean_ctor_set(v___x_2944_, 2, v_type_2933_);
v_decl_2953_ = v___x_2944_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_fvarId_2937_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v_binderName_2938_);
lean_ctor_set(v_reuseFailAlloc_2960_, 2, v_type_2933_);
lean_ctor_set(v_reuseFailAlloc_2960_, 3, v_value_2934_);
v_decl_2953_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
lean_object* v___x_2954_; lean_object* v___x_2956_; 
lean_inc_ref(v_decl_2953_);
v___x_2954_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2931_, v_lctx_2947_, v_decl_2953_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v___x_2954_);
v___x_2956_ = v___x_2950_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2954_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v_nextIdx_2948_);
v___x_2956_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2957_ = lean_st_ref_put(v_a_2935_, v___x_2956_);
v___x_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2958_, 0, v_decl_2953_);
return v___x_2958_;
}
}
}
}
}
else
{
lean_object* v___x_2967_; 
lean_dec(v_value_2934_);
lean_dec_ref(v_type_2933_);
v___x_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2967_, 0, v_decl_2932_);
return v___x_2967_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg___boxed(lean_object* v_pu_2974_, lean_object* v_decl_2975_, lean_object* v_type_2976_, lean_object* v_value_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
uint8_t v_pu_boxed_2980_; lean_object* v_res_2981_; 
v_pu_boxed_2980_ = lean_unbox(v_pu_2974_);
v_res_2981_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_boxed_2980_, v_decl_2975_, v_type_2976_, v_value_2977_, v_a_2978_);
lean_dec(v_a_2978_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(uint8_t v_pu_2982_, lean_object* v_decl_2983_, lean_object* v_type_2984_, lean_object* v_value_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2982_, v_decl_2983_, v_type_2984_, v_value_2985_, v_a_2987_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(lean_object* v_pu_2992_, lean_object* v_decl_2993_, lean_object* v_type_2994_, lean_object* v_value_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_){
_start:
{
uint8_t v_pu_boxed_3001_; lean_object* v_res_3002_; 
v_pu_boxed_3001_ = lean_unbox(v_pu_2992_);
v_res_3002_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(v_pu_boxed_3001_, v_decl_2993_, v_type_2994_, v_value_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_);
lean_dec(v_a_2999_);
lean_dec_ref(v_a_2998_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t v_pu_3003_, lean_object* v_decl_3004_, lean_object* v_value_3005_, lean_object* v_a_3006_){
_start:
{
lean_object* v_type_3008_; lean_object* v___x_3009_; 
v_type_3008_ = lean_ctor_get(v_decl_3004_, 2);
lean_inc_ref(v_type_3008_);
v___x_3009_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_3003_, v_decl_3004_, v_type_3008_, v_value_3005_, v_a_3006_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg___boxed(lean_object* v_pu_3010_, lean_object* v_decl_3011_, lean_object* v_value_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_){
_start:
{
uint8_t v_pu_boxed_3015_; lean_object* v_res_3016_; 
v_pu_boxed_3015_ = lean_unbox(v_pu_3010_);
v_res_3016_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_boxed_3015_, v_decl_3011_, v_value_3012_, v_a_3013_);
lean_dec(v_a_3013_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(uint8_t v_pu_3017_, lean_object* v_decl_3018_, lean_object* v_value_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_){
_start:
{
lean_object* v___x_3025_; 
v___x_3025_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_3017_, v_decl_3018_, v_value_3019_, v_a_3021_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___boxed(lean_object* v_pu_3026_, lean_object* v_decl_3027_, lean_object* v_value_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_){
_start:
{
uint8_t v_pu_boxed_3034_; lean_object* v_res_3035_; 
v_pu_boxed_3034_ = lean_unbox(v_pu_3026_);
v_res_3035_ = l_Lean_Compiler_LCNF_LetDecl_updateValue(v_pu_boxed_3034_, v_decl_3027_, v_value_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t v_pu_3036_, lean_object* v_decl_3037_, lean_object* v_type_3038_, lean_object* v_params_3039_, lean_object* v_value_3040_, lean_object* v_a_3041_){
_start:
{
lean_object* v_fvarId_3043_; lean_object* v_binderName_3044_; lean_object* v_params_3045_; lean_object* v_type_3046_; lean_object* v_value_3047_; uint8_t v___y_3064_; size_t v___x_3069_; size_t v___x_3070_; uint8_t v___x_3071_; 
v_fvarId_3043_ = lean_ctor_get(v_decl_3037_, 0);
v_binderName_3044_ = lean_ctor_get(v_decl_3037_, 1);
v_params_3045_ = lean_ctor_get(v_decl_3037_, 2);
v_type_3046_ = lean_ctor_get(v_decl_3037_, 3);
v_value_3047_ = lean_ctor_get(v_decl_3037_, 4);
v___x_3069_ = lean_ptr_addr(v_type_3038_);
v___x_3070_ = lean_ptr_addr(v_type_3046_);
v___x_3071_ = lean_usize_dec_eq(v___x_3069_, v___x_3070_);
if (v___x_3071_ == 0)
{
v___y_3064_ = v___x_3071_;
goto v___jp_3063_;
}
else
{
size_t v___x_3072_; size_t v___x_3073_; uint8_t v___x_3074_; 
v___x_3072_ = lean_ptr_addr(v_params_3039_);
v___x_3073_ = lean_ptr_addr(v_params_3045_);
v___x_3074_ = lean_usize_dec_eq(v___x_3072_, v___x_3073_);
v___y_3064_ = v___x_3074_;
goto v___jp_3063_;
}
v___jp_3048_:
{
lean_object* v___x_3049_; lean_object* v_lctx_3050_; lean_object* v_nextIdx_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3062_; 
v___x_3049_ = lean_st_ref_take(v_a_3041_);
v_lctx_3050_ = lean_ctor_get(v___x_3049_, 0);
v_nextIdx_3051_ = lean_ctor_get(v___x_3049_, 1);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3053_ = v___x_3049_;
v_isShared_3054_ = v_isSharedCheck_3062_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_nextIdx_3051_);
lean_inc(v_lctx_3050_);
lean_dec(v___x_3049_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3062_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v_decl_3055_; lean_object* v___x_3056_; lean_object* v___x_3058_; 
v_decl_3055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_decl_3055_, 0, v_fvarId_3043_);
lean_ctor_set(v_decl_3055_, 1, v_binderName_3044_);
lean_ctor_set(v_decl_3055_, 2, v_params_3039_);
lean_ctor_set(v_decl_3055_, 3, v_type_3038_);
lean_ctor_set(v_decl_3055_, 4, v_value_3040_);
lean_inc_ref(v_decl_3055_);
v___x_3056_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_3036_, v_lctx_3050_, v_decl_3055_);
if (v_isShared_3054_ == 0)
{
lean_ctor_set(v___x_3053_, 0, v___x_3056_);
v___x_3058_ = v___x_3053_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3056_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v_nextIdx_3051_);
v___x_3058_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = lean_st_ref_put(v_a_3041_, v___x_3058_);
v___x_3060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3060_, 0, v_decl_3055_);
return v___x_3060_;
}
}
}
v___jp_3063_:
{
if (v___y_3064_ == 0)
{
lean_inc(v_binderName_3044_);
lean_inc(v_fvarId_3043_);
lean_dec_ref(v_decl_3037_);
goto v___jp_3048_;
}
else
{
size_t v___x_3065_; size_t v___x_3066_; uint8_t v___x_3067_; 
v___x_3065_ = lean_ptr_addr(v_value_3040_);
v___x_3066_ = lean_ptr_addr(v_value_3047_);
v___x_3067_ = lean_usize_dec_eq(v___x_3065_, v___x_3066_);
if (v___x_3067_ == 0)
{
lean_inc(v_binderName_3044_);
lean_inc(v_fvarId_3043_);
lean_dec_ref(v_decl_3037_);
goto v___jp_3048_;
}
else
{
lean_object* v___x_3068_; 
lean_dec_ref(v_value_3040_);
lean_dec_ref(v_params_3039_);
lean_dec_ref(v_type_3038_);
v___x_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3068_, 0, v_decl_3037_);
return v___x_3068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg___boxed(lean_object* v_pu_3075_, lean_object* v_decl_3076_, lean_object* v_type_3077_, lean_object* v_params_3078_, lean_object* v_value_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_){
_start:
{
uint8_t v_pu_boxed_3082_; lean_object* v_res_3083_; 
v_pu_boxed_3082_ = lean_unbox(v_pu_3075_);
v_res_3083_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_boxed_3082_, v_decl_3076_, v_type_3077_, v_params_3078_, v_value_3079_, v_a_3080_);
lean_dec(v_a_3080_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(uint8_t v_pu_3084_, lean_object* v_decl_3085_, lean_object* v_type_3086_, lean_object* v_params_3087_, lean_object* v_value_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_){
_start:
{
lean_object* v___x_3094_; 
v___x_3094_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_3084_, v_decl_3085_, v_type_3086_, v_params_3087_, v_value_3088_, v_a_3090_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(lean_object* v_pu_3095_, lean_object* v_decl_3096_, lean_object* v_type_3097_, lean_object* v_params_3098_, lean_object* v_value_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_){
_start:
{
uint8_t v_pu_boxed_3105_; lean_object* v_res_3106_; 
v_pu_boxed_3105_ = lean_unbox(v_pu_3095_);
v_res_3106_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(v_pu_boxed_3105_, v_decl_3096_, v_type_3097_, v_params_3098_, v_value_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_);
lean_dec(v_a_3103_);
lean_dec_ref(v_a_3102_);
lean_dec(v_a_3101_);
lean_dec_ref(v_a_3100_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(uint8_t v_pu_3107_, lean_object* v_decl_3108_, lean_object* v_type_3109_, lean_object* v_value_3110_, lean_object* v_a_3111_){
_start:
{
lean_object* v_params_3113_; lean_object* v___x_3114_; 
v_params_3113_ = lean_ctor_get(v_decl_3108_, 2);
lean_inc_ref(v_params_3113_);
v___x_3114_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_3107_, v_decl_3108_, v_type_3109_, v_params_3113_, v_value_3110_, v_a_3111_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg___boxed(lean_object* v_pu_3115_, lean_object* v_decl_3116_, lean_object* v_type_3117_, lean_object* v_value_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_){
_start:
{
uint8_t v_pu_boxed_3121_; lean_object* v_res_3122_; 
v_pu_boxed_3121_ = lean_unbox(v_pu_3115_);
v_res_3122_ = l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(v_pu_boxed_3121_, v_decl_3116_, v_type_3117_, v_value_3118_, v_a_3119_);
lean_dec(v_a_3119_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27(uint8_t v_pu_3123_, lean_object* v_decl_3124_, lean_object* v_type_3125_, lean_object* v_value_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_){
_start:
{
lean_object* v_params_3132_; lean_object* v___x_3133_; 
v_params_3132_ = lean_ctor_get(v_decl_3124_, 2);
lean_inc_ref(v_params_3132_);
v___x_3133_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_3123_, v_decl_3124_, v_type_3125_, v_params_3132_, v_value_3126_, v_a_3128_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___boxed(lean_object* v_pu_3134_, lean_object* v_decl_3135_, lean_object* v_type_3136_, lean_object* v_value_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_){
_start:
{
uint8_t v_pu_boxed_3143_; lean_object* v_res_3144_; 
v_pu_boxed_3143_ = lean_unbox(v_pu_3134_);
v_res_3144_ = l_Lean_Compiler_LCNF_FunDecl_update_x27(v_pu_boxed_3143_, v_decl_3135_, v_type_3136_, v_value_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_);
lean_dec(v_a_3141_);
lean_dec_ref(v_a_3140_);
lean_dec(v_a_3139_);
lean_dec_ref(v_a_3138_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(uint8_t v_pu_3145_, lean_object* v_decl_3146_, lean_object* v_value_3147_, lean_object* v_a_3148_){
_start:
{
lean_object* v_params_3150_; lean_object* v_type_3151_; lean_object* v___x_3152_; 
v_params_3150_ = lean_ctor_get(v_decl_3146_, 2);
lean_inc_ref(v_params_3150_);
v_type_3151_ = lean_ctor_get(v_decl_3146_, 3);
lean_inc_ref(v_type_3151_);
v___x_3152_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_3145_, v_decl_3146_, v_type_3151_, v_params_3150_, v_value_3147_, v_a_3148_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg___boxed(lean_object* v_pu_3153_, lean_object* v_decl_3154_, lean_object* v_value_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_){
_start:
{
uint8_t v_pu_boxed_3158_; lean_object* v_res_3159_; 
v_pu_boxed_3158_ = lean_unbox(v_pu_3153_);
v_res_3159_ = l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(v_pu_boxed_3158_, v_decl_3154_, v_value_3155_, v_a_3156_);
lean_dec(v_a_3156_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue(uint8_t v_pu_3160_, lean_object* v_decl_3161_, lean_object* v_value_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_){
_start:
{
lean_object* v_params_3168_; lean_object* v_type_3169_; lean_object* v___x_3170_; 
v_params_3168_ = lean_ctor_get(v_decl_3161_, 2);
lean_inc_ref(v_params_3168_);
v_type_3169_ = lean_ctor_get(v_decl_3161_, 3);
lean_inc_ref(v_type_3169_);
v___x_3170_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_3160_, v_decl_3161_, v_type_3169_, v_params_3168_, v_value_3162_, v_a_3164_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___boxed(lean_object* v_pu_3171_, lean_object* v_decl_3172_, lean_object* v_value_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_){
_start:
{
uint8_t v_pu_boxed_3179_; lean_object* v_res_3180_; 
v_pu_boxed_3179_ = lean_unbox(v_pu_3171_);
v_res_3180_ = l_Lean_Compiler_LCNF_FunDecl_updateValue(v_pu_boxed_3179_, v_decl_3172_, v_value_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_);
lean_dec(v_a_3177_);
lean_dec_ref(v_a_3176_);
lean_dec(v_a_3175_);
lean_dec_ref(v_a_3174_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0(uint8_t v_pu_3181_, lean_object* v_p_3182_, lean_object* v_inst_3183_, lean_object* v_____do__lift_3184_){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3185_ = lean_box(v_pu_3181_);
v___x_3186_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_3186_, 0, v___x_3185_);
lean_closure_set(v___x_3186_, 1, v_p_3182_);
lean_closure_set(v___x_3186_, 2, v_____do__lift_3184_);
v___x_3187_ = lean_apply_2(v_inst_3183_, lean_box(0), v___x_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed(lean_object* v_pu_3188_, lean_object* v_p_3189_, lean_object* v_inst_3190_, lean_object* v_____do__lift_3191_){
_start:
{
uint8_t v_pu_boxed_3192_; lean_object* v_res_3193_; 
v_pu_boxed_3192_ = lean_unbox(v_pu_3188_);
v_res_3193_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__0(v_pu_boxed_3192_, v_p_3189_, v_inst_3190_, v_____do__lift_3191_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1(uint8_t v_pu_3194_, uint8_t v_t_3195_, lean_object* v_type_3196_, lean_object* v_toPure_3197_, lean_object* v_____do__lift_3198_){
_start:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3199_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3194_, v_____do__lift_3198_, v_t_3195_, v_type_3196_);
v___x_3200_ = lean_apply_2(v_toPure_3197_, lean_box(0), v___x_3199_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed(lean_object* v_pu_3201_, lean_object* v_t_3202_, lean_object* v_type_3203_, lean_object* v_toPure_3204_, lean_object* v_____do__lift_3205_){
_start:
{
uint8_t v_pu_boxed_3206_; uint8_t v_t_boxed_3207_; lean_object* v_res_3208_; 
v_pu_boxed_3206_ = lean_unbox(v_pu_3201_);
v_t_boxed_3207_ = lean_unbox(v_t_3202_);
v_res_3208_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__1(v_pu_boxed_3206_, v_t_boxed_3207_, v_type_3203_, v_toPure_3204_, v_____do__lift_3205_);
lean_dec_ref(v_____do__lift_3205_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg(uint8_t v_pu_3209_, uint8_t v_t_3210_, lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_inst_3213_, lean_object* v_p_3214_){
_start:
{
lean_object* v_toApplicative_3215_; lean_object* v_toBind_3216_; lean_object* v_type_3217_; lean_object* v_toPure_3218_; lean_object* v___x_3219_; lean_object* v___f_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___f_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v_toApplicative_3215_ = lean_ctor_get(v_inst_3212_, 0);
lean_inc_ref(v_toApplicative_3215_);
v_toBind_3216_ = lean_ctor_get(v_inst_3212_, 1);
lean_inc_n(v_toBind_3216_, 2);
lean_dec_ref(v_inst_3212_);
v_type_3217_ = lean_ctor_get(v_p_3214_, 2);
lean_inc_ref(v_type_3217_);
v_toPure_3218_ = lean_ctor_get(v_toApplicative_3215_, 1);
lean_inc(v_toPure_3218_);
lean_dec_ref(v_toApplicative_3215_);
v___x_3219_ = lean_box(v_pu_3209_);
v___f_3220_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3220_, 0, v___x_3219_);
lean_closure_set(v___f_3220_, 1, v_p_3214_);
lean_closure_set(v___f_3220_, 2, v_inst_3211_);
v___x_3221_ = lean_box(v_pu_3209_);
v___x_3222_ = lean_box(v_t_3210_);
v___f_3223_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3223_, 0, v___x_3221_);
lean_closure_set(v___f_3223_, 1, v___x_3222_);
lean_closure_set(v___f_3223_, 2, v_type_3217_);
lean_closure_set(v___f_3223_, 3, v_toPure_3218_);
v___x_3224_ = lean_apply_4(v_toBind_3216_, lean_box(0), lean_box(0), v_inst_3213_, v___f_3223_);
v___x_3225_ = lean_apply_4(v_toBind_3216_, lean_box(0), lean_box(0), v___x_3224_, v___f_3220_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___boxed(lean_object* v_pu_3226_, lean_object* v_t_3227_, lean_object* v_inst_3228_, lean_object* v_inst_3229_, lean_object* v_inst_3230_, lean_object* v_p_3231_){
_start:
{
uint8_t v_pu_boxed_3232_; uint8_t v_t_boxed_3233_; lean_object* v_res_3234_; 
v_pu_boxed_3232_ = lean_unbox(v_pu_3226_);
v_t_boxed_3233_ = lean_unbox(v_t_3227_);
v_res_3234_ = l_Lean_Compiler_LCNF_normParam___redArg(v_pu_boxed_3232_, v_t_boxed_3233_, v_inst_3228_, v_inst_3229_, v_inst_3230_, v_p_3231_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam(lean_object* v_m_3235_, uint8_t v_pu_3236_, uint8_t v_t_3237_, lean_object* v_inst_3238_, lean_object* v_inst_3239_, lean_object* v_inst_3240_, lean_object* v_p_3241_){
_start:
{
lean_object* v_toApplicative_3242_; lean_object* v_toBind_3243_; lean_object* v_type_3244_; lean_object* v_toPure_3245_; lean_object* v___x_3246_; lean_object* v___f_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___f_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v_toApplicative_3242_ = lean_ctor_get(v_inst_3239_, 0);
lean_inc_ref(v_toApplicative_3242_);
v_toBind_3243_ = lean_ctor_get(v_inst_3239_, 1);
lean_inc_n(v_toBind_3243_, 2);
lean_dec_ref(v_inst_3239_);
v_type_3244_ = lean_ctor_get(v_p_3241_, 2);
lean_inc_ref(v_type_3244_);
v_toPure_3245_ = lean_ctor_get(v_toApplicative_3242_, 1);
lean_inc(v_toPure_3245_);
lean_dec_ref(v_toApplicative_3242_);
v___x_3246_ = lean_box(v_pu_3236_);
v___f_3247_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3247_, 0, v___x_3246_);
lean_closure_set(v___f_3247_, 1, v_p_3241_);
lean_closure_set(v___f_3247_, 2, v_inst_3238_);
v___x_3248_ = lean_box(v_pu_3236_);
v___x_3249_ = lean_box(v_t_3237_);
v___f_3250_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3250_, 0, v___x_3248_);
lean_closure_set(v___f_3250_, 1, v___x_3249_);
lean_closure_set(v___f_3250_, 2, v_type_3244_);
lean_closure_set(v___f_3250_, 3, v_toPure_3245_);
v___x_3251_ = lean_apply_4(v_toBind_3243_, lean_box(0), lean_box(0), v_inst_3240_, v___f_3250_);
v___x_3252_ = lean_apply_4(v_toBind_3243_, lean_box(0), lean_box(0), v___x_3251_, v___f_3247_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___boxed(lean_object* v_m_3253_, lean_object* v_pu_3254_, lean_object* v_t_3255_, lean_object* v_inst_3256_, lean_object* v_inst_3257_, lean_object* v_inst_3258_, lean_object* v_p_3259_){
_start:
{
uint8_t v_pu_boxed_3260_; uint8_t v_t_boxed_3261_; lean_object* v_res_3262_; 
v_pu_boxed_3260_ = lean_unbox(v_pu_3254_);
v_t_boxed_3261_ = lean_unbox(v_t_3255_);
v_res_3262_ = l_Lean_Compiler_LCNF_normParam(v_m_3253_, v_pu_boxed_3260_, v_t_boxed_3261_, v_inst_3256_, v_inst_3257_, v_inst_3258_, v_p_3259_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg(uint8_t v_pu_3263_, uint8_t v_t_3264_, lean_object* v_inst_3265_, lean_object* v_inst_3266_, lean_object* v_inst_3267_, lean_object* v_ps_3268_){
_start:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3269_ = lean_box(v_pu_3263_);
v___x_3270_ = lean_box(v_t_3264_);
lean_inc_ref(v_inst_3266_);
v___x_3271_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___boxed), 7, 6);
lean_closure_set(v___x_3271_, 0, lean_box(0));
lean_closure_set(v___x_3271_, 1, v___x_3269_);
lean_closure_set(v___x_3271_, 2, v___x_3270_);
lean_closure_set(v___x_3271_, 3, v_inst_3265_);
lean_closure_set(v___x_3271_, 4, v_inst_3266_);
lean_closure_set(v___x_3271_, 5, v_inst_3267_);
v___x_3272_ = lean_unsigned_to_nat(0u);
v___x_3273_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_3266_, v___x_3271_, v___x_3272_, v_ps_3268_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg___boxed(lean_object* v_pu_3274_, lean_object* v_t_3275_, lean_object* v_inst_3276_, lean_object* v_inst_3277_, lean_object* v_inst_3278_, lean_object* v_ps_3279_){
_start:
{
uint8_t v_pu_boxed_3280_; uint8_t v_t_boxed_3281_; lean_object* v_res_3282_; 
v_pu_boxed_3280_ = lean_unbox(v_pu_3274_);
v_t_boxed_3281_ = lean_unbox(v_t_3275_);
v_res_3282_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_boxed_3280_, v_t_boxed_3281_, v_inst_3276_, v_inst_3277_, v_inst_3278_, v_ps_3279_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams(lean_object* v_m_3283_, uint8_t v_pu_3284_, uint8_t v_t_3285_, lean_object* v_inst_3286_, lean_object* v_inst_3287_, lean_object* v_inst_3288_, lean_object* v_ps_3289_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_3284_, v_t_3285_, v_inst_3286_, v_inst_3287_, v_inst_3288_, v_ps_3289_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___boxed(lean_object* v_m_3291_, lean_object* v_pu_3292_, lean_object* v_t_3293_, lean_object* v_inst_3294_, lean_object* v_inst_3295_, lean_object* v_inst_3296_, lean_object* v_ps_3297_){
_start:
{
uint8_t v_pu_boxed_3298_; uint8_t v_t_boxed_3299_; lean_object* v_res_3300_; 
v_pu_boxed_3298_ = lean_unbox(v_pu_3292_);
v_t_boxed_3299_ = lean_unbox(v_t_3293_);
v_res_3300_ = l_Lean_Compiler_LCNF_normParams(v_m_3291_, v_pu_boxed_3298_, v_t_boxed_3299_, v_inst_3294_, v_inst_3295_, v_inst_3296_, v_ps_3297_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(uint8_t v_pu_3301_, lean_object* v_decl_3302_, lean_object* v_____do__lift_3303_, lean_object* v_inst_3304_, lean_object* v_____do__lift_3305_){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3306_ = lean_box(v_pu_3301_);
v___x_3307_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_3307_, 0, v___x_3306_);
lean_closure_set(v___x_3307_, 1, v_decl_3302_);
lean_closure_set(v___x_3307_, 2, v_____do__lift_3303_);
lean_closure_set(v___x_3307_, 3, v_____do__lift_3305_);
v___x_3308_ = lean_apply_2(v_inst_3304_, lean_box(0), v___x_3307_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed(lean_object* v_pu_3309_, lean_object* v_decl_3310_, lean_object* v_____do__lift_3311_, lean_object* v_inst_3312_, lean_object* v_____do__lift_3313_){
_start:
{
uint8_t v_pu_boxed_3314_; lean_object* v_res_3315_; 
v_pu_boxed_3314_ = lean_unbox(v_pu_3309_);
v_res_3315_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(v_pu_boxed_3314_, v_decl_3310_, v_____do__lift_3311_, v_inst_3312_, v_____do__lift_3313_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(uint8_t v_pu_3316_, lean_object* v_value_3317_, uint8_t v_t_3318_, lean_object* v_toPure_3319_, lean_object* v_____do__lift_3320_){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3316_, v_____do__lift_3320_, v_value_3317_, v_t_3318_);
v___x_3322_ = lean_apply_2(v_toPure_3319_, lean_box(0), v___x_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed(lean_object* v_pu_3323_, lean_object* v_value_3324_, lean_object* v_t_3325_, lean_object* v_toPure_3326_, lean_object* v_____do__lift_3327_){
_start:
{
uint8_t v_pu_boxed_3328_; uint8_t v_t_boxed_3329_; lean_object* v_res_3330_; 
v_pu_boxed_3328_ = lean_unbox(v_pu_3323_);
v_t_boxed_3329_ = lean_unbox(v_t_3325_);
v_res_3330_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(v_pu_boxed_3328_, v_value_3324_, v_t_boxed_3329_, v_toPure_3326_, v_____do__lift_3327_);
lean_dec_ref(v_____do__lift_3327_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(uint8_t v_pu_3331_, lean_object* v_decl_3332_, lean_object* v_inst_3333_, lean_object* v_value_3334_, uint8_t v_t_3335_, lean_object* v_toPure_3336_, lean_object* v_toBind_3337_, lean_object* v_inst_3338_, lean_object* v_____do__lift_3339_){
_start:
{
lean_object* v___x_3340_; lean_object* v___f_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___f_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3340_ = lean_box(v_pu_3331_);
v___f_3341_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3341_, 0, v___x_3340_);
lean_closure_set(v___f_3341_, 1, v_decl_3332_);
lean_closure_set(v___f_3341_, 2, v_____do__lift_3339_);
lean_closure_set(v___f_3341_, 3, v_inst_3333_);
v___x_3342_ = lean_box(v_pu_3331_);
v___x_3343_ = lean_box(v_t_3335_);
v___f_3344_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3344_, 0, v___x_3342_);
lean_closure_set(v___f_3344_, 1, v_value_3334_);
lean_closure_set(v___f_3344_, 2, v___x_3343_);
lean_closure_set(v___f_3344_, 3, v_toPure_3336_);
lean_inc(v_toBind_3337_);
v___x_3345_ = lean_apply_4(v_toBind_3337_, lean_box(0), lean_box(0), v_inst_3338_, v___f_3344_);
v___x_3346_ = lean_apply_4(v_toBind_3337_, lean_box(0), lean_box(0), v___x_3345_, v___f_3341_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed(lean_object* v_pu_3347_, lean_object* v_decl_3348_, lean_object* v_inst_3349_, lean_object* v_value_3350_, lean_object* v_t_3351_, lean_object* v_toPure_3352_, lean_object* v_toBind_3353_, lean_object* v_inst_3354_, lean_object* v_____do__lift_3355_){
_start:
{
uint8_t v_pu_boxed_3356_; uint8_t v_t_boxed_3357_; lean_object* v_res_3358_; 
v_pu_boxed_3356_ = lean_unbox(v_pu_3347_);
v_t_boxed_3357_ = lean_unbox(v_t_3351_);
v_res_3358_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(v_pu_boxed_3356_, v_decl_3348_, v_inst_3349_, v_value_3350_, v_t_boxed_3357_, v_toPure_3352_, v_toBind_3353_, v_inst_3354_, v_____do__lift_3355_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg(uint8_t v_pu_3359_, uint8_t v_t_3360_, lean_object* v_inst_3361_, lean_object* v_inst_3362_, lean_object* v_inst_3363_, lean_object* v_decl_3364_){
_start:
{
lean_object* v_toApplicative_3365_; lean_object* v_toBind_3366_; lean_object* v_type_3367_; lean_object* v_value_3368_; lean_object* v_toPure_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___f_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___f_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v_toApplicative_3365_ = lean_ctor_get(v_inst_3362_, 0);
lean_inc_ref(v_toApplicative_3365_);
v_toBind_3366_ = lean_ctor_get(v_inst_3362_, 1);
lean_inc_n(v_toBind_3366_, 3);
lean_dec_ref(v_inst_3362_);
v_type_3367_ = lean_ctor_get(v_decl_3364_, 2);
lean_inc_ref(v_type_3367_);
v_value_3368_ = lean_ctor_get(v_decl_3364_, 3);
lean_inc(v_value_3368_);
v_toPure_3369_ = lean_ctor_get(v_toApplicative_3365_, 1);
lean_inc_n(v_toPure_3369_, 2);
lean_dec_ref(v_toApplicative_3365_);
v___x_3370_ = lean_box(v_pu_3359_);
v___x_3371_ = lean_box(v_t_3360_);
lean_inc(v_inst_3363_);
v___f_3372_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_3372_, 0, v___x_3370_);
lean_closure_set(v___f_3372_, 1, v_decl_3364_);
lean_closure_set(v___f_3372_, 2, v_inst_3361_);
lean_closure_set(v___f_3372_, 3, v_value_3368_);
lean_closure_set(v___f_3372_, 4, v___x_3371_);
lean_closure_set(v___f_3372_, 5, v_toPure_3369_);
lean_closure_set(v___f_3372_, 6, v_toBind_3366_);
lean_closure_set(v___f_3372_, 7, v_inst_3363_);
v___x_3373_ = lean_box(v_pu_3359_);
v___x_3374_ = lean_box(v_t_3360_);
v___f_3375_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3375_, 0, v___x_3373_);
lean_closure_set(v___f_3375_, 1, v___x_3374_);
lean_closure_set(v___f_3375_, 2, v_type_3367_);
lean_closure_set(v___f_3375_, 3, v_toPure_3369_);
v___x_3376_ = lean_apply_4(v_toBind_3366_, lean_box(0), lean_box(0), v_inst_3363_, v___f_3375_);
v___x_3377_ = lean_apply_4(v_toBind_3366_, lean_box(0), lean_box(0), v___x_3376_, v___f_3372_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___boxed(lean_object* v_pu_3378_, lean_object* v_t_3379_, lean_object* v_inst_3380_, lean_object* v_inst_3381_, lean_object* v_inst_3382_, lean_object* v_decl_3383_){
_start:
{
uint8_t v_pu_boxed_3384_; uint8_t v_t_boxed_3385_; lean_object* v_res_3386_; 
v_pu_boxed_3384_ = lean_unbox(v_pu_3378_);
v_t_boxed_3385_ = lean_unbox(v_t_3379_);
v_res_3386_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_boxed_3384_, v_t_boxed_3385_, v_inst_3380_, v_inst_3381_, v_inst_3382_, v_decl_3383_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl(lean_object* v_m_3387_, uint8_t v_pu_3388_, uint8_t v_t_3389_, lean_object* v_inst_3390_, lean_object* v_inst_3391_, lean_object* v_inst_3392_, lean_object* v_decl_3393_){
_start:
{
lean_object* v___x_3394_; 
v___x_3394_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_3388_, v_t_3389_, v_inst_3390_, v_inst_3391_, v_inst_3392_, v_decl_3393_);
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___boxed(lean_object* v_m_3395_, lean_object* v_pu_3396_, lean_object* v_t_3397_, lean_object* v_inst_3398_, lean_object* v_inst_3399_, lean_object* v_inst_3400_, lean_object* v_decl_3401_){
_start:
{
uint8_t v_pu_boxed_3402_; uint8_t v_t_boxed_3403_; lean_object* v_res_3404_; 
v_pu_boxed_3402_ = lean_unbox(v_pu_3396_);
v_t_boxed_3403_ = lean_unbox(v_t_3397_);
v_res_3404_ = l_Lean_Compiler_LCNF_normLetDecl(v_m_3395_, v_pu_boxed_3402_, v_t_boxed_3403_, v_inst_3398_, v_inst_3399_, v_inst_3400_, v_decl_3401_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(uint8_t v_pu_3405_, uint8_t v_t_3406_){
_start:
{
lean_object* v___x_3407_; lean_object* v_toApplicative_3408_; lean_object* v_toFunctor_3409_; lean_object* v_toSeq_3410_; lean_object* v_toSeqLeft_3411_; lean_object* v_toSeqRight_3412_; lean_object* v___f_3413_; lean_object* v___f_3414_; lean_object* v___f_3415_; lean_object* v___f_3416_; lean_object* v___x_3417_; lean_object* v___f_3418_; lean_object* v___f_3419_; lean_object* v___f_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v_toApplicative_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3452_; 
v___x_3407_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_3408_ = lean_ctor_get(v___x_3407_, 0);
v_toFunctor_3409_ = lean_ctor_get(v_toApplicative_3408_, 0);
v_toSeq_3410_ = lean_ctor_get(v_toApplicative_3408_, 2);
v_toSeqLeft_3411_ = lean_ctor_get(v_toApplicative_3408_, 3);
v_toSeqRight_3412_ = lean_ctor_get(v_toApplicative_3408_, 4);
v___f_3413_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_3414_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_3409_, 2);
v___f_3415_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3415_, 0, v_toFunctor_3409_);
v___f_3416_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3416_, 0, v_toFunctor_3409_);
v___x_3417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___f_3415_);
lean_ctor_set(v___x_3417_, 1, v___f_3416_);
lean_inc(v_toSeqRight_3412_);
v___f_3418_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3418_, 0, v_toSeqRight_3412_);
lean_inc(v_toSeqLeft_3411_);
v___f_3419_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3419_, 0, v_toSeqLeft_3411_);
lean_inc(v_toSeq_3410_);
v___f_3420_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3420_, 0, v_toSeq_3410_);
v___x_3421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3417_);
lean_ctor_set(v___x_3421_, 1, v___f_3413_);
lean_ctor_set(v___x_3421_, 2, v___f_3420_);
lean_ctor_set(v___x_3421_, 3, v___f_3419_);
lean_ctor_set(v___x_3421_, 4, v___f_3418_);
v___x_3422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
lean_ctor_set(v___x_3422_, 1, v___f_3414_);
v___x_3423_ = l_StateRefT_x27_instMonad___redArg(v___x_3422_);
v_toApplicative_3424_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3452_ == 0)
{
lean_object* v_unused_3453_; 
v_unused_3453_ = lean_ctor_get(v___x_3423_, 1);
lean_dec(v_unused_3453_);
v___x_3426_ = v___x_3423_;
v_isShared_3427_ = v_isSharedCheck_3452_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_toApplicative_3424_);
lean_dec(v___x_3423_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3452_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v_toFunctor_3428_; lean_object* v_toSeq_3429_; lean_object* v_toSeqLeft_3430_; lean_object* v_toSeqRight_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3450_; 
v_toFunctor_3428_ = lean_ctor_get(v_toApplicative_3424_, 0);
v_toSeq_3429_ = lean_ctor_get(v_toApplicative_3424_, 2);
v_toSeqLeft_3430_ = lean_ctor_get(v_toApplicative_3424_, 3);
v_toSeqRight_3431_ = lean_ctor_get(v_toApplicative_3424_, 4);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_toApplicative_3424_);
if (v_isSharedCheck_3450_ == 0)
{
lean_object* v_unused_3451_; 
v_unused_3451_ = lean_ctor_get(v_toApplicative_3424_, 1);
lean_dec(v_unused_3451_);
v___x_3433_ = v_toApplicative_3424_;
v_isShared_3434_ = v_isSharedCheck_3450_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_toSeqRight_3431_);
lean_inc(v_toSeqLeft_3430_);
lean_inc(v_toSeq_3429_);
lean_inc(v_toFunctor_3428_);
lean_dec(v_toApplicative_3424_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3450_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___f_3435_; lean_object* v___f_3436_; lean_object* v___f_3437_; lean_object* v___f_3438_; lean_object* v___x_3439_; lean_object* v___f_3440_; lean_object* v___f_3441_; lean_object* v___f_3442_; lean_object* v___x_3444_; 
v___f_3435_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_3436_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_3428_);
v___f_3437_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3437_, 0, v_toFunctor_3428_);
v___f_3438_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3438_, 0, v_toFunctor_3428_);
v___x_3439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3439_, 0, v___f_3437_);
lean_ctor_set(v___x_3439_, 1, v___f_3438_);
v___f_3440_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3440_, 0, v_toSeqRight_3431_);
v___f_3441_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3441_, 0, v_toSeqLeft_3430_);
v___f_3442_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3442_, 0, v_toSeq_3429_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 4, v___f_3440_);
lean_ctor_set(v___x_3433_, 3, v___f_3441_);
lean_ctor_set(v___x_3433_, 2, v___f_3442_);
lean_ctor_set(v___x_3433_, 1, v___f_3435_);
lean_ctor_set(v___x_3433_, 0, v___x_3439_);
v___x_3444_ = v___x_3433_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3439_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v___f_3435_);
lean_ctor_set(v_reuseFailAlloc_3449_, 2, v___f_3442_);
lean_ctor_set(v_reuseFailAlloc_3449_, 3, v___f_3441_);
lean_ctor_set(v_reuseFailAlloc_3449_, 4, v___f_3440_);
v___x_3444_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3446_; 
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 1, v___f_3436_);
lean_ctor_set(v___x_3426_, 0, v___x_3444_);
v___x_3446_ = v___x_3426_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3444_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v___f_3436_);
v___x_3446_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3447_; 
v___x_3447_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_3447_, 0, lean_box(0));
lean_closure_set(v___x_3447_, 1, lean_box(0));
lean_closure_set(v___x_3447_, 2, v___x_3446_);
return v___x_3447_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___boxed(lean_object* v_pu_3454_, lean_object* v_t_3455_){
_start:
{
uint8_t v_pu_boxed_3456_; uint8_t v_t_boxed_3457_; lean_object* v_res_3458_; 
v_pu_boxed_3456_ = lean_unbox(v_pu_3454_);
v_t_boxed_3457_ = lean_unbox(v_t_3455_);
v_res_3458_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(v_pu_boxed_3456_, v_t_boxed_3457_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg(uint8_t v_pu_3459_, lean_object* v_inst_3460_, lean_object* v_result_3461_, lean_object* v_x_3462_){
_start:
{
if (lean_obj_tag(v_result_3461_) == 0)
{
lean_object* v_fvarId_3463_; lean_object* v___x_3464_; 
lean_dec(v_inst_3460_);
v_fvarId_3463_ = lean_ctor_get(v_result_3461_, 0);
lean_inc(v_fvarId_3463_);
lean_dec_ref_known(v_result_3461_, 1);
v___x_3464_ = lean_apply_1(v_x_3462_, v_fvarId_3463_);
return v___x_3464_;
}
else
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
lean_dec(v_x_3462_);
v___x_3465_ = lean_box(v_pu_3459_);
v___x_3466_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3466_, 0, v___x_3465_);
v___x_3467_ = lean_apply_2(v_inst_3460_, lean_box(0), v___x_3466_);
return v___x_3467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg___boxed(lean_object* v_pu_3468_, lean_object* v_inst_3469_, lean_object* v_result_3470_, lean_object* v_x_3471_){
_start:
{
uint8_t v_pu_boxed_3472_; lean_object* v_res_3473_; 
v_pu_boxed_3472_ = lean_unbox(v_pu_3468_);
v_res_3473_ = l_Lean_Compiler_LCNF_withNormFVarResult___redArg(v_pu_boxed_3472_, v_inst_3469_, v_result_3470_, v_x_3471_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult(lean_object* v_m_3474_, uint8_t v_pu_3475_, lean_object* v_inst_3476_, lean_object* v_inst_3477_, lean_object* v_result_3478_, lean_object* v_x_3479_){
_start:
{
if (lean_obj_tag(v_result_3478_) == 0)
{
lean_object* v_fvarId_3480_; lean_object* v___x_3481_; 
lean_dec(v_inst_3476_);
v_fvarId_3480_ = lean_ctor_get(v_result_3478_, 0);
lean_inc(v_fvarId_3480_);
lean_dec_ref_known(v_result_3478_, 1);
v___x_3481_ = lean_apply_1(v_x_3479_, v_fvarId_3480_);
return v___x_3481_;
}
else
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
lean_dec(v_x_3479_);
v___x_3482_ = lean_box(v_pu_3475_);
v___x_3483_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3483_, 0, v___x_3482_);
v___x_3484_ = lean_apply_2(v_inst_3476_, lean_box(0), v___x_3483_);
return v___x_3484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___boxed(lean_object* v_m_3485_, lean_object* v_pu_3486_, lean_object* v_inst_3487_, lean_object* v_inst_3488_, lean_object* v_result_3489_, lean_object* v_x_3490_){
_start:
{
uint8_t v_pu_boxed_3491_; lean_object* v_res_3492_; 
v_pu_boxed_3491_ = lean_unbox(v_pu_3486_);
v_res_3492_ = l_Lean_Compiler_LCNF_withNormFVarResult(v_m_3485_, v_pu_boxed_3491_, v_inst_3487_, v_inst_3488_, v_result_3489_, v_x_3490_);
lean_dec_ref(v_inst_3488_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(uint8_t v_pu_3493_, uint8_t v_t_3494_, lean_object* v_args_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3498_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_3493_, v___y_3496_, v_args_3495_, v_t_3494_);
v___x_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg___boxed(lean_object* v_pu_3500_, lean_object* v_t_3501_, lean_object* v_args_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
uint8_t v_pu_boxed_3505_; uint8_t v_t_boxed_3506_; lean_object* v_res_3507_; 
v_pu_boxed_3505_ = lean_unbox(v_pu_3500_);
v_t_boxed_3506_ = lean_unbox(v_t_3501_);
v_res_3507_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_boxed_3505_, v_t_boxed_3506_, v_args_3502_, v___y_3503_);
lean_dec_ref(v___y_3503_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(uint8_t v_pu_3508_, uint8_t v_t_3509_, lean_object* v_i_3510_, lean_object* v_as_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v___x_3515_; uint8_t v___x_3516_; 
v___x_3515_ = lean_array_get_size(v_as_3511_);
v___x_3516_ = lean_nat_dec_lt(v_i_3510_, v___x_3515_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; 
lean_dec(v_i_3510_);
v___x_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3517_, 0, v_as_3511_);
return v___x_3517_;
}
else
{
lean_object* v_a_3518_; lean_object* v_type_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v_a_3518_ = lean_array_fget_borrowed(v_as_3511_, v_i_3510_);
v_type_3519_ = lean_ctor_get(v_a_3518_, 2);
lean_inc_ref(v_type_3519_);
v___x_3520_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3508_, v___y_3512_, v_t_3509_, v_type_3519_);
lean_inc(v_a_3518_);
v___x_3521_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_3508_, v_a_3518_, v___x_3520_, v___y_3513_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; size_t v___x_3523_; size_t v___x_3524_; uint8_t v___x_3525_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref_known(v___x_3521_, 1);
v___x_3523_ = lean_ptr_addr(v_a_3518_);
v___x_3524_ = lean_ptr_addr(v_a_3522_);
v___x_3525_ = lean_usize_dec_eq(v___x_3523_, v___x_3524_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3526_ = lean_unsigned_to_nat(1u);
v___x_3527_ = lean_nat_add(v_i_3510_, v___x_3526_);
v___x_3528_ = lean_array_fset(v_as_3511_, v_i_3510_, v_a_3522_);
lean_dec(v_i_3510_);
v_i_3510_ = v___x_3527_;
v_as_3511_ = v___x_3528_;
goto _start;
}
else
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
lean_dec(v_a_3522_);
v___x_3530_ = lean_unsigned_to_nat(1u);
v___x_3531_ = lean_nat_add(v_i_3510_, v___x_3530_);
lean_dec(v_i_3510_);
v_i_3510_ = v___x_3531_;
goto _start;
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_dec_ref(v_as_3511_);
lean_dec(v_i_3510_);
v_a_3533_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3521_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3521_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg___boxed(lean_object* v_pu_3541_, lean_object* v_t_3542_, lean_object* v_i_3543_, lean_object* v_as_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
uint8_t v_pu_boxed_3548_; uint8_t v_t_boxed_3549_; lean_object* v_res_3550_; 
v_pu_boxed_3548_ = lean_unbox(v_pu_3541_);
v_t_boxed_3549_ = lean_unbox(v_t_3542_);
v_res_3550_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_boxed_3548_, v_t_boxed_3549_, v_i_3543_, v_as_3544_, v___y_3545_, v___y_3546_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(uint8_t v_pu_3551_, uint8_t v_t_3552_, lean_object* v_ps_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = lean_unsigned_to_nat(0u);
v___x_3561_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_3551_, v_t_3552_, v___x_3560_, v_ps_3553_, v___y_3554_, v___y_3556_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg___boxed(lean_object* v_pu_3562_, lean_object* v_t_3563_, lean_object* v_ps_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
uint8_t v_pu_boxed_3571_; uint8_t v_t_boxed_3572_; lean_object* v_res_3573_; 
v_pu_boxed_3571_ = lean_unbox(v_pu_3562_);
v_t_boxed_3572_ = lean_unbox(v_t_3563_);
v_res_3573_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_boxed_3571_, v_t_boxed_3572_, v_ps_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec_ref(v___y_3565_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(uint8_t v_pu_3574_, uint8_t v_t_3575_, lean_object* v_decl_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
lean_object* v_type_3580_; lean_object* v_value_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v_type_3580_ = lean_ctor_get(v_decl_3576_, 2);
v_value_3581_ = lean_ctor_get(v_decl_3576_, 3);
lean_inc_ref(v_type_3580_);
v___x_3582_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3574_, v___y_3577_, v_t_3575_, v_type_3580_);
lean_inc(v_value_3581_);
v___x_3583_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3574_, v___y_3577_, v_value_3581_, v_t_3575_);
v___x_3584_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_3574_, v_decl_3576_, v___x_3582_, v___x_3583_, v___y_3578_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg___boxed(lean_object* v_pu_3585_, lean_object* v_t_3586_, lean_object* v_decl_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
uint8_t v_pu_boxed_3591_; uint8_t v_t_boxed_3592_; lean_object* v_res_3593_; 
v_pu_boxed_3591_ = lean_unbox(v_pu_3585_);
v_t_boxed_3592_ = lean_unbox(v_t_3586_);
v_res_3593_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_boxed_3591_, v_t_boxed_3592_, v_decl_3587_, v___y_3588_, v___y_3589_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(uint8_t v_pu_3594_, uint8_t v_t_3595_, lean_object* v_i_3596_, lean_object* v_as_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
lean_object* v___x_3604_; uint8_t v___x_3605_; 
v___x_3604_ = lean_array_get_size(v_as_3597_);
v___x_3605_ = lean_nat_dec_lt(v_i_3596_, v___x_3604_);
if (v___x_3605_ == 0)
{
lean_object* v___x_3606_; 
lean_dec(v_i_3596_);
v___x_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3606_, 0, v_as_3597_);
return v___x_3606_;
}
else
{
lean_object* v_a_3607_; lean_object* v_a_3609_; 
v_a_3607_ = lean_array_fget_borrowed(v_as_3597_, v_i_3596_);
switch(lean_obj_tag(v_a_3607_))
{
case 0:
{
lean_object* v_params_3620_; lean_object* v_code_3621_; lean_object* v___x_3622_; 
v_params_3620_ = lean_ctor_get(v_a_3607_, 1);
v_code_3621_ = lean_ctor_get(v_a_3607_, 2);
lean_inc_ref(v_params_3620_);
v___x_3622_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_3594_, v_t_3595_, v_params_3620_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v_a_3623_; lean_object* v___x_3624_; 
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_a_3623_);
lean_dec_ref_known(v___x_3622_, 1);
lean_inc_ref(v_code_3621_);
v___x_3624_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3594_, v_t_3595_, v_code_3621_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v___x_3626_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
lean_dec_ref_known(v___x_3624_, 1);
lean_inc_ref(v_a_3607_);
v___x_3626_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_3594_, v_a_3607_, v_a_3623_, v_a_3625_);
v_a_3609_ = v___x_3626_;
goto v___jp_3608_;
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec(v_a_3623_);
lean_dec_ref(v_as_3597_);
lean_dec(v_i_3596_);
v_a_3627_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3624_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3624_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
lean_dec_ref(v_as_3597_);
lean_dec(v_i_3596_);
v_a_3635_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3622_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3622_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
case 1:
{
lean_object* v_code_3643_; lean_object* v___x_3644_; 
v_code_3643_ = lean_ctor_get(v_a_3607_, 1);
lean_inc_ref(v_code_3643_);
v___x_3644_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3594_, v_t_3595_, v_code_3643_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v___x_3646_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref_known(v___x_3644_, 1);
lean_inc_ref(v_a_3607_);
v___x_3646_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3607_, v_a_3645_);
v_a_3609_ = v___x_3646_;
goto v___jp_3608_;
}
else
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3654_; 
lean_dec_ref(v_as_3597_);
lean_dec(v_i_3596_);
v_a_3647_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3649_ = v___x_3644_;
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3644_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3652_; 
if (v_isShared_3650_ == 0)
{
v___x_3652_ = v___x_3649_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_a_3647_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
}
default: 
{
lean_object* v_code_3655_; lean_object* v___x_3656_; 
v_code_3655_ = lean_ctor_get(v_a_3607_, 0);
lean_inc_ref(v_code_3655_);
v___x_3656_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3594_, v_t_3595_, v_code_3655_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v_a_3657_; lean_object* v___x_3658_; 
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_a_3657_);
lean_dec_ref_known(v___x_3656_, 1);
lean_inc_ref(v_a_3607_);
v___x_3658_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3607_, v_a_3657_);
v_a_3609_ = v___x_3658_;
goto v___jp_3608_;
}
else
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
lean_dec_ref(v_as_3597_);
lean_dec(v_i_3596_);
v_a_3659_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3656_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3656_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3659_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
}
v___jp_3608_:
{
size_t v___x_3610_; size_t v___x_3611_; uint8_t v___x_3612_; 
v___x_3610_ = lean_ptr_addr(v_a_3607_);
v___x_3611_ = lean_ptr_addr(v_a_3609_);
v___x_3612_ = lean_usize_dec_eq(v___x_3610_, v___x_3611_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3613_ = lean_unsigned_to_nat(1u);
v___x_3614_ = lean_nat_add(v_i_3596_, v___x_3613_);
v___x_3615_ = lean_array_fset(v_as_3597_, v_i_3596_, v_a_3609_);
lean_dec(v_i_3596_);
v_i_3596_ = v___x_3614_;
v_as_3597_ = v___x_3615_;
goto _start;
}
else
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
lean_dec_ref(v_a_3609_);
v___x_3617_ = lean_unsigned_to_nat(1u);
v___x_3618_ = lean_nat_add(v_i_3596_, v___x_3617_);
lean_dec(v_i_3596_);
v_i_3596_ = v___x_3618_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp(uint8_t v_pu_3667_, uint8_t v_t_3668_, lean_object* v_code_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_){
_start:
{
switch(lean_obj_tag(v_code_3669_))
{
case 0:
{
lean_object* v_decl_3676_; lean_object* v_k_3677_; lean_object* v___x_3678_; 
v_decl_3676_ = lean_ctor_get(v_code_3669_, 0);
v_k_3677_ = lean_ctor_get(v_code_3669_, 1);
lean_inc_ref(v_decl_3676_);
v___x_3678_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_3667_, v_t_3668_, v_decl_3676_, v_a_3670_, v_a_3672_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; lean_object* v___x_3680_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_a_3679_);
lean_dec_ref_known(v___x_3678_, 1);
lean_inc_ref(v_k_3677_);
v___x_3680_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3667_, v_t_3668_, v_k_3677_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3708_; 
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3683_ = v___x_3680_;
v_isShared_3684_ = v_isSharedCheck_3708_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3680_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3708_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
uint8_t v___y_3686_; size_t v___x_3702_; size_t v___x_3703_; uint8_t v___x_3704_; 
v___x_3702_ = lean_ptr_addr(v_k_3677_);
v___x_3703_ = lean_ptr_addr(v_a_3681_);
v___x_3704_ = lean_usize_dec_eq(v___x_3702_, v___x_3703_);
if (v___x_3704_ == 0)
{
v___y_3686_ = v___x_3704_;
goto v___jp_3685_;
}
else
{
size_t v___x_3705_; size_t v___x_3706_; uint8_t v___x_3707_; 
v___x_3705_ = lean_ptr_addr(v_decl_3676_);
v___x_3706_ = lean_ptr_addr(v_a_3679_);
v___x_3707_ = lean_usize_dec_eq(v___x_3705_, v___x_3706_);
v___y_3686_ = v___x_3707_;
goto v___jp_3685_;
}
v___jp_3685_:
{
if (v___y_3686_ == 0)
{
lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3696_; 
v_isSharedCheck_3696_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_3696_ == 0)
{
lean_object* v_unused_3697_; lean_object* v_unused_3698_; 
v_unused_3697_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_3697_);
v_unused_3698_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_3698_);
v___x_3688_ = v_code_3669_;
v_isShared_3689_ = v_isSharedCheck_3696_;
goto v_resetjp_3687_;
}
else
{
lean_dec(v_code_3669_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3696_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 1, v_a_3681_);
lean_ctor_set(v___x_3688_, 0, v_a_3679_);
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3679_);
lean_ctor_set(v_reuseFailAlloc_3695_, 1, v_a_3681_);
v___x_3691_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
lean_object* v___x_3693_; 
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 0, v___x_3691_);
v___x_3693_ = v___x_3683_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
else
{
lean_object* v___x_3700_; 
lean_dec(v_a_3681_);
lean_dec(v_a_3679_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 0, v_code_3669_);
v___x_3700_ = v___x_3683_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_code_3669_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
}
else
{
lean_dec(v_a_3679_);
lean_dec_ref_known(v_code_3669_, 2);
return v___x_3680_;
}
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_dec_ref_known(v_code_3669_, 2);
v_a_3709_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3678_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3678_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
case 1:
{
lean_object* v_decl_3717_; lean_object* v_k_3718_; lean_object* v___x_3719_; 
v_decl_3717_ = lean_ctor_get(v_code_3669_, 0);
v_k_3718_ = lean_ctor_get(v_code_3669_, 1);
lean_inc_ref(v_decl_3717_);
v___x_3719_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3667_, v_t_3668_, v_decl_3717_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_a_3720_; lean_object* v___x_3721_; 
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_a_3720_);
lean_dec_ref_known(v___x_3719_, 1);
lean_inc_ref(v_k_3718_);
v___x_3721_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3667_, v_t_3668_, v_k_3718_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3749_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3724_ = v___x_3721_;
v_isShared_3725_ = v_isSharedCheck_3749_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3721_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3749_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
uint8_t v___y_3727_; size_t v___x_3743_; size_t v___x_3744_; uint8_t v___x_3745_; 
v___x_3743_ = lean_ptr_addr(v_k_3718_);
v___x_3744_ = lean_ptr_addr(v_a_3722_);
v___x_3745_ = lean_usize_dec_eq(v___x_3743_, v___x_3744_);
if (v___x_3745_ == 0)
{
v___y_3727_ = v___x_3745_;
goto v___jp_3726_;
}
else
{
size_t v___x_3746_; size_t v___x_3747_; uint8_t v___x_3748_; 
v___x_3746_ = lean_ptr_addr(v_decl_3717_);
v___x_3747_ = lean_ptr_addr(v_a_3720_);
v___x_3748_ = lean_usize_dec_eq(v___x_3746_, v___x_3747_);
v___y_3727_ = v___x_3748_;
goto v___jp_3726_;
}
v___jp_3726_:
{
if (v___y_3727_ == 0)
{
lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3737_; 
v_isSharedCheck_3737_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_3737_ == 0)
{
lean_object* v_unused_3738_; lean_object* v_unused_3739_; 
v_unused_3738_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_3738_);
v_unused_3739_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_3739_);
v___x_3729_ = v_code_3669_;
v_isShared_3730_ = v_isSharedCheck_3737_;
goto v_resetjp_3728_;
}
else
{
lean_dec(v_code_3669_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3737_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 1, v_a_3722_);
lean_ctor_set(v___x_3729_, 0, v_a_3720_);
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3720_);
lean_ctor_set(v_reuseFailAlloc_3736_, 1, v_a_3722_);
v___x_3732_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
lean_object* v___x_3734_; 
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 0, v___x_3732_);
v___x_3734_ = v___x_3724_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3732_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
}
else
{
lean_object* v___x_3741_; 
lean_dec(v_a_3722_);
lean_dec(v_a_3720_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 0, v_code_3669_);
v___x_3741_ = v___x_3724_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_code_3669_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
}
else
{
lean_dec(v_a_3720_);
lean_dec_ref_known(v_code_3669_, 2);
return v___x_3721_;
}
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
lean_dec_ref_known(v_code_3669_, 2);
v_a_3750_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3719_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3719_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
case 2:
{
lean_object* v_decl_3758_; lean_object* v_k_3759_; lean_object* v___x_3760_; 
v_decl_3758_ = lean_ctor_get(v_code_3669_, 0);
v_k_3759_ = lean_ctor_get(v_code_3669_, 1);
lean_inc_ref(v_decl_3758_);
v___x_3760_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3667_, v_t_3668_, v_decl_3758_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3762_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_a_3761_);
lean_dec_ref_known(v___x_3760_, 1);
lean_inc_ref(v_k_3759_);
v___x_3762_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3667_, v_t_3668_, v_k_3759_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3790_; 
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3765_ = v___x_3762_;
v_isShared_3766_ = v_isSharedCheck_3790_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3762_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3790_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
uint8_t v___y_3768_; size_t v___x_3784_; size_t v___x_3785_; uint8_t v___x_3786_; 
v___x_3784_ = lean_ptr_addr(v_k_3759_);
v___x_3785_ = lean_ptr_addr(v_a_3763_);
v___x_3786_ = lean_usize_dec_eq(v___x_3784_, v___x_3785_);
if (v___x_3786_ == 0)
{
v___y_3768_ = v___x_3786_;
goto v___jp_3767_;
}
else
{
size_t v___x_3787_; size_t v___x_3788_; uint8_t v___x_3789_; 
v___x_3787_ = lean_ptr_addr(v_decl_3758_);
v___x_3788_ = lean_ptr_addr(v_a_3761_);
v___x_3789_ = lean_usize_dec_eq(v___x_3787_, v___x_3788_);
v___y_3768_ = v___x_3789_;
goto v___jp_3767_;
}
v___jp_3767_:
{
if (v___y_3768_ == 0)
{
lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3778_; 
v_isSharedCheck_3778_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_3778_ == 0)
{
lean_object* v_unused_3779_; lean_object* v_unused_3780_; 
v_unused_3779_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_3779_);
v_unused_3780_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_3780_);
v___x_3770_ = v_code_3669_;
v_isShared_3771_ = v_isSharedCheck_3778_;
goto v_resetjp_3769_;
}
else
{
lean_dec(v_code_3669_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3778_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 1, v_a_3763_);
lean_ctor_set(v___x_3770_, 0, v_a_3761_);
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3761_);
lean_ctor_set(v_reuseFailAlloc_3777_, 1, v_a_3763_);
v___x_3773_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
lean_object* v___x_3775_; 
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 0, v___x_3773_);
v___x_3775_ = v___x_3765_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3773_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
else
{
lean_object* v___x_3782_; 
lean_dec(v_a_3763_);
lean_dec(v_a_3761_);
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 0, v_code_3669_);
v___x_3782_ = v___x_3765_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_code_3669_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
}
else
{
lean_dec(v_a_3761_);
lean_dec_ref_known(v_code_3669_, 2);
return v___x_3762_;
}
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
lean_dec_ref_known(v_code_3669_, 2);
v_a_3791_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3760_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3760_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3799_; lean_object* v_args_3800_; lean_object* v___x_3801_; 
v_fvarId_3799_ = lean_ctor_get(v_code_3669_, 0);
v_args_3800_ = lean_ctor_get(v_code_3669_, 1);
lean_inc(v_fvarId_3799_);
v___x_3801_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3670_, v_fvarId_3799_, v_t_3668_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_fvarId_3802_; lean_object* v___x_3803_; 
v_fvarId_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_fvarId_3802_);
lean_dec_ref_known(v___x_3801_, 1);
lean_inc_ref(v_args_3800_);
v___x_3803_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_3667_, v_t_3668_, v_args_3800_, v_a_3670_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3829_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3806_ = v___x_3803_;
v_isShared_3807_ = v_isSharedCheck_3829_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3803_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3829_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
uint8_t v___y_3809_; uint8_t v___x_3825_; 
v___x_3825_ = l_Lean_instBEqFVarId_beq(v_fvarId_3799_, v_fvarId_3802_);
if (v___x_3825_ == 0)
{
v___y_3809_ = v___x_3825_;
goto v___jp_3808_;
}
else
{
size_t v___x_3826_; size_t v___x_3827_; uint8_t v___x_3828_; 
v___x_3826_ = lean_ptr_addr(v_args_3800_);
v___x_3827_ = lean_ptr_addr(v_a_3804_);
v___x_3828_ = lean_usize_dec_eq(v___x_3826_, v___x_3827_);
v___y_3809_ = v___x_3828_;
goto v___jp_3808_;
}
v___jp_3808_:
{
if (v___y_3809_ == 0)
{
lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3819_; 
v_isSharedCheck_3819_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_3819_ == 0)
{
lean_object* v_unused_3820_; lean_object* v_unused_3821_; 
v_unused_3820_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_3820_);
v_unused_3821_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_3821_);
v___x_3811_ = v_code_3669_;
v_isShared_3812_ = v_isSharedCheck_3819_;
goto v_resetjp_3810_;
}
else
{
lean_dec(v_code_3669_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3819_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 1, v_a_3804_);
lean_ctor_set(v___x_3811_, 0, v_fvarId_3802_);
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_fvarId_3802_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v_a_3804_);
v___x_3814_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
lean_object* v___x_3816_; 
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 0, v___x_3814_);
v___x_3816_ = v___x_3806_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3814_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
else
{
lean_object* v___x_3823_; 
lean_dec(v_a_3804_);
lean_dec(v_fvarId_3802_);
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 0, v_code_3669_);
v___x_3823_ = v___x_3806_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_code_3669_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
}
else
{
lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3837_; 
lean_dec(v_fvarId_3802_);
lean_dec_ref_known(v_code_3669_, 2);
v_a_3830_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3832_ = v___x_3803_;
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v___x_3803_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3835_; 
if (v_isShared_3833_ == 0)
{
v___x_3835_ = v___x_3832_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3830_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
}
else
{
lean_object* v___x_3838_; 
lean_dec_ref_known(v_code_3669_, 2);
v___x_3838_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3667_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
return v___x_3838_;
}
}
case 4:
{
lean_object* v_cases_3839_; lean_object* v_typeName_3840_; lean_object* v_resultType_3841_; lean_object* v_discr_3842_; lean_object* v_alts_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3890_; 
v_cases_3839_ = lean_ctor_get(v_code_3669_, 0);
lean_inc_ref(v_cases_3839_);
v_typeName_3840_ = lean_ctor_get(v_cases_3839_, 0);
v_resultType_3841_ = lean_ctor_get(v_cases_3839_, 1);
v_discr_3842_ = lean_ctor_get(v_cases_3839_, 2);
v_alts_3843_ = lean_ctor_get(v_cases_3839_, 3);
v_isSharedCheck_3890_ = !lean_is_exclusive(v_cases_3839_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3845_ = v_cases_3839_;
v_isShared_3846_ = v_isSharedCheck_3890_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_alts_3843_);
lean_inc(v_discr_3842_);
lean_inc(v_resultType_3841_);
lean_inc(v_typeName_3840_);
lean_dec(v_cases_3839_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3890_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; 
lean_inc_ref(v_resultType_3841_);
v___x_3847_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3667_, v_a_3670_, v_t_3668_, v_resultType_3841_);
lean_inc(v_discr_3842_);
v___x_3848_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3670_, v_discr_3842_, v_t_3668_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v_fvarId_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3888_; 
v_fvarId_3849_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3851_ = v___x_3848_;
v_isShared_3852_ = v_isSharedCheck_3888_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_fvarId_3849_);
lean_dec(v___x_3848_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3888_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3853_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3843_);
v___x_3854_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_3667_, v_t_3668_, v___x_3853_, v_alts_3843_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3879_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3857_ = v___x_3854_;
v_isShared_3858_ = v_isSharedCheck_3879_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3854_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3879_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
uint8_t v___y_3870_; size_t v___x_3873_; size_t v___x_3874_; uint8_t v___x_3875_; 
v___x_3873_ = lean_ptr_addr(v_alts_3843_);
lean_dec_ref(v_alts_3843_);
v___x_3874_ = lean_ptr_addr(v_a_3855_);
v___x_3875_ = lean_usize_dec_eq(v___x_3873_, v___x_3874_);
if (v___x_3875_ == 0)
{
lean_dec_ref(v_resultType_3841_);
v___y_3870_ = v___x_3875_;
goto v___jp_3869_;
}
else
{
size_t v___x_3876_; size_t v___x_3877_; uint8_t v___x_3878_; 
v___x_3876_ = lean_ptr_addr(v_resultType_3841_);
lean_dec_ref(v_resultType_3841_);
v___x_3877_ = lean_ptr_addr(v___x_3847_);
v___x_3878_ = lean_usize_dec_eq(v___x_3876_, v___x_3877_);
v___y_3870_ = v___x_3878_;
goto v___jp_3869_;
}
v___jp_3859_:
{
lean_object* v___x_3861_; 
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 3, v_a_3855_);
lean_ctor_set(v___x_3845_, 2, v_fvarId_3849_);
lean_ctor_set(v___x_3845_, 1, v___x_3847_);
v___x_3861_ = v___x_3845_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_typeName_3840_);
lean_ctor_set(v_reuseFailAlloc_3868_, 1, v___x_3847_);
lean_ctor_set(v_reuseFailAlloc_3868_, 2, v_fvarId_3849_);
lean_ctor_set(v_reuseFailAlloc_3868_, 3, v_a_3855_);
v___x_3861_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3863_; 
if (v_isShared_3852_ == 0)
{
lean_ctor_set_tag(v___x_3851_, 4);
lean_ctor_set(v___x_3851_, 0, v___x_3861_);
v___x_3863_ = v___x_3851_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3865_; 
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 0, v___x_3863_);
v___x_3865_ = v___x_3857_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v___x_3863_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
v___jp_3869_:
{
if (v___y_3870_ == 0)
{
lean_dec(v_discr_3842_);
lean_dec_ref_known(v_code_3669_, 1);
goto v___jp_3859_;
}
else
{
uint8_t v___x_3871_; 
v___x_3871_ = l_Lean_instBEqFVarId_beq(v_discr_3842_, v_fvarId_3849_);
lean_dec(v_discr_3842_);
if (v___x_3871_ == 0)
{
lean_dec_ref_known(v_code_3669_, 1);
goto v___jp_3859_;
}
else
{
lean_object* v___x_3872_; 
lean_del_object(v___x_3857_);
lean_dec(v_a_3855_);
lean_del_object(v___x_3851_);
lean_dec(v_fvarId_3849_);
lean_dec_ref(v___x_3847_);
lean_del_object(v___x_3845_);
lean_dec(v_typeName_3840_);
v___x_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3872_, 0, v_code_3669_);
return v___x_3872_;
}
}
}
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
lean_del_object(v___x_3851_);
lean_dec(v_fvarId_3849_);
lean_dec_ref(v___x_3847_);
lean_del_object(v___x_3845_);
lean_dec_ref(v_alts_3843_);
lean_dec(v_discr_3842_);
lean_dec_ref(v_resultType_3841_);
lean_dec(v_typeName_3840_);
lean_dec_ref_known(v_code_3669_, 1);
v_a_3880_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3854_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3854_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
}
else
{
lean_object* v___x_3889_; 
lean_dec_ref(v___x_3847_);
lean_del_object(v___x_3845_);
lean_dec_ref(v_alts_3843_);
lean_dec(v_discr_3842_);
lean_dec_ref(v_resultType_3841_);
lean_dec(v_typeName_3840_);
lean_dec_ref_known(v_code_3669_, 1);
v___x_3889_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3667_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
return v___x_3889_;
}
}
}
case 5:
{
lean_object* v_fvarId_3891_; lean_object* v___x_3892_; 
v_fvarId_3891_ = lean_ctor_get(v_code_3669_, 0);
lean_inc(v_fvarId_3891_);
v___x_3892_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3670_, v_fvarId_3891_, v_t_3668_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_fvarId_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3912_; 
v_fvarId_3893_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3895_ = v___x_3892_;
v_isShared_3896_ = v_isSharedCheck_3912_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_fvarId_3893_);
lean_dec(v___x_3892_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3912_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
uint8_t v___x_3897_; 
v___x_3897_ = l_Lean_instBEqFVarId_beq(v_fvarId_3891_, v_fvarId_3893_);
if (v___x_3897_ == 0)
{
lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3907_; 
v_isSharedCheck_3907_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_3907_ == 0)
{
lean_object* v_unused_3908_; 
v_unused_3908_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_3908_);
v___x_3899_ = v_code_3669_;
v_isShared_3900_ = v_isSharedCheck_3907_;
goto v_resetjp_3898_;
}
else
{
lean_dec(v_code_3669_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3907_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 0, v_fvarId_3893_);
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_fvarId_3893_);
v___x_3902_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
lean_object* v___x_3904_; 
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 0, v___x_3902_);
v___x_3904_ = v___x_3895_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3902_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
else
{
lean_object* v___x_3910_; 
lean_dec(v_fvarId_3893_);
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 0, v_code_3669_);
v___x_3910_ = v___x_3895_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_code_3669_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
}
else
{
lean_object* v___x_3913_; 
lean_dec_ref_known(v_code_3669_, 1);
v___x_3913_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3667_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
return v___x_3913_;
}
}
case 6:
{
lean_object* v_type_3914_; lean_object* v___x_3915_; size_t v___x_3916_; size_t v___x_3917_; uint8_t v___x_3918_; 
v_type_3914_ = lean_ctor_get(v_code_3669_, 0);
lean_inc_ref(v_type_3914_);
v___x_3915_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3667_, v_a_3670_, v_t_3668_, v_type_3914_);
v___x_3916_ = lean_ptr_addr(v_type_3914_);
v___x_3917_ = lean_ptr_addr(v___x_3915_);
v___x_3918_ = lean_usize_dec_eq(v___x_3916_, v___x_3917_);
if (v___x_3918_ == 0)
{
lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3926_; 
v_isSharedCheck_3926_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_3926_ == 0)
{
lean_object* v_unused_3927_; 
v_unused_3927_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_3927_);
v___x_3920_ = v_code_3669_;
v_isShared_3921_ = v_isSharedCheck_3926_;
goto v_resetjp_3919_;
}
else
{
lean_dec(v_code_3669_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3926_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 0, v___x_3915_);
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3915_);
v___x_3923_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
lean_object* v___x_3924_; 
v___x_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
return v___x_3924_;
}
}
}
else
{
lean_object* v___x_3928_; 
lean_dec_ref(v___x_3915_);
v___x_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3928_, 0, v_code_3669_);
return v___x_3928_;
}
}
case 7:
{
lean_object* v_fvarId_3929_; lean_object* v_i_3930_; lean_object* v_y_3931_; lean_object* v_k_3932_; lean_object* v___x_3933_; 
v_fvarId_3929_ = lean_ctor_get(v_code_3669_, 0);
v_i_3930_ = lean_ctor_get(v_code_3669_, 1);
v_y_3931_ = lean_ctor_get(v_code_3669_, 2);
v_k_3932_ = lean_ctor_get(v_code_3669_, 3);
lean_inc(v_fvarId_3929_);
v___x_3933_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3670_, v_fvarId_3929_, v_t_3668_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v_fvarId_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; 
v_fvarId_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_fvarId_3934_);
lean_dec_ref_known(v___x_3933_, 1);
lean_inc(v_y_3931_);
v___x_3935_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_3667_, v_a_3670_, v_y_3931_, v_t_3668_);
lean_inc_ref(v_k_3932_);
v___x_3936_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3667_, v_t_3668_, v_k_3932_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3998_; 
v_a_3937_ = lean_ctor_get(v___x_3936_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3939_ = v___x_3936_;
v_isShared_3940_ = v_isSharedCheck_3998_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3936_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3998_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
uint8_t v___y_3942_; size_t v___x_3994_; size_t v___x_3995_; uint8_t v___x_3996_; 
v___x_3994_ = lean_ptr_addr(v_fvarId_3929_);
v___x_3995_ = lean_ptr_addr(v_fvarId_3934_);
v___x_3996_ = lean_usize_dec_eq(v___x_3994_, v___x_3995_);
if (v___x_3996_ == 0)
{
v___y_3942_ = v___x_3996_;
goto v___jp_3941_;
}
else
{
uint8_t v___x_3997_; 
v___x_3997_ = lean_nat_dec_eq(v_i_3930_, v_i_3930_);
v___y_3942_ = v___x_3997_;
goto v___jp_3941_;
}
v___jp_3941_:
{
if (v___y_3942_ == 0)
{
lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3952_; 
lean_inc(v_i_3930_);
v_isSharedCheck_3952_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_3952_ == 0)
{
lean_object* v_unused_3953_; lean_object* v_unused_3954_; lean_object* v_unused_3955_; lean_object* v_unused_3956_; 
v_unused_3953_ = lean_ctor_get(v_code_3669_, 3);
lean_dec(v_unused_3953_);
v_unused_3954_ = lean_ctor_get(v_code_3669_, 2);
lean_dec(v_unused_3954_);
v_unused_3955_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_3955_);
v_unused_3956_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_3956_);
v___x_3944_ = v_code_3669_;
v_isShared_3945_ = v_isSharedCheck_3952_;
goto v_resetjp_3943_;
}
else
{
lean_dec(v_code_3669_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3952_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
lean_ctor_set(v___x_3944_, 3, v_a_3937_);
lean_ctor_set(v___x_3944_, 2, v___x_3935_);
lean_ctor_set(v___x_3944_, 0, v_fvarId_3934_);
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_fvarId_3934_);
lean_ctor_set(v_reuseFailAlloc_3951_, 1, v_i_3930_);
lean_ctor_set(v_reuseFailAlloc_3951_, 2, v___x_3935_);
lean_ctor_set(v_reuseFailAlloc_3951_, 3, v_a_3937_);
v___x_3947_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
lean_object* v___x_3949_; 
if (v_isShared_3940_ == 0)
{
lean_ctor_set(v___x_3939_, 0, v___x_3947_);
v___x_3949_ = v___x_3939_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v___x_3947_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
}
}
else
{
size_t v___x_3957_; size_t v___x_3958_; uint8_t v___x_3959_; 
v___x_3957_ = lean_ptr_addr(v_y_3931_);
v___x_3958_ = lean_ptr_addr(v___x_3935_);
v___x_3959_ = lean_usize_dec_eq(v___x_3957_, v___x_3958_);
if (v___x_3959_ == 0)
{
lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3969_; 
lean_inc(v_i_3930_);
v_isSharedCheck_3969_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_3969_ == 0)
{
lean_object* v_unused_3970_; lean_object* v_unused_3971_; lean_object* v_unused_3972_; lean_object* v_unused_3973_; 
v_unused_3970_ = lean_ctor_get(v_code_3669_, 3);
lean_dec(v_unused_3970_);
v_unused_3971_ = lean_ctor_get(v_code_3669_, 2);
lean_dec(v_unused_3971_);
v_unused_3972_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_3972_);
v_unused_3973_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_3973_);
v___x_3961_ = v_code_3669_;
v_isShared_3962_ = v_isSharedCheck_3969_;
goto v_resetjp_3960_;
}
else
{
lean_dec(v_code_3669_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3969_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 3, v_a_3937_);
lean_ctor_set(v___x_3961_, 2, v___x_3935_);
lean_ctor_set(v___x_3961_, 0, v_fvarId_3934_);
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_fvarId_3934_);
lean_ctor_set(v_reuseFailAlloc_3968_, 1, v_i_3930_);
lean_ctor_set(v_reuseFailAlloc_3968_, 2, v___x_3935_);
lean_ctor_set(v_reuseFailAlloc_3968_, 3, v_a_3937_);
v___x_3964_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
lean_object* v___x_3966_; 
if (v_isShared_3940_ == 0)
{
lean_ctor_set(v___x_3939_, 0, v___x_3964_);
v___x_3966_ = v___x_3939_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v___x_3964_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
}
else
{
size_t v___x_3974_; size_t v___x_3975_; uint8_t v___x_3976_; 
v___x_3974_ = lean_ptr_addr(v_k_3932_);
v___x_3975_ = lean_ptr_addr(v_a_3937_);
v___x_3976_ = lean_usize_dec_eq(v___x_3974_, v___x_3975_);
if (v___x_3976_ == 0)
{
lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3986_; 
lean_inc(v_i_3930_);
v_isSharedCheck_3986_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_3986_ == 0)
{
lean_object* v_unused_3987_; lean_object* v_unused_3988_; lean_object* v_unused_3989_; lean_object* v_unused_3990_; 
v_unused_3987_ = lean_ctor_get(v_code_3669_, 3);
lean_dec(v_unused_3987_);
v_unused_3988_ = lean_ctor_get(v_code_3669_, 2);
lean_dec(v_unused_3988_);
v_unused_3989_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_3989_);
v_unused_3990_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_3990_);
v___x_3978_ = v_code_3669_;
v_isShared_3979_ = v_isSharedCheck_3986_;
goto v_resetjp_3977_;
}
else
{
lean_dec(v_code_3669_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3986_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3981_; 
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 3, v_a_3937_);
lean_ctor_set(v___x_3978_, 2, v___x_3935_);
lean_ctor_set(v___x_3978_, 0, v_fvarId_3934_);
v___x_3981_ = v___x_3978_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_fvarId_3934_);
lean_ctor_set(v_reuseFailAlloc_3985_, 1, v_i_3930_);
lean_ctor_set(v_reuseFailAlloc_3985_, 2, v___x_3935_);
lean_ctor_set(v_reuseFailAlloc_3985_, 3, v_a_3937_);
v___x_3981_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
lean_object* v___x_3983_; 
if (v_isShared_3940_ == 0)
{
lean_ctor_set(v___x_3939_, 0, v___x_3981_);
v___x_3983_ = v___x_3939_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v___x_3981_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
else
{
lean_object* v___x_3992_; 
lean_dec(v_a_3937_);
lean_dec(v___x_3935_);
lean_dec(v_fvarId_3934_);
if (v_isShared_3940_ == 0)
{
lean_ctor_set(v___x_3939_, 0, v_code_3669_);
v___x_3992_ = v___x_3939_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_code_3669_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3935_);
lean_dec(v_fvarId_3934_);
lean_dec_ref_known(v_code_3669_, 4);
return v___x_3936_;
}
}
else
{
lean_object* v___x_3999_; 
lean_dec_ref_known(v_code_3669_, 4);
v___x_3999_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3667_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
return v___x_3999_;
}
}
case 8:
{
lean_object* v_fvarId_4000_; lean_object* v_i_4001_; lean_object* v_y_4002_; lean_object* v_k_4003_; lean_object* v___x_4004_; 
v_fvarId_4000_ = lean_ctor_get(v_code_3669_, 0);
v_i_4001_ = lean_ctor_get(v_code_3669_, 1);
v_y_4002_ = lean_ctor_get(v_code_3669_, 2);
v_k_4003_ = lean_ctor_get(v_code_3669_, 3);
lean_inc(v_fvarId_4000_);
v___x_4004_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3670_, v_fvarId_4000_, v_t_3668_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_fvarId_4005_; lean_object* v___x_4006_; 
v_fvarId_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc(v_fvarId_4005_);
lean_dec_ref_known(v___x_4004_, 1);
lean_inc(v_y_4002_);
v___x_4006_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3670_, v_y_4002_, v_t_3668_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_fvarId_4007_; lean_object* v___x_4008_; 
v_fvarId_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc(v_fvarId_4007_);
lean_dec_ref_known(v___x_4006_, 1);
lean_inc_ref(v_k_4003_);
v___x_4008_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3667_, v_t_3668_, v_k_4003_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4070_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4011_ = v___x_4008_;
v_isShared_4012_ = v_isSharedCheck_4070_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_4008_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4070_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
uint8_t v___y_4014_; size_t v___x_4066_; size_t v___x_4067_; uint8_t v___x_4068_; 
v___x_4066_ = lean_ptr_addr(v_fvarId_4000_);
v___x_4067_ = lean_ptr_addr(v_fvarId_4005_);
v___x_4068_ = lean_usize_dec_eq(v___x_4066_, v___x_4067_);
if (v___x_4068_ == 0)
{
v___y_4014_ = v___x_4068_;
goto v___jp_4013_;
}
else
{
uint8_t v___x_4069_; 
v___x_4069_ = lean_nat_dec_eq(v_i_4001_, v_i_4001_);
v___y_4014_ = v___x_4069_;
goto v___jp_4013_;
}
v___jp_4013_:
{
if (v___y_4014_ == 0)
{
lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4024_; 
lean_inc(v_i_4001_);
v_isSharedCheck_4024_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_4024_ == 0)
{
lean_object* v_unused_4025_; lean_object* v_unused_4026_; lean_object* v_unused_4027_; lean_object* v_unused_4028_; 
v_unused_4025_ = lean_ctor_get(v_code_3669_, 3);
lean_dec(v_unused_4025_);
v_unused_4026_ = lean_ctor_get(v_code_3669_, 2);
lean_dec(v_unused_4026_);
v_unused_4027_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_4027_);
v_unused_4028_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_4028_);
v___x_4016_ = v_code_3669_;
v_isShared_4017_ = v_isSharedCheck_4024_;
goto v_resetjp_4015_;
}
else
{
lean_dec(v_code_3669_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4024_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 3, v_a_4009_);
lean_ctor_set(v___x_4016_, 2, v_fvarId_4007_);
lean_ctor_set(v___x_4016_, 0, v_fvarId_4005_);
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_fvarId_4005_);
lean_ctor_set(v_reuseFailAlloc_4023_, 1, v_i_4001_);
lean_ctor_set(v_reuseFailAlloc_4023_, 2, v_fvarId_4007_);
lean_ctor_set(v_reuseFailAlloc_4023_, 3, v_a_4009_);
v___x_4019_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
lean_object* v___x_4021_; 
if (v_isShared_4012_ == 0)
{
lean_ctor_set(v___x_4011_, 0, v___x_4019_);
v___x_4021_ = v___x_4011_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v___x_4019_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
else
{
size_t v___x_4029_; size_t v___x_4030_; uint8_t v___x_4031_; 
v___x_4029_ = lean_ptr_addr(v_y_4002_);
v___x_4030_ = lean_ptr_addr(v_fvarId_4007_);
v___x_4031_ = lean_usize_dec_eq(v___x_4029_, v___x_4030_);
if (v___x_4031_ == 0)
{
lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4041_; 
lean_inc(v_i_4001_);
v_isSharedCheck_4041_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_4041_ == 0)
{
lean_object* v_unused_4042_; lean_object* v_unused_4043_; lean_object* v_unused_4044_; lean_object* v_unused_4045_; 
v_unused_4042_ = lean_ctor_get(v_code_3669_, 3);
lean_dec(v_unused_4042_);
v_unused_4043_ = lean_ctor_get(v_code_3669_, 2);
lean_dec(v_unused_4043_);
v_unused_4044_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_4044_);
v_unused_4045_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_4045_);
v___x_4033_ = v_code_3669_;
v_isShared_4034_ = v_isSharedCheck_4041_;
goto v_resetjp_4032_;
}
else
{
lean_dec(v_code_3669_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4041_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4036_; 
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 3, v_a_4009_);
lean_ctor_set(v___x_4033_, 2, v_fvarId_4007_);
lean_ctor_set(v___x_4033_, 0, v_fvarId_4005_);
v___x_4036_ = v___x_4033_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_fvarId_4005_);
lean_ctor_set(v_reuseFailAlloc_4040_, 1, v_i_4001_);
lean_ctor_set(v_reuseFailAlloc_4040_, 2, v_fvarId_4007_);
lean_ctor_set(v_reuseFailAlloc_4040_, 3, v_a_4009_);
v___x_4036_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
lean_object* v___x_4038_; 
if (v_isShared_4012_ == 0)
{
lean_ctor_set(v___x_4011_, 0, v___x_4036_);
v___x_4038_ = v___x_4011_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v___x_4036_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
else
{
size_t v___x_4046_; size_t v___x_4047_; uint8_t v___x_4048_; 
v___x_4046_ = lean_ptr_addr(v_k_4003_);
v___x_4047_ = lean_ptr_addr(v_a_4009_);
v___x_4048_ = lean_usize_dec_eq(v___x_4046_, v___x_4047_);
if (v___x_4048_ == 0)
{
lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4058_; 
lean_inc(v_i_4001_);
v_isSharedCheck_4058_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_4058_ == 0)
{
lean_object* v_unused_4059_; lean_object* v_unused_4060_; lean_object* v_unused_4061_; lean_object* v_unused_4062_; 
v_unused_4059_ = lean_ctor_get(v_code_3669_, 3);
lean_dec(v_unused_4059_);
v_unused_4060_ = lean_ctor_get(v_code_3669_, 2);
lean_dec(v_unused_4060_);
v_unused_4061_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_4061_);
v_unused_4062_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_4062_);
v___x_4050_ = v_code_3669_;
v_isShared_4051_ = v_isSharedCheck_4058_;
goto v_resetjp_4049_;
}
else
{
lean_dec(v_code_3669_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4058_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 3, v_a_4009_);
lean_ctor_set(v___x_4050_, 2, v_fvarId_4007_);
lean_ctor_set(v___x_4050_, 0, v_fvarId_4005_);
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_fvarId_4005_);
lean_ctor_set(v_reuseFailAlloc_4057_, 1, v_i_4001_);
lean_ctor_set(v_reuseFailAlloc_4057_, 2, v_fvarId_4007_);
lean_ctor_set(v_reuseFailAlloc_4057_, 3, v_a_4009_);
v___x_4053_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
lean_object* v___x_4055_; 
if (v_isShared_4012_ == 0)
{
lean_ctor_set(v___x_4011_, 0, v___x_4053_);
v___x_4055_ = v___x_4011_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4053_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
}
}
else
{
lean_object* v___x_4064_; 
lean_dec(v_a_4009_);
lean_dec(v_fvarId_4007_);
lean_dec(v_fvarId_4005_);
if (v_isShared_4012_ == 0)
{
lean_ctor_set(v___x_4011_, 0, v_code_3669_);
v___x_4064_ = v___x_4011_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_code_3669_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4007_);
lean_dec(v_fvarId_4005_);
lean_dec_ref_known(v_code_3669_, 4);
return v___x_4008_;
}
}
else
{
lean_object* v___x_4071_; 
lean_dec(v_fvarId_4005_);
lean_dec_ref_known(v_code_3669_, 4);
v___x_4071_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3667_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
return v___x_4071_;
}
}
else
{
lean_object* v___x_4072_; 
lean_dec_ref_known(v_code_3669_, 4);
v___x_4072_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3667_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
return v___x_4072_;
}
}
case 9:
{
lean_object* v_fvarId_4073_; lean_object* v_i_4074_; lean_object* v_offset_4075_; lean_object* v_y_4076_; lean_object* v_ty_4077_; lean_object* v_k_4078_; lean_object* v___x_4079_; 
v_fvarId_4073_ = lean_ctor_get(v_code_3669_, 0);
v_i_4074_ = lean_ctor_get(v_code_3669_, 1);
v_offset_4075_ = lean_ctor_get(v_code_3669_, 2);
v_y_4076_ = lean_ctor_get(v_code_3669_, 3);
v_ty_4077_ = lean_ctor_get(v_code_3669_, 4);
v_k_4078_ = lean_ctor_get(v_code_3669_, 5);
lean_inc(v_fvarId_4073_);
v___x_4079_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3670_, v_fvarId_4073_, v_t_3668_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_fvarId_4080_; lean_object* v___x_4081_; 
v_fvarId_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_fvarId_4080_);
lean_dec_ref_known(v___x_4079_, 1);
lean_inc(v_y_4076_);
v___x_4081_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3670_, v_y_4076_, v_t_3668_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_fvarId_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
v_fvarId_4082_ = lean_ctor_get(v___x_4081_, 0);
lean_inc(v_fvarId_4082_);
lean_dec_ref_known(v___x_4081_, 1);
lean_inc_ref(v_ty_4077_);
v___x_4083_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3667_, v_a_3670_, v_t_3668_, v_ty_4077_);
lean_inc_ref(v_k_4078_);
v___x_4084_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3667_, v_t_3668_, v_k_4078_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4188_; 
v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4087_ = v___x_4084_;
v_isShared_4088_ = v_isSharedCheck_4188_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4084_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4188_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
uint8_t v___y_4090_; size_t v___x_4184_; size_t v___x_4185_; uint8_t v___x_4186_; 
v___x_4184_ = lean_ptr_addr(v_fvarId_4073_);
v___x_4185_ = lean_ptr_addr(v_fvarId_4080_);
v___x_4186_ = lean_usize_dec_eq(v___x_4184_, v___x_4185_);
if (v___x_4186_ == 0)
{
v___y_4090_ = v___x_4186_;
goto v___jp_4089_;
}
else
{
uint8_t v___x_4187_; 
v___x_4187_ = lean_nat_dec_eq(v_i_4074_, v_i_4074_);
v___y_4090_ = v___x_4187_;
goto v___jp_4089_;
}
v___jp_4089_:
{
if (v___y_4090_ == 0)
{
lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4100_; 
lean_inc(v_offset_4075_);
lean_inc(v_i_4074_);
v_isSharedCheck_4100_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_4100_ == 0)
{
lean_object* v_unused_4101_; lean_object* v_unused_4102_; lean_object* v_unused_4103_; lean_object* v_unused_4104_; lean_object* v_unused_4105_; lean_object* v_unused_4106_; 
v_unused_4101_ = lean_ctor_get(v_code_3669_, 5);
lean_dec(v_unused_4101_);
v_unused_4102_ = lean_ctor_get(v_code_3669_, 4);
lean_dec(v_unused_4102_);
v_unused_4103_ = lean_ctor_get(v_code_3669_, 3);
lean_dec(v_unused_4103_);
v_unused_4104_ = lean_ctor_get(v_code_3669_, 2);
lean_dec(v_unused_4104_);
v_unused_4105_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_4105_);
v_unused_4106_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_4106_);
v___x_4092_ = v_code_3669_;
v_isShared_4093_ = v_isSharedCheck_4100_;
goto v_resetjp_4091_;
}
else
{
lean_dec(v_code_3669_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4100_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
lean_ctor_set(v___x_4092_, 5, v_a_4085_);
lean_ctor_set(v___x_4092_, 4, v___x_4083_);
lean_ctor_set(v___x_4092_, 3, v_fvarId_4082_);
lean_ctor_set(v___x_4092_, 0, v_fvarId_4080_);
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_fvarId_4080_);
lean_ctor_set(v_reuseFailAlloc_4099_, 1, v_i_4074_);
lean_ctor_set(v_reuseFailAlloc_4099_, 2, v_offset_4075_);
lean_ctor_set(v_reuseFailAlloc_4099_, 3, v_fvarId_4082_);
lean_ctor_set(v_reuseFailAlloc_4099_, 4, v___x_4083_);
lean_ctor_set(v_reuseFailAlloc_4099_, 5, v_a_4085_);
v___x_4095_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
lean_object* v___x_4097_; 
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 0, v___x_4095_);
v___x_4097_ = v___x_4087_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v___x_4095_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
else
{
uint8_t v___x_4107_; 
v___x_4107_ = lean_nat_dec_eq(v_offset_4075_, v_offset_4075_);
if (v___x_4107_ == 0)
{
lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4117_; 
lean_inc(v_offset_4075_);
lean_inc(v_i_4074_);
v_isSharedCheck_4117_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_4117_ == 0)
{
lean_object* v_unused_4118_; lean_object* v_unused_4119_; lean_object* v_unused_4120_; lean_object* v_unused_4121_; lean_object* v_unused_4122_; lean_object* v_unused_4123_; 
v_unused_4118_ = lean_ctor_get(v_code_3669_, 5);
lean_dec(v_unused_4118_);
v_unused_4119_ = lean_ctor_get(v_code_3669_, 4);
lean_dec(v_unused_4119_);
v_unused_4120_ = lean_ctor_get(v_code_3669_, 3);
lean_dec(v_unused_4120_);
v_unused_4121_ = lean_ctor_get(v_code_3669_, 2);
lean_dec(v_unused_4121_);
v_unused_4122_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_4122_);
v_unused_4123_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_4123_);
v___x_4109_ = v_code_3669_;
v_isShared_4110_ = v_isSharedCheck_4117_;
goto v_resetjp_4108_;
}
else
{
lean_dec(v_code_3669_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4117_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
lean_ctor_set(v___x_4109_, 5, v_a_4085_);
lean_ctor_set(v___x_4109_, 4, v___x_4083_);
lean_ctor_set(v___x_4109_, 3, v_fvarId_4082_);
lean_ctor_set(v___x_4109_, 0, v_fvarId_4080_);
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_fvarId_4080_);
lean_ctor_set(v_reuseFailAlloc_4116_, 1, v_i_4074_);
lean_ctor_set(v_reuseFailAlloc_4116_, 2, v_offset_4075_);
lean_ctor_set(v_reuseFailAlloc_4116_, 3, v_fvarId_4082_);
lean_ctor_set(v_reuseFailAlloc_4116_, 4, v___x_4083_);
lean_ctor_set(v_reuseFailAlloc_4116_, 5, v_a_4085_);
v___x_4112_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
lean_object* v___x_4114_; 
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 0, v___x_4112_);
v___x_4114_ = v___x_4087_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v___x_4112_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
else
{
size_t v___x_4124_; size_t v___x_4125_; uint8_t v___x_4126_; 
v___x_4124_ = lean_ptr_addr(v_y_4076_);
v___x_4125_ = lean_ptr_addr(v_fvarId_4082_);
v___x_4126_ = lean_usize_dec_eq(v___x_4124_, v___x_4125_);
if (v___x_4126_ == 0)
{
lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4136_; 
lean_inc(v_offset_4075_);
lean_inc(v_i_4074_);
v_isSharedCheck_4136_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_4136_ == 0)
{
lean_object* v_unused_4137_; lean_object* v_unused_4138_; lean_object* v_unused_4139_; lean_object* v_unused_4140_; lean_object* v_unused_4141_; lean_object* v_unused_4142_; 
v_unused_4137_ = lean_ctor_get(v_code_3669_, 5);
lean_dec(v_unused_4137_);
v_unused_4138_ = lean_ctor_get(v_code_3669_, 4);
lean_dec(v_unused_4138_);
v_unused_4139_ = lean_ctor_get(v_code_3669_, 3);
lean_dec(v_unused_4139_);
v_unused_4140_ = lean_ctor_get(v_code_3669_, 2);
lean_dec(v_unused_4140_);
v_unused_4141_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_4141_);
v_unused_4142_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_4142_);
v___x_4128_ = v_code_3669_;
v_isShared_4129_ = v_isSharedCheck_4136_;
goto v_resetjp_4127_;
}
else
{
lean_dec(v_code_3669_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4136_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 5, v_a_4085_);
lean_ctor_set(v___x_4128_, 4, v___x_4083_);
lean_ctor_set(v___x_4128_, 3, v_fvarId_4082_);
lean_ctor_set(v___x_4128_, 0, v_fvarId_4080_);
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_fvarId_4080_);
lean_ctor_set(v_reuseFailAlloc_4135_, 1, v_i_4074_);
lean_ctor_set(v_reuseFailAlloc_4135_, 2, v_offset_4075_);
lean_ctor_set(v_reuseFailAlloc_4135_, 3, v_fvarId_4082_);
lean_ctor_set(v_reuseFailAlloc_4135_, 4, v___x_4083_);
lean_ctor_set(v_reuseFailAlloc_4135_, 5, v_a_4085_);
v___x_4131_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
lean_object* v___x_4133_; 
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 0, v___x_4131_);
v___x_4133_ = v___x_4087_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4131_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
}
else
{
size_t v___x_4143_; size_t v___x_4144_; uint8_t v___x_4145_; 
v___x_4143_ = lean_ptr_addr(v_ty_4077_);
v___x_4144_ = lean_ptr_addr(v___x_4083_);
v___x_4145_ = lean_usize_dec_eq(v___x_4143_, v___x_4144_);
if (v___x_4145_ == 0)
{
lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4155_; 
lean_inc(v_offset_4075_);
lean_inc(v_i_4074_);
v_isSharedCheck_4155_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_4155_ == 0)
{
lean_object* v_unused_4156_; lean_object* v_unused_4157_; lean_object* v_unused_4158_; lean_object* v_unused_4159_; lean_object* v_unused_4160_; lean_object* v_unused_4161_; 
v_unused_4156_ = lean_ctor_get(v_code_3669_, 5);
lean_dec(v_unused_4156_);
v_unused_4157_ = lean_ctor_get(v_code_3669_, 4);
lean_dec(v_unused_4157_);
v_unused_4158_ = lean_ctor_get(v_code_3669_, 3);
lean_dec(v_unused_4158_);
v_unused_4159_ = lean_ctor_get(v_code_3669_, 2);
lean_dec(v_unused_4159_);
v_unused_4160_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_4160_);
v_unused_4161_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_4161_);
v___x_4147_ = v_code_3669_;
v_isShared_4148_ = v_isSharedCheck_4155_;
goto v_resetjp_4146_;
}
else
{
lean_dec(v_code_3669_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4155_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 5, v_a_4085_);
lean_ctor_set(v___x_4147_, 4, v___x_4083_);
lean_ctor_set(v___x_4147_, 3, v_fvarId_4082_);
lean_ctor_set(v___x_4147_, 0, v_fvarId_4080_);
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_fvarId_4080_);
lean_ctor_set(v_reuseFailAlloc_4154_, 1, v_i_4074_);
lean_ctor_set(v_reuseFailAlloc_4154_, 2, v_offset_4075_);
lean_ctor_set(v_reuseFailAlloc_4154_, 3, v_fvarId_4082_);
lean_ctor_set(v_reuseFailAlloc_4154_, 4, v___x_4083_);
lean_ctor_set(v_reuseFailAlloc_4154_, 5, v_a_4085_);
v___x_4150_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
lean_object* v___x_4152_; 
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 0, v___x_4150_);
v___x_4152_ = v___x_4087_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v___x_4150_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
else
{
size_t v___x_4162_; size_t v___x_4163_; uint8_t v___x_4164_; 
v___x_4162_ = lean_ptr_addr(v_k_4078_);
v___x_4163_ = lean_ptr_addr(v_a_4085_);
v___x_4164_ = lean_usize_dec_eq(v___x_4162_, v___x_4163_);
if (v___x_4164_ == 0)
{
lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4174_; 
lean_inc(v_offset_4075_);
lean_inc(v_i_4074_);
v_isSharedCheck_4174_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_4174_ == 0)
{
lean_object* v_unused_4175_; lean_object* v_unused_4176_; lean_object* v_unused_4177_; lean_object* v_unused_4178_; lean_object* v_unused_4179_; lean_object* v_unused_4180_; 
v_unused_4175_ = lean_ctor_get(v_code_3669_, 5);
lean_dec(v_unused_4175_);
v_unused_4176_ = lean_ctor_get(v_code_3669_, 4);
lean_dec(v_unused_4176_);
v_unused_4177_ = lean_ctor_get(v_code_3669_, 3);
lean_dec(v_unused_4177_);
v_unused_4178_ = lean_ctor_get(v_code_3669_, 2);
lean_dec(v_unused_4178_);
v_unused_4179_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_4179_);
v_unused_4180_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_4180_);
v___x_4166_ = v_code_3669_;
v_isShared_4167_ = v_isSharedCheck_4174_;
goto v_resetjp_4165_;
}
else
{
lean_dec(v_code_3669_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4174_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
lean_ctor_set(v___x_4166_, 5, v_a_4085_);
lean_ctor_set(v___x_4166_, 4, v___x_4083_);
lean_ctor_set(v___x_4166_, 3, v_fvarId_4082_);
lean_ctor_set(v___x_4166_, 0, v_fvarId_4080_);
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_fvarId_4080_);
lean_ctor_set(v_reuseFailAlloc_4173_, 1, v_i_4074_);
lean_ctor_set(v_reuseFailAlloc_4173_, 2, v_offset_4075_);
lean_ctor_set(v_reuseFailAlloc_4173_, 3, v_fvarId_4082_);
lean_ctor_set(v_reuseFailAlloc_4173_, 4, v___x_4083_);
lean_ctor_set(v_reuseFailAlloc_4173_, 5, v_a_4085_);
v___x_4169_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
lean_object* v___x_4171_; 
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 0, v___x_4169_);
v___x_4171_ = v___x_4087_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v___x_4169_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
else
{
lean_object* v___x_4182_; 
lean_dec(v_a_4085_);
lean_dec_ref(v___x_4083_);
lean_dec(v_fvarId_4082_);
lean_dec(v_fvarId_4080_);
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 0, v_code_3669_);
v___x_4182_ = v___x_4087_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_code_3669_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
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
lean_dec_ref(v___x_4083_);
lean_dec(v_fvarId_4082_);
lean_dec(v_fvarId_4080_);
lean_dec_ref_known(v_code_3669_, 6);
return v___x_4084_;
}
}
else
{
lean_object* v___x_4189_; 
lean_dec(v_fvarId_4080_);
lean_dec_ref_known(v_code_3669_, 6);
v___x_4189_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3667_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
return v___x_4189_;
}
}
else
{
lean_object* v___x_4190_; 
lean_dec_ref_known(v_code_3669_, 6);
v___x_4190_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3667_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
return v___x_4190_;
}
}
case 10:
{
lean_object* v_fvarId_4191_; lean_object* v_cidx_4192_; lean_object* v_k_4193_; lean_object* v___x_4194_; 
v_fvarId_4191_ = lean_ctor_get(v_code_3669_, 0);
v_cidx_4192_ = lean_ctor_get(v_code_3669_, 1);
v_k_4193_ = lean_ctor_get(v_code_3669_, 2);
lean_inc(v_fvarId_4191_);
v___x_4194_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3670_, v_fvarId_4191_, v_t_3668_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_fvarId_4195_; lean_object* v___x_4196_; 
v_fvarId_4195_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_fvarId_4195_);
lean_dec_ref_known(v___x_4194_, 1);
lean_inc_ref(v_k_4193_);
v___x_4196_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3667_, v_t_3668_, v_k_4193_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v_a_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4239_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4199_ = v___x_4196_;
v_isShared_4200_ = v_isSharedCheck_4239_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v___x_4196_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4239_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
uint8_t v___y_4202_; size_t v___x_4235_; size_t v___x_4236_; uint8_t v___x_4237_; 
v___x_4235_ = lean_ptr_addr(v_fvarId_4191_);
v___x_4236_ = lean_ptr_addr(v_fvarId_4195_);
v___x_4237_ = lean_usize_dec_eq(v___x_4235_, v___x_4236_);
if (v___x_4237_ == 0)
{
v___y_4202_ = v___x_4237_;
goto v___jp_4201_;
}
else
{
uint8_t v___x_4238_; 
v___x_4238_ = lean_nat_dec_eq(v_cidx_4192_, v_cidx_4192_);
v___y_4202_ = v___x_4238_;
goto v___jp_4201_;
}
v___jp_4201_:
{
if (v___y_4202_ == 0)
{
lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4212_; 
lean_inc(v_cidx_4192_);
v_isSharedCheck_4212_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_4212_ == 0)
{
lean_object* v_unused_4213_; lean_object* v_unused_4214_; lean_object* v_unused_4215_; 
v_unused_4213_ = lean_ctor_get(v_code_3669_, 2);
lean_dec(v_unused_4213_);
v_unused_4214_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_4214_);
v_unused_4215_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_4215_);
v___x_4204_ = v_code_3669_;
v_isShared_4205_ = v_isSharedCheck_4212_;
goto v_resetjp_4203_;
}
else
{
lean_dec(v_code_3669_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4212_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
lean_ctor_set(v___x_4204_, 2, v_a_4197_);
lean_ctor_set(v___x_4204_, 0, v_fvarId_4195_);
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_fvarId_4195_);
lean_ctor_set(v_reuseFailAlloc_4211_, 1, v_cidx_4192_);
lean_ctor_set(v_reuseFailAlloc_4211_, 2, v_a_4197_);
v___x_4207_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
lean_object* v___x_4209_; 
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 0, v___x_4207_);
v___x_4209_ = v___x_4199_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v___x_4207_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
return v___x_4209_;
}
}
}
}
else
{
size_t v___x_4216_; size_t v___x_4217_; uint8_t v___x_4218_; 
v___x_4216_ = lean_ptr_addr(v_k_4193_);
v___x_4217_ = lean_ptr_addr(v_a_4197_);
v___x_4218_ = lean_usize_dec_eq(v___x_4216_, v___x_4217_);
if (v___x_4218_ == 0)
{
lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4228_; 
lean_inc(v_cidx_4192_);
v_isSharedCheck_4228_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_4228_ == 0)
{
lean_object* v_unused_4229_; lean_object* v_unused_4230_; lean_object* v_unused_4231_; 
v_unused_4229_ = lean_ctor_get(v_code_3669_, 2);
lean_dec(v_unused_4229_);
v_unused_4230_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_4230_);
v_unused_4231_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_4231_);
v___x_4220_ = v_code_3669_;
v_isShared_4221_ = v_isSharedCheck_4228_;
goto v_resetjp_4219_;
}
else
{
lean_dec(v_code_3669_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4228_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4223_; 
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 2, v_a_4197_);
lean_ctor_set(v___x_4220_, 0, v_fvarId_4195_);
v___x_4223_ = v___x_4220_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_fvarId_4195_);
lean_ctor_set(v_reuseFailAlloc_4227_, 1, v_cidx_4192_);
lean_ctor_set(v_reuseFailAlloc_4227_, 2, v_a_4197_);
v___x_4223_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
lean_object* v___x_4225_; 
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 0, v___x_4223_);
v___x_4225_ = v___x_4199_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4223_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
}
else
{
lean_object* v___x_4233_; 
lean_dec(v_a_4197_);
lean_dec(v_fvarId_4195_);
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 0, v_code_3669_);
v___x_4233_ = v___x_4199_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_code_3669_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4195_);
lean_dec_ref_known(v_code_3669_, 3);
return v___x_4196_;
}
}
else
{
lean_object* v___x_4240_; 
lean_dec_ref_known(v_code_3669_, 3);
v___x_4240_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3667_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
return v___x_4240_;
}
}
case 11:
{
lean_object* v_fvarId_4241_; lean_object* v_n_4242_; uint8_t v_check_4243_; uint8_t v_persistent_4244_; lean_object* v_k_4245_; lean_object* v___x_4246_; 
v_fvarId_4241_ = lean_ctor_get(v_code_3669_, 0);
v_n_4242_ = lean_ctor_get(v_code_3669_, 1);
v_check_4243_ = lean_ctor_get_uint8(v_code_3669_, sizeof(void*)*3);
v_persistent_4244_ = lean_ctor_get_uint8(v_code_3669_, sizeof(void*)*3 + 1);
v_k_4245_ = lean_ctor_get(v_code_3669_, 2);
lean_inc(v_fvarId_4241_);
v___x_4246_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3670_, v_fvarId_4241_, v_t_3668_);
if (lean_obj_tag(v___x_4246_) == 0)
{
lean_object* v_fvarId_4247_; lean_object* v___x_4248_; 
v_fvarId_4247_ = lean_ctor_get(v___x_4246_, 0);
lean_inc(v_fvarId_4247_);
lean_dec_ref_known(v___x_4246_, 1);
lean_inc_ref(v_k_4245_);
v___x_4248_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3667_, v_t_3668_, v_k_4245_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4291_; 
v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4251_ = v___x_4248_;
v_isShared_4252_ = v_isSharedCheck_4291_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4248_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4291_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
uint8_t v___y_4254_; size_t v___x_4287_; size_t v___x_4288_; uint8_t v___x_4289_; 
v___x_4287_ = lean_ptr_addr(v_fvarId_4241_);
v___x_4288_ = lean_ptr_addr(v_fvarId_4247_);
v___x_4289_ = lean_usize_dec_eq(v___x_4287_, v___x_4288_);
if (v___x_4289_ == 0)
{
v___y_4254_ = v___x_4289_;
goto v___jp_4253_;
}
else
{
uint8_t v___x_4290_; 
v___x_4290_ = lean_nat_dec_eq(v_n_4242_, v_n_4242_);
v___y_4254_ = v___x_4290_;
goto v___jp_4253_;
}
v___jp_4253_:
{
if (v___y_4254_ == 0)
{
lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4264_; 
lean_inc(v_n_4242_);
v_isSharedCheck_4264_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_4264_ == 0)
{
lean_object* v_unused_4265_; lean_object* v_unused_4266_; lean_object* v_unused_4267_; 
v_unused_4265_ = lean_ctor_get(v_code_3669_, 2);
lean_dec(v_unused_4265_);
v_unused_4266_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_4266_);
v_unused_4267_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_4267_);
v___x_4256_ = v_code_3669_;
v_isShared_4257_ = v_isSharedCheck_4264_;
goto v_resetjp_4255_;
}
else
{
lean_dec(v_code_3669_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4264_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4259_; 
if (v_isShared_4257_ == 0)
{
lean_ctor_set(v___x_4256_, 2, v_a_4249_);
lean_ctor_set(v___x_4256_, 0, v_fvarId_4247_);
v___x_4259_ = v___x_4256_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v_fvarId_4247_);
lean_ctor_set(v_reuseFailAlloc_4263_, 1, v_n_4242_);
lean_ctor_set(v_reuseFailAlloc_4263_, 2, v_a_4249_);
lean_ctor_set_uint8(v_reuseFailAlloc_4263_, sizeof(void*)*3, v_check_4243_);
lean_ctor_set_uint8(v_reuseFailAlloc_4263_, sizeof(void*)*3 + 1, v_persistent_4244_);
v___x_4259_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
lean_object* v___x_4261_; 
if (v_isShared_4252_ == 0)
{
lean_ctor_set(v___x_4251_, 0, v___x_4259_);
v___x_4261_ = v___x_4251_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v___x_4259_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
else
{
size_t v___x_4268_; size_t v___x_4269_; uint8_t v___x_4270_; 
v___x_4268_ = lean_ptr_addr(v_k_4245_);
v___x_4269_ = lean_ptr_addr(v_a_4249_);
v___x_4270_ = lean_usize_dec_eq(v___x_4268_, v___x_4269_);
if (v___x_4270_ == 0)
{
lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4280_; 
lean_inc(v_n_4242_);
v_isSharedCheck_4280_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_4280_ == 0)
{
lean_object* v_unused_4281_; lean_object* v_unused_4282_; lean_object* v_unused_4283_; 
v_unused_4281_ = lean_ctor_get(v_code_3669_, 2);
lean_dec(v_unused_4281_);
v_unused_4282_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_4282_);
v_unused_4283_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_4283_);
v___x_4272_ = v_code_3669_;
v_isShared_4273_ = v_isSharedCheck_4280_;
goto v_resetjp_4271_;
}
else
{
lean_dec(v_code_3669_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4280_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4275_; 
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 2, v_a_4249_);
lean_ctor_set(v___x_4272_, 0, v_fvarId_4247_);
v___x_4275_ = v___x_4272_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_fvarId_4247_);
lean_ctor_set(v_reuseFailAlloc_4279_, 1, v_n_4242_);
lean_ctor_set(v_reuseFailAlloc_4279_, 2, v_a_4249_);
lean_ctor_set_uint8(v_reuseFailAlloc_4279_, sizeof(void*)*3, v_check_4243_);
lean_ctor_set_uint8(v_reuseFailAlloc_4279_, sizeof(void*)*3 + 1, v_persistent_4244_);
v___x_4275_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
lean_object* v___x_4277_; 
if (v_isShared_4252_ == 0)
{
lean_ctor_set(v___x_4251_, 0, v___x_4275_);
v___x_4277_ = v___x_4251_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v___x_4275_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
}
else
{
lean_object* v___x_4285_; 
lean_dec(v_a_4249_);
lean_dec(v_fvarId_4247_);
if (v_isShared_4252_ == 0)
{
lean_ctor_set(v___x_4251_, 0, v_code_3669_);
v___x_4285_ = v___x_4251_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_code_3669_);
v___x_4285_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
return v___x_4285_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4247_);
lean_dec_ref_known(v_code_3669_, 3);
return v___x_4248_;
}
}
else
{
lean_object* v___x_4292_; 
lean_dec_ref_known(v_code_3669_, 3);
v___x_4292_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3667_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
return v___x_4292_;
}
}
case 12:
{
lean_object* v_fvarId_4293_; lean_object* v_n_4294_; uint8_t v_check_4295_; uint8_t v_persistent_4296_; lean_object* v_objs_x3f_4297_; lean_object* v_k_4298_; lean_object* v___x_4299_; 
v_fvarId_4293_ = lean_ctor_get(v_code_3669_, 0);
v_n_4294_ = lean_ctor_get(v_code_3669_, 1);
v_check_4295_ = lean_ctor_get_uint8(v_code_3669_, sizeof(void*)*4);
v_persistent_4296_ = lean_ctor_get_uint8(v_code_3669_, sizeof(void*)*4 + 1);
v_objs_x3f_4297_ = lean_ctor_get(v_code_3669_, 2);
v_k_4298_ = lean_ctor_get(v_code_3669_, 3);
lean_inc(v_fvarId_4293_);
v___x_4299_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3670_, v_fvarId_4293_, v_t_3668_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_fvarId_4300_; lean_object* v___x_4301_; 
v_fvarId_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc(v_fvarId_4300_);
lean_dec_ref_known(v___x_4299_, 1);
lean_inc_ref(v_k_4298_);
v___x_4301_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3667_, v_t_3668_, v_k_4298_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4362_; 
v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4304_ = v___x_4301_;
v_isShared_4305_ = v_isSharedCheck_4362_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4301_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4362_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
uint8_t v___y_4307_; size_t v___x_4358_; size_t v___x_4359_; uint8_t v___x_4360_; 
v___x_4358_ = lean_ptr_addr(v_fvarId_4293_);
v___x_4359_ = lean_ptr_addr(v_fvarId_4300_);
v___x_4360_ = lean_usize_dec_eq(v___x_4358_, v___x_4359_);
if (v___x_4360_ == 0)
{
v___y_4307_ = v___x_4360_;
goto v___jp_4306_;
}
else
{
uint8_t v___x_4361_; 
v___x_4361_ = lean_nat_dec_eq(v_n_4294_, v_n_4294_);
v___y_4307_ = v___x_4361_;
goto v___jp_4306_;
}
v___jp_4306_:
{
if (v___y_4307_ == 0)
{
lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4317_; 
lean_inc(v_objs_x3f_4297_);
lean_inc(v_n_4294_);
v_isSharedCheck_4317_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_4317_ == 0)
{
lean_object* v_unused_4318_; lean_object* v_unused_4319_; lean_object* v_unused_4320_; lean_object* v_unused_4321_; 
v_unused_4318_ = lean_ctor_get(v_code_3669_, 3);
lean_dec(v_unused_4318_);
v_unused_4319_ = lean_ctor_get(v_code_3669_, 2);
lean_dec(v_unused_4319_);
v_unused_4320_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_4320_);
v_unused_4321_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_4321_);
v___x_4309_ = v_code_3669_;
v_isShared_4310_ = v_isSharedCheck_4317_;
goto v_resetjp_4308_;
}
else
{
lean_dec(v_code_3669_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4317_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 3, v_a_4302_);
lean_ctor_set(v___x_4309_, 0, v_fvarId_4300_);
v___x_4312_ = v___x_4309_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_fvarId_4300_);
lean_ctor_set(v_reuseFailAlloc_4316_, 1, v_n_4294_);
lean_ctor_set(v_reuseFailAlloc_4316_, 2, v_objs_x3f_4297_);
lean_ctor_set(v_reuseFailAlloc_4316_, 3, v_a_4302_);
lean_ctor_set_uint8(v_reuseFailAlloc_4316_, sizeof(void*)*4, v_check_4295_);
lean_ctor_set_uint8(v_reuseFailAlloc_4316_, sizeof(void*)*4 + 1, v_persistent_4296_);
v___x_4312_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
lean_object* v___x_4314_; 
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 0, v___x_4312_);
v___x_4314_ = v___x_4304_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v___x_4312_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
}
}
}
}
else
{
size_t v___x_4322_; uint8_t v___x_4323_; 
v___x_4322_ = lean_ptr_addr(v_objs_x3f_4297_);
v___x_4323_ = lean_usize_dec_eq(v___x_4322_, v___x_4322_);
if (v___x_4323_ == 0)
{
lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4333_; 
lean_inc(v_objs_x3f_4297_);
lean_inc(v_n_4294_);
v_isSharedCheck_4333_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_4333_ == 0)
{
lean_object* v_unused_4334_; lean_object* v_unused_4335_; lean_object* v_unused_4336_; lean_object* v_unused_4337_; 
v_unused_4334_ = lean_ctor_get(v_code_3669_, 3);
lean_dec(v_unused_4334_);
v_unused_4335_ = lean_ctor_get(v_code_3669_, 2);
lean_dec(v_unused_4335_);
v_unused_4336_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_4336_);
v_unused_4337_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_4337_);
v___x_4325_ = v_code_3669_;
v_isShared_4326_ = v_isSharedCheck_4333_;
goto v_resetjp_4324_;
}
else
{
lean_dec(v_code_3669_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4333_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
lean_ctor_set(v___x_4325_, 3, v_a_4302_);
lean_ctor_set(v___x_4325_, 0, v_fvarId_4300_);
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_fvarId_4300_);
lean_ctor_set(v_reuseFailAlloc_4332_, 1, v_n_4294_);
lean_ctor_set(v_reuseFailAlloc_4332_, 2, v_objs_x3f_4297_);
lean_ctor_set(v_reuseFailAlloc_4332_, 3, v_a_4302_);
lean_ctor_set_uint8(v_reuseFailAlloc_4332_, sizeof(void*)*4, v_check_4295_);
lean_ctor_set_uint8(v_reuseFailAlloc_4332_, sizeof(void*)*4 + 1, v_persistent_4296_);
v___x_4328_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
lean_object* v___x_4330_; 
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 0, v___x_4328_);
v___x_4330_ = v___x_4304_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4328_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
}
else
{
size_t v___x_4338_; size_t v___x_4339_; uint8_t v___x_4340_; 
v___x_4338_ = lean_ptr_addr(v_k_4298_);
v___x_4339_ = lean_ptr_addr(v_a_4302_);
v___x_4340_ = lean_usize_dec_eq(v___x_4338_, v___x_4339_);
if (v___x_4340_ == 0)
{
lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4350_; 
lean_inc(v_objs_x3f_4297_);
lean_inc(v_n_4294_);
v_isSharedCheck_4350_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_4350_ == 0)
{
lean_object* v_unused_4351_; lean_object* v_unused_4352_; lean_object* v_unused_4353_; lean_object* v_unused_4354_; 
v_unused_4351_ = lean_ctor_get(v_code_3669_, 3);
lean_dec(v_unused_4351_);
v_unused_4352_ = lean_ctor_get(v_code_3669_, 2);
lean_dec(v_unused_4352_);
v_unused_4353_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_4353_);
v_unused_4354_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_4354_);
v___x_4342_ = v_code_3669_;
v_isShared_4343_ = v_isSharedCheck_4350_;
goto v_resetjp_4341_;
}
else
{
lean_dec(v_code_3669_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4350_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4345_; 
if (v_isShared_4343_ == 0)
{
lean_ctor_set(v___x_4342_, 3, v_a_4302_);
lean_ctor_set(v___x_4342_, 0, v_fvarId_4300_);
v___x_4345_ = v___x_4342_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_fvarId_4300_);
lean_ctor_set(v_reuseFailAlloc_4349_, 1, v_n_4294_);
lean_ctor_set(v_reuseFailAlloc_4349_, 2, v_objs_x3f_4297_);
lean_ctor_set(v_reuseFailAlloc_4349_, 3, v_a_4302_);
lean_ctor_set_uint8(v_reuseFailAlloc_4349_, sizeof(void*)*4, v_check_4295_);
lean_ctor_set_uint8(v_reuseFailAlloc_4349_, sizeof(void*)*4 + 1, v_persistent_4296_);
v___x_4345_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
lean_object* v___x_4347_; 
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 0, v___x_4345_);
v___x_4347_ = v___x_4304_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v___x_4345_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
return v___x_4347_;
}
}
}
}
else
{
lean_object* v___x_4356_; 
lean_dec(v_a_4302_);
lean_dec(v_fvarId_4300_);
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 0, v_code_3669_);
v___x_4356_ = v___x_4304_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_code_3669_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4300_);
lean_dec_ref_known(v_code_3669_, 4);
return v___x_4301_;
}
}
else
{
lean_object* v___x_4363_; 
lean_dec_ref_known(v_code_3669_, 4);
v___x_4363_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3667_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
return v___x_4363_;
}
}
default: 
{
lean_object* v_fvarId_4364_; lean_object* v_k_4365_; lean_object* v___x_4366_; 
v_fvarId_4364_ = lean_ctor_get(v_code_3669_, 0);
v_k_4365_ = lean_ctor_get(v_code_3669_, 1);
lean_inc(v_fvarId_4364_);
v___x_4366_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3670_, v_fvarId_4364_, v_t_3668_);
if (lean_obj_tag(v___x_4366_) == 0)
{
lean_object* v_fvarId_4367_; lean_object* v___x_4368_; 
v_fvarId_4367_ = lean_ctor_get(v___x_4366_, 0);
lean_inc(v_fvarId_4367_);
lean_dec_ref_known(v___x_4366_, 1);
lean_inc_ref(v_k_4365_);
v___x_4368_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3667_, v_t_3668_, v_k_4365_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_object* v_a_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4396_; 
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4371_ = v___x_4368_;
v_isShared_4372_ = v_isSharedCheck_4396_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_a_4369_);
lean_dec(v___x_4368_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4396_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
uint8_t v___y_4374_; size_t v___x_4390_; size_t v___x_4391_; uint8_t v___x_4392_; 
v___x_4390_ = lean_ptr_addr(v_fvarId_4364_);
v___x_4391_ = lean_ptr_addr(v_fvarId_4367_);
v___x_4392_ = lean_usize_dec_eq(v___x_4390_, v___x_4391_);
if (v___x_4392_ == 0)
{
v___y_4374_ = v___x_4392_;
goto v___jp_4373_;
}
else
{
size_t v___x_4393_; size_t v___x_4394_; uint8_t v___x_4395_; 
v___x_4393_ = lean_ptr_addr(v_k_4365_);
v___x_4394_ = lean_ptr_addr(v_a_4369_);
v___x_4395_ = lean_usize_dec_eq(v___x_4393_, v___x_4394_);
v___y_4374_ = v___x_4395_;
goto v___jp_4373_;
}
v___jp_4373_:
{
if (v___y_4374_ == 0)
{
lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4384_; 
v_isSharedCheck_4384_ = !lean_is_exclusive(v_code_3669_);
if (v_isSharedCheck_4384_ == 0)
{
lean_object* v_unused_4385_; lean_object* v_unused_4386_; 
v_unused_4385_ = lean_ctor_get(v_code_3669_, 1);
lean_dec(v_unused_4385_);
v_unused_4386_ = lean_ctor_get(v_code_3669_, 0);
lean_dec(v_unused_4386_);
v___x_4376_ = v_code_3669_;
v_isShared_4377_ = v_isSharedCheck_4384_;
goto v_resetjp_4375_;
}
else
{
lean_dec(v_code_3669_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4384_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v___x_4379_; 
if (v_isShared_4377_ == 0)
{
lean_ctor_set(v___x_4376_, 1, v_a_4369_);
lean_ctor_set(v___x_4376_, 0, v_fvarId_4367_);
v___x_4379_ = v___x_4376_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_fvarId_4367_);
lean_ctor_set(v_reuseFailAlloc_4383_, 1, v_a_4369_);
v___x_4379_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
lean_object* v___x_4381_; 
if (v_isShared_4372_ == 0)
{
lean_ctor_set(v___x_4371_, 0, v___x_4379_);
v___x_4381_ = v___x_4371_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4379_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
}
else
{
lean_object* v___x_4388_; 
lean_dec(v_a_4369_);
lean_dec(v_fvarId_4367_);
if (v_isShared_4372_ == 0)
{
lean_ctor_set(v___x_4371_, 0, v_code_3669_);
v___x_4388_ = v___x_4371_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_code_3669_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_4367_);
lean_dec_ref_known(v_code_3669_, 2);
return v___x_4368_;
}
}
else
{
lean_object* v___x_4397_; 
lean_dec_ref_known(v_code_3669_, 2);
v___x_4397_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3667_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
return v___x_4397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t v_pu_4398_, uint8_t v_t_4399_, lean_object* v_decl_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_){
_start:
{
lean_object* v_params_4407_; lean_object* v_type_4408_; lean_object* v_value_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v_params_4407_ = lean_ctor_get(v_decl_4400_, 2);
v_type_4408_ = lean_ctor_get(v_decl_4400_, 3);
v_value_4409_ = lean_ctor_get(v_decl_4400_, 4);
lean_inc_ref(v_type_4408_);
v___x_4410_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4398_, v_a_4401_, v_t_4399_, v_type_4408_);
lean_inc_ref(v_params_4407_);
v___x_4411_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4398_, v_t_4399_, v_params_4407_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v_a_4412_; lean_object* v___x_4413_; 
v_a_4412_ = lean_ctor_get(v___x_4411_, 0);
lean_inc(v_a_4412_);
lean_dec_ref_known(v___x_4411_, 1);
lean_inc_ref(v_value_4409_);
v___x_4413_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4398_, v_t_4399_, v_value_4409_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v_a_4414_; lean_object* v___x_4415_; 
v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
lean_inc(v_a_4414_);
lean_dec_ref_known(v___x_4413_, 1);
v___x_4415_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_4398_, v_decl_4400_, v___x_4410_, v_a_4412_, v_a_4414_, v_a_4403_);
return v___x_4415_;
}
else
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4423_; 
lean_dec(v_a_4412_);
lean_dec_ref(v___x_4410_);
lean_dec_ref(v_decl_4400_);
v_a_4416_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4418_ = v___x_4413_;
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4413_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4421_; 
if (v_isShared_4419_ == 0)
{
v___x_4421_ = v___x_4418_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_a_4416_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
}
}
else
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4431_; 
lean_dec_ref(v___x_4410_);
lean_dec_ref(v_decl_4400_);
v_a_4424_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4426_ = v___x_4411_;
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4411_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4429_; 
if (v_isShared_4427_ == 0)
{
v___x_4429_ = v___x_4426_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4424_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
return v___x_4429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp___boxed(lean_object* v_pu_4432_, lean_object* v_t_4433_, lean_object* v_decl_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_){
_start:
{
uint8_t v_pu_boxed_4441_; uint8_t v_t_boxed_4442_; lean_object* v_res_4443_; 
v_pu_boxed_4441_ = lean_unbox(v_pu_4432_);
v_t_boxed_4442_ = lean_unbox(v_t_4433_);
v_res_4443_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_boxed_4441_, v_t_boxed_4442_, v_decl_4434_, v_a_4435_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_);
lean_dec(v_a_4439_);
lean_dec_ref(v_a_4438_);
lean_dec(v_a_4437_);
lean_dec_ref(v_a_4436_);
lean_dec_ref(v_a_4435_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4___boxed(lean_object* v_pu_4444_, lean_object* v_t_4445_, lean_object* v_i_4446_, lean_object* v_as_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_){
_start:
{
uint8_t v_pu_boxed_4454_; uint8_t v_t_boxed_4455_; lean_object* v_res_4456_; 
v_pu_boxed_4454_ = lean_unbox(v_pu_4444_);
v_t_boxed_4455_ = lean_unbox(v_t_4445_);
v_res_4456_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_boxed_4454_, v_t_boxed_4455_, v_i_4446_, v_as_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec_ref(v___y_4448_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp___boxed(lean_object* v_pu_4457_, lean_object* v_t_4458_, lean_object* v_code_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_){
_start:
{
uint8_t v_pu_boxed_4466_; uint8_t v_t_boxed_4467_; lean_object* v_res_4468_; 
v_pu_boxed_4466_ = lean_unbox(v_pu_4457_);
v_t_boxed_4467_ = lean_unbox(v_t_4458_);
v_res_4468_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_boxed_4466_, v_t_boxed_4467_, v_code_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_);
lean_dec(v_a_4464_);
lean_dec_ref(v_a_4463_);
lean_dec(v_a_4462_);
lean_dec_ref(v_a_4461_);
lean_dec_ref(v_a_4460_);
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(uint8_t v_pu_4469_, uint8_t v_t_4470_, uint8_t v_pu_4471_, uint8_t v_t_4472_, lean_object* v_decl_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_){
_start:
{
lean_object* v___x_4480_; 
v___x_4480_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_4471_, v_t_4472_, v_decl_4473_, v___y_4474_, v___y_4476_);
return v___x_4480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___boxed(lean_object* v_pu_4481_, lean_object* v_t_4482_, lean_object* v_pu_4483_, lean_object* v_t_4484_, lean_object* v_decl_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
uint8_t v_pu_boxed_4492_; uint8_t v_t_boxed_4493_; uint8_t v_pu_boxed_4494_; uint8_t v_t_boxed_4495_; lean_object* v_res_4496_; 
v_pu_boxed_4492_ = lean_unbox(v_pu_4481_);
v_t_boxed_4493_ = lean_unbox(v_t_4482_);
v_pu_boxed_4494_ = lean_unbox(v_pu_4483_);
v_t_boxed_4495_ = lean_unbox(v_t_4484_);
v_res_4496_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(v_pu_boxed_4492_, v_t_boxed_4493_, v_pu_boxed_4494_, v_t_boxed_4495_, v_decl_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec_ref(v___y_4486_);
return v_res_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(uint8_t v_pu_4497_, uint8_t v_t_4498_, uint8_t v_pu_4499_, uint8_t v_t_4500_, lean_object* v_args_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
lean_object* v___x_4508_; 
v___x_4508_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_4499_, v_t_4500_, v_args_4501_, v___y_4502_);
return v___x_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___boxed(lean_object* v_pu_4509_, lean_object* v_t_4510_, lean_object* v_pu_4511_, lean_object* v_t_4512_, lean_object* v_args_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
uint8_t v_pu_boxed_4520_; uint8_t v_t_boxed_4521_; uint8_t v_pu_boxed_4522_; uint8_t v_t_boxed_4523_; lean_object* v_res_4524_; 
v_pu_boxed_4520_ = lean_unbox(v_pu_4509_);
v_t_boxed_4521_ = lean_unbox(v_t_4510_);
v_pu_boxed_4522_ = lean_unbox(v_pu_4511_);
v_t_boxed_4523_ = lean_unbox(v_t_4512_);
v_res_4524_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(v_pu_boxed_4520_, v_t_boxed_4521_, v_pu_boxed_4522_, v_t_boxed_4523_, v_args_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec_ref(v___y_4514_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(uint8_t v_pu_4525_, uint8_t v_t_4526_, uint8_t v_pu_4527_, uint8_t v_t_4528_, lean_object* v_ps_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_){
_start:
{
lean_object* v___x_4536_; 
v___x_4536_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4527_, v_t_4528_, v_ps_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
return v___x_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___boxed(lean_object* v_pu_4537_, lean_object* v_t_4538_, lean_object* v_pu_4539_, lean_object* v_t_4540_, lean_object* v_ps_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_){
_start:
{
uint8_t v_pu_boxed_4548_; uint8_t v_t_boxed_4549_; uint8_t v_pu_boxed_4550_; uint8_t v_t_boxed_4551_; lean_object* v_res_4552_; 
v_pu_boxed_4548_ = lean_unbox(v_pu_4537_);
v_t_boxed_4549_ = lean_unbox(v_t_4538_);
v_pu_boxed_4550_ = lean_unbox(v_pu_4539_);
v_t_boxed_4551_ = lean_unbox(v_t_4540_);
v_res_4552_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(v_pu_boxed_4548_, v_t_boxed_4549_, v_pu_boxed_4550_, v_t_boxed_4551_, v_ps_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec_ref(v___y_4542_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(uint8_t v_pu_4553_, uint8_t v_t_4554_, lean_object* v_i_4555_, lean_object* v_as_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v___x_4563_; 
v___x_4563_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_4553_, v_t_4554_, v_i_4555_, v_as_4556_, v___y_4557_, v___y_4559_);
return v___x_4563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___boxed(lean_object* v_pu_4564_, lean_object* v_t_4565_, lean_object* v_i_4566_, lean_object* v_as_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
uint8_t v_pu_boxed_4574_; uint8_t v_t_boxed_4575_; lean_object* v_res_4576_; 
v_pu_boxed_4574_ = lean_unbox(v_pu_4564_);
v_t_boxed_4575_ = lean_unbox(v_t_4565_);
v_res_4576_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(v_pu_boxed_4574_, v_t_boxed_4575_, v_i_4566_, v_as_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec_ref(v___y_4568_);
return v_res_4576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(uint8_t v_pu_4577_, uint8_t v_t_4578_, lean_object* v_decl_4579_, lean_object* v_inst_4580_, lean_object* v_____do__lift_4581_){
_start:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4582_ = lean_box(v_pu_4577_);
v___x_4583_ = lean_box(v_t_4578_);
v___x_4584_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDeclImp___boxed), 9, 4);
lean_closure_set(v___x_4584_, 0, v___x_4582_);
lean_closure_set(v___x_4584_, 1, v___x_4583_);
lean_closure_set(v___x_4584_, 2, v_decl_4579_);
lean_closure_set(v___x_4584_, 3, v_____do__lift_4581_);
v___x_4585_ = lean_apply_2(v_inst_4580_, lean_box(0), v___x_4584_);
return v___x_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed(lean_object* v_pu_4586_, lean_object* v_t_4587_, lean_object* v_decl_4588_, lean_object* v_inst_4589_, lean_object* v_____do__lift_4590_){
_start:
{
uint8_t v_pu_boxed_4591_; uint8_t v_t_boxed_4592_; lean_object* v_res_4593_; 
v_pu_boxed_4591_ = lean_unbox(v_pu_4586_);
v_t_boxed_4592_ = lean_unbox(v_t_4587_);
v_res_4593_ = l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(v_pu_boxed_4591_, v_t_boxed_4592_, v_decl_4588_, v_inst_4589_, v_____do__lift_4590_);
return v_res_4593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg(uint8_t v_pu_4594_, uint8_t v_t_4595_, lean_object* v_inst_4596_, lean_object* v_inst_4597_, lean_object* v_inst_4598_, lean_object* v_decl_4599_){
_start:
{
lean_object* v_toBind_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___f_4603_; lean_object* v___x_4604_; 
v_toBind_4600_ = lean_ctor_get(v_inst_4597_, 1);
lean_inc(v_toBind_4600_);
lean_dec_ref(v_inst_4597_);
v___x_4601_ = lean_box(v_pu_4594_);
v___x_4602_ = lean_box(v_t_4595_);
v___f_4603_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4603_, 0, v___x_4601_);
lean_closure_set(v___f_4603_, 1, v___x_4602_);
lean_closure_set(v___f_4603_, 2, v_decl_4599_);
lean_closure_set(v___f_4603_, 3, v_inst_4596_);
v___x_4604_ = lean_apply_4(v_toBind_4600_, lean_box(0), lean_box(0), v_inst_4598_, v___f_4603_);
return v___x_4604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___boxed(lean_object* v_pu_4605_, lean_object* v_t_4606_, lean_object* v_inst_4607_, lean_object* v_inst_4608_, lean_object* v_inst_4609_, lean_object* v_decl_4610_){
_start:
{
uint8_t v_pu_boxed_4611_; uint8_t v_t_boxed_4612_; lean_object* v_res_4613_; 
v_pu_boxed_4611_ = lean_unbox(v_pu_4605_);
v_t_boxed_4612_ = lean_unbox(v_t_4606_);
v_res_4613_ = l_Lean_Compiler_LCNF_normFunDecl___redArg(v_pu_boxed_4611_, v_t_boxed_4612_, v_inst_4607_, v_inst_4608_, v_inst_4609_, v_decl_4610_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl(lean_object* v_m_4614_, uint8_t v_pu_4615_, uint8_t v_t_4616_, lean_object* v_inst_4617_, lean_object* v_inst_4618_, lean_object* v_inst_4619_, lean_object* v_decl_4620_){
_start:
{
lean_object* v_toBind_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___f_4624_; lean_object* v___x_4625_; 
v_toBind_4621_ = lean_ctor_get(v_inst_4618_, 1);
lean_inc(v_toBind_4621_);
lean_dec_ref(v_inst_4618_);
v___x_4622_ = lean_box(v_pu_4615_);
v___x_4623_ = lean_box(v_t_4616_);
v___f_4624_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4624_, 0, v___x_4622_);
lean_closure_set(v___f_4624_, 1, v___x_4623_);
lean_closure_set(v___f_4624_, 2, v_decl_4620_);
lean_closure_set(v___f_4624_, 3, v_inst_4617_);
v___x_4625_ = lean_apply_4(v_toBind_4621_, lean_box(0), lean_box(0), v_inst_4619_, v___f_4624_);
return v___x_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___boxed(lean_object* v_m_4626_, lean_object* v_pu_4627_, lean_object* v_t_4628_, lean_object* v_inst_4629_, lean_object* v_inst_4630_, lean_object* v_inst_4631_, lean_object* v_decl_4632_){
_start:
{
uint8_t v_pu_boxed_4633_; uint8_t v_t_boxed_4634_; lean_object* v_res_4635_; 
v_pu_boxed_4633_ = lean_unbox(v_pu_4627_);
v_t_boxed_4634_ = lean_unbox(v_t_4628_);
v_res_4635_ = l_Lean_Compiler_LCNF_normFunDecl(v_m_4626_, v_pu_boxed_4633_, v_t_boxed_4634_, v_inst_4629_, v_inst_4630_, v_inst_4631_, v_decl_4632_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0(uint8_t v_pu_4636_, uint8_t v_t_4637_, lean_object* v_code_4638_, lean_object* v_inst_4639_, lean_object* v_____do__lift_4640_){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4641_ = lean_box(v_pu_4636_);
v___x_4642_ = lean_box(v_t_4637_);
v___x_4643_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCodeImp___boxed), 9, 4);
lean_closure_set(v___x_4643_, 0, v___x_4641_);
lean_closure_set(v___x_4643_, 1, v___x_4642_);
lean_closure_set(v___x_4643_, 2, v_code_4638_);
lean_closure_set(v___x_4643_, 3, v_____do__lift_4640_);
v___x_4644_ = lean_apply_2(v_inst_4639_, lean_box(0), v___x_4643_);
return v___x_4644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed(lean_object* v_pu_4645_, lean_object* v_t_4646_, lean_object* v_code_4647_, lean_object* v_inst_4648_, lean_object* v_____do__lift_4649_){
_start:
{
uint8_t v_pu_boxed_4650_; uint8_t v_t_boxed_4651_; lean_object* v_res_4652_; 
v_pu_boxed_4650_ = lean_unbox(v_pu_4645_);
v_t_boxed_4651_ = lean_unbox(v_t_4646_);
v_res_4652_ = l_Lean_Compiler_LCNF_normCode___redArg___lam__0(v_pu_boxed_4650_, v_t_boxed_4651_, v_code_4647_, v_inst_4648_, v_____do__lift_4649_);
return v_res_4652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg(uint8_t v_pu_4653_, uint8_t v_t_4654_, lean_object* v_inst_4655_, lean_object* v_inst_4656_, lean_object* v_inst_4657_, lean_object* v_code_4658_){
_start:
{
lean_object* v_toBind_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___f_4662_; lean_object* v___x_4663_; 
v_toBind_4659_ = lean_ctor_get(v_inst_4656_, 1);
lean_inc(v_toBind_4659_);
lean_dec_ref(v_inst_4656_);
v___x_4660_ = lean_box(v_pu_4653_);
v___x_4661_ = lean_box(v_t_4654_);
v___f_4662_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4662_, 0, v___x_4660_);
lean_closure_set(v___f_4662_, 1, v___x_4661_);
lean_closure_set(v___f_4662_, 2, v_code_4658_);
lean_closure_set(v___f_4662_, 3, v_inst_4655_);
v___x_4663_ = lean_apply_4(v_toBind_4659_, lean_box(0), lean_box(0), v_inst_4657_, v___f_4662_);
return v___x_4663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___boxed(lean_object* v_pu_4664_, lean_object* v_t_4665_, lean_object* v_inst_4666_, lean_object* v_inst_4667_, lean_object* v_inst_4668_, lean_object* v_code_4669_){
_start:
{
uint8_t v_pu_boxed_4670_; uint8_t v_t_boxed_4671_; lean_object* v_res_4672_; 
v_pu_boxed_4670_ = lean_unbox(v_pu_4664_);
v_t_boxed_4671_ = lean_unbox(v_t_4665_);
v_res_4672_ = l_Lean_Compiler_LCNF_normCode___redArg(v_pu_boxed_4670_, v_t_boxed_4671_, v_inst_4666_, v_inst_4667_, v_inst_4668_, v_code_4669_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode(lean_object* v_m_4673_, uint8_t v_pu_4674_, uint8_t v_t_4675_, lean_object* v_inst_4676_, lean_object* v_inst_4677_, lean_object* v_inst_4678_, lean_object* v_code_4679_){
_start:
{
lean_object* v_toBind_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___f_4683_; lean_object* v___x_4684_; 
v_toBind_4680_ = lean_ctor_get(v_inst_4677_, 1);
lean_inc(v_toBind_4680_);
lean_dec_ref(v_inst_4677_);
v___x_4681_ = lean_box(v_pu_4674_);
v___x_4682_ = lean_box(v_t_4675_);
v___f_4683_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4683_, 0, v___x_4681_);
lean_closure_set(v___f_4683_, 1, v___x_4682_);
lean_closure_set(v___f_4683_, 2, v_code_4679_);
lean_closure_set(v___f_4683_, 3, v_inst_4676_);
v___x_4684_ = lean_apply_4(v_toBind_4680_, lean_box(0), lean_box(0), v_inst_4678_, v___f_4683_);
return v___x_4684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___boxed(lean_object* v_m_4685_, lean_object* v_pu_4686_, lean_object* v_t_4687_, lean_object* v_inst_4688_, lean_object* v_inst_4689_, lean_object* v_inst_4690_, lean_object* v_code_4691_){
_start:
{
uint8_t v_pu_boxed_4692_; uint8_t v_t_boxed_4693_; lean_object* v_res_4694_; 
v_pu_boxed_4692_ = lean_unbox(v_pu_4686_);
v_t_boxed_4693_ = lean_unbox(v_t_4687_);
v_res_4694_ = l_Lean_Compiler_LCNF_normCode(v_m_4685_, v_pu_boxed_4692_, v_t_boxed_4693_, v_inst_4688_, v_inst_4689_, v_inst_4690_, v_code_4691_);
return v_res_4694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t v_pu_4695_, lean_object* v_e_4696_, lean_object* v_s_4697_, uint8_t v_translator_4698_){
_start:
{
lean_object* v___x_4700_; lean_object* v___x_4701_; 
v___x_4700_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4695_, v_s_4697_, v_translator_4698_, v_e_4696_);
v___x_4701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4701_, 0, v___x_4700_);
return v___x_4701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg___boxed(lean_object* v_pu_4702_, lean_object* v_e_4703_, lean_object* v_s_4704_, lean_object* v_translator_4705_, lean_object* v_a_4706_){
_start:
{
uint8_t v_pu_boxed_4707_; uint8_t v_translator_boxed_4708_; lean_object* v_res_4709_; 
v_pu_boxed_4707_ = lean_unbox(v_pu_4702_);
v_translator_boxed_4708_ = lean_unbox(v_translator_4705_);
v_res_4709_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_boxed_4707_, v_e_4703_, v_s_4704_, v_translator_boxed_4708_);
lean_dec_ref(v_s_4704_);
return v_res_4709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(uint8_t v_pu_4710_, lean_object* v_e_4711_, lean_object* v_s_4712_, uint8_t v_translator_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_){
_start:
{
lean_object* v___x_4719_; 
v___x_4719_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_4710_, v_e_4711_, v_s_4712_, v_translator_4713_);
return v___x_4719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___boxed(lean_object* v_pu_4720_, lean_object* v_e_4721_, lean_object* v_s_4722_, lean_object* v_translator_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_){
_start:
{
uint8_t v_pu_boxed_4729_; uint8_t v_translator_boxed_4730_; lean_object* v_res_4731_; 
v_pu_boxed_4729_ = lean_unbox(v_pu_4720_);
v_translator_boxed_4730_ = lean_unbox(v_translator_4723_);
v_res_4731_ = l_Lean_Compiler_LCNF_replaceExprFVars(v_pu_boxed_4729_, v_e_4721_, v_s_4722_, v_translator_boxed_4730_, v_a_4724_, v_a_4725_, v_a_4726_, v_a_4727_);
lean_dec(v_a_4727_);
lean_dec_ref(v_a_4726_);
lean_dec(v_a_4725_);
lean_dec_ref(v_a_4724_);
lean_dec_ref(v_s_4722_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t v_pu_4732_, lean_object* v_code_4733_, lean_object* v_s_4734_, uint8_t v_translator_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_){
_start:
{
lean_object* v___x_4741_; 
v___x_4741_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4732_, v_translator_4735_, v_code_4733_, v_s_4734_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_);
return v___x_4741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars___boxed(lean_object* v_pu_4742_, lean_object* v_code_4743_, lean_object* v_s_4744_, lean_object* v_translator_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_){
_start:
{
uint8_t v_pu_boxed_4751_; uint8_t v_translator_boxed_4752_; lean_object* v_res_4753_; 
v_pu_boxed_4751_ = lean_unbox(v_pu_4742_);
v_translator_boxed_4752_ = lean_unbox(v_translator_4745_);
v_res_4753_ = l_Lean_Compiler_LCNF_replaceFVars(v_pu_boxed_4751_, v_code_4743_, v_s_4744_, v_translator_boxed_4752_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_);
lean_dec(v_a_4749_);
lean_dec_ref(v_a_4748_);
lean_dec(v_a_4747_);
lean_dec_ref(v_a_4746_);
lean_dec_ref(v_s_4744_);
return v_res_4753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg(lean_object* v_a_4757_){
_start:
{
lean_object* v___x_4759_; lean_object* v___x_4760_; 
v___x_4759_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1));
v___x_4760_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4759_, v_a_4757_);
return v___x_4760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___boxed(lean_object* v_a_4761_, lean_object* v_a_4762_){
_start:
{
lean_object* v_res_4763_; 
v_res_4763_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4761_);
lean_dec(v_a_4761_);
return v_res_4763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName(lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_){
_start:
{
lean_object* v___x_4769_; 
v___x_4769_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4765_);
return v___x_4769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___boxed(lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_){
_start:
{
lean_object* v_res_4775_; 
v_res_4775_ = l_Lean_Compiler_LCNF_mkFreshJpName(v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_);
lean_dec(v_a_4773_);
lean_dec_ref(v_a_4772_);
lean_dec(v_a_4771_);
lean_dec_ref(v_a_4770_);
return v_res_4775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t v_pu_4776_, lean_object* v_type_4777_, uint8_t v_borrow_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_){
_start:
{
lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v_a_4786_; lean_object* v___x_4787_; 
v___x_4784_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_4785_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4784_, v_a_4780_);
v_a_4786_ = lean_ctor_get(v___x_4785_, 0);
lean_inc(v_a_4786_);
lean_dec_ref(v___x_4785_);
v___x_4787_ = l_Lean_Compiler_LCNF_mkParam(v_pu_4776_, v_a_4786_, v_type_4777_, v_borrow_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_);
return v___x_4787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam___boxed(lean_object* v_pu_4788_, lean_object* v_type_4789_, lean_object* v_borrow_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_){
_start:
{
uint8_t v_pu_boxed_4796_; uint8_t v_borrow_boxed_4797_; lean_object* v_res_4798_; 
v_pu_boxed_4796_ = lean_unbox(v_pu_4788_);
v_borrow_boxed_4797_ = lean_unbox(v_borrow_4790_);
v_res_4798_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_boxed_4796_, v_type_4789_, v_borrow_boxed_4797_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_);
lean_dec(v_a_4794_);
lean_dec_ref(v_a_4793_);
lean_dec(v_a_4792_);
lean_dec_ref(v_a_4791_);
return v_res_4798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object* v_a_4799_){
_start:
{
lean_object* v_config_4801_; lean_object* v___x_4802_; 
v_config_4801_ = lean_ctor_get(v_a_4799_, 0);
lean_inc_ref(v_config_4801_);
v___x_4802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4802_, 0, v_config_4801_);
return v___x_4802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg___boxed(lean_object* v_a_4803_, lean_object* v_a_4804_){
_start:
{
lean_object* v_res_4805_; 
v_res_4805_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4803_);
lean_dec_ref(v_a_4803_);
return v_res_4805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig(lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_){
_start:
{
lean_object* v___x_4811_; 
v___x_4811_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4806_);
return v___x_4811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___boxed(lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_){
_start:
{
lean_object* v_res_4817_; 
v_res_4817_ = l_Lean_Compiler_LCNF_getConfig(v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_);
lean_dec(v_a_4815_);
lean_dec_ref(v_a_4814_);
lean_dec(v_a_4813_);
lean_dec_ref(v_a_4812_);
return v_res_4817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object* v_x_4818_, lean_object* v_s_4819_, uint8_t v_phase_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_){
_start:
{
lean_object* v___x_4824_; lean_object* v_options_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; 
v___x_4824_ = lean_st_mk_ref(v_s_4819_);
v_options_4825_ = lean_ctor_get(v_a_4821_, 2);
v___x_4826_ = l_Lean_Compiler_LCNF_toConfigOptions(v_options_4825_);
v___x_4827_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4827_, 0, v___x_4826_);
lean_ctor_set_uint8(v___x_4827_, sizeof(void*)*1, v_phase_4820_);
lean_inc(v_a_4822_);
lean_inc_ref(v_a_4821_);
lean_inc(v___x_4824_);
v___x_4828_ = lean_apply_5(v_x_4818_, v___x_4827_, v___x_4824_, v_a_4821_, v_a_4822_, lean_box(0));
if (lean_obj_tag(v___x_4828_) == 0)
{
lean_object* v_a_4829_; lean_object* v___x_4831_; uint8_t v_isShared_4832_; uint8_t v_isSharedCheck_4837_; 
v_a_4829_ = lean_ctor_get(v___x_4828_, 0);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4828_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4831_ = v___x_4828_;
v_isShared_4832_ = v_isSharedCheck_4837_;
goto v_resetjp_4830_;
}
else
{
lean_inc(v_a_4829_);
lean_dec(v___x_4828_);
v___x_4831_ = lean_box(0);
v_isShared_4832_ = v_isSharedCheck_4837_;
goto v_resetjp_4830_;
}
v_resetjp_4830_:
{
lean_object* v___x_4833_; lean_object* v___x_4835_; 
v___x_4833_ = lean_st_ref_get(v___x_4824_);
lean_dec(v___x_4824_);
lean_dec(v___x_4833_);
if (v_isShared_4832_ == 0)
{
v___x_4835_ = v___x_4831_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v_a_4829_);
v___x_4835_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
return v___x_4835_;
}
}
}
else
{
lean_dec(v___x_4824_);
return v___x_4828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg___boxed(lean_object* v_x_4838_, lean_object* v_s_4839_, lean_object* v_phase_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_){
_start:
{
uint8_t v_phase_boxed_4844_; lean_object* v_res_4845_; 
v_phase_boxed_4844_ = lean_unbox(v_phase_4840_);
v_res_4845_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4838_, v_s_4839_, v_phase_boxed_4844_, v_a_4841_, v_a_4842_);
lean_dec(v_a_4842_);
lean_dec_ref(v_a_4841_);
return v_res_4845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run(lean_object* v_00_u03b1_4846_, lean_object* v_x_4847_, lean_object* v_s_4848_, uint8_t v_phase_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_){
_start:
{
lean_object* v___x_4853_; 
v___x_4853_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4847_, v_s_4848_, v_phase_4849_, v_a_4850_, v_a_4851_);
return v___x_4853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___boxed(lean_object* v_00_u03b1_4854_, lean_object* v_x_4855_, lean_object* v_s_4856_, lean_object* v_phase_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_){
_start:
{
uint8_t v_phase_boxed_4861_; lean_object* v_res_4862_; 
v_phase_boxed_4861_ = lean_unbox(v_phase_4857_);
v_res_4862_ = l_Lean_Compiler_LCNF_CompilerM_run(v_00_u03b1_4854_, v_x_4855_, v_s_4856_, v_phase_boxed_4861_, v_a_4858_, v_a_4859_);
lean_dec(v_a_4859_);
lean_dec_ref(v_a_4858_);
return v_res_4862_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0(void){
_start:
{
lean_object* v___x_4863_; 
v___x_4863_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_4863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(lean_object* v_00_u03b1_4864_, lean_object* v_00_u03b2_4865_, lean_object* v_inst_4866_, lean_object* v_inst_4867_){
_start:
{
lean_object* v___x_4868_; 
v___x_4868_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(lean_object* v_00_u03b1_4869_, lean_object* v_00_u03b2_4870_, lean_object* v_inst_4871_, lean_object* v_inst_4872_){
_start:
{
lean_object* v_res_4873_; 
v_res_4873_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(v_00_u03b1_4869_, v_00_u03b2_4870_, v_inst_4871_, v_inst_4872_);
lean_dec_ref(v_inst_4872_);
lean_dec_ref(v_inst_4871_);
return v_res_4873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension(lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_){
_start:
{
lean_object* v___x_4878_; 
v___x_4878_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___boxed(lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_){
_start:
{
lean_object* v_res_4883_; 
v_res_4883_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension(v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_);
lean_dec_ref(v_a_4882_);
lean_dec_ref(v_a_4881_);
return v_res_4883_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; 
v___x_4887_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2));
v___x_4888_ = lean_unsigned_to_nat(14u);
v___x_4889_ = lean_unsigned_to_nat(178u);
v___x_4890_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1));
v___x_4891_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0));
v___x_4892_ = l_mkPanicMessageWithDecl(v___x_4891_, v___x_4890_, v___x_4889_, v___x_4888_, v___x_4887_);
return v___x_4892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(lean_object* v_inst_4893_, lean_object* v_inst_4894_, lean_object* v_snd_4895_, lean_object* v_inst_4896_, lean_object* v_s_4897_, lean_object* v_e_4898_){
_start:
{
lean_object* v_fst_4899_; lean_object* v_snd_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4915_; 
v_fst_4899_ = lean_ctor_get(v_s_4897_, 0);
v_snd_4900_ = lean_ctor_get(v_s_4897_, 1);
v_isSharedCheck_4915_ = !lean_is_exclusive(v_s_4897_);
if (v_isSharedCheck_4915_ == 0)
{
v___x_4902_ = v_s_4897_;
v_isShared_4903_ = v_isSharedCheck_4915_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_snd_4900_);
lean_inc(v_fst_4899_);
lean_dec(v_s_4897_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4915_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4904_; lean_object* v___y_4906_; lean_object* v___x_4911_; 
lean_inc_n(v_e_4898_, 2);
v___x_4904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4904_, 0, v_e_4898_);
lean_ctor_set(v___x_4904_, 1, v_fst_4899_);
lean_inc_ref(v_inst_4894_);
lean_inc_ref(v_inst_4893_);
v___x_4911_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4893_, v_inst_4894_, v_snd_4895_, v_e_4898_);
if (lean_obj_tag(v___x_4911_) == 0)
{
lean_object* v___x_4912_; lean_object* v___x_4913_; 
v___x_4912_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3);
v___x_4913_ = l_panic___redArg(v_inst_4896_, v___x_4912_);
v___y_4906_ = v___x_4913_;
goto v___jp_4905_;
}
else
{
lean_object* v_val_4914_; 
v_val_4914_ = lean_ctor_get(v___x_4911_, 0);
lean_inc(v_val_4914_);
lean_dec_ref_known(v___x_4911_, 1);
v___y_4906_ = v_val_4914_;
goto v___jp_4905_;
}
v___jp_4905_:
{
lean_object* v___x_4907_; lean_object* v___x_4909_; 
v___x_4907_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4893_, v_inst_4894_, v_snd_4900_, v_e_4898_, v___y_4906_);
if (v_isShared_4903_ == 0)
{
lean_ctor_set(v___x_4902_, 1, v___x_4907_);
lean_ctor_set(v___x_4902_, 0, v___x_4904_);
v___x_4909_ = v___x_4902_;
goto v_reusejp_4908_;
}
else
{
lean_object* v_reuseFailAlloc_4910_; 
v_reuseFailAlloc_4910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4910_, 0, v___x_4904_);
lean_ctor_set(v_reuseFailAlloc_4910_, 1, v___x_4907_);
v___x_4909_ = v_reuseFailAlloc_4910_;
goto v_reusejp_4908_;
}
v_reusejp_4908_:
{
return v___x_4909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed(lean_object* v_inst_4916_, lean_object* v_inst_4917_, lean_object* v_snd_4918_, lean_object* v_inst_4919_, lean_object* v_s_4920_, lean_object* v_e_4921_){
_start:
{
lean_object* v_res_4922_; 
v_res_4922_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(v_inst_4916_, v_inst_4917_, v_snd_4918_, v_inst_4919_, v_s_4920_, v_e_4921_);
lean_dec(v_inst_4919_);
lean_dec(v_snd_4918_);
return v_res_4922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(lean_object* v_inst_4925_, lean_object* v_inst_4926_, lean_object* v_inst_4927_, lean_object* v_oldState_4928_, lean_object* v_newState_4929_, lean_object* v_x_4930_, lean_object* v_s_4931_){
_start:
{
lean_object* v_fst_4932_; lean_object* v_snd_4933_; lean_object* v_fst_4934_; lean_object* v___f_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v_newEntries_4940_; lean_object* v___x_4941_; 
v_fst_4932_ = lean_ctor_get(v_newState_4929_, 0);
lean_inc_n(v_fst_4932_, 2);
v_snd_4933_ = lean_ctor_get(v_newState_4929_, 1);
lean_inc(v_snd_4933_);
lean_dec_ref(v_newState_4929_);
v_fst_4934_ = lean_ctor_get(v_oldState_4928_, 0);
v___f_4935_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_4935_, 0, v_inst_4925_);
lean_closure_set(v___f_4935_, 1, v_inst_4926_);
lean_closure_set(v___f_4935_, 2, v_snd_4933_);
lean_closure_set(v___f_4935_, 3, v_inst_4927_);
v___x_4936_ = l_List_lengthTR___redArg(v_fst_4932_);
v___x_4937_ = l_List_lengthTR___redArg(v_fst_4934_);
v___x_4938_ = lean_nat_sub(v___x_4936_, v___x_4937_);
lean_dec(v___x_4937_);
lean_dec(v___x_4936_);
v___x_4939_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0));
v_newEntries_4940_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_fst_4932_, v_fst_4932_, v___x_4938_, v___x_4939_);
lean_dec(v_fst_4932_);
v___x_4941_ = l_List_foldl___redArg(v___f_4935_, v_s_4931_, v_newEntries_4940_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(lean_object* v_inst_4942_, lean_object* v_inst_4943_, lean_object* v_inst_4944_, lean_object* v_oldState_4945_, lean_object* v_newState_4946_, lean_object* v_x_4947_, lean_object* v_s_4948_){
_start:
{
lean_object* v_res_4949_; 
v_res_4949_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(v_inst_4942_, v_inst_4943_, v_inst_4944_, v_oldState_4945_, v_newState_4946_, v_x_4947_, v_s_4948_);
lean_dec(v_x_4947_);
lean_dec_ref(v_oldState_4945_);
return v_res_4949_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0(void){
_start:
{
lean_object* v___x_4950_; 
v___x_4950_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4950_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1(void){
_start:
{
lean_object* v___x_4951_; lean_object* v___x_4952_; 
v___x_4951_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0);
v___x_4952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4952_, 0, v___x_4951_);
return v___x_4952_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2(void){
_start:
{
lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; 
v___x_4953_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1);
v___x_4954_ = lean_box(0);
v___x_4955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4955_, 0, v___x_4954_);
lean_ctor_set(v___x_4955_, 1, v___x_4953_);
return v___x_4955_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3(void){
_start:
{
lean_object* v___x_4956_; lean_object* v___x_4957_; 
v___x_4956_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2);
v___x_4957_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_4957_, 0, lean_box(0));
lean_closure_set(v___x_4957_, 1, lean_box(0));
lean_closure_set(v___x_4957_, 2, v___x_4956_);
return v___x_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object* v_inst_4958_, lean_object* v_inst_4959_, lean_object* v_inst_4960_){
_start:
{
lean_object* v___f_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; 
v___f_4962_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4962_, 0, v_inst_4958_);
lean_closure_set(v___f_4962_, 1, v_inst_4959_);
lean_closure_set(v___f_4962_, 2, v_inst_4960_);
v___x_4963_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3);
v___x_4964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4964_, 0, v___f_4962_);
v___x_4965_ = lean_box(0);
v___x_4966_ = l_Lean_registerEnvExtension___redArg(v___x_4963_, v___x_4964_, v___x_4965_);
if (lean_obj_tag(v___x_4966_) == 0)
{
lean_object* v_a_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_4974_; 
v_a_4967_ = lean_ctor_get(v___x_4966_, 0);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4966_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4969_ = v___x_4966_;
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_a_4967_);
lean_dec(v___x_4966_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v___x_4972_; 
if (v_isShared_4970_ == 0)
{
v___x_4972_ = v___x_4969_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_a_4967_);
v___x_4972_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
return v___x_4972_;
}
}
}
else
{
lean_object* v_a_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_4982_; 
v_a_4975_ = lean_ctor_get(v___x_4966_, 0);
v_isSharedCheck_4982_ = !lean_is_exclusive(v___x_4966_);
if (v_isSharedCheck_4982_ == 0)
{
v___x_4977_ = v___x_4966_;
v_isShared_4978_ = v_isSharedCheck_4982_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_a_4975_);
lean_dec(v___x_4966_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_4982_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
lean_object* v___x_4980_; 
if (v_isShared_4978_ == 0)
{
v___x_4980_ = v___x_4977_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_a_4975_);
v___x_4980_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
return v___x_4980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object* v_inst_4983_, lean_object* v_inst_4984_, lean_object* v_inst_4985_, lean_object* v_a_4986_){
_start:
{
lean_object* v_res_4987_; 
v_res_4987_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4983_, v_inst_4984_, v_inst_4985_);
return v_res_4987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object* v_00_u03b1_4988_, lean_object* v_00_u03b2_4989_, lean_object* v_inst_4990_, lean_object* v_inst_4991_, lean_object* v_inst_4992_){
_start:
{
lean_object* v___x_4994_; 
v___x_4994_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4990_, v_inst_4991_, v_inst_4992_);
return v___x_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object* v_00_u03b1_4995_, lean_object* v_00_u03b2_4996_, lean_object* v_inst_4997_, lean_object* v_inst_4998_, lean_object* v_inst_4999_, lean_object* v_a_5000_){
_start:
{
lean_object* v_res_5001_; 
v_res_5001_ = l_Lean_Compiler_LCNF_CacheExtension_register(v_00_u03b1_4995_, v_00_u03b2_4996_, v_inst_4997_, v_inst_4998_, v_inst_4999_);
return v_res_5001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object* v_a_5002_, lean_object* v_inst_5003_, lean_object* v_inst_5004_, lean_object* v_b_5005_, lean_object* v_x_5006_){
_start:
{
lean_object* v_fst_5007_; lean_object* v_snd_5008_; lean_object* v___x_5010_; uint8_t v_isShared_5011_; uint8_t v_isSharedCheck_5017_; 
v_fst_5007_ = lean_ctor_get(v_x_5006_, 0);
v_snd_5008_ = lean_ctor_get(v_x_5006_, 1);
v_isSharedCheck_5017_ = !lean_is_exclusive(v_x_5006_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_5010_ = v_x_5006_;
v_isShared_5011_ = v_isSharedCheck_5017_;
goto v_resetjp_5009_;
}
else
{
lean_inc(v_snd_5008_);
lean_inc(v_fst_5007_);
lean_dec(v_x_5006_);
v___x_5010_ = lean_box(0);
v_isShared_5011_ = v_isSharedCheck_5017_;
goto v_resetjp_5009_;
}
v_resetjp_5009_:
{
lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5015_; 
lean_inc(v_a_5002_);
v___x_5012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5012_, 0, v_a_5002_);
lean_ctor_set(v___x_5012_, 1, v_fst_5007_);
v___x_5013_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_5003_, v_inst_5004_, v_snd_5008_, v_a_5002_, v_b_5005_);
if (v_isShared_5011_ == 0)
{
lean_ctor_set(v___x_5010_, 1, v___x_5013_);
lean_ctor_set(v___x_5010_, 0, v___x_5012_);
v___x_5015_ = v___x_5010_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v___x_5012_);
lean_ctor_set(v_reuseFailAlloc_5016_, 1, v___x_5013_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_5018_; 
v___x_5018_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5018_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_5019_; lean_object* v___x_5020_; 
v___x_5019_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0);
v___x_5020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5020_, 0, v___x_5019_);
return v___x_5020_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2(void){
_start:
{
lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5021_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1);
v___x_5022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5022_, 0, v___x_5021_);
lean_ctor_set(v___x_5022_, 1, v___x_5021_);
return v___x_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object* v_inst_5023_, lean_object* v_inst_5024_, lean_object* v_ext_5025_, lean_object* v_a_5026_, lean_object* v_b_5027_, lean_object* v_a_5028_){
_start:
{
lean_object* v___x_5030_; lean_object* v_env_5031_; lean_object* v_nextMacroScope_5032_; lean_object* v_ngen_5033_; lean_object* v_auxDeclNGen_5034_; lean_object* v_traceState_5035_; lean_object* v_messages_5036_; lean_object* v_infoState_5037_; lean_object* v_snapshotTasks_5038_; lean_object* v___x_5040_; uint8_t v_isShared_5041_; uint8_t v_isSharedCheck_5053_; 
v___x_5030_ = lean_st_ref_take(v_a_5028_);
v_env_5031_ = lean_ctor_get(v___x_5030_, 0);
v_nextMacroScope_5032_ = lean_ctor_get(v___x_5030_, 1);
v_ngen_5033_ = lean_ctor_get(v___x_5030_, 2);
v_auxDeclNGen_5034_ = lean_ctor_get(v___x_5030_, 3);
v_traceState_5035_ = lean_ctor_get(v___x_5030_, 4);
v_messages_5036_ = lean_ctor_get(v___x_5030_, 6);
v_infoState_5037_ = lean_ctor_get(v___x_5030_, 7);
v_snapshotTasks_5038_ = lean_ctor_get(v___x_5030_, 8);
v_isSharedCheck_5053_ = !lean_is_exclusive(v___x_5030_);
if (v_isSharedCheck_5053_ == 0)
{
lean_object* v_unused_5054_; 
v_unused_5054_ = lean_ctor_get(v___x_5030_, 5);
lean_dec(v_unused_5054_);
v___x_5040_ = v___x_5030_;
v_isShared_5041_ = v_isSharedCheck_5053_;
goto v_resetjp_5039_;
}
else
{
lean_inc(v_snapshotTasks_5038_);
lean_inc(v_infoState_5037_);
lean_inc(v_messages_5036_);
lean_inc(v_traceState_5035_);
lean_inc(v_auxDeclNGen_5034_);
lean_inc(v_ngen_5033_);
lean_inc(v_nextMacroScope_5032_);
lean_inc(v_env_5031_);
lean_dec(v___x_5030_);
v___x_5040_ = lean_box(0);
v_isShared_5041_ = v_isSharedCheck_5053_;
goto v_resetjp_5039_;
}
v_resetjp_5039_:
{
lean_object* v_asyncMode_5042_; lean_object* v___f_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5048_; 
v_asyncMode_5042_ = lean_ctor_get(v_ext_5025_, 2);
lean_inc(v_asyncMode_5042_);
v___f_5043_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0), 5, 4);
lean_closure_set(v___f_5043_, 0, v_a_5026_);
lean_closure_set(v___f_5043_, 1, v_inst_5023_);
lean_closure_set(v___f_5043_, 2, v_inst_5024_);
lean_closure_set(v___f_5043_, 3, v_b_5027_);
v___x_5044_ = lean_box(0);
v___x_5045_ = l_Lean_EnvExtension_modifyState___redArg(v_ext_5025_, v_env_5031_, v___f_5043_, v_asyncMode_5042_, v___x_5044_);
lean_dec(v_asyncMode_5042_);
v___x_5046_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2);
if (v_isShared_5041_ == 0)
{
lean_ctor_set(v___x_5040_, 5, v___x_5046_);
lean_ctor_set(v___x_5040_, 0, v___x_5045_);
v___x_5048_ = v___x_5040_;
goto v_reusejp_5047_;
}
else
{
lean_object* v_reuseFailAlloc_5052_; 
v_reuseFailAlloc_5052_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5052_, 0, v___x_5045_);
lean_ctor_set(v_reuseFailAlloc_5052_, 1, v_nextMacroScope_5032_);
lean_ctor_set(v_reuseFailAlloc_5052_, 2, v_ngen_5033_);
lean_ctor_set(v_reuseFailAlloc_5052_, 3, v_auxDeclNGen_5034_);
lean_ctor_set(v_reuseFailAlloc_5052_, 4, v_traceState_5035_);
lean_ctor_set(v_reuseFailAlloc_5052_, 5, v___x_5046_);
lean_ctor_set(v_reuseFailAlloc_5052_, 6, v_messages_5036_);
lean_ctor_set(v_reuseFailAlloc_5052_, 7, v_infoState_5037_);
lean_ctor_set(v_reuseFailAlloc_5052_, 8, v_snapshotTasks_5038_);
v___x_5048_ = v_reuseFailAlloc_5052_;
goto v_reusejp_5047_;
}
v_reusejp_5047_:
{
lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; 
v___x_5049_ = lean_st_ref_put(v_a_5028_, v___x_5048_);
v___x_5050_ = lean_box(0);
v___x_5051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5051_, 0, v___x_5050_);
return v___x_5051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object* v_inst_5055_, lean_object* v_inst_5056_, lean_object* v_ext_5057_, lean_object* v_a_5058_, lean_object* v_b_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_){
_start:
{
lean_object* v_res_5062_; 
v_res_5062_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_5055_, v_inst_5056_, v_ext_5057_, v_a_5058_, v_b_5059_, v_a_5060_);
lean_dec(v_a_5060_);
return v_res_5062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object* v_00_u03b1_5063_, lean_object* v_00_u03b2_5064_, lean_object* v_inst_5065_, lean_object* v_inst_5066_, lean_object* v_inst_5067_, lean_object* v_ext_5068_, lean_object* v_a_5069_, lean_object* v_b_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_){
_start:
{
lean_object* v___x_5074_; 
v___x_5074_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_5065_, v_inst_5066_, v_ext_5068_, v_a_5069_, v_b_5070_, v_a_5072_);
return v___x_5074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object* v_00_u03b1_5075_, lean_object* v_00_u03b2_5076_, lean_object* v_inst_5077_, lean_object* v_inst_5078_, lean_object* v_inst_5079_, lean_object* v_ext_5080_, lean_object* v_a_5081_, lean_object* v_b_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_){
_start:
{
lean_object* v_res_5086_; 
v_res_5086_ = l_Lean_Compiler_LCNF_CacheExtension_insert(v_00_u03b1_5075_, v_00_u03b2_5076_, v_inst_5077_, v_inst_5078_, v_inst_5079_, v_ext_5080_, v_a_5081_, v_b_5082_, v_a_5083_, v_a_5084_);
lean_dec(v_a_5084_);
lean_dec_ref(v_a_5083_);
lean_dec(v_inst_5079_);
return v_res_5086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(lean_object* v_inst_5087_, lean_object* v_inst_5088_, lean_object* v_ext_5089_, lean_object* v_a_5090_, lean_object* v_a_5091_){
_start:
{
lean_object* v___x_5093_; lean_object* v_env_5094_; lean_object* v_asyncMode_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v_snd_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; 
v___x_5093_ = lean_st_ref_get(v_a_5091_);
v_env_5094_ = lean_ctor_get(v___x_5093_, 0);
lean_inc_ref(v_env_5094_);
lean_dec(v___x_5093_);
v_asyncMode_5095_ = lean_ctor_get(v_ext_5089_, 2);
v___x_5096_ = lean_box(0);
v___x_5097_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v_inst_5087_, v_inst_5088_);
v___x_5098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5098_, 0, v___x_5096_);
lean_ctor_set(v___x_5098_, 1, v___x_5097_);
v___x_5099_ = lean_box(0);
v___x_5100_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_5098_, v_ext_5089_, v_env_5094_, v_asyncMode_5095_, v___x_5099_);
lean_dec_ref_known(v___x_5098_, 2);
v_snd_5101_ = lean_ctor_get(v___x_5100_, 1);
lean_inc(v_snd_5101_);
lean_dec(v___x_5100_);
v___x_5102_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_5087_, v_inst_5088_, v_snd_5101_, v_a_5090_);
lean_dec(v_snd_5101_);
v___x_5103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5103_, 0, v___x_5102_);
return v___x_5103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(lean_object* v_inst_5104_, lean_object* v_inst_5105_, lean_object* v_ext_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_){
_start:
{
lean_object* v_res_5110_; 
v_res_5110_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_5104_, v_inst_5105_, v_ext_5106_, v_a_5107_, v_a_5108_);
lean_dec(v_a_5108_);
lean_dec_ref(v_ext_5106_);
return v_res_5110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_object* v_00_u03b1_5111_, lean_object* v_00_u03b2_5112_, lean_object* v_inst_5113_, lean_object* v_inst_5114_, lean_object* v_inst_5115_, lean_object* v_ext_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_){
_start:
{
lean_object* v___x_5121_; 
v___x_5121_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_5113_, v_inst_5114_, v_ext_5116_, v_a_5117_, v_a_5119_);
return v___x_5121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(lean_object* v_00_u03b1_5122_, lean_object* v_00_u03b2_5123_, lean_object* v_inst_5124_, lean_object* v_inst_5125_, lean_object* v_inst_5126_, lean_object* v_ext_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_){
_start:
{
lean_object* v_res_5132_; 
v_res_5132_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f(v_00_u03b1_5122_, v_00_u03b2_5123_, v_inst_5124_, v_inst_5125_, v_inst_5126_, v_ext_5127_, v_a_5128_, v_a_5129_, v_a_5130_);
lean_dec(v_a_5130_);
lean_dec_ref(v_a_5129_);
lean_dec_ref(v_ext_5127_);
lean_dec(v_inst_5126_);
return v_res_5132_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_LCtx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ConfigOptions(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
