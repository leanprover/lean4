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
extern lean_object* l_Lean_instInhabitedFVarId_default;
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
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedLCtx_default;
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
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedNormFVarResult;
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
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = l_Lean_Compiler_LCNF_instInhabitedLCtx_default;
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v___x_98_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default(void){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState(void){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default;
return v___x_102_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0(void){
_start:
{
lean_object* v___x_103_; uint8_t v___x_104_; lean_object* v___x_105_; 
v___x_103_ = l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default;
v___x_104_ = 0;
v___x_105_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_105_, 0, v___x_103_);
lean_ctor_set_uint8(v___x_105_, sizeof(void*)*1, v___x_104_);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default(void){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext(void){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default;
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(lean_object* v_00_u03b1_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v___y_109_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object* v_00_u03b1_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(v_00_u03b1_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object* v_00_u03b1_124_, lean_object* v_00_u03b2_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; 
lean_inc(v___y_131_);
lean_inc_ref(v___y_130_);
lean_inc(v___y_129_);
lean_inc_ref(v___y_128_);
v___x_133_ = lean_apply_5(v___y_126_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, lean_box(0));
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_135_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
lean_dec_ref(v___x_133_);
lean_inc(v___y_131_);
lean_inc_ref(v___y_130_);
lean_inc(v___y_129_);
lean_inc_ref(v___y_128_);
v___x_135_ = lean_apply_6(v___y_127_, v_a_134_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, lean_box(0));
return v___x_135_;
}
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
lean_dec_ref(v___y_127_);
v_a_136_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_133_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_133_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object* v_00_u03b1_144_, lean_object* v_00_u03b2_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(v_00_u03b1_144_, v_00_u03b2_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
return v_res_153_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0(void){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_instMonadEIO(lean_box(0));
return v___x_154_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0);
v___x_156_ = l_StateRefT_x27_instMonad___redArg(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM(void){
_start:
{
lean_object* v___x_161_; lean_object* v_toApplicative_162_; lean_object* v_toFunctor_163_; lean_object* v_toSeq_164_; lean_object* v_toSeqLeft_165_; lean_object* v_toSeqRight_166_; lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___f_169_; lean_object* v___f_170_; lean_object* v___x_171_; lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___f_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v_toApplicative_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_205_; 
v___x_161_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_162_ = lean_ctor_get(v___x_161_, 0);
v_toFunctor_163_ = lean_ctor_get(v_toApplicative_162_, 0);
v_toSeq_164_ = lean_ctor_get(v_toApplicative_162_, 2);
v_toSeqLeft_165_ = lean_ctor_get(v_toApplicative_162_, 3);
v_toSeqRight_166_ = lean_ctor_get(v_toApplicative_162_, 4);
v___f_167_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_168_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_163_, 2);
v___f_169_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_169_, 0, v_toFunctor_163_);
v___f_170_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_170_, 0, v_toFunctor_163_);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v___f_169_);
lean_ctor_set(v___x_171_, 1, v___f_170_);
lean_inc(v_toSeqRight_166_);
v___f_172_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_172_, 0, v_toSeqRight_166_);
lean_inc(v_toSeqLeft_165_);
v___f_173_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_173_, 0, v_toSeqLeft_165_);
lean_inc(v_toSeq_164_);
v___f_174_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_174_, 0, v_toSeq_164_);
v___x_175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_175_, 0, v___x_171_);
lean_ctor_set(v___x_175_, 1, v___f_167_);
lean_ctor_set(v___x_175_, 2, v___f_174_);
lean_ctor_set(v___x_175_, 3, v___f_173_);
lean_ctor_set(v___x_175_, 4, v___f_172_);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___f_168_);
v___x_177_ = l_StateRefT_x27_instMonad___redArg(v___x_176_);
v_toApplicative_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v___x_177_, 1);
lean_dec(v_unused_206_);
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_205_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_toApplicative_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_205_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v_toFunctor_182_; lean_object* v_toSeq_183_; lean_object* v_toSeqLeft_184_; lean_object* v_toSeqRight_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_203_; 
v_toFunctor_182_ = lean_ctor_get(v_toApplicative_178_, 0);
v_toSeq_183_ = lean_ctor_get(v_toApplicative_178_, 2);
v_toSeqLeft_184_ = lean_ctor_get(v_toApplicative_178_, 3);
v_toSeqRight_185_ = lean_ctor_get(v_toApplicative_178_, 4);
v_isSharedCheck_203_ = !lean_is_exclusive(v_toApplicative_178_);
if (v_isSharedCheck_203_ == 0)
{
lean_object* v_unused_204_; 
v_unused_204_ = lean_ctor_get(v_toApplicative_178_, 1);
lean_dec(v_unused_204_);
v___x_187_ = v_toApplicative_178_;
v_isShared_188_ = v_isSharedCheck_203_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_toSeqRight_185_);
lean_inc(v_toSeqLeft_184_);
lean_inc(v_toSeq_183_);
lean_inc(v_toFunctor_182_);
lean_dec(v_toApplicative_178_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_203_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___f_189_; lean_object* v___f_190_; lean_object* v___f_191_; lean_object* v___f_192_; lean_object* v___x_193_; lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___f_196_; lean_object* v___x_198_; 
v___f_189_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_190_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_182_);
v___f_191_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_191_, 0, v_toFunctor_182_);
v___f_192_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_192_, 0, v_toFunctor_182_);
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v___f_191_);
lean_ctor_set(v___x_193_, 1, v___f_192_);
v___f_194_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_194_, 0, v_toSeqRight_185_);
v___f_195_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_195_, 0, v_toSeqLeft_184_);
v___f_196_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_196_, 0, v_toSeq_183_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 4, v___f_194_);
lean_ctor_set(v___x_187_, 3, v___f_195_);
lean_ctor_set(v___x_187_, 2, v___f_196_);
lean_ctor_set(v___x_187_, 1, v___f_189_);
lean_ctor_set(v___x_187_, 0, v___x_193_);
v___x_198_ = v___x_187_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v___f_189_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v___f_196_);
lean_ctor_set(v_reuseFailAlloc_202_, 3, v___f_195_);
lean_ctor_set(v_reuseFailAlloc_202_, 4, v___f_194_);
v___x_198_ = v_reuseFailAlloc_202_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_200_; 
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 1, v___f_190_);
lean_ctor_set(v___x_180_, 0, v___x_198_);
v___x_200_ = v___x_180_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___f_190_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg(uint8_t v_phase_207_, lean_object* v_x_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_config_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_config_214_ = lean_ctor_get(v_a_209_, 0);
lean_inc_ref(v_config_214_);
v___x_215_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_215_, 0, v_config_214_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*1, v_phase_207_);
lean_inc(v_a_212_);
lean_inc_ref(v_a_211_);
lean_inc(v_a_210_);
v___x_216_ = lean_apply_5(v_x_208_, v___x_215_, v_a_210_, v_a_211_, v_a_212_, lean_box(0));
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg___boxed(lean_object* v_phase_217_, lean_object* v_x_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
uint8_t v_phase_boxed_224_; lean_object* v_res_225_; 
v_phase_boxed_224_ = lean_unbox(v_phase_217_);
v_res_225_ = l_Lean_Compiler_LCNF_withPhase___redArg(v_phase_boxed_224_, v_x_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase(lean_object* v_00_u03b1_226_, uint8_t v_phase_227_, lean_object* v_x_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_config_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_config_234_ = lean_ctor_get(v_a_229_, 0);
lean_inc_ref(v_config_234_);
v___x_235_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_235_, 0, v_config_234_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*1, v_phase_227_);
lean_inc(v_a_232_);
lean_inc_ref(v_a_231_);
lean_inc(v_a_230_);
v___x_236_ = lean_apply_5(v_x_228_, v___x_235_, v_a_230_, v_a_231_, v_a_232_, lean_box(0));
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___boxed(lean_object* v_00_u03b1_237_, lean_object* v_phase_238_, lean_object* v_x_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
uint8_t v_phase_boxed_245_; lean_object* v_res_246_; 
v_phase_boxed_245_ = lean_unbox(v_phase_238_);
v_res_246_ = l_Lean_Compiler_LCNF_withPhase(v_00_u03b1_237_, v_phase_boxed_245_, v_x_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object* v_a_247_){
_start:
{
uint8_t v_phase_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_phase_249_ = lean_ctor_get_uint8(v_a_247_, sizeof(void*)*1);
v___x_250_ = lean_box(v_phase_249_);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg___boxed(lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_252_);
lean_dec_ref(v_a_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase(lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_255_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___boxed(lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Compiler_LCNF_getPhase(v_a_261_, v_a_262_, v_a_263_, v_a_264_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object* v_a_267_){
_start:
{
lean_object* v___x_269_; lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_280_; 
v___x_269_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_267_);
v_a_270_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_280_ == 0)
{
v___x_272_ = v___x_269_;
v_isShared_273_ = v_isSharedCheck_280_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_280_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
uint8_t v___x_274_; uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_274_ = lean_unbox(v_a_270_);
lean_dec(v_a_270_);
v___x_275_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_274_);
v___x_276_ = lean_box(v___x_275_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_276_);
v___x_278_ = v___x_272_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg___boxed(lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_281_);
lean_dec_ref(v_a_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity(lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_284_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___boxed(lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Compiler_LCNF_getPurity(v_a_290_, v_a_291_, v_a_292_, v_a_293_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg(lean_object* v_a_296_){
_start:
{
lean_object* v___x_298_; lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_314_; 
v___x_298_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_296_);
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_314_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_314_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_314_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
uint8_t v___x_303_; 
v___x_303_ = lean_unbox(v_a_299_);
lean_dec(v_a_299_);
if (v___x_303_ == 0)
{
uint8_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_304_ = 1;
v___x_305_ = lean_box(v___x_304_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_305_);
v___x_307_ = v___x_301_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
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
uint8_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_309_ = 0;
v___x_310_ = lean_box(v___x_309_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_310_);
v___x_312_ = v___x_301_;
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg___boxed(lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_315_);
lean_dec_ref(v_a_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase(lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_318_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___boxed(lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Compiler_LCNF_inBasePhase(v_a_324_, v_a_325_, v_a_326_, v_a_327_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
return v_res_329_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0(void){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_330_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1);
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
lean_ctor_set(v___x_335_, 2, v___x_334_);
lean_ctor_set(v___x_335_, 3, v___x_334_);
lean_ctor_set(v___x_335_, 4, v___x_333_);
lean_ctor_set(v___x_335_, 5, v___x_333_);
lean_ctor_set(v___x_335_, 6, v___x_333_);
lean_ctor_set(v___x_335_, 7, v___x_333_);
lean_ctor_set(v___x_335_, 8, v___x_333_);
lean_ctor_set(v___x_335_, 9, v___x_333_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(lean_object* v_msgData_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = lean_st_ref_get(v___y_340_);
v___x_343_ = lean_st_ref_get(v___y_338_);
v___x_344_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_337_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_367_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_367_ == 0)
{
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_367_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_367_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v_env_349_; lean_object* v_lctx_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_365_; 
v_env_349_ = lean_ctor_get(v___x_342_, 0);
lean_inc_ref(v_env_349_);
lean_dec(v___x_342_);
v_lctx_350_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; 
v_unused_366_ = lean_ctor_get(v___x_343_, 1);
lean_dec(v_unused_366_);
v___x_352_ = v___x_343_;
v_isShared_353_ = v_isSharedCheck_365_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_lctx_350_);
lean_dec(v___x_343_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_365_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v_options_354_; uint8_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
v_options_354_ = lean_ctor_get(v___y_339_, 2);
v___x_355_ = lean_unbox(v_a_345_);
lean_dec(v_a_345_);
v___x_356_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_350_, v___x_355_);
lean_dec_ref(v_lctx_350_);
v___x_357_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_354_);
v___x_358_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_358_, 0, v_env_349_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
lean_ctor_set(v___x_358_, 2, v___x_356_);
lean_ctor_set(v___x_358_, 3, v_options_354_);
if (v_isShared_353_ == 0)
{
lean_ctor_set_tag(v___x_352_, 3);
lean_ctor_set(v___x_352_, 1, v_msgData_336_);
lean_ctor_set(v___x_352_, 0, v___x_358_);
v___x_360_ = v___x_352_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_msgData_336_);
v___x_360_ = v_reuseFailAlloc_364_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_362_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_360_);
v___x_362_ = v___x_347_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec(v___x_343_);
lean_dec(v___x_342_);
lean_dec_ref(v_msgData_336_);
v_a_368_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_344_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_344_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed(lean_object* v_msgData_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(v_msgData_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(lean_object* v_msg_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_options_391_; lean_object* v_ref_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_options_391_ = lean_ctor_get(v___y_388_, 2);
v_ref_392_ = lean_ctor_get(v___y_388_, 5);
v___x_393_ = lean_st_ref_get(v___y_389_);
v___x_394_ = lean_st_ref_get(v___y_387_);
v___x_395_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_386_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_418_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_418_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_418_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_418_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v_env_400_; lean_object* v_lctx_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_416_; 
v_env_400_ = lean_ctor_get(v___x_393_, 0);
lean_inc_ref(v_env_400_);
lean_dec(v___x_393_);
v_lctx_401_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_416_ == 0)
{
lean_object* v_unused_417_; 
v_unused_417_ = lean_ctor_get(v___x_394_, 1);
lean_dec(v_unused_417_);
v___x_403_ = v___x_394_;
v_isShared_404_ = v_isSharedCheck_416_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_lctx_401_);
lean_dec(v___x_394_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_416_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
uint8_t v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_405_ = lean_unbox(v_a_396_);
lean_dec(v_a_396_);
v___x_406_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_401_, v___x_405_);
lean_dec_ref(v_lctx_401_);
v___x_407_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_391_);
v___x_408_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_408_, 0, v_env_400_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
lean_ctor_set(v___x_408_, 2, v___x_406_);
lean_ctor_set(v___x_408_, 3, v_options_391_);
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 3);
lean_ctor_set(v___x_403_, 1, v_msg_385_);
lean_ctor_set(v___x_403_, 0, v___x_408_);
v___x_410_ = v___x_403_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_msg_385_);
v___x_410_ = v_reuseFailAlloc_415_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
lean_inc(v_ref_392_);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v_ref_392_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
if (v_isShared_399_ == 0)
{
lean_ctor_set_tag(v___x_398_, 1);
lean_ctor_set(v___x_398_, 0, v___x_411_);
v___x_413_ = v___x_398_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec(v___x_394_);
lean_dec(v___x_393_);
lean_dec_ref(v_msg_385_);
v_a_419_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_395_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_395_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg___boxed(lean_object* v_msg_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(lean_object* v_00_u03b1_434_, lean_object* v_msg_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___boxed(lean_object* v_00_u03b1_442_, lean_object* v_msg_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(v_00_u03b1_442_, v_msg_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(lean_object* v_a_450_, lean_object* v_x_451_){
_start:
{
if (lean_obj_tag(v_x_451_) == 0)
{
lean_object* v___x_452_; 
v___x_452_ = lean_box(0);
return v___x_452_;
}
else
{
lean_object* v_key_453_; lean_object* v_value_454_; lean_object* v_tail_455_; uint8_t v___x_456_; 
v_key_453_ = lean_ctor_get(v_x_451_, 0);
v_value_454_ = lean_ctor_get(v_x_451_, 1);
v_tail_455_ = lean_ctor_get(v_x_451_, 2);
v___x_456_ = l_Lean_instBEqFVarId_beq(v_key_453_, v_a_450_);
if (v___x_456_ == 0)
{
v_x_451_ = v_tail_455_;
goto _start;
}
else
{
lean_object* v___x_458_; 
lean_inc(v_value_454_);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v_value_454_);
return v___x_458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg___boxed(lean_object* v_a_459_, lean_object* v_x_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_459_, v_x_460_);
lean_dec(v_x_460_);
lean_dec(v_a_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object* v_m_462_, lean_object* v_a_463_){
_start:
{
lean_object* v_buckets_464_; lean_object* v___x_465_; uint64_t v___x_466_; uint64_t v___x_467_; uint64_t v___x_468_; uint64_t v_fold_469_; uint64_t v___x_470_; uint64_t v___x_471_; uint64_t v___x_472_; size_t v___x_473_; size_t v___x_474_; size_t v___x_475_; size_t v___x_476_; size_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_buckets_464_ = lean_ctor_get(v_m_462_, 1);
v___x_465_ = lean_array_get_size(v_buckets_464_);
v___x_466_ = l_Lean_instHashableFVarId_hash(v_a_463_);
v___x_467_ = 32ULL;
v___x_468_ = lean_uint64_shift_right(v___x_466_, v___x_467_);
v_fold_469_ = lean_uint64_xor(v___x_466_, v___x_468_);
v___x_470_ = 16ULL;
v___x_471_ = lean_uint64_shift_right(v_fold_469_, v___x_470_);
v___x_472_ = lean_uint64_xor(v_fold_469_, v___x_471_);
v___x_473_ = lean_uint64_to_usize(v___x_472_);
v___x_474_ = lean_usize_of_nat(v___x_465_);
v___x_475_ = ((size_t)1ULL);
v___x_476_ = lean_usize_sub(v___x_474_, v___x_475_);
v___x_477_ = lean_usize_land(v___x_473_, v___x_476_);
v___x_478_ = lean_array_uget_borrowed(v_buckets_464_, v___x_477_);
v___x_479_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_463_, v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg___boxed(lean_object* v_m_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_480_, v_a_481_);
lean_dec(v_a_481_);
lean_dec_ref(v_m_480_);
return v_res_482_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getType___closed__1(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l_Lean_Compiler_LCNF_getType___closed__0));
v___x_485_ = l_Lean_stringToMessageData(v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType(lean_object* v_fvarId_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_st_ref_get(v_a_488_);
v___x_493_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_487_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_544_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_544_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_544_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_544_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___y_499_; lean_object* v_lctx_510_; lean_object* v___y_512_; lean_object* v___y_527_; uint8_t v___x_541_; 
v_lctx_510_ = lean_ctor_get(v___x_492_, 0);
lean_inc_ref(v_lctx_510_);
lean_dec(v___x_492_);
v___x_541_ = lean_unbox(v_a_494_);
if (v___x_541_ == 0)
{
lean_object* v_letDeclsPure_542_; 
v_letDeclsPure_542_ = lean_ctor_get(v_lctx_510_, 2);
lean_inc_ref(v_letDeclsPure_542_);
v___y_527_ = v_letDeclsPure_542_;
goto v___jp_526_;
}
else
{
lean_object* v_letDeclsImpure_543_; 
v_letDeclsImpure_543_ = lean_ctor_get(v_lctx_510_, 3);
lean_inc_ref(v_letDeclsImpure_543_);
v___y_527_ = v_letDeclsImpure_543_;
goto v___jp_526_;
}
v___jp_498_:
{
lean_object* v___x_500_; 
v___x_500_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_499_, v_fvarId_486_);
lean_dec_ref(v___y_499_);
if (lean_obj_tag(v___x_500_) == 1)
{
lean_object* v_val_501_; lean_object* v_type_502_; lean_object* v___x_504_; 
lean_dec(v_fvarId_486_);
v_val_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_val_501_);
lean_dec_ref(v___x_500_);
v_type_502_ = lean_ctor_get(v_val_501_, 3);
lean_inc_ref(v_type_502_);
lean_dec(v_val_501_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v_type_502_);
v___x_504_ = v___x_496_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_type_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec(v___x_500_);
lean_del_object(v___x_496_);
v___x_506_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_507_ = l_Lean_MessageData_ofName(v_fvarId_486_);
v___x_508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_506_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_508_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
return v___x_509_;
}
}
v___jp_511_:
{
lean_object* v___x_513_; 
v___x_513_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_512_, v_fvarId_486_);
lean_dec_ref(v___y_512_);
if (lean_obj_tag(v___x_513_) == 1)
{
lean_object* v_val_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_522_; 
lean_dec_ref(v_lctx_510_);
lean_del_object(v___x_496_);
lean_dec(v_a_494_);
lean_dec(v_fvarId_486_);
v_val_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_522_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_val_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v_type_518_; lean_object* v___x_520_; 
v_type_518_ = lean_ctor_get(v_val_514_, 2);
lean_inc_ref(v_type_518_);
lean_dec(v_val_514_);
if (v_isShared_517_ == 0)
{
lean_ctor_set_tag(v___x_516_, 0);
lean_ctor_set(v___x_516_, 0, v_type_518_);
v___x_520_ = v___x_516_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_type_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
else
{
uint8_t v___x_523_; 
lean_dec(v___x_513_);
v___x_523_ = lean_unbox(v_a_494_);
lean_dec(v_a_494_);
if (v___x_523_ == 0)
{
lean_object* v_funDeclsPure_524_; 
v_funDeclsPure_524_ = lean_ctor_get(v_lctx_510_, 4);
lean_inc_ref(v_funDeclsPure_524_);
lean_dec_ref(v_lctx_510_);
v___y_499_ = v_funDeclsPure_524_;
goto v___jp_498_;
}
else
{
lean_object* v_funDeclsImpure_525_; 
v_funDeclsImpure_525_ = lean_ctor_get(v_lctx_510_, 5);
lean_inc_ref(v_funDeclsImpure_525_);
lean_dec_ref(v_lctx_510_);
v___y_499_ = v_funDeclsImpure_525_;
goto v___jp_498_;
}
}
}
v___jp_526_:
{
lean_object* v___x_528_; 
v___x_528_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_527_, v_fvarId_486_);
lean_dec_ref(v___y_527_);
if (lean_obj_tag(v___x_528_) == 1)
{
lean_object* v_val_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_537_; 
lean_dec_ref(v_lctx_510_);
lean_del_object(v___x_496_);
lean_dec(v_a_494_);
lean_dec(v_fvarId_486_);
v_val_529_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_537_ == 0)
{
v___x_531_ = v___x_528_;
v_isShared_532_ = v_isSharedCheck_537_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_val_529_);
lean_dec(v___x_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_537_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v_type_533_; lean_object* v___x_535_; 
v_type_533_ = lean_ctor_get(v_val_529_, 2);
lean_inc_ref(v_type_533_);
lean_dec(v_val_529_);
if (v_isShared_532_ == 0)
{
lean_ctor_set_tag(v___x_531_, 0);
lean_ctor_set(v___x_531_, 0, v_type_533_);
v___x_535_ = v___x_531_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_type_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
else
{
uint8_t v___x_538_; 
lean_dec(v___x_528_);
v___x_538_ = lean_unbox(v_a_494_);
if (v___x_538_ == 0)
{
lean_object* v_paramsPure_539_; 
v_paramsPure_539_ = lean_ctor_get(v_lctx_510_, 0);
lean_inc_ref(v_paramsPure_539_);
v___y_512_ = v_paramsPure_539_;
goto v___jp_511_;
}
else
{
lean_object* v_paramsImpure_540_; 
v_paramsImpure_540_ = lean_ctor_get(v_lctx_510_, 1);
lean_inc_ref(v_paramsImpure_540_);
v___y_512_ = v_paramsImpure_540_;
goto v___jp_511_;
}
}
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec(v___x_492_);
lean_dec(v_fvarId_486_);
v_a_545_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_493_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_493_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType___boxed(lean_object* v_fvarId_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Compiler_LCNF_getType(v_fvarId_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(lean_object* v_00_u03b2_560_, lean_object* v_m_561_, lean_object* v_a_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_561_, v_a_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___boxed(lean_object* v_00_u03b2_564_, lean_object* v_m_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(v_00_u03b2_564_, v_m_565_, v_a_566_);
lean_dec(v_a_566_);
lean_dec_ref(v_m_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(lean_object* v_00_u03b2_568_, lean_object* v_a_569_, lean_object* v_x_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_569_, v_x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_572_, lean_object* v_a_573_, lean_object* v_x_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(v_00_u03b2_572_, v_a_573_, v_x_574_);
lean_dec(v_x_574_);
lean_dec(v_a_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object* v_fvarId_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_st_ref_get(v_a_578_);
v___x_583_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_577_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_634_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_634_ == 0)
{
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_634_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_634_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___y_589_; lean_object* v_lctx_600_; lean_object* v___y_602_; lean_object* v___y_617_; uint8_t v___x_631_; 
v_lctx_600_ = lean_ctor_get(v___x_582_, 0);
lean_inc_ref(v_lctx_600_);
lean_dec(v___x_582_);
v___x_631_ = lean_unbox(v_a_584_);
if (v___x_631_ == 0)
{
lean_object* v_letDeclsPure_632_; 
v_letDeclsPure_632_ = lean_ctor_get(v_lctx_600_, 2);
lean_inc_ref(v_letDeclsPure_632_);
v___y_617_ = v_letDeclsPure_632_;
goto v___jp_616_;
}
else
{
lean_object* v_letDeclsImpure_633_; 
v_letDeclsImpure_633_ = lean_ctor_get(v_lctx_600_, 3);
lean_inc_ref(v_letDeclsImpure_633_);
v___y_617_ = v_letDeclsImpure_633_;
goto v___jp_616_;
}
v___jp_588_:
{
lean_object* v___x_590_; 
v___x_590_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_589_, v_fvarId_576_);
lean_dec_ref(v___y_589_);
if (lean_obj_tag(v___x_590_) == 1)
{
lean_object* v_val_591_; lean_object* v_binderName_592_; lean_object* v___x_594_; 
lean_dec(v_fvarId_576_);
v_val_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_val_591_);
lean_dec_ref(v___x_590_);
v_binderName_592_ = lean_ctor_get(v_val_591_, 1);
lean_inc(v_binderName_592_);
lean_dec(v_val_591_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v_binderName_592_);
v___x_594_ = v___x_586_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_binderName_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v___x_590_);
lean_del_object(v___x_586_);
v___x_596_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_597_ = l_Lean_MessageData_ofName(v_fvarId_576_);
v___x_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_598_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
return v___x_599_;
}
}
v___jp_601_:
{
lean_object* v___x_603_; 
v___x_603_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_602_, v_fvarId_576_);
lean_dec_ref(v___y_602_);
if (lean_obj_tag(v___x_603_) == 1)
{
lean_object* v_val_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_612_; 
lean_dec_ref(v_lctx_600_);
lean_del_object(v___x_586_);
lean_dec(v_a_584_);
lean_dec(v_fvarId_576_);
v_val_604_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_612_ == 0)
{
v___x_606_ = v___x_603_;
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_val_604_);
lean_dec(v___x_603_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v_binderName_608_; lean_object* v___x_610_; 
v_binderName_608_ = lean_ctor_get(v_val_604_, 1);
lean_inc(v_binderName_608_);
lean_dec(v_val_604_);
if (v_isShared_607_ == 0)
{
lean_ctor_set_tag(v___x_606_, 0);
lean_ctor_set(v___x_606_, 0, v_binderName_608_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_binderName_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
else
{
uint8_t v___x_613_; 
lean_dec(v___x_603_);
v___x_613_ = lean_unbox(v_a_584_);
lean_dec(v_a_584_);
if (v___x_613_ == 0)
{
lean_object* v_funDeclsPure_614_; 
v_funDeclsPure_614_ = lean_ctor_get(v_lctx_600_, 4);
lean_inc_ref(v_funDeclsPure_614_);
lean_dec_ref(v_lctx_600_);
v___y_589_ = v_funDeclsPure_614_;
goto v___jp_588_;
}
else
{
lean_object* v_funDeclsImpure_615_; 
v_funDeclsImpure_615_ = lean_ctor_get(v_lctx_600_, 5);
lean_inc_ref(v_funDeclsImpure_615_);
lean_dec_ref(v_lctx_600_);
v___y_589_ = v_funDeclsImpure_615_;
goto v___jp_588_;
}
}
}
v___jp_616_:
{
lean_object* v___x_618_; 
v___x_618_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_617_, v_fvarId_576_);
lean_dec_ref(v___y_617_);
if (lean_obj_tag(v___x_618_) == 1)
{
lean_object* v_val_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_627_; 
lean_dec_ref(v_lctx_600_);
lean_del_object(v___x_586_);
lean_dec(v_a_584_);
lean_dec(v_fvarId_576_);
v_val_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_627_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_627_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_val_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_627_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v_binderName_623_; lean_object* v___x_625_; 
v_binderName_623_ = lean_ctor_get(v_val_619_, 1);
lean_inc(v_binderName_623_);
lean_dec(v_val_619_);
if (v_isShared_622_ == 0)
{
lean_ctor_set_tag(v___x_621_, 0);
lean_ctor_set(v___x_621_, 0, v_binderName_623_);
v___x_625_ = v___x_621_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_binderName_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
else
{
uint8_t v___x_628_; 
lean_dec(v___x_618_);
v___x_628_ = lean_unbox(v_a_584_);
if (v___x_628_ == 0)
{
lean_object* v_paramsPure_629_; 
v_paramsPure_629_ = lean_ctor_get(v_lctx_600_, 0);
lean_inc_ref(v_paramsPure_629_);
v___y_602_ = v_paramsPure_629_;
goto v___jp_601_;
}
else
{
lean_object* v_paramsImpure_630_; 
v_paramsImpure_630_ = lean_ctor_get(v_lctx_600_, 1);
lean_inc_ref(v_paramsImpure_630_);
v___y_602_ = v_paramsImpure_630_;
goto v___jp_601_;
}
}
}
}
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_dec(v___x_582_);
lean_dec(v_fvarId_576_);
v_a_635_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_583_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_583_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName___boxed(lean_object* v_fvarId_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t v_pu_650_, lean_object* v_fvarId_651_, lean_object* v_a_652_){
_start:
{
lean_object* v___x_654_; lean_object* v___y_656_; 
v___x_654_ = lean_st_ref_get(v_a_652_);
if (v_pu_650_ == 0)
{
lean_object* v_lctx_659_; lean_object* v_paramsPure_660_; 
v_lctx_659_ = lean_ctor_get(v___x_654_, 0);
lean_inc_ref(v_lctx_659_);
lean_dec(v___x_654_);
v_paramsPure_660_ = lean_ctor_get(v_lctx_659_, 0);
lean_inc_ref(v_paramsPure_660_);
lean_dec_ref(v_lctx_659_);
v___y_656_ = v_paramsPure_660_;
goto v___jp_655_;
}
else
{
lean_object* v_lctx_661_; lean_object* v_paramsImpure_662_; 
v_lctx_661_ = lean_ctor_get(v___x_654_, 0);
lean_inc_ref(v_lctx_661_);
lean_dec(v___x_654_);
v_paramsImpure_662_ = lean_ctor_get(v_lctx_661_, 1);
lean_inc_ref(v_paramsImpure_662_);
lean_dec_ref(v_lctx_661_);
v___y_656_ = v_paramsImpure_662_;
goto v___jp_655_;
}
v___jp_655_:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_656_, v_fvarId_651_);
lean_dec_ref(v___y_656_);
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg___boxed(lean_object* v_pu_663_, lean_object* v_fvarId_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
uint8_t v_pu_boxed_667_; lean_object* v_res_668_; 
v_pu_boxed_667_ = lean_unbox(v_pu_663_);
v_res_668_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_boxed_667_, v_fvarId_664_, v_a_665_);
lean_dec(v_a_665_);
lean_dec(v_fvarId_664_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f(uint8_t v_pu_669_, lean_object* v_fvarId_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_669_, v_fvarId_670_, v_a_672_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___boxed(lean_object* v_pu_677_, lean_object* v_fvarId_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
uint8_t v_pu_boxed_684_; lean_object* v_res_685_; 
v_pu_boxed_684_ = lean_unbox(v_pu_677_);
v_res_685_ = l_Lean_Compiler_LCNF_findParam_x3f(v_pu_boxed_684_, v_fvarId_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_fvarId_678_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t v_pu_686_, lean_object* v_fvarId_687_, lean_object* v_a_688_){
_start:
{
lean_object* v___x_690_; lean_object* v___y_692_; 
v___x_690_ = lean_st_ref_get(v_a_688_);
if (v_pu_686_ == 0)
{
lean_object* v_lctx_695_; lean_object* v_letDeclsPure_696_; 
v_lctx_695_ = lean_ctor_get(v___x_690_, 0);
lean_inc_ref(v_lctx_695_);
lean_dec(v___x_690_);
v_letDeclsPure_696_ = lean_ctor_get(v_lctx_695_, 2);
lean_inc_ref(v_letDeclsPure_696_);
lean_dec_ref(v_lctx_695_);
v___y_692_ = v_letDeclsPure_696_;
goto v___jp_691_;
}
else
{
lean_object* v_lctx_697_; lean_object* v_letDeclsImpure_698_; 
v_lctx_697_ = lean_ctor_get(v___x_690_, 0);
lean_inc_ref(v_lctx_697_);
lean_dec(v___x_690_);
v_letDeclsImpure_698_ = lean_ctor_get(v_lctx_697_, 3);
lean_inc_ref(v_letDeclsImpure_698_);
lean_dec_ref(v_lctx_697_);
v___y_692_ = v_letDeclsImpure_698_;
goto v___jp_691_;
}
v___jp_691_:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_692_, v_fvarId_687_);
lean_dec_ref(v___y_692_);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg___boxed(lean_object* v_pu_699_, lean_object* v_fvarId_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
uint8_t v_pu_boxed_703_; lean_object* v_res_704_; 
v_pu_boxed_703_ = lean_unbox(v_pu_699_);
v_res_704_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_boxed_703_, v_fvarId_700_, v_a_701_);
lean_dec(v_a_701_);
lean_dec(v_fvarId_700_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(uint8_t v_pu_705_, lean_object* v_fvarId_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_705_, v_fvarId_706_, v_a_708_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___boxed(lean_object* v_pu_713_, lean_object* v_fvarId_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
uint8_t v_pu_boxed_720_; lean_object* v_res_721_; 
v_pu_boxed_720_ = lean_unbox(v_pu_713_);
v_res_721_ = l_Lean_Compiler_LCNF_findLetDecl_x3f(v_pu_boxed_720_, v_fvarId_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_fvarId_714_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t v_pu_722_, lean_object* v_fvarId_723_, lean_object* v_a_724_){
_start:
{
lean_object* v___x_726_; lean_object* v___y_728_; 
v___x_726_ = lean_st_ref_get(v_a_724_);
if (v_pu_722_ == 0)
{
lean_object* v_lctx_731_; lean_object* v_funDeclsPure_732_; 
v_lctx_731_ = lean_ctor_get(v___x_726_, 0);
lean_inc_ref(v_lctx_731_);
lean_dec(v___x_726_);
v_funDeclsPure_732_ = lean_ctor_get(v_lctx_731_, 4);
lean_inc_ref(v_funDeclsPure_732_);
lean_dec_ref(v_lctx_731_);
v___y_728_ = v_funDeclsPure_732_;
goto v___jp_727_;
}
else
{
lean_object* v_lctx_733_; lean_object* v_funDeclsImpure_734_; 
v_lctx_733_ = lean_ctor_get(v___x_726_, 0);
lean_inc_ref(v_lctx_733_);
lean_dec(v___x_726_);
v_funDeclsImpure_734_ = lean_ctor_get(v_lctx_733_, 5);
lean_inc_ref(v_funDeclsImpure_734_);
lean_dec_ref(v_lctx_733_);
v___y_728_ = v_funDeclsImpure_734_;
goto v___jp_727_;
}
v___jp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_728_, v_fvarId_723_);
lean_dec_ref(v___y_728_);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg___boxed(lean_object* v_pu_735_, lean_object* v_fvarId_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
uint8_t v_pu_boxed_739_; lean_object* v_res_740_; 
v_pu_boxed_739_ = lean_unbox(v_pu_735_);
v_res_740_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_boxed_739_, v_fvarId_736_, v_a_737_);
lean_dec(v_a_737_);
lean_dec(v_fvarId_736_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(uint8_t v_pu_741_, lean_object* v_fvarId_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_741_, v_fvarId_742_, v_a_744_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___boxed(lean_object* v_pu_749_, lean_object* v_fvarId_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
uint8_t v_pu_boxed_756_; lean_object* v_res_757_; 
v_pu_boxed_756_ = lean_unbox(v_pu_749_);
v_res_757_ = l_Lean_Compiler_LCNF_findFunDecl_x3f(v_pu_boxed_756_, v_fvarId_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec(v_fvarId_750_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t v_pu_758_, lean_object* v_fvarId_759_, lean_object* v_a_760_){
_start:
{
lean_object* v___x_762_; lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_783_; 
v___x_762_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_758_, v_fvarId_759_, v_a_760_);
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_783_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_783_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_783_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
if (lean_obj_tag(v_a_763_) == 1)
{
lean_object* v_val_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_778_; 
v_val_767_ = lean_ctor_get(v_a_763_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v_a_763_);
if (v_isSharedCheck_778_ == 0)
{
v___x_769_ = v_a_763_;
v_isShared_770_ = v_isSharedCheck_778_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_val_767_);
lean_dec(v_a_763_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_778_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v_value_771_; lean_object* v___x_773_; 
v_value_771_ = lean_ctor_get(v_val_767_, 3);
lean_inc(v_value_771_);
lean_dec(v_val_767_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v_value_771_);
v___x_773_ = v___x_769_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_value_771_);
v___x_773_ = v_reuseFailAlloc_777_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_775_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_773_);
v___x_775_ = v___x_765_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
else
{
lean_object* v___x_779_; lean_object* v___x_781_; 
lean_dec(v_a_763_);
v___x_779_ = lean_box(0);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_779_);
v___x_781_ = v___x_765_;
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg___boxed(lean_object* v_pu_784_, lean_object* v_fvarId_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
uint8_t v_pu_boxed_788_; lean_object* v_res_789_; 
v_pu_boxed_788_ = lean_unbox(v_pu_784_);
v_res_789_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_boxed_788_, v_fvarId_785_, v_a_786_);
lean_dec(v_a_786_);
lean_dec(v_fvarId_785_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f(uint8_t v_pu_790_, lean_object* v_fvarId_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_790_, v_fvarId_791_, v_a_793_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___boxed(lean_object* v_pu_798_, lean_object* v_fvarId_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
uint8_t v_pu_boxed_805_; lean_object* v_res_806_; 
v_pu_boxed_805_ = lean_unbox(v_pu_798_);
v_res_806_ = l_Lean_Compiler_LCNF_findLetValue_x3f(v_pu_boxed_805_, v_fvarId_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_fvarId_799_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg(lean_object* v_fvarId_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
uint8_t v___x_811_; lean_object* v___x_812_; 
v___x_811_ = 0;
v___x_812_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_811_, v_fvarId_807_, v_a_808_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_856_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_856_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_856_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_856_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
if (lean_obj_tag(v_a_813_) == 1)
{
lean_object* v_val_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_855_; 
v_val_823_ = lean_ctor_get(v_a_813_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v_a_813_);
if (v_isSharedCheck_855_ == 0)
{
v___x_825_ = v_a_813_;
v_isShared_826_ = v_isSharedCheck_855_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_val_823_);
lean_dec(v_a_813_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_855_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
if (lean_obj_tag(v_val_823_) == 3)
{
lean_object* v_declName_827_; lean_object* v___x_828_; lean_object* v_env_829_; uint8_t v___x_830_; lean_object* v___x_831_; 
lean_del_object(v___x_815_);
v_declName_827_ = lean_ctor_get(v_val_823_, 0);
lean_inc(v_declName_827_);
lean_dec_ref(v_val_823_);
v___x_828_ = lean_st_ref_get(v_a_809_);
v_env_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc_ref(v_env_829_);
lean_dec(v___x_828_);
v___x_830_ = 0;
v___x_831_ = l_Lean_Environment_find_x3f(v_env_829_, v_declName_827_, v___x_830_);
if (lean_obj_tag(v___x_831_) == 1)
{
lean_object* v_val_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_850_; 
lean_del_object(v___x_825_);
v_val_832_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_850_ == 0)
{
v___x_834_ = v___x_831_;
v_isShared_835_ = v_isSharedCheck_850_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_val_832_);
lean_dec(v___x_831_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_850_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
if (lean_obj_tag(v_val_832_) == 6)
{
lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_844_; 
lean_del_object(v___x_834_);
v_isSharedCheck_844_ = !lean_is_exclusive(v_val_832_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; 
v_unused_845_ = lean_ctor_get(v_val_832_, 0);
lean_dec(v_unused_845_);
v___x_837_ = v_val_832_;
v_isShared_838_ = v_isSharedCheck_844_;
goto v_resetjp_836_;
}
else
{
lean_dec(v_val_832_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_844_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
uint8_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_839_ = 1;
v___x_840_ = lean_box(v___x_839_);
if (v_isShared_838_ == 0)
{
lean_ctor_set_tag(v___x_837_, 0);
lean_ctor_set(v___x_837_, 0, v___x_840_);
v___x_842_ = v___x_837_;
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
}
else
{
lean_object* v___x_846_; lean_object* v___x_848_; 
lean_dec(v_val_832_);
v___x_846_ = lean_box(v___x_830_);
if (v_isShared_835_ == 0)
{
lean_ctor_set_tag(v___x_834_, 0);
lean_ctor_set(v___x_834_, 0, v___x_846_);
v___x_848_ = v___x_834_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
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
else
{
lean_object* v___x_851_; lean_object* v___x_853_; 
lean_dec(v___x_831_);
v___x_851_ = lean_box(v___x_830_);
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 0);
lean_ctor_set(v___x_825_, 0, v___x_851_);
v___x_853_ = v___x_825_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
else
{
lean_del_object(v___x_825_);
lean_dec(v_val_823_);
goto v___jp_817_;
}
}
}
else
{
lean_dec(v_a_813_);
goto v___jp_817_;
}
v___jp_817_:
{
uint8_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_818_ = 0;
v___x_819_ = lean_box(v___x_818_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_819_);
v___x_821_ = v___x_815_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
v_a_857_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_812_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_812_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg___boxed(lean_object* v_fvarId_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_865_, v_a_866_, v_a_867_);
lean_dec(v_a_867_);
lean_dec(v_a_866_);
lean_dec(v_fvarId_865_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp(lean_object* v_fvarId_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_870_, v_a_872_, v_a_874_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___boxed(lean_object* v_fvarId_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_Compiler_LCNF_isConstructorApp(v_fvarId_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_fvarId_877_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(lean_object* v_arg_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
if (lean_obj_tag(v_arg_884_) == 1)
{
lean_object* v_fvarId_888_; lean_object* v___x_889_; 
v_fvarId_888_ = lean_ctor_get(v_arg_884_, 0);
v___x_889_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_888_, v_a_885_, v_a_886_);
return v___x_889_;
}
else
{
uint8_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_890_ = 0;
v___x_891_ = lean_box(v___x_890_);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg___boxed(lean_object* v_arg_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_893_, v_a_894_, v_a_895_);
lean_dec(v_a_895_);
lean_dec(v_a_894_);
lean_dec(v_arg_893_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp(uint8_t v_pu_898_, lean_object* v_arg_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_899_, v_a_901_, v_a_903_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___boxed(lean_object* v_pu_906_, lean_object* v_arg_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
uint8_t v_pu_boxed_913_; lean_object* v_res_914_; 
v_pu_boxed_913_ = lean_unbox(v_pu_906_);
v_res_914_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp(v_pu_boxed_913_, v_arg_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_arg_907_);
return v_res_914_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getParam___closed__1(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParam___closed__0));
v___x_917_ = l_Lean_stringToMessageData(v___x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam(uint8_t v_pu_918_, lean_object* v_fvarId_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_925_; lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_938_; 
v___x_925_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_918_, v_fvarId_919_, v_a_921_);
v_a_926_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_938_ == 0)
{
v___x_928_ = v___x_925_;
v_isShared_929_ = v_isSharedCheck_938_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_925_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_938_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
if (lean_obj_tag(v_a_926_) == 1)
{
lean_object* v_val_930_; lean_object* v___x_932_; 
lean_dec(v_fvarId_919_);
v_val_930_ = lean_ctor_get(v_a_926_, 0);
lean_inc(v_val_930_);
lean_dec_ref(v_a_926_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v_val_930_);
v___x_932_ = v___x_928_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_val_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
lean_del_object(v___x_928_);
lean_dec(v_a_926_);
v___x_934_ = lean_obj_once(&l_Lean_Compiler_LCNF_getParam___closed__1, &l_Lean_Compiler_LCNF_getParam___closed__1_once, _init_l_Lean_Compiler_LCNF_getParam___closed__1);
v___x_935_ = l_Lean_MessageData_ofName(v_fvarId_919_);
v___x_936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_936_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
return v___x_937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam___boxed(lean_object* v_pu_939_, lean_object* v_fvarId_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
uint8_t v_pu_boxed_946_; lean_object* v_res_947_; 
v_pu_boxed_946_ = lean_unbox(v_pu_939_);
v_res_947_ = l_Lean_Compiler_LCNF_getParam(v_pu_boxed_946_, v_fvarId_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
return v_res_947_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = ((lean_object*)(l_Lean_Compiler_LCNF_getLetDecl___closed__0));
v___x_950_ = l_Lean_stringToMessageData(v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl(uint8_t v_pu_951_, lean_object* v_fvarId_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v___x_958_; lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_971_; 
v___x_958_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_951_, v_fvarId_952_, v_a_954_);
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_971_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_971_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_971_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
if (lean_obj_tag(v_a_959_) == 1)
{
lean_object* v_val_963_; lean_object* v___x_965_; 
lean_dec(v_fvarId_952_);
v_val_963_ = lean_ctor_get(v_a_959_, 0);
lean_inc(v_val_963_);
lean_dec_ref(v_a_959_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v_val_963_);
v___x_965_ = v___x_961_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_val_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
lean_del_object(v___x_961_);
lean_dec(v_a_959_);
v___x_967_ = lean_obj_once(&l_Lean_Compiler_LCNF_getLetDecl___closed__1, &l_Lean_Compiler_LCNF_getLetDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1);
v___x_968_ = l_Lean_MessageData_ofName(v_fvarId_952_);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_969_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
return v___x_970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl___boxed(lean_object* v_pu_972_, lean_object* v_fvarId_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
uint8_t v_pu_boxed_979_; lean_object* v_res_980_; 
v_pu_boxed_979_ = lean_unbox(v_pu_972_);
v_res_980_ = l_Lean_Compiler_LCNF_getLetDecl(v_pu_boxed_979_, v_fvarId_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
return v_res_980_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = ((lean_object*)(l_Lean_Compiler_LCNF_getFunDecl___closed__0));
v___x_983_ = l_Lean_stringToMessageData(v___x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t v_pu_984_, lean_object* v_fvarId_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
lean_object* v___x_991_; lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1004_; 
v___x_991_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_984_, v_fvarId_985_, v_a_987_);
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1004_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1004_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
if (lean_obj_tag(v_a_992_) == 1)
{
lean_object* v_val_996_; lean_object* v___x_998_; 
lean_dec(v_fvarId_985_);
v_val_996_ = lean_ctor_get(v_a_992_, 0);
lean_inc(v_val_996_);
lean_dec_ref(v_a_992_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v_val_996_);
v___x_998_ = v___x_994_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_val_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_del_object(v___x_994_);
lean_dec(v_a_992_);
v___x_1000_ = lean_obj_once(&l_Lean_Compiler_LCNF_getFunDecl___closed__1, &l_Lean_Compiler_LCNF_getFunDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1);
v___x_1001_ = l_Lean_MessageData_ofName(v_fvarId_985_);
v___x_1002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_1002_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
return v___x_1003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl___boxed(lean_object* v_pu_1005_, lean_object* v_fvarId_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
uint8_t v_pu_boxed_1012_; lean_object* v_res_1013_; 
v_pu_boxed_1012_ = lean_unbox(v_pu_1005_);
v_res_1013_ = l_Lean_Compiler_LCNF_getFunDecl(v_pu_boxed_1012_, v_fvarId_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg(lean_object* v_f_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v___x_1017_; lean_object* v_lctx_1018_; lean_object* v_nextIdx_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1030_; 
v___x_1017_ = lean_st_ref_take(v_a_1015_);
v_lctx_1018_ = lean_ctor_get(v___x_1017_, 0);
v_nextIdx_1019_ = lean_ctor_get(v___x_1017_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1021_ = v___x_1017_;
v_isShared_1022_ = v_isSharedCheck_1030_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_nextIdx_1019_);
lean_inc(v_lctx_1018_);
lean_dec(v___x_1017_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1030_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1023_; lean_object* v___x_1025_; 
v___x_1023_ = lean_apply_1(v_f_1014_, v_lctx_1018_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v___x_1023_);
v___x_1025_ = v___x_1021_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_nextIdx_1019_);
v___x_1025_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = lean_st_ref_set(v_a_1015_, v___x_1025_);
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
return v___x_1028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg___boxed(lean_object* v_f_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_Compiler_LCNF_modifyLCtx___redArg(v_f_1031_, v_a_1032_);
lean_dec(v_a_1032_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx(lean_object* v_f_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___x_1041_; lean_object* v_lctx_1042_; lean_object* v_nextIdx_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1054_; 
v___x_1041_ = lean_st_ref_take(v_a_1037_);
v_lctx_1042_ = lean_ctor_get(v___x_1041_, 0);
v_nextIdx_1043_ = lean_ctor_get(v___x_1041_, 1);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1045_ = v___x_1041_;
v_isShared_1046_ = v_isSharedCheck_1054_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_nextIdx_1043_);
lean_inc(v_lctx_1042_);
lean_dec(v___x_1041_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1054_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1047_ = lean_apply_1(v_f_1035_, v_lctx_1042_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1047_);
v___x_1049_ = v___x_1045_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_nextIdx_1043_);
v___x_1049_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1050_ = lean_st_ref_set(v_a_1037_, v___x_1049_);
v___x_1051_ = lean_box(0);
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___boxed(lean_object* v_f_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_Compiler_LCNF_modifyLCtx(v_f_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t v_pu_1062_, lean_object* v_decl_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v___x_1066_; lean_object* v_lctx_1067_; lean_object* v_nextIdx_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1079_; 
v___x_1066_ = lean_st_ref_take(v_a_1064_);
v_lctx_1067_ = lean_ctor_get(v___x_1066_, 0);
v_nextIdx_1068_ = lean_ctor_get(v___x_1066_, 1);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1070_ = v___x_1066_;
v_isShared_1071_ = v_isSharedCheck_1079_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_nextIdx_1068_);
lean_inc(v_lctx_1067_);
lean_dec(v___x_1066_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1079_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1072_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_1062_, v_lctx_1067_, v_decl_1063_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1072_);
v___x_1074_ = v___x_1070_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_nextIdx_1068_);
v___x_1074_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1075_ = lean_st_ref_set(v_a_1064_, v___x_1074_);
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
return v___x_1077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg___boxed(lean_object* v_pu_1080_, lean_object* v_decl_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
uint8_t v_pu_boxed_1084_; lean_object* v_res_1085_; 
v_pu_boxed_1084_ = lean_unbox(v_pu_1080_);
v_res_1085_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_boxed_1084_, v_decl_1081_, v_a_1082_);
lean_dec(v_a_1082_);
lean_dec_ref(v_decl_1081_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(uint8_t v_pu_1086_, lean_object* v_decl_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1086_, v_decl_1087_, v_a_1089_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___boxed(lean_object* v_pu_1094_, lean_object* v_decl_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
uint8_t v_pu_boxed_1101_; lean_object* v_res_1102_; 
v_pu_boxed_1101_ = lean_unbox(v_pu_1094_);
v_res_1102_ = l_Lean_Compiler_LCNF_eraseLetDecl(v_pu_boxed_1101_, v_decl_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec_ref(v_decl_1095_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t v_pu_1103_, lean_object* v_decl_1104_, uint8_t v_recursive_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v___x_1108_; lean_object* v_lctx_1109_; lean_object* v_nextIdx_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1121_; 
v___x_1108_ = lean_st_ref_take(v_a_1106_);
v_lctx_1109_ = lean_ctor_get(v___x_1108_, 0);
v_nextIdx_1110_ = lean_ctor_get(v___x_1108_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1112_ = v___x_1108_;
v_isShared_1113_ = v_isSharedCheck_1121_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_nextIdx_1110_);
lean_inc(v_lctx_1109_);
lean_dec(v___x_1108_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1121_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1114_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_1103_, v_lctx_1109_, v_decl_1104_, v_recursive_1105_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1114_);
v___x_1116_ = v___x_1112_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_nextIdx_1110_);
v___x_1116_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = lean_st_ref_set(v_a_1106_, v___x_1116_);
v___x_1118_ = lean_box(0);
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg___boxed(lean_object* v_pu_1122_, lean_object* v_decl_1123_, lean_object* v_recursive_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
uint8_t v_pu_boxed_1127_; uint8_t v_recursive_boxed_1128_; lean_object* v_res_1129_; 
v_pu_boxed_1127_ = lean_unbox(v_pu_1122_);
v_recursive_boxed_1128_ = lean_unbox(v_recursive_1124_);
v_res_1129_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_boxed_1127_, v_decl_1123_, v_recursive_boxed_1128_, v_a_1125_);
lean_dec(v_a_1125_);
lean_dec_ref(v_decl_1123_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(uint8_t v_pu_1130_, lean_object* v_decl_1131_, uint8_t v_recursive_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1130_, v_decl_1131_, v_recursive_1132_, v_a_1134_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___boxed(lean_object* v_pu_1139_, lean_object* v_decl_1140_, lean_object* v_recursive_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
uint8_t v_pu_boxed_1147_; uint8_t v_recursive_boxed_1148_; lean_object* v_res_1149_; 
v_pu_boxed_1147_ = lean_unbox(v_pu_1139_);
v_recursive_boxed_1148_ = lean_unbox(v_recursive_1141_);
v_res_1149_ = l_Lean_Compiler_LCNF_eraseFunDecl(v_pu_boxed_1147_, v_decl_1140_, v_recursive_boxed_1148_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec_ref(v_decl_1140_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t v_pu_1150_, lean_object* v_code_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v___x_1154_; lean_object* v_lctx_1155_; lean_object* v_nextIdx_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1167_; 
v___x_1154_ = lean_st_ref_take(v_a_1152_);
v_lctx_1155_ = lean_ctor_get(v___x_1154_, 0);
v_nextIdx_1156_ = lean_ctor_get(v___x_1154_, 1);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1158_ = v___x_1154_;
v_isShared_1159_ = v_isSharedCheck_1167_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_nextIdx_1156_);
lean_inc(v_lctx_1155_);
lean_dec(v___x_1154_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1167_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v___x_1162_; 
v___x_1160_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_1150_, v_code_1151_, v_lctx_1155_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1160_);
v___x_1162_ = v___x_1158_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_nextIdx_1156_);
v___x_1162_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1163_ = lean_st_ref_set(v_a_1152_, v___x_1162_);
v___x_1164_ = lean_box(0);
v___x_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
return v___x_1165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg___boxed(lean_object* v_pu_1168_, lean_object* v_code_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
uint8_t v_pu_boxed_1172_; lean_object* v_res_1173_; 
v_pu_boxed_1172_ = lean_unbox(v_pu_1168_);
v_res_1173_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_boxed_1172_, v_code_1169_, v_a_1170_);
lean_dec(v_a_1170_);
lean_dec_ref(v_code_1169_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode(uint8_t v_pu_1174_, lean_object* v_code_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_1174_, v_code_1175_, v_a_1177_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___boxed(lean_object* v_pu_1182_, lean_object* v_code_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
uint8_t v_pu_boxed_1189_; lean_object* v_res_1190_; 
v_pu_boxed_1189_ = lean_unbox(v_pu_1182_);
v_res_1190_ = l_Lean_Compiler_LCNF_eraseCode(v_pu_boxed_1189_, v_code_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
lean_dec(v_a_1187_);
lean_dec_ref(v_a_1186_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
lean_dec_ref(v_code_1183_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t v_pu_1191_, lean_object* v_param_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v___x_1195_; lean_object* v_lctx_1196_; lean_object* v_nextIdx_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1208_; 
v___x_1195_ = lean_st_ref_take(v_a_1193_);
v_lctx_1196_ = lean_ctor_get(v___x_1195_, 0);
v_nextIdx_1197_ = lean_ctor_get(v___x_1195_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1199_ = v___x_1195_;
v_isShared_1200_ = v_isSharedCheck_1208_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_nextIdx_1197_);
lean_inc(v_lctx_1196_);
lean_dec(v___x_1195_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1208_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1201_ = l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_1191_, v_lctx_1196_, v_param_1192_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 0, v___x_1201_);
v___x_1203_ = v___x_1199_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_nextIdx_1197_);
v___x_1203_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = lean_st_ref_set(v_a_1193_, v___x_1203_);
v___x_1205_ = lean_box(0);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg___boxed(lean_object* v_pu_1209_, lean_object* v_param_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
uint8_t v_pu_boxed_1213_; lean_object* v_res_1214_; 
v_pu_boxed_1213_ = lean_unbox(v_pu_1209_);
v_res_1214_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_boxed_1213_, v_param_1210_, v_a_1211_);
lean_dec(v_a_1211_);
lean_dec_ref(v_param_1210_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam(uint8_t v_pu_1215_, lean_object* v_param_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_1215_, v_param_1216_, v_a_1218_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___boxed(lean_object* v_pu_1223_, lean_object* v_param_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
uint8_t v_pu_boxed_1230_; lean_object* v_res_1231_; 
v_pu_boxed_1230_ = lean_unbox(v_pu_1223_);
v_res_1231_ = l_Lean_Compiler_LCNF_eraseParam(v_pu_boxed_1230_, v_param_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec_ref(v_param_1224_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t v_pu_1232_, lean_object* v_params_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v___x_1236_; lean_object* v_lctx_1237_; lean_object* v_nextIdx_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1249_; 
v___x_1236_ = lean_st_ref_take(v_a_1234_);
v_lctx_1237_ = lean_ctor_get(v___x_1236_, 0);
v_nextIdx_1238_ = lean_ctor_get(v___x_1236_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1240_ = v___x_1236_;
v_isShared_1241_ = v_isSharedCheck_1249_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_nextIdx_1238_);
lean_inc(v_lctx_1237_);
lean_dec(v___x_1236_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1249_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1242_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_1232_, v_lctx_1237_, v_params_1233_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v___x_1242_);
v___x_1244_ = v___x_1240_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_nextIdx_1238_);
v___x_1244_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = lean_st_ref_set(v_a_1234_, v___x_1244_);
v___x_1246_ = lean_box(0);
v___x_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
return v___x_1247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg___boxed(lean_object* v_pu_1250_, lean_object* v_params_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_){
_start:
{
uint8_t v_pu_boxed_1254_; lean_object* v_res_1255_; 
v_pu_boxed_1254_ = lean_unbox(v_pu_1250_);
v_res_1255_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_boxed_1254_, v_params_1251_, v_a_1252_);
lean_dec(v_a_1252_);
lean_dec_ref(v_params_1251_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams(uint8_t v_pu_1256_, lean_object* v_params_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1256_, v_params_1257_, v_a_1259_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___boxed(lean_object* v_pu_1264_, lean_object* v_params_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
uint8_t v_pu_boxed_1271_; lean_object* v_res_1272_; 
v_pu_boxed_1271_ = lean_unbox(v_pu_1264_);
v_res_1272_ = l_Lean_Compiler_LCNF_eraseParams(v_pu_boxed_1271_, v_params_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec_ref(v_params_1265_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t v_pu_1273_, lean_object* v_decl_1274_, lean_object* v_a_1275_){
_start:
{
switch(lean_obj_tag(v_decl_1274_))
{
case 0:
{
lean_object* v_decl_1277_; lean_object* v___x_1278_; 
v_decl_1277_ = lean_ctor_get(v_decl_1274_, 0);
v___x_1278_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1273_, v_decl_1277_, v_a_1275_);
return v___x_1278_;
}
case 1:
{
lean_object* v_decl_1279_; uint8_t v___x_1280_; lean_object* v___x_1281_; 
v_decl_1279_ = lean_ctor_get(v_decl_1274_, 0);
v___x_1280_ = 1;
v___x_1281_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1273_, v_decl_1279_, v___x_1280_, v_a_1275_);
return v___x_1281_;
}
case 2:
{
lean_object* v_decl_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; 
v_decl_1282_ = lean_ctor_get(v_decl_1274_, 0);
v___x_1283_ = 1;
v___x_1284_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1273_, v_decl_1282_, v___x_1283_, v_a_1275_);
return v___x_1284_;
}
default: 
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = lean_box(0);
v___x_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
return v___x_1286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg___boxed(lean_object* v_pu_1287_, lean_object* v_decl_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
uint8_t v_pu_boxed_1291_; lean_object* v_res_1292_; 
v_pu_boxed_1291_ = lean_unbox(v_pu_1287_);
v_res_1292_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_boxed_1291_, v_decl_1288_, v_a_1289_);
lean_dec(v_a_1289_);
lean_dec_ref(v_decl_1288_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl(uint8_t v_pu_1293_, lean_object* v_decl_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1293_, v_decl_1294_, v_a_1296_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___boxed(lean_object* v_pu_1301_, lean_object* v_decl_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
uint8_t v_pu_boxed_1308_; lean_object* v_res_1309_; 
v_pu_boxed_1308_ = lean_unbox(v_pu_1301_);
v_res_1309_ = l_Lean_Compiler_LCNF_eraseCodeDecl(v_pu_boxed_1308_, v_decl_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec_ref(v_decl_1302_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(uint8_t v_pu_1310_, lean_object* v_as_1311_, size_t v_i_1312_, size_t v_stop_1313_, lean_object* v_b_1314_, lean_object* v___y_1315_){
_start:
{
uint8_t v___x_1317_; 
v___x_1317_ = lean_usize_dec_eq(v_i_1312_, v_stop_1313_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_array_uget_borrowed(v_as_1311_, v_i_1312_);
v___x_1319_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1310_, v___x_1318_, v___y_1315_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; size_t v___x_1321_; size_t v___x_1322_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref(v___x_1319_);
v___x_1321_ = ((size_t)1ULL);
v___x_1322_ = lean_usize_add(v_i_1312_, v___x_1321_);
v_i_1312_ = v___x_1322_;
v_b_1314_ = v_a_1320_;
goto _start;
}
else
{
return v___x_1319_;
}
}
else
{
lean_object* v___x_1324_; 
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v_b_1314_);
return v___x_1324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg___boxed(lean_object* v_pu_1325_, lean_object* v_as_1326_, lean_object* v_i_1327_, lean_object* v_stop_1328_, lean_object* v_b_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
uint8_t v_pu_boxed_1332_; size_t v_i_boxed_1333_; size_t v_stop_boxed_1334_; lean_object* v_res_1335_; 
v_pu_boxed_1332_ = lean_unbox(v_pu_1325_);
v_i_boxed_1333_ = lean_unbox_usize(v_i_1327_);
lean_dec(v_i_1327_);
v_stop_boxed_1334_ = lean_unbox_usize(v_stop_1328_);
lean_dec(v_stop_1328_);
v_res_1335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_boxed_1332_, v_as_1326_, v_i_boxed_1333_, v_stop_boxed_1334_, v_b_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v_as_1326_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls(uint8_t v_pu_1336_, lean_object* v_decls_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1343_ = lean_unsigned_to_nat(0u);
v___x_1344_ = lean_array_get_size(v_decls_1337_);
v___x_1345_ = lean_box(0);
v___x_1346_ = lean_nat_dec_lt(v___x_1343_, v___x_1344_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; 
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1345_);
return v___x_1347_;
}
else
{
uint8_t v___x_1348_; 
v___x_1348_ = lean_nat_dec_le(v___x_1344_, v___x_1344_);
if (v___x_1348_ == 0)
{
if (v___x_1346_ == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1345_);
return v___x_1349_;
}
else
{
size_t v___x_1350_; size_t v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = ((size_t)0ULL);
v___x_1351_ = lean_usize_of_nat(v___x_1344_);
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1336_, v_decls_1337_, v___x_1350_, v___x_1351_, v___x_1345_, v_a_1339_);
return v___x_1352_;
}
}
else
{
size_t v___x_1353_; size_t v___x_1354_; lean_object* v___x_1355_; 
v___x_1353_ = ((size_t)0ULL);
v___x_1354_ = lean_usize_of_nat(v___x_1344_);
v___x_1355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1336_, v_decls_1337_, v___x_1353_, v___x_1354_, v___x_1345_, v_a_1339_);
return v___x_1355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls___boxed(lean_object* v_pu_1356_, lean_object* v_decls_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
uint8_t v_pu_boxed_1363_; lean_object* v_res_1364_; 
v_pu_boxed_1363_ = lean_unbox(v_pu_1356_);
v_res_1364_ = l_Lean_Compiler_LCNF_eraseCodeDecls(v_pu_boxed_1363_, v_decls_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec_ref(v_decls_1357_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(uint8_t v_pu_1365_, lean_object* v_as_1366_, size_t v_i_1367_, size_t v_stop_1368_, lean_object* v_b_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1365_, v_as_1366_, v_i_1367_, v_stop_1368_, v_b_1369_, v___y_1371_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___boxed(lean_object* v_pu_1376_, lean_object* v_as_1377_, lean_object* v_i_1378_, lean_object* v_stop_1379_, lean_object* v_b_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
uint8_t v_pu_boxed_1386_; size_t v_i_boxed_1387_; size_t v_stop_boxed_1388_; lean_object* v_res_1389_; 
v_pu_boxed_1386_ = lean_unbox(v_pu_1376_);
v_i_boxed_1387_ = lean_unbox_usize(v_i_1378_);
lean_dec(v_i_1378_);
v_stop_boxed_1388_ = lean_unbox_usize(v_stop_1379_);
lean_dec(v_stop_1379_);
v_res_1389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(v_pu_boxed_1386_, v_as_1377_, v_i_boxed_1387_, v_stop_boxed_1388_, v_b_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec_ref(v_as_1377_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(lean_object* v_f_1390_, lean_object* v_v_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
if (lean_obj_tag(v_v_1391_) == 0)
{
lean_object* v_code_1397_; lean_object* v___x_1398_; 
v_code_1397_ = lean_ctor_get(v_v_1391_, 0);
lean_inc_ref(v_code_1397_);
lean_dec_ref(v_v_1391_);
lean_inc(v___y_1395_);
lean_inc_ref(v___y_1394_);
lean_inc(v___y_1393_);
lean_inc_ref(v___y_1392_);
v___x_1398_ = lean_apply_6(v_f_1390_, v_code_1397_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, lean_box(0));
return v___x_1398_;
}
else
{
lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1406_; 
lean_dec_ref(v_f_1390_);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_v_1391_);
if (v_isSharedCheck_1406_ == 0)
{
lean_object* v_unused_1407_; 
v_unused_1407_ = lean_ctor_get(v_v_1391_, 0);
lean_dec(v_unused_1407_);
v___x_1400_ = v_v_1391_;
v_isShared_1401_ = v_isSharedCheck_1406_;
goto v_resetjp_1399_;
}
else
{
lean_dec(v_v_1391_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1406_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1402_ = lean_box(0);
if (v_isShared_1401_ == 0)
{
lean_ctor_set_tag(v___x_1400_, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1402_);
v___x_1404_ = v___x_1400_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg___boxed(lean_object* v_f_1408_, lean_object* v_v_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1408_, v_v_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(uint8_t v_pu_1416_, lean_object* v_f_1417_, lean_object* v_v_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1417_, v_v_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___boxed(lean_object* v_pu_1425_, lean_object* v_f_1426_, lean_object* v_v_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
uint8_t v_pu_boxed_1433_; lean_object* v_res_1434_; 
v_pu_boxed_1433_ = lean_unbox(v_pu_1425_);
v_res_1434_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(v_pu_boxed_1433_, v_f_1426_, v_v_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t v_pu_1435_, lean_object* v_decl_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v_toSignature_1442_; lean_object* v_value_1443_; lean_object* v_params_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v_toSignature_1442_ = lean_ctor_get(v_decl_1436_, 0);
lean_inc_ref(v_toSignature_1442_);
v_value_1443_ = lean_ctor_get(v_decl_1436_, 1);
lean_inc_ref(v_value_1443_);
lean_dec_ref(v_decl_1436_);
v_params_1444_ = lean_ctor_get(v_toSignature_1442_, 3);
lean_inc_ref(v_params_1444_);
lean_dec_ref(v_toSignature_1442_);
v___x_1445_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1435_, v_params_1444_, v_a_1438_);
lean_dec_ref(v_params_1444_);
lean_dec_ref(v___x_1445_);
v___x_1446_ = lean_box(v_pu_1435_);
v___x_1447_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_eraseCode___boxed), 7, 1);
lean_closure_set(v___x_1447_, 0, v___x_1446_);
v___x_1448_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v___x_1447_, v_value_1443_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl___boxed(lean_object* v_pu_1449_, lean_object* v_decl_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
uint8_t v_pu_boxed_1456_; lean_object* v_res_1457_; 
v_pu_boxed_1456_ = lean_unbox(v_pu_1449_);
v_res_1457_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_boxed_1456_, v_decl_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase(uint8_t v_pu_1458_, lean_object* v_decl_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_1458_, v_decl_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase___boxed(lean_object* v_pu_1466_, lean_object* v_decl_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
uint8_t v_pu_boxed_1473_; lean_object* v_res_1474_; 
v_pu_boxed_1473_ = lean_unbox(v_pu_1466_);
v_res_1474_ = l_Lean_Compiler_LCNF_Decl_erase(v_pu_boxed_1473_, v_decl_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(lean_object* v_msg_1475_){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = l_Lean_instInhabitedExpr;
v___x_1477_ = lean_panic_fn_borrowed(v___x_1476_, v_msg_1475_);
return v___x_1477_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1481_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2));
v___x_1482_ = lean_unsigned_to_nat(20u);
v___x_1483_ = lean_unsigned_to_nat(215u);
v___x_1484_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1));
v___x_1485_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0));
v___x_1486_ = l_mkPanicMessageWithDecl(v___x_1485_, v___x_1484_, v___x_1483_, v___x_1482_, v___x_1481_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t v_pu_1487_, lean_object* v_s_1488_, uint8_t v_translator_1489_, lean_object* v_e_1490_){
_start:
{
uint8_t v___x_1491_; 
v___x_1491_ = l_Lean_Expr_hasFVar(v_e_1490_);
if (v___x_1491_ == 0)
{
return v_e_1490_;
}
else
{
switch(lean_obj_tag(v_e_1490_))
{
case 1:
{
lean_object* v_fvarId_1492_; lean_object* v___x_1493_; 
v_fvarId_1492_ = lean_ctor_get(v_e_1490_, 0);
v___x_1493_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1488_, v_fvarId_1492_);
if (lean_obj_tag(v___x_1493_) == 0)
{
return v_e_1490_;
}
else
{
lean_object* v_val_1494_; 
lean_dec_ref(v_e_1490_);
v_val_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_val_1494_);
lean_dec_ref(v___x_1493_);
switch(lean_obj_tag(v_val_1494_))
{
case 0:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Lean_Compiler_LCNF_erasedExpr;
return v___x_1495_;
}
case 1:
{
if (v_translator_1489_ == 0)
{
lean_object* v_fvarId_1496_; lean_object* v___x_1497_; 
v_fvarId_1496_ = lean_ctor_get(v_val_1494_, 0);
lean_inc(v_fvarId_1496_);
lean_dec_ref(v_val_1494_);
v___x_1497_ = l_Lean_Expr_fvar___override(v_fvarId_1496_);
v_e_1490_ = v___x_1497_;
goto _start;
}
else
{
lean_object* v_fvarId_1499_; lean_object* v___x_1500_; 
v_fvarId_1499_ = lean_ctor_get(v_val_1494_, 0);
lean_inc(v_fvarId_1499_);
lean_dec_ref(v_val_1494_);
v___x_1500_ = l_Lean_Expr_fvar___override(v_fvarId_1499_);
return v___x_1500_;
}
}
default: 
{
if (v_translator_1489_ == 0)
{
lean_object* v_expr_1501_; 
v_expr_1501_ = lean_ctor_get(v_val_1494_, 0);
lean_inc_ref(v_expr_1501_);
lean_dec_ref(v_val_1494_);
v_e_1490_ = v_expr_1501_;
goto _start;
}
else
{
lean_object* v_expr_1503_; 
v_expr_1503_ = lean_ctor_get(v_val_1494_, 0);
lean_inc_ref(v_expr_1503_);
lean_dec_ref(v_val_1494_);
return v_expr_1503_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_1504_; lean_object* v_arg_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; uint8_t v___y_1509_; size_t v___x_1513_; size_t v___x_1514_; uint8_t v___x_1515_; 
v_fn_1504_ = lean_ctor_get(v_e_1490_, 0);
v_arg_1505_ = lean_ctor_get(v_e_1490_, 1);
lean_inc_ref(v_fn_1504_);
v___x_1506_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1487_, v_s_1488_, v_translator_1489_, v_fn_1504_);
lean_inc_ref(v_arg_1505_);
v___x_1507_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1487_, v_s_1488_, v_translator_1489_, v_arg_1505_);
v___x_1513_ = lean_ptr_addr(v_fn_1504_);
v___x_1514_ = lean_ptr_addr(v___x_1506_);
v___x_1515_ = lean_usize_dec_eq(v___x_1513_, v___x_1514_);
if (v___x_1515_ == 0)
{
v___y_1509_ = v___x_1515_;
goto v___jp_1508_;
}
else
{
size_t v___x_1516_; size_t v___x_1517_; uint8_t v___x_1518_; 
v___x_1516_ = lean_ptr_addr(v_arg_1505_);
v___x_1517_ = lean_ptr_addr(v___x_1507_);
v___x_1518_ = lean_usize_dec_eq(v___x_1516_, v___x_1517_);
v___y_1509_ = v___x_1518_;
goto v___jp_1508_;
}
v___jp_1508_:
{
if (v___y_1509_ == 0)
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec_ref(v_e_1490_);
v___x_1510_ = l_Lean_Expr_app___override(v___x_1506_, v___x_1507_);
v___x_1511_ = l_Lean_Expr_headBeta(v___x_1510_);
return v___x_1511_;
}
else
{
lean_object* v___x_1512_; 
lean_dec_ref(v___x_1507_);
lean_dec_ref(v___x_1506_);
v___x_1512_ = l_Lean_Expr_headBeta(v_e_1490_);
return v___x_1512_;
}
}
}
case 6:
{
lean_object* v_binderName_1519_; lean_object* v_binderType_1520_; lean_object* v_body_1521_; uint8_t v_binderInfo_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___y_1526_; size_t v___x_1530_; size_t v___x_1531_; uint8_t v___x_1532_; 
v_binderName_1519_ = lean_ctor_get(v_e_1490_, 0);
v_binderType_1520_ = lean_ctor_get(v_e_1490_, 1);
v_body_1521_ = lean_ctor_get(v_e_1490_, 2);
v_binderInfo_1522_ = lean_ctor_get_uint8(v_e_1490_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1520_);
v___x_1523_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1487_, v_s_1488_, v_translator_1489_, v_binderType_1520_);
lean_inc_ref(v_body_1521_);
v___x_1524_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1487_, v_s_1488_, v_translator_1489_, v_body_1521_);
v___x_1530_ = lean_ptr_addr(v_binderType_1520_);
v___x_1531_ = lean_ptr_addr(v___x_1523_);
v___x_1532_ = lean_usize_dec_eq(v___x_1530_, v___x_1531_);
if (v___x_1532_ == 0)
{
v___y_1526_ = v___x_1532_;
goto v___jp_1525_;
}
else
{
size_t v___x_1533_; size_t v___x_1534_; uint8_t v___x_1535_; 
v___x_1533_ = lean_ptr_addr(v_body_1521_);
v___x_1534_ = lean_ptr_addr(v___x_1524_);
v___x_1535_ = lean_usize_dec_eq(v___x_1533_, v___x_1534_);
v___y_1526_ = v___x_1535_;
goto v___jp_1525_;
}
v___jp_1525_:
{
if (v___y_1526_ == 0)
{
lean_object* v___x_1527_; 
lean_inc(v_binderName_1519_);
lean_dec_ref(v_e_1490_);
v___x_1527_ = l_Lean_Expr_lam___override(v_binderName_1519_, v___x_1523_, v___x_1524_, v_binderInfo_1522_);
return v___x_1527_;
}
else
{
uint8_t v___x_1528_; 
v___x_1528_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1522_, v_binderInfo_1522_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
lean_inc(v_binderName_1519_);
lean_dec_ref(v_e_1490_);
v___x_1529_ = l_Lean_Expr_lam___override(v_binderName_1519_, v___x_1523_, v___x_1524_, v_binderInfo_1522_);
return v___x_1529_;
}
else
{
lean_dec_ref(v___x_1524_);
lean_dec_ref(v___x_1523_);
return v_e_1490_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1536_; lean_object* v_binderType_1537_; lean_object* v_body_1538_; uint8_t v_binderInfo_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___y_1543_; size_t v___x_1547_; size_t v___x_1548_; uint8_t v___x_1549_; 
v_binderName_1536_ = lean_ctor_get(v_e_1490_, 0);
v_binderType_1537_ = lean_ctor_get(v_e_1490_, 1);
v_body_1538_ = lean_ctor_get(v_e_1490_, 2);
v_binderInfo_1539_ = lean_ctor_get_uint8(v_e_1490_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1537_);
v___x_1540_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1487_, v_s_1488_, v_translator_1489_, v_binderType_1537_);
lean_inc_ref(v_body_1538_);
v___x_1541_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1487_, v_s_1488_, v_translator_1489_, v_body_1538_);
v___x_1547_ = lean_ptr_addr(v_binderType_1537_);
v___x_1548_ = lean_ptr_addr(v___x_1540_);
v___x_1549_ = lean_usize_dec_eq(v___x_1547_, v___x_1548_);
if (v___x_1549_ == 0)
{
v___y_1543_ = v___x_1549_;
goto v___jp_1542_;
}
else
{
size_t v___x_1550_; size_t v___x_1551_; uint8_t v___x_1552_; 
v___x_1550_ = lean_ptr_addr(v_body_1538_);
v___x_1551_ = lean_ptr_addr(v___x_1541_);
v___x_1552_ = lean_usize_dec_eq(v___x_1550_, v___x_1551_);
v___y_1543_ = v___x_1552_;
goto v___jp_1542_;
}
v___jp_1542_:
{
if (v___y_1543_ == 0)
{
lean_object* v___x_1544_; 
lean_inc(v_binderName_1536_);
lean_dec_ref(v_e_1490_);
v___x_1544_ = l_Lean_Expr_forallE___override(v_binderName_1536_, v___x_1540_, v___x_1541_, v_binderInfo_1539_);
return v___x_1544_;
}
else
{
uint8_t v___x_1545_; 
v___x_1545_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1539_, v_binderInfo_1539_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; 
lean_inc(v_binderName_1536_);
lean_dec_ref(v_e_1490_);
v___x_1546_ = l_Lean_Expr_forallE___override(v_binderName_1536_, v___x_1540_, v___x_1541_, v_binderInfo_1539_);
return v___x_1546_;
}
else
{
lean_dec_ref(v___x_1541_);
lean_dec_ref(v___x_1540_);
return v_e_1490_;
}
}
}
}
case 8:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
lean_dec_ref(v_e_1490_);
v___x_1553_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3, &l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3);
v___x_1554_ = l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(v___x_1553_);
return v___x_1554_;
}
case 10:
{
lean_object* v_data_1555_; lean_object* v_expr_1556_; lean_object* v___x_1557_; size_t v___x_1558_; size_t v___x_1559_; uint8_t v___x_1560_; 
v_data_1555_ = lean_ctor_get(v_e_1490_, 0);
v_expr_1556_ = lean_ctor_get(v_e_1490_, 1);
lean_inc_ref(v_expr_1556_);
v___x_1557_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1487_, v_s_1488_, v_translator_1489_, v_expr_1556_);
v___x_1558_ = lean_ptr_addr(v_expr_1556_);
v___x_1559_ = lean_ptr_addr(v___x_1557_);
v___x_1560_ = lean_usize_dec_eq(v___x_1558_, v___x_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; 
lean_inc(v_data_1555_);
lean_dec_ref(v_e_1490_);
v___x_1561_ = l_Lean_Expr_mdata___override(v_data_1555_, v___x_1557_);
return v___x_1561_;
}
else
{
lean_dec_ref(v___x_1557_);
return v_e_1490_;
}
}
case 11:
{
lean_object* v_typeName_1562_; lean_object* v_idx_1563_; lean_object* v_struct_1564_; lean_object* v___x_1565_; size_t v___x_1566_; size_t v___x_1567_; uint8_t v___x_1568_; 
v_typeName_1562_ = lean_ctor_get(v_e_1490_, 0);
v_idx_1563_ = lean_ctor_get(v_e_1490_, 1);
v_struct_1564_ = lean_ctor_get(v_e_1490_, 2);
lean_inc_ref(v_struct_1564_);
v___x_1565_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1487_, v_s_1488_, v_translator_1489_, v_struct_1564_);
v___x_1566_ = lean_ptr_addr(v_struct_1564_);
v___x_1567_ = lean_ptr_addr(v___x_1565_);
v___x_1568_ = lean_usize_dec_eq(v___x_1566_, v___x_1567_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; 
lean_inc(v_idx_1563_);
lean_inc(v_typeName_1562_);
lean_dec_ref(v_e_1490_);
v___x_1569_ = l_Lean_Expr_proj___override(v_typeName_1562_, v_idx_1563_, v___x_1565_);
return v___x_1569_;
}
else
{
lean_dec_ref(v___x_1565_);
return v_e_1490_;
}
}
default: 
{
return v_e_1490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(uint8_t v_pu_1570_, lean_object* v_s_1571_, uint8_t v_translator_1572_, lean_object* v_e_1573_){
_start:
{
if (lean_obj_tag(v_e_1573_) == 5)
{
lean_object* v_fn_1574_; lean_object* v_arg_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; uint8_t v___y_1579_; size_t v___x_1581_; size_t v___x_1582_; uint8_t v___x_1583_; 
v_fn_1574_ = lean_ctor_get(v_e_1573_, 0);
v_arg_1575_ = lean_ctor_get(v_e_1573_, 1);
lean_inc_ref(v_fn_1574_);
v___x_1576_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1570_, v_s_1571_, v_translator_1572_, v_fn_1574_);
lean_inc_ref(v_arg_1575_);
v___x_1577_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1570_, v_s_1571_, v_translator_1572_, v_arg_1575_);
v___x_1581_ = lean_ptr_addr(v_fn_1574_);
v___x_1582_ = lean_ptr_addr(v___x_1576_);
v___x_1583_ = lean_usize_dec_eq(v___x_1581_, v___x_1582_);
if (v___x_1583_ == 0)
{
v___y_1579_ = v___x_1583_;
goto v___jp_1578_;
}
else
{
size_t v___x_1584_; size_t v___x_1585_; uint8_t v___x_1586_; 
v___x_1584_ = lean_ptr_addr(v_arg_1575_);
v___x_1585_ = lean_ptr_addr(v___x_1577_);
v___x_1586_ = lean_usize_dec_eq(v___x_1584_, v___x_1585_);
v___y_1579_ = v___x_1586_;
goto v___jp_1578_;
}
v___jp_1578_:
{
if (v___y_1579_ == 0)
{
lean_object* v___x_1580_; 
lean_dec_ref(v_e_1573_);
v___x_1580_ = l_Lean_Expr_app___override(v___x_1576_, v___x_1577_);
return v___x_1580_;
}
else
{
lean_dec_ref(v___x_1577_);
lean_dec_ref(v___x_1576_);
return v_e_1573_;
}
}
}
else
{
lean_object* v___x_1587_; 
v___x_1587_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1570_, v_s_1571_, v_translator_1572_, v_e_1573_);
return v___x_1587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(lean_object* v_pu_1588_, lean_object* v_s_1589_, lean_object* v_translator_1590_, lean_object* v_e_1591_){
_start:
{
uint8_t v_pu_boxed_1592_; uint8_t v_translator_boxed_1593_; lean_object* v_res_1594_; 
v_pu_boxed_1592_ = lean_unbox(v_pu_1588_);
v_translator_boxed_1593_ = lean_unbox(v_translator_1590_);
v_res_1594_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_boxed_1592_, v_s_1589_, v_translator_boxed_1593_, v_e_1591_);
lean_dec_ref(v_s_1589_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(lean_object* v_pu_1595_, lean_object* v_s_1596_, lean_object* v_translator_1597_, lean_object* v_e_1598_){
_start:
{
uint8_t v_pu_boxed_1599_; uint8_t v_translator_boxed_1600_; lean_object* v_res_1601_; 
v_pu_boxed_1599_ = lean_unbox(v_pu_1595_);
v_translator_boxed_1600_ = lean_unbox(v_translator_1597_);
v_res_1601_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_boxed_1599_, v_s_1596_, v_translator_boxed_1600_, v_e_1598_);
lean_dec_ref(v_s_1596_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(uint8_t v_pu_1602_, lean_object* v_s_1603_, lean_object* v_e_1604_, uint8_t v_translator_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1602_, v_s_1603_, v_translator_1605_, v_e_1604_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(lean_object* v_pu_1607_, lean_object* v_s_1608_, lean_object* v_e_1609_, lean_object* v_translator_1610_){
_start:
{
uint8_t v_pu_boxed_1611_; uint8_t v_translator_boxed_1612_; lean_object* v_res_1613_; 
v_pu_boxed_1611_ = lean_unbox(v_pu_1607_);
v_translator_boxed_1612_ = lean_unbox(v_translator_1610_);
v_res_1613_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(v_pu_boxed_1611_, v_s_1608_, v_e_1609_, v_translator_boxed_1612_);
lean_dec_ref(v_s_1608_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(lean_object* v_x_1614_){
_start:
{
if (lean_obj_tag(v_x_1614_) == 0)
{
lean_object* v___x_1615_; 
v___x_1615_ = lean_unsigned_to_nat(0u);
return v___x_1615_;
}
else
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_unsigned_to_nat(1u);
return v___x_1616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___boxed(lean_object* v_x_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(v_x_1617_);
lean_dec(v_x_1617_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(lean_object* v_t_1619_, lean_object* v_k_1620_){
_start:
{
if (lean_obj_tag(v_t_1619_) == 0)
{
lean_object* v_fvarId_1621_; lean_object* v___x_1622_; 
v_fvarId_1621_ = lean_ctor_get(v_t_1619_, 0);
lean_inc(v_fvarId_1621_);
lean_dec_ref(v_t_1619_);
v___x_1622_ = lean_apply_1(v_k_1620_, v_fvarId_1621_);
return v___x_1622_;
}
else
{
return v_k_1620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(lean_object* v_motive_1623_, lean_object* v_ctorIdx_1624_, lean_object* v_t_1625_, lean_object* v_h_1626_, lean_object* v_k_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1625_, v_k_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___boxed(lean_object* v_motive_1629_, lean_object* v_ctorIdx_1630_, lean_object* v_t_1631_, lean_object* v_h_1632_, lean_object* v_k_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(v_motive_1629_, v_ctorIdx_1630_, v_t_1631_, v_h_1632_, v_k_1633_);
lean_dec(v_ctorIdx_1630_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim___redArg(lean_object* v_t_1635_, lean_object* v_fvar_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1635_, v_fvar_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim(lean_object* v_motive_1638_, lean_object* v_t_1639_, lean_object* v_h_1640_, lean_object* v_fvar_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1639_, v_fvar_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim___redArg(lean_object* v_t_1643_, lean_object* v_erased_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1643_, v_erased_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim(lean_object* v_motive_1646_, lean_object* v_t_1647_, lean_object* v_h_1648_, lean_object* v_erased_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1647_, v_erased_1649_);
return v___x_1650_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = l_Lean_instInhabitedFVarId_default;
v___x_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default(void){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0);
return v___x_1653_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedNormFVarResult(void){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default;
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object* v_s_1655_, lean_object* v_fvarId_1656_, uint8_t v_translator_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1655_, v_fvarId_1656_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v_fvarId_1656_);
return v___x_1659_;
}
else
{
lean_object* v_val_1660_; 
lean_dec(v_fvarId_1656_);
v_val_1660_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_val_1660_);
lean_dec_ref(v___x_1658_);
if (lean_obj_tag(v_val_1660_) == 1)
{
if (v_translator_1657_ == 0)
{
lean_object* v_fvarId_1661_; 
v_fvarId_1661_ = lean_ctor_get(v_val_1660_, 0);
lean_inc(v_fvarId_1661_);
lean_dec_ref(v_val_1660_);
v_fvarId_1656_ = v_fvarId_1661_;
goto _start;
}
else
{
lean_object* v_fvarId_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
v_fvarId_1663_ = lean_ctor_get(v_val_1660_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_val_1660_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v_val_1660_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_fvarId_1663_);
lean_dec(v_val_1660_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
lean_ctor_set_tag(v___x_1665_, 0);
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_fvarId_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
else
{
lean_object* v___x_1671_; 
lean_dec(v_val_1660_);
v___x_1671_ = lean_box(1);
return v___x_1671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg___boxed(lean_object* v_s_1672_, lean_object* v_fvarId_1673_, lean_object* v_translator_1674_){
_start:
{
uint8_t v_translator_boxed_1675_; lean_object* v_res_1676_; 
v_translator_boxed_1675_ = lean_unbox(v_translator_1674_);
v_res_1676_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1672_, v_fvarId_1673_, v_translator_boxed_1675_);
lean_dec_ref(v_s_1672_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp(uint8_t v_pu_1677_, lean_object* v_s_1678_, lean_object* v_fvarId_1679_, uint8_t v_translator_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1678_, v_fvarId_1679_, v_translator_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___boxed(lean_object* v_pu_1682_, lean_object* v_s_1683_, lean_object* v_fvarId_1684_, lean_object* v_translator_1685_){
_start:
{
uint8_t v_pu_boxed_1686_; uint8_t v_translator_boxed_1687_; lean_object* v_res_1688_; 
v_pu_boxed_1686_ = lean_unbox(v_pu_1682_);
v_translator_boxed_1687_ = lean_unbox(v_translator_1685_);
v_res_1688_ = l_Lean_Compiler_LCNF_normFVarImp(v_pu_boxed_1686_, v_s_1683_, v_fvarId_1684_, v_translator_boxed_1687_);
lean_dec_ref(v_s_1683_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t v_pu_1689_, lean_object* v_s_1690_, lean_object* v_arg_1691_, uint8_t v_translator_1692_){
_start:
{
switch(lean_obj_tag(v_arg_1691_))
{
case 0:
{
return v_arg_1691_;
}
case 1:
{
lean_object* v_fvarId_1693_; lean_object* v___x_1694_; 
v_fvarId_1693_ = lean_ctor_get(v_arg_1691_, 0);
v___x_1694_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1690_, v_fvarId_1693_);
if (lean_obj_tag(v___x_1694_) == 0)
{
return v_arg_1691_;
}
else
{
lean_object* v_val_1695_; 
lean_dec_ref(v_arg_1691_);
v_val_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_val_1695_);
lean_dec_ref(v___x_1694_);
switch(lean_obj_tag(v_val_1695_))
{
case 0:
{
lean_object* v___x_1696_; 
v___x_1696_ = lean_box(0);
return v___x_1696_;
}
case 1:
{
lean_object* v_fvarId_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1705_; 
v_fvarId_1697_ = lean_ctor_get(v_val_1695_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_val_1695_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1699_ = v_val_1695_;
v_isShared_1700_ = v_isSharedCheck_1705_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_fvarId_1697_);
lean_dec(v_val_1695_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1705_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_fvarId_1697_);
v___x_1702_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
if (v_translator_1692_ == 0)
{
v_arg_1691_ = v___x_1702_;
goto _start;
}
else
{
return v___x_1702_;
}
}
}
}
default: 
{
lean_object* v_expr_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
v_expr_1706_ = lean_ctor_get(v_val_1695_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_val_1695_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v_val_1695_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_expr_1706_);
lean_dec(v_val_1695_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_expr_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
}
}
default: 
{
lean_object* v_expr_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_expr_1714_ = lean_ctor_get(v_arg_1691_, 0);
lean_inc_ref(v_expr_1714_);
v___x_1715_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1689_, v_s_1690_, v_translator_1692_, v_expr_1714_);
v___x_1716_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1689_, v_arg_1691_, v___x_1715_);
return v___x_1716_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp___boxed(lean_object* v_pu_1717_, lean_object* v_s_1718_, lean_object* v_arg_1719_, lean_object* v_translator_1720_){
_start:
{
uint8_t v_pu_boxed_1721_; uint8_t v_translator_boxed_1722_; lean_object* v_res_1723_; 
v_pu_boxed_1721_ = lean_unbox(v_pu_1717_);
v_translator_boxed_1722_ = lean_unbox(v_translator_1720_);
v_res_1723_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_boxed_1721_, v_s_1718_, v_arg_1719_, v_translator_boxed_1722_);
lean_dec_ref(v_s_1718_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(uint8_t v_pu_1724_, lean_object* v_s_1725_, uint8_t v_translator_1726_, lean_object* v_i_1727_, lean_object* v_as_1728_){
_start:
{
lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1729_ = lean_array_get_size(v_as_1728_);
v___x_1730_ = lean_nat_dec_lt(v_i_1727_, v___x_1729_);
if (v___x_1730_ == 0)
{
lean_dec(v_i_1727_);
return v_as_1728_;
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1732_; size_t v___x_1733_; size_t v___x_1734_; uint8_t v___x_1735_; 
v_a_1731_ = lean_array_fget_borrowed(v_as_1728_, v_i_1727_);
lean_inc(v_a_1731_);
v___x_1732_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1724_, v_s_1725_, v_a_1731_, v_translator_1726_);
v___x_1733_ = lean_ptr_addr(v_a_1731_);
v___x_1734_ = lean_ptr_addr(v___x_1732_);
v___x_1735_ = lean_usize_dec_eq(v___x_1733_, v___x_1734_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = lean_unsigned_to_nat(1u);
v___x_1737_ = lean_nat_add(v_i_1727_, v___x_1736_);
v___x_1738_ = lean_array_fset(v_as_1728_, v_i_1727_, v___x_1732_);
lean_dec(v_i_1727_);
v_i_1727_ = v___x_1737_;
v_as_1728_ = v___x_1738_;
goto _start;
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_dec(v___x_1732_);
v___x_1740_ = lean_unsigned_to_nat(1u);
v___x_1741_ = lean_nat_add(v_i_1727_, v___x_1740_);
lean_dec(v_i_1727_);
v_i_1727_ = v___x_1741_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0___boxed(lean_object* v_pu_1743_, lean_object* v_s_1744_, lean_object* v_translator_1745_, lean_object* v_i_1746_, lean_object* v_as_1747_){
_start:
{
uint8_t v_pu_boxed_1748_; uint8_t v_translator_boxed_1749_; lean_object* v_res_1750_; 
v_pu_boxed_1748_ = lean_unbox(v_pu_1743_);
v_translator_boxed_1749_ = lean_unbox(v_translator_1745_);
v_res_1750_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_boxed_1748_, v_s_1744_, v_translator_boxed_1749_, v_i_1746_, v_as_1747_);
lean_dec_ref(v_s_1744_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t v_pu_1751_, lean_object* v_s_1752_, lean_object* v_args_1753_, uint8_t v_translator_1754_){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_unsigned_to_nat(0u);
v___x_1756_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_1751_, v_s_1752_, v_translator_1754_, v___x_1755_, v_args_1753_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp___boxed(lean_object* v_pu_1757_, lean_object* v_s_1758_, lean_object* v_args_1759_, lean_object* v_translator_1760_){
_start:
{
uint8_t v_pu_boxed_1761_; uint8_t v_translator_boxed_1762_; lean_object* v_res_1763_; 
v_pu_boxed_1761_ = lean_unbox(v_pu_1757_);
v_translator_boxed_1762_ = lean_unbox(v_translator_1760_);
v_res_1763_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_boxed_1761_, v_s_1758_, v_args_1759_, v_translator_boxed_1762_);
lean_dec_ref(v_s_1758_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t v_pu_1764_, lean_object* v_s_1765_, lean_object* v_e_1766_, uint8_t v_translator_1767_){
_start:
{
lean_object* v_fvarId_1769_; lean_object* v_args_1775_; 
switch(lean_obj_tag(v_e_1766_))
{
case 2:
{
lean_object* v_struct_1778_; lean_object* v___x_1779_; 
v_struct_1778_ = lean_ctor_get(v_e_1766_, 2);
lean_inc(v_struct_1778_);
v___x_1779_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1765_, v_struct_1778_, v_translator_1767_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_fvarId_1780_; lean_object* v___x_1781_; 
v_fvarId_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_fvarId_1780_);
lean_dec_ref(v___x_1779_);
v___x_1781_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1764_, v_e_1766_, v_fvarId_1780_);
return v___x_1781_;
}
else
{
lean_object* v___x_1782_; 
lean_dec_ref(v_e_1766_);
v___x_1782_ = lean_box(1);
return v___x_1782_;
}
}
case 3:
{
lean_object* v_args_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v_args_1783_ = lean_ctor_get(v_e_1766_, 2);
lean_inc_ref(v_args_1783_);
v___x_1784_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1764_, v_s_1765_, v_args_1783_, v_translator_1767_);
v___x_1785_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1764_, v_e_1766_, v___x_1784_);
return v___x_1785_;
}
case 4:
{
lean_object* v_fvarId_1786_; lean_object* v_args_1787_; lean_object* v___x_1788_; 
v_fvarId_1786_ = lean_ctor_get(v_e_1766_, 0);
v_args_1787_ = lean_ctor_get(v_e_1766_, 1);
lean_inc(v_fvarId_1786_);
v___x_1788_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1765_, v_fvarId_1786_, v_translator_1767_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_fvarId_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v_fvarId_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_fvarId_1789_);
lean_dec_ref(v___x_1788_);
lean_inc_ref(v_args_1787_);
v___x_1790_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1764_, v_s_1765_, v_args_1787_, v_translator_1767_);
v___x_1791_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_1764_, v_e_1766_, v_fvarId_1789_, v___x_1790_);
lean_dec_ref(v_e_1766_);
return v___x_1791_;
}
else
{
lean_object* v___x_1792_; 
lean_dec_ref(v_e_1766_);
v___x_1792_ = lean_box(1);
return v___x_1792_;
}
}
case 5:
{
lean_object* v_args_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v_args_1793_ = lean_ctor_get(v_e_1766_, 1);
lean_inc_ref(v_args_1793_);
v___x_1794_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1764_, v_s_1765_, v_args_1793_, v_translator_1767_);
v___x_1795_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1764_, v_e_1766_, v___x_1794_);
return v___x_1795_;
}
case 6:
{
lean_object* v_var_1796_; 
v_var_1796_ = lean_ctor_get(v_e_1766_, 1);
lean_inc(v_var_1796_);
v_fvarId_1769_ = v_var_1796_;
goto v___jp_1768_;
}
case 7:
{
lean_object* v_var_1797_; 
v_var_1797_ = lean_ctor_get(v_e_1766_, 1);
lean_inc(v_var_1797_);
v_fvarId_1769_ = v_var_1797_;
goto v___jp_1768_;
}
case 8:
{
lean_object* v_var_1798_; lean_object* v___x_1799_; 
v_var_1798_ = lean_ctor_get(v_e_1766_, 2);
lean_inc(v_var_1798_);
v___x_1799_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1765_, v_var_1798_, v_translator_1767_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_fvarId_1800_; lean_object* v___x_1801_; 
v_fvarId_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_fvarId_1800_);
lean_dec_ref(v___x_1799_);
v___x_1801_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1764_, v_e_1766_, v_fvarId_1800_);
return v___x_1801_;
}
else
{
lean_object* v___x_1802_; 
lean_dec_ref(v_e_1766_);
v___x_1802_ = lean_box(1);
return v___x_1802_;
}
}
case 9:
{
lean_object* v_args_1803_; 
v_args_1803_ = lean_ctor_get(v_e_1766_, 1);
lean_inc_ref(v_args_1803_);
v_args_1775_ = v_args_1803_;
goto v___jp_1774_;
}
case 10:
{
lean_object* v_args_1804_; 
v_args_1804_ = lean_ctor_get(v_e_1766_, 1);
lean_inc_ref(v_args_1804_);
v_args_1775_ = v_args_1804_;
goto v___jp_1774_;
}
case 11:
{
lean_object* v_n_1805_; lean_object* v_var_1806_; lean_object* v___x_1807_; 
v_n_1805_ = lean_ctor_get(v_e_1766_, 0);
lean_inc(v_n_1805_);
v_var_1806_ = lean_ctor_get(v_e_1766_, 1);
lean_inc(v_var_1806_);
v___x_1807_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1765_, v_var_1806_, v_translator_1767_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_fvarId_1808_; lean_object* v___x_1809_; 
v_fvarId_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_fvarId_1808_);
lean_dec_ref(v___x_1807_);
v___x_1809_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_1764_, v_e_1766_, v_n_1805_, v_fvarId_1808_);
lean_dec_ref(v_e_1766_);
return v___x_1809_;
}
else
{
lean_object* v___x_1810_; 
lean_dec(v_n_1805_);
lean_dec_ref(v_e_1766_);
v___x_1810_ = lean_box(1);
return v___x_1810_;
}
}
case 12:
{
lean_object* v_var_1811_; lean_object* v_i_1812_; uint8_t v_updateHeader_1813_; lean_object* v_args_1814_; lean_object* v___x_1815_; 
v_var_1811_ = lean_ctor_get(v_e_1766_, 0);
v_i_1812_ = lean_ctor_get(v_e_1766_, 1);
lean_inc_ref(v_i_1812_);
v_updateHeader_1813_ = lean_ctor_get_uint8(v_e_1766_, sizeof(void*)*3);
v_args_1814_ = lean_ctor_get(v_e_1766_, 2);
lean_inc(v_var_1811_);
v___x_1815_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1765_, v_var_1811_, v_translator_1767_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_fvarId_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v_fvarId_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_fvarId_1816_);
lean_dec_ref(v___x_1815_);
lean_inc_ref(v_args_1814_);
v___x_1817_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1764_, v_s_1765_, v_args_1814_, v_translator_1767_);
v___x_1818_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_1764_, v_e_1766_, v_fvarId_1816_, v_i_1812_, v_updateHeader_1813_, v___x_1817_);
return v___x_1818_;
}
else
{
lean_object* v___x_1819_; 
lean_dec_ref(v_i_1812_);
lean_dec_ref(v_e_1766_);
v___x_1819_ = lean_box(1);
return v___x_1819_;
}
}
case 13:
{
lean_object* v_ty_1820_; lean_object* v_fvarId_1821_; lean_object* v___x_1822_; 
v_ty_1820_ = lean_ctor_get(v_e_1766_, 0);
lean_inc_ref(v_ty_1820_);
v_fvarId_1821_ = lean_ctor_get(v_e_1766_, 1);
lean_inc(v_fvarId_1821_);
v___x_1822_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1765_, v_fvarId_1821_, v_translator_1767_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_fvarId_1823_; lean_object* v___x_1824_; 
v_fvarId_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_fvarId_1823_);
lean_dec_ref(v___x_1822_);
v___x_1824_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_1764_, v_e_1766_, v_ty_1820_, v_fvarId_1823_);
lean_dec_ref(v_e_1766_);
return v___x_1824_;
}
else
{
lean_object* v___x_1825_; 
lean_dec_ref(v_e_1766_);
lean_dec_ref(v_ty_1820_);
v___x_1825_ = lean_box(1);
return v___x_1825_;
}
}
case 14:
{
lean_object* v_fvarId_1826_; lean_object* v___x_1827_; 
v_fvarId_1826_ = lean_ctor_get(v_e_1766_, 0);
lean_inc(v_fvarId_1826_);
v___x_1827_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1765_, v_fvarId_1826_, v_translator_1767_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_fvarId_1828_; lean_object* v___x_1829_; 
v_fvarId_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_fvarId_1828_);
lean_dec_ref(v___x_1827_);
v___x_1829_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_1764_, v_e_1766_, v_fvarId_1828_);
return v___x_1829_;
}
else
{
lean_object* v___x_1830_; 
lean_dec_ref(v_e_1766_);
v___x_1830_ = lean_box(1);
return v___x_1830_;
}
}
case 15:
{
lean_object* v_fvarId_1831_; lean_object* v___x_1832_; 
v_fvarId_1831_ = lean_ctor_get(v_e_1766_, 0);
lean_inc(v_fvarId_1831_);
v___x_1832_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1765_, v_fvarId_1831_, v_translator_1767_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_fvarId_1833_; lean_object* v___x_1834_; 
v_fvarId_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_fvarId_1833_);
lean_dec_ref(v___x_1832_);
v___x_1834_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_1764_, v_e_1766_, v_fvarId_1833_);
return v___x_1834_;
}
else
{
lean_object* v___x_1835_; 
lean_dec_ref(v_e_1766_);
v___x_1835_ = lean_box(1);
return v___x_1835_;
}
}
default: 
{
return v_e_1766_;
}
}
v___jp_1768_:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1765_, v_fvarId_1769_, v_translator_1767_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_fvarId_1771_; lean_object* v___x_1772_; 
v_fvarId_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_fvarId_1771_);
lean_dec_ref(v___x_1770_);
v___x_1772_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1764_, v_e_1766_, v_fvarId_1771_);
return v___x_1772_;
}
else
{
lean_object* v___x_1773_; 
lean_dec(v_e_1766_);
v___x_1773_ = lean_box(1);
return v___x_1773_;
}
}
v___jp_1774_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1764_, v_s_1765_, v_args_1775_, v_translator_1767_);
v___x_1777_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1764_, v_e_1766_, v___x_1776_);
return v___x_1777_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp___boxed(lean_object* v_pu_1836_, lean_object* v_s_1837_, lean_object* v_e_1838_, lean_object* v_translator_1839_){
_start:
{
uint8_t v_pu_boxed_1840_; uint8_t v_translator_boxed_1841_; lean_object* v_res_1842_; 
v_pu_boxed_1840_ = lean_unbox(v_pu_1836_);
v_translator_boxed_1841_ = lean_unbox(v_translator_1839_);
v_res_1842_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_boxed_1840_, v_s_1837_, v_e_1838_, v_translator_boxed_1841_);
lean_dec_ref(v_s_1837_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___redArg(lean_object* v_inst_1843_, lean_object* v_inst_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = lean_apply_2(v_inst_1843_, lean_box(0), v_inst_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(uint8_t v_pu_1846_, uint8_t v_t_1847_, lean_object* v_m_1848_, lean_object* v_n_1849_, lean_object* v_inst_1850_, lean_object* v_inst_1851_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = lean_apply_2(v_inst_1850_, lean_box(0), v_inst_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___boxed(lean_object* v_pu_1853_, lean_object* v_t_1854_, lean_object* v_m_1855_, lean_object* v_n_1856_, lean_object* v_inst_1857_, lean_object* v_inst_1858_){
_start:
{
uint8_t v_pu_boxed_1859_; uint8_t v_t_boxed_1860_; lean_object* v_res_1861_; 
v_pu_boxed_1859_ = lean_unbox(v_pu_1853_);
v_t_boxed_1860_ = lean_unbox(v_t_1854_);
v_res_1861_ = l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(v_pu_boxed_1859_, v_t_boxed_1860_, v_m_1855_, v_n_1856_, v_inst_1857_, v_inst_1858_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0(lean_object* v_inst_1862_, lean_object* v_inst_1863_, lean_object* v_f_1864_){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = lean_apply_1(v_inst_1862_, v_f_1864_);
v___x_1866_ = lean_apply_2(v_inst_1863_, lean_box(0), v___x_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg(lean_object* v_inst_1867_, lean_object* v_inst_1868_){
_start:
{
lean_object* v___f_1869_; 
v___f_1869_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1869_, 0, v_inst_1868_);
lean_closure_set(v___f_1869_, 1, v_inst_1867_);
return v___f_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(uint8_t v_pu_1870_, lean_object* v_m_1871_, lean_object* v_n_1872_, lean_object* v_inst_1873_, lean_object* v_inst_1874_){
_start:
{
lean_object* v___f_1875_; 
v___f_1875_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1875_, 0, v_inst_1874_);
lean_closure_set(v___f_1875_, 1, v_inst_1873_);
return v___f_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___boxed(lean_object* v_pu_1876_, lean_object* v_m_1877_, lean_object* v_n_1878_, lean_object* v_inst_1879_, lean_object* v_inst_1880_){
_start:
{
uint8_t v_pu_boxed_1881_; lean_object* v_res_1882_; 
v_pu_boxed_1881_ = lean_unbox(v_pu_1876_);
v_res_1882_ = l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(v_pu_boxed_1881_, v_m_1877_, v_n_1878_, v_inst_1879_, v_inst_1880_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___lam__0(lean_object* v___x_1883_, lean_object* v___x_1884_, lean_object* v_fvarId_1885_, lean_object* v_arg_1886_, lean_object* v_s_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1883_, v___x_1884_, v_s_1887_, v_fvarId_1885_, v_arg_1886_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg(lean_object* v_inst_1891_, lean_object* v_fvarId_1892_, lean_object* v_arg_1893_){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___f_1896_; lean_object* v___x_1897_; 
v___x_1894_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1895_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1896_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1896_, 0, v___x_1894_);
lean_closure_set(v___f_1896_, 1, v___x_1895_);
lean_closure_set(v___f_1896_, 2, v_fvarId_1892_);
lean_closure_set(v___f_1896_, 3, v_arg_1893_);
v___x_1897_ = lean_apply_1(v_inst_1891_, v___f_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst(lean_object* v_m_1898_, uint8_t v_pu_1899_, lean_object* v_inst_1900_, lean_object* v_fvarId_1901_, lean_object* v_arg_1902_){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___f_1905_; lean_object* v___x_1906_; 
v___x_1903_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1904_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1905_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1905_, 0, v___x_1903_);
lean_closure_set(v___f_1905_, 1, v___x_1904_);
lean_closure_set(v___f_1905_, 2, v_fvarId_1901_);
lean_closure_set(v___f_1905_, 3, v_arg_1902_);
v___x_1906_ = lean_apply_1(v_inst_1900_, v___f_1905_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___boxed(lean_object* v_m_1907_, lean_object* v_pu_1908_, lean_object* v_inst_1909_, lean_object* v_fvarId_1910_, lean_object* v_arg_1911_){
_start:
{
uint8_t v_pu_boxed_1912_; lean_object* v_res_1913_; 
v_pu_boxed_1912_ = lean_unbox(v_pu_1908_);
v_res_1913_ = l_Lean_Compiler_LCNF_addSubst(v_m_1907_, v_pu_boxed_1912_, v_inst_1909_, v_fvarId_1910_, v_arg_1911_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0(lean_object* v_fvarId_x27_1914_, lean_object* v___x_1915_, lean_object* v___x_1916_, lean_object* v_fvarId_1917_, lean_object* v_s_1918_){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1919_, 0, v_fvarId_x27_1914_);
v___x_1920_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1915_, v___x_1916_, v_s_1918_, v_fvarId_1917_, v___x_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg(lean_object* v_inst_1921_, lean_object* v_fvarId_1922_, lean_object* v_fvarId_x27_1923_){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___f_1926_; lean_object* v___x_1927_; 
v___x_1924_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1925_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1926_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1926_, 0, v_fvarId_x27_1923_);
lean_closure_set(v___f_1926_, 1, v___x_1924_);
lean_closure_set(v___f_1926_, 2, v___x_1925_);
lean_closure_set(v___f_1926_, 3, v_fvarId_1922_);
v___x_1927_ = lean_apply_1(v_inst_1921_, v___f_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst(lean_object* v_m_1928_, uint8_t v_ph_1929_, lean_object* v_inst_1930_, lean_object* v_fvarId_1931_, lean_object* v_fvarId_x27_1932_){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___f_1935_; lean_object* v___x_1936_; 
v___x_1933_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1934_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1935_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1935_, 0, v_fvarId_x27_1932_);
lean_closure_set(v___f_1935_, 1, v___x_1933_);
lean_closure_set(v___f_1935_, 2, v___x_1934_);
lean_closure_set(v___f_1935_, 3, v_fvarId_1931_);
v___x_1936_ = lean_apply_1(v_inst_1930_, v___f_1935_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___boxed(lean_object* v_m_1937_, lean_object* v_ph_1938_, lean_object* v_inst_1939_, lean_object* v_fvarId_1940_, lean_object* v_fvarId_x27_1941_){
_start:
{
uint8_t v_ph_boxed_1942_; lean_object* v_res_1943_; 
v_ph_boxed_1942_ = lean_unbox(v_ph_1938_);
v_res_1943_ = l_Lean_Compiler_LCNF_addFVarSubst(v_m_1937_, v_ph_boxed_1942_, v_inst_1939_, v_fvarId_1940_, v_fvarId_x27_1941_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(lean_object* v_fvarId_1944_, uint8_t v_t_1945_, lean_object* v_toPure_1946_, lean_object* v_____do__lift_1947_){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_____do__lift_1947_, v_fvarId_1944_, v_t_1945_);
v___x_1949_ = lean_apply_2(v_toPure_1946_, lean_box(0), v___x_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed(lean_object* v_fvarId_1950_, lean_object* v_t_1951_, lean_object* v_toPure_1952_, lean_object* v_____do__lift_1953_){
_start:
{
uint8_t v_t_boxed_1954_; lean_object* v_res_1955_; 
v_t_boxed_1954_ = lean_unbox(v_t_1951_);
v_res_1955_ = l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(v_fvarId_1950_, v_t_boxed_1954_, v_toPure_1952_, v_____do__lift_1953_);
lean_dec_ref(v_____do__lift_1953_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg(uint8_t v_t_1956_, lean_object* v_inst_1957_, lean_object* v_inst_1958_, lean_object* v_fvarId_1959_){
_start:
{
lean_object* v_toApplicative_1960_; lean_object* v_toBind_1961_; lean_object* v_toPure_1962_; lean_object* v___x_1963_; lean_object* v___f_1964_; lean_object* v___x_1965_; 
v_toApplicative_1960_ = lean_ctor_get(v_inst_1958_, 0);
lean_inc_ref(v_toApplicative_1960_);
v_toBind_1961_ = lean_ctor_get(v_inst_1958_, 1);
lean_inc(v_toBind_1961_);
lean_dec_ref(v_inst_1958_);
v_toPure_1962_ = lean_ctor_get(v_toApplicative_1960_, 1);
lean_inc(v_toPure_1962_);
lean_dec_ref(v_toApplicative_1960_);
v___x_1963_ = lean_box(v_t_1956_);
v___f_1964_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1964_, 0, v_fvarId_1959_);
lean_closure_set(v___f_1964_, 1, v___x_1963_);
lean_closure_set(v___f_1964_, 2, v_toPure_1962_);
v___x_1965_ = lean_apply_4(v_toBind_1961_, lean_box(0), lean_box(0), v_inst_1957_, v___f_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___boxed(lean_object* v_t_1966_, lean_object* v_inst_1967_, lean_object* v_inst_1968_, lean_object* v_fvarId_1969_){
_start:
{
uint8_t v_t_boxed_1970_; lean_object* v_res_1971_; 
v_t_boxed_1970_ = lean_unbox(v_t_1966_);
v_res_1971_ = l_Lean_Compiler_LCNF_normFVar___redArg(v_t_boxed_1970_, v_inst_1967_, v_inst_1968_, v_fvarId_1969_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar(lean_object* v_m_1972_, uint8_t v_pu_1973_, uint8_t v_t_1974_, lean_object* v_inst_1975_, lean_object* v_inst_1976_, lean_object* v_fvarId_1977_){
_start:
{
lean_object* v_toApplicative_1978_; lean_object* v_toBind_1979_; lean_object* v_toPure_1980_; lean_object* v___x_1981_; lean_object* v___f_1982_; lean_object* v___x_1983_; 
v_toApplicative_1978_ = lean_ctor_get(v_inst_1976_, 0);
lean_inc_ref(v_toApplicative_1978_);
v_toBind_1979_ = lean_ctor_get(v_inst_1976_, 1);
lean_inc(v_toBind_1979_);
lean_dec_ref(v_inst_1976_);
v_toPure_1980_ = lean_ctor_get(v_toApplicative_1978_, 1);
lean_inc(v_toPure_1980_);
lean_dec_ref(v_toApplicative_1978_);
v___x_1981_ = lean_box(v_t_1974_);
v___f_1982_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1982_, 0, v_fvarId_1977_);
lean_closure_set(v___f_1982_, 1, v___x_1981_);
lean_closure_set(v___f_1982_, 2, v_toPure_1980_);
v___x_1983_ = lean_apply_4(v_toBind_1979_, lean_box(0), lean_box(0), v_inst_1975_, v___f_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___boxed(lean_object* v_m_1984_, lean_object* v_pu_1985_, lean_object* v_t_1986_, lean_object* v_inst_1987_, lean_object* v_inst_1988_, lean_object* v_fvarId_1989_){
_start:
{
uint8_t v_pu_boxed_1990_; uint8_t v_t_boxed_1991_; lean_object* v_res_1992_; 
v_pu_boxed_1990_ = lean_unbox(v_pu_1985_);
v_t_boxed_1991_ = lean_unbox(v_t_1986_);
v_res_1992_ = l_Lean_Compiler_LCNF_normFVar(v_m_1984_, v_pu_boxed_1990_, v_t_boxed_1991_, v_inst_1987_, v_inst_1988_, v_fvarId_1989_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(uint8_t v_pu_1993_, uint8_t v_t_1994_, lean_object* v_e_1995_, lean_object* v_toPure_1996_, lean_object* v_____do__lift_1997_){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1993_, v_____do__lift_1997_, v_t_1994_, v_e_1995_);
v___x_1999_ = lean_apply_2(v_toPure_1996_, lean_box(0), v___x_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed(lean_object* v_pu_2000_, lean_object* v_t_2001_, lean_object* v_e_2002_, lean_object* v_toPure_2003_, lean_object* v_____do__lift_2004_){
_start:
{
uint8_t v_pu_boxed_2005_; uint8_t v_t_boxed_2006_; lean_object* v_res_2007_; 
v_pu_boxed_2005_ = lean_unbox(v_pu_2000_);
v_t_boxed_2006_ = lean_unbox(v_t_2001_);
v_res_2007_ = l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(v_pu_boxed_2005_, v_t_boxed_2006_, v_e_2002_, v_toPure_2003_, v_____do__lift_2004_);
lean_dec_ref(v_____do__lift_2004_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg(uint8_t v_pu_2008_, uint8_t v_t_2009_, lean_object* v_inst_2010_, lean_object* v_inst_2011_, lean_object* v_e_2012_){
_start:
{
lean_object* v_toApplicative_2013_; lean_object* v_toBind_2014_; lean_object* v_toPure_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___f_2018_; lean_object* v___x_2019_; 
v_toApplicative_2013_ = lean_ctor_get(v_inst_2011_, 0);
lean_inc_ref(v_toApplicative_2013_);
v_toBind_2014_ = lean_ctor_get(v_inst_2011_, 1);
lean_inc(v_toBind_2014_);
lean_dec_ref(v_inst_2011_);
v_toPure_2015_ = lean_ctor_get(v_toApplicative_2013_, 1);
lean_inc(v_toPure_2015_);
lean_dec_ref(v_toApplicative_2013_);
v___x_2016_ = lean_box(v_pu_2008_);
v___x_2017_ = lean_box(v_t_2009_);
v___f_2018_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2018_, 0, v___x_2016_);
lean_closure_set(v___f_2018_, 1, v___x_2017_);
lean_closure_set(v___f_2018_, 2, v_e_2012_);
lean_closure_set(v___f_2018_, 3, v_toPure_2015_);
v___x_2019_ = lean_apply_4(v_toBind_2014_, lean_box(0), lean_box(0), v_inst_2010_, v___f_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___boxed(lean_object* v_pu_2020_, lean_object* v_t_2021_, lean_object* v_inst_2022_, lean_object* v_inst_2023_, lean_object* v_e_2024_){
_start:
{
uint8_t v_pu_boxed_2025_; uint8_t v_t_boxed_2026_; lean_object* v_res_2027_; 
v_pu_boxed_2025_ = lean_unbox(v_pu_2020_);
v_t_boxed_2026_ = lean_unbox(v_t_2021_);
v_res_2027_ = l_Lean_Compiler_LCNF_normExpr___redArg(v_pu_boxed_2025_, v_t_boxed_2026_, v_inst_2022_, v_inst_2023_, v_e_2024_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr(lean_object* v_m_2028_, uint8_t v_pu_2029_, uint8_t v_t_2030_, lean_object* v_inst_2031_, lean_object* v_inst_2032_, lean_object* v_e_2033_){
_start:
{
lean_object* v_toApplicative_2034_; lean_object* v_toBind_2035_; lean_object* v_toPure_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___f_2039_; lean_object* v___x_2040_; 
v_toApplicative_2034_ = lean_ctor_get(v_inst_2032_, 0);
lean_inc_ref(v_toApplicative_2034_);
v_toBind_2035_ = lean_ctor_get(v_inst_2032_, 1);
lean_inc(v_toBind_2035_);
lean_dec_ref(v_inst_2032_);
v_toPure_2036_ = lean_ctor_get(v_toApplicative_2034_, 1);
lean_inc(v_toPure_2036_);
lean_dec_ref(v_toApplicative_2034_);
v___x_2037_ = lean_box(v_pu_2029_);
v___x_2038_ = lean_box(v_t_2030_);
v___f_2039_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2039_, 0, v___x_2037_);
lean_closure_set(v___f_2039_, 1, v___x_2038_);
lean_closure_set(v___f_2039_, 2, v_e_2033_);
lean_closure_set(v___f_2039_, 3, v_toPure_2036_);
v___x_2040_ = lean_apply_4(v_toBind_2035_, lean_box(0), lean_box(0), v_inst_2031_, v___f_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___boxed(lean_object* v_m_2041_, lean_object* v_pu_2042_, lean_object* v_t_2043_, lean_object* v_inst_2044_, lean_object* v_inst_2045_, lean_object* v_e_2046_){
_start:
{
uint8_t v_pu_boxed_2047_; uint8_t v_t_boxed_2048_; lean_object* v_res_2049_; 
v_pu_boxed_2047_ = lean_unbox(v_pu_2042_);
v_t_boxed_2048_ = lean_unbox(v_t_2043_);
v_res_2049_ = l_Lean_Compiler_LCNF_normExpr(v_m_2041_, v_pu_boxed_2047_, v_t_boxed_2048_, v_inst_2044_, v_inst_2045_, v_e_2046_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0(uint8_t v_pu_2050_, lean_object* v_arg_2051_, uint8_t v_t_2052_, lean_object* v_toPure_2053_, lean_object* v_____do__lift_2054_){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2050_, v_____do__lift_2054_, v_arg_2051_, v_t_2052_);
v___x_2056_ = lean_apply_2(v_toPure_2053_, lean_box(0), v___x_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed(lean_object* v_pu_2057_, lean_object* v_arg_2058_, lean_object* v_t_2059_, lean_object* v_toPure_2060_, lean_object* v_____do__lift_2061_){
_start:
{
uint8_t v_pu_boxed_2062_; uint8_t v_t_boxed_2063_; lean_object* v_res_2064_; 
v_pu_boxed_2062_ = lean_unbox(v_pu_2057_);
v_t_boxed_2063_ = lean_unbox(v_t_2059_);
v_res_2064_ = l_Lean_Compiler_LCNF_normArg___redArg___lam__0(v_pu_boxed_2062_, v_arg_2058_, v_t_boxed_2063_, v_toPure_2060_, v_____do__lift_2061_);
lean_dec_ref(v_____do__lift_2061_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg(uint8_t v_pu_2065_, uint8_t v_t_2066_, lean_object* v_inst_2067_, lean_object* v_inst_2068_, lean_object* v_arg_2069_){
_start:
{
lean_object* v_toApplicative_2070_; lean_object* v_toBind_2071_; lean_object* v_toPure_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___f_2075_; lean_object* v___x_2076_; 
v_toApplicative_2070_ = lean_ctor_get(v_inst_2068_, 0);
lean_inc_ref(v_toApplicative_2070_);
v_toBind_2071_ = lean_ctor_get(v_inst_2068_, 1);
lean_inc(v_toBind_2071_);
lean_dec_ref(v_inst_2068_);
v_toPure_2072_ = lean_ctor_get(v_toApplicative_2070_, 1);
lean_inc(v_toPure_2072_);
lean_dec_ref(v_toApplicative_2070_);
v___x_2073_ = lean_box(v_pu_2065_);
v___x_2074_ = lean_box(v_t_2066_);
v___f_2075_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2075_, 0, v___x_2073_);
lean_closure_set(v___f_2075_, 1, v_arg_2069_);
lean_closure_set(v___f_2075_, 2, v___x_2074_);
lean_closure_set(v___f_2075_, 3, v_toPure_2072_);
v___x_2076_ = lean_apply_4(v_toBind_2071_, lean_box(0), lean_box(0), v_inst_2067_, v___f_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___boxed(lean_object* v_pu_2077_, lean_object* v_t_2078_, lean_object* v_inst_2079_, lean_object* v_inst_2080_, lean_object* v_arg_2081_){
_start:
{
uint8_t v_pu_boxed_2082_; uint8_t v_t_boxed_2083_; lean_object* v_res_2084_; 
v_pu_boxed_2082_ = lean_unbox(v_pu_2077_);
v_t_boxed_2083_ = lean_unbox(v_t_2078_);
v_res_2084_ = l_Lean_Compiler_LCNF_normArg___redArg(v_pu_boxed_2082_, v_t_boxed_2083_, v_inst_2079_, v_inst_2080_, v_arg_2081_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg(lean_object* v_m_2085_, uint8_t v_pu_2086_, uint8_t v_t_2087_, lean_object* v_inst_2088_, lean_object* v_inst_2089_, lean_object* v_arg_2090_){
_start:
{
lean_object* v_toApplicative_2091_; lean_object* v_toBind_2092_; lean_object* v_toPure_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___f_2096_; lean_object* v___x_2097_; 
v_toApplicative_2091_ = lean_ctor_get(v_inst_2089_, 0);
lean_inc_ref(v_toApplicative_2091_);
v_toBind_2092_ = lean_ctor_get(v_inst_2089_, 1);
lean_inc(v_toBind_2092_);
lean_dec_ref(v_inst_2089_);
v_toPure_2093_ = lean_ctor_get(v_toApplicative_2091_, 1);
lean_inc(v_toPure_2093_);
lean_dec_ref(v_toApplicative_2091_);
v___x_2094_ = lean_box(v_pu_2086_);
v___x_2095_ = lean_box(v_t_2087_);
v___f_2096_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2096_, 0, v___x_2094_);
lean_closure_set(v___f_2096_, 1, v_arg_2090_);
lean_closure_set(v___f_2096_, 2, v___x_2095_);
lean_closure_set(v___f_2096_, 3, v_toPure_2093_);
v___x_2097_ = lean_apply_4(v_toBind_2092_, lean_box(0), lean_box(0), v_inst_2088_, v___f_2096_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___boxed(lean_object* v_m_2098_, lean_object* v_pu_2099_, lean_object* v_t_2100_, lean_object* v_inst_2101_, lean_object* v_inst_2102_, lean_object* v_arg_2103_){
_start:
{
uint8_t v_pu_boxed_2104_; uint8_t v_t_boxed_2105_; lean_object* v_res_2106_; 
v_pu_boxed_2104_ = lean_unbox(v_pu_2099_);
v_t_boxed_2105_ = lean_unbox(v_t_2100_);
v_res_2106_ = l_Lean_Compiler_LCNF_normArg(v_m_2098_, v_pu_boxed_2104_, v_t_boxed_2105_, v_inst_2101_, v_inst_2102_, v_arg_2103_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(uint8_t v_pu_2107_, lean_object* v_e_2108_, uint8_t v_t_2109_, lean_object* v_toPure_2110_, lean_object* v_____do__lift_2111_){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_2107_, v_____do__lift_2111_, v_e_2108_, v_t_2109_);
v___x_2113_ = lean_apply_2(v_toPure_2110_, lean_box(0), v___x_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed(lean_object* v_pu_2114_, lean_object* v_e_2115_, lean_object* v_t_2116_, lean_object* v_toPure_2117_, lean_object* v_____do__lift_2118_){
_start:
{
uint8_t v_pu_boxed_2119_; uint8_t v_t_boxed_2120_; lean_object* v_res_2121_; 
v_pu_boxed_2119_ = lean_unbox(v_pu_2114_);
v_t_boxed_2120_ = lean_unbox(v_t_2116_);
v_res_2121_ = l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(v_pu_boxed_2119_, v_e_2115_, v_t_boxed_2120_, v_toPure_2117_, v_____do__lift_2118_);
lean_dec_ref(v_____do__lift_2118_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg(uint8_t v_pu_2122_, uint8_t v_t_2123_, lean_object* v_inst_2124_, lean_object* v_inst_2125_, lean_object* v_e_2126_){
_start:
{
lean_object* v_toApplicative_2127_; lean_object* v_toBind_2128_; lean_object* v_toPure_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___f_2132_; lean_object* v___x_2133_; 
v_toApplicative_2127_ = lean_ctor_get(v_inst_2125_, 0);
lean_inc_ref(v_toApplicative_2127_);
v_toBind_2128_ = lean_ctor_get(v_inst_2125_, 1);
lean_inc(v_toBind_2128_);
lean_dec_ref(v_inst_2125_);
v_toPure_2129_ = lean_ctor_get(v_toApplicative_2127_, 1);
lean_inc(v_toPure_2129_);
lean_dec_ref(v_toApplicative_2127_);
v___x_2130_ = lean_box(v_pu_2122_);
v___x_2131_ = lean_box(v_t_2123_);
v___f_2132_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2132_, 0, v___x_2130_);
lean_closure_set(v___f_2132_, 1, v_e_2126_);
lean_closure_set(v___f_2132_, 2, v___x_2131_);
lean_closure_set(v___f_2132_, 3, v_toPure_2129_);
v___x_2133_ = lean_apply_4(v_toBind_2128_, lean_box(0), lean_box(0), v_inst_2124_, v___f_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___boxed(lean_object* v_pu_2134_, lean_object* v_t_2135_, lean_object* v_inst_2136_, lean_object* v_inst_2137_, lean_object* v_e_2138_){
_start:
{
uint8_t v_pu_boxed_2139_; uint8_t v_t_boxed_2140_; lean_object* v_res_2141_; 
v_pu_boxed_2139_ = lean_unbox(v_pu_2134_);
v_t_boxed_2140_ = lean_unbox(v_t_2135_);
v_res_2141_ = l_Lean_Compiler_LCNF_normLetValue___redArg(v_pu_boxed_2139_, v_t_boxed_2140_, v_inst_2136_, v_inst_2137_, v_e_2138_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue(lean_object* v_m_2142_, uint8_t v_pu_2143_, uint8_t v_t_2144_, lean_object* v_inst_2145_, lean_object* v_inst_2146_, lean_object* v_e_2147_){
_start:
{
lean_object* v_toApplicative_2148_; lean_object* v_toBind_2149_; lean_object* v_toPure_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___f_2153_; lean_object* v___x_2154_; 
v_toApplicative_2148_ = lean_ctor_get(v_inst_2146_, 0);
lean_inc_ref(v_toApplicative_2148_);
v_toBind_2149_ = lean_ctor_get(v_inst_2146_, 1);
lean_inc(v_toBind_2149_);
lean_dec_ref(v_inst_2146_);
v_toPure_2150_ = lean_ctor_get(v_toApplicative_2148_, 1);
lean_inc(v_toPure_2150_);
lean_dec_ref(v_toApplicative_2148_);
v___x_2151_ = lean_box(v_pu_2143_);
v___x_2152_ = lean_box(v_t_2144_);
v___f_2153_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2153_, 0, v___x_2151_);
lean_closure_set(v___f_2153_, 1, v_e_2147_);
lean_closure_set(v___f_2153_, 2, v___x_2152_);
lean_closure_set(v___f_2153_, 3, v_toPure_2150_);
v___x_2154_ = lean_apply_4(v_toBind_2149_, lean_box(0), lean_box(0), v_inst_2145_, v___f_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___boxed(lean_object* v_m_2155_, lean_object* v_pu_2156_, lean_object* v_t_2157_, lean_object* v_inst_2158_, lean_object* v_inst_2159_, lean_object* v_e_2160_){
_start:
{
uint8_t v_pu_boxed_2161_; uint8_t v_t_boxed_2162_; lean_object* v_res_2163_; 
v_pu_boxed_2161_ = lean_unbox(v_pu_2156_);
v_t_boxed_2162_ = lean_unbox(v_t_2157_);
v_res_2163_ = l_Lean_Compiler_LCNF_normLetValue(v_m_2155_, v_pu_boxed_2161_, v_t_boxed_2162_, v_inst_2158_, v_inst_2159_, v_e_2160_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore(uint8_t v_pu_2164_, lean_object* v_s_2165_, lean_object* v_e_2166_, uint8_t v_translator_2167_){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2164_, v_s_2165_, v_translator_2167_, v_e_2166_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore___boxed(lean_object* v_pu_2169_, lean_object* v_s_2170_, lean_object* v_e_2171_, lean_object* v_translator_2172_){
_start:
{
uint8_t v_pu_boxed_2173_; uint8_t v_translator_boxed_2174_; lean_object* v_res_2175_; 
v_pu_boxed_2173_ = lean_unbox(v_pu_2169_);
v_translator_boxed_2174_ = lean_unbox(v_translator_2172_);
v_res_2175_ = l_Lean_Compiler_LCNF_normExprCore(v_pu_boxed_2173_, v_s_2170_, v_e_2171_, v_translator_boxed_2174_);
lean_dec_ref(v_s_2170_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(uint8_t v_pu_2176_, lean_object* v_args_2177_, uint8_t v_t_2178_, lean_object* v_toPure_2179_, lean_object* v_____do__lift_2180_){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_2176_, v_____do__lift_2180_, v_args_2177_, v_t_2178_);
v___x_2182_ = lean_apply_2(v_toPure_2179_, lean_box(0), v___x_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed(lean_object* v_pu_2183_, lean_object* v_args_2184_, lean_object* v_t_2185_, lean_object* v_toPure_2186_, lean_object* v_____do__lift_2187_){
_start:
{
uint8_t v_pu_boxed_2188_; uint8_t v_t_boxed_2189_; lean_object* v_res_2190_; 
v_pu_boxed_2188_ = lean_unbox(v_pu_2183_);
v_t_boxed_2189_ = lean_unbox(v_t_2185_);
v_res_2190_ = l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(v_pu_boxed_2188_, v_args_2184_, v_t_boxed_2189_, v_toPure_2186_, v_____do__lift_2187_);
lean_dec_ref(v_____do__lift_2187_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg(uint8_t v_pu_2191_, uint8_t v_t_2192_, lean_object* v_inst_2193_, lean_object* v_inst_2194_, lean_object* v_args_2195_){
_start:
{
lean_object* v_toApplicative_2196_; lean_object* v_toBind_2197_; lean_object* v_toPure_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___f_2201_; lean_object* v___x_2202_; 
v_toApplicative_2196_ = lean_ctor_get(v_inst_2194_, 0);
lean_inc_ref(v_toApplicative_2196_);
v_toBind_2197_ = lean_ctor_get(v_inst_2194_, 1);
lean_inc(v_toBind_2197_);
lean_dec_ref(v_inst_2194_);
v_toPure_2198_ = lean_ctor_get(v_toApplicative_2196_, 1);
lean_inc(v_toPure_2198_);
lean_dec_ref(v_toApplicative_2196_);
v___x_2199_ = lean_box(v_pu_2191_);
v___x_2200_ = lean_box(v_t_2192_);
v___f_2201_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2201_, 0, v___x_2199_);
lean_closure_set(v___f_2201_, 1, v_args_2195_);
lean_closure_set(v___f_2201_, 2, v___x_2200_);
lean_closure_set(v___f_2201_, 3, v_toPure_2198_);
v___x_2202_ = lean_apply_4(v_toBind_2197_, lean_box(0), lean_box(0), v_inst_2193_, v___f_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___boxed(lean_object* v_pu_2203_, lean_object* v_t_2204_, lean_object* v_inst_2205_, lean_object* v_inst_2206_, lean_object* v_args_2207_){
_start:
{
uint8_t v_pu_boxed_2208_; uint8_t v_t_boxed_2209_; lean_object* v_res_2210_; 
v_pu_boxed_2208_ = lean_unbox(v_pu_2203_);
v_t_boxed_2209_ = lean_unbox(v_t_2204_);
v_res_2210_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_boxed_2208_, v_t_boxed_2209_, v_inst_2205_, v_inst_2206_, v_args_2207_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs(lean_object* v_m_2211_, uint8_t v_pu_2212_, uint8_t v_t_2213_, lean_object* v_inst_2214_, lean_object* v_inst_2215_, lean_object* v_args_2216_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_2212_, v_t_2213_, v_inst_2214_, v_inst_2215_, v_args_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___boxed(lean_object* v_m_2218_, lean_object* v_pu_2219_, lean_object* v_t_2220_, lean_object* v_inst_2221_, lean_object* v_inst_2222_, lean_object* v_args_2223_){
_start:
{
uint8_t v_pu_boxed_2224_; uint8_t v_t_boxed_2225_; lean_object* v_res_2226_; 
v_pu_boxed_2224_ = lean_unbox(v_pu_2219_);
v_t_boxed_2225_ = lean_unbox(v_t_2220_);
v_res_2226_ = l_Lean_Compiler_LCNF_normArgs(v_m_2218_, v_pu_boxed_2224_, v_t_boxed_2225_, v_inst_2221_, v_inst_2222_, v_args_2223_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object* v_binderName_2227_, lean_object* v_a_2228_){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v_lctx_2232_; lean_object* v_nextIdx_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2246_; 
v___x_2230_ = lean_st_ref_get(v_a_2228_);
v___x_2231_ = lean_st_ref_take(v_a_2228_);
v_lctx_2232_ = lean_ctor_get(v___x_2231_, 0);
v_nextIdx_2233_ = lean_ctor_get(v___x_2231_, 1);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2235_ = v___x_2231_;
v_isShared_2236_ = v_isSharedCheck_2246_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_nextIdx_2233_);
lean_inc(v_lctx_2232_);
lean_dec(v___x_2231_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2246_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2240_; 
v___x_2237_ = lean_unsigned_to_nat(1u);
v___x_2238_ = lean_nat_add(v_nextIdx_2233_, v___x_2237_);
lean_dec(v_nextIdx_2233_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 1, v___x_2238_);
v___x_2240_ = v___x_2235_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_lctx_2232_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
lean_object* v___x_2241_; lean_object* v_nextIdx_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2241_ = lean_st_ref_set(v_a_2228_, v___x_2240_);
v_nextIdx_2242_ = lean_ctor_get(v___x_2230_, 1);
lean_inc(v_nextIdx_2242_);
lean_dec(v___x_2230_);
v___x_2243_ = l_Lean_Name_num___override(v_binderName_2227_, v_nextIdx_2242_);
v___x_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
return v___x_2244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg___boxed(lean_object* v_binderName_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2247_, v_a_2248_);
lean_dec(v_a_2248_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object* v_binderName_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2251_, v_a_2253_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___boxed(lean_object* v_binderName_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_Compiler_LCNF_mkFreshBinderName(v_binderName_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
lean_dec(v_a_2262_);
lean_dec_ref(v_a_2261_);
lean_dec(v_a_2260_);
lean_dec_ref(v_a_2259_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(lean_object* v_binderName_2265_, lean_object* v_baseName_2266_, lean_object* v_a_2267_){
_start:
{
uint8_t v___x_2269_; 
v___x_2269_ = l_Lean_Name_isAnonymous(v_binderName_2265_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; 
lean_dec(v_baseName_2266_);
v___x_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2270_, 0, v_binderName_2265_);
return v___x_2270_;
}
else
{
lean_object* v___x_2271_; 
lean_dec(v_binderName_2265_);
v___x_2271_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_baseName_2266_, v_a_2267_);
return v___x_2271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg___boxed(lean_object* v_binderName_2272_, lean_object* v_baseName_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2272_, v_baseName_2273_, v_a_2274_);
lean_dec(v_a_2274_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous(lean_object* v_binderName_2277_, lean_object* v_baseName_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2277_, v_baseName_2278_, v_a_2280_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___boxed(lean_object* v_binderName_2285_, lean_object* v_baseName_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_Compiler_LCNF_ensureNotAnonymous(v_binderName_2285_, v_baseName_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(lean_object* v___y_2293_){
_start:
{
lean_object* v___x_2295_; lean_object* v_ngen_2296_; lean_object* v_namePrefix_2297_; lean_object* v_idx_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2327_; 
v___x_2295_ = lean_st_ref_get(v___y_2293_);
v_ngen_2296_ = lean_ctor_get(v___x_2295_, 2);
lean_inc_ref(v_ngen_2296_);
lean_dec(v___x_2295_);
v_namePrefix_2297_ = lean_ctor_get(v_ngen_2296_, 0);
v_idx_2298_ = lean_ctor_get(v_ngen_2296_, 1);
v_isSharedCheck_2327_ = !lean_is_exclusive(v_ngen_2296_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2300_ = v_ngen_2296_;
v_isShared_2301_ = v_isSharedCheck_2327_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_idx_2298_);
lean_inc(v_namePrefix_2297_);
lean_dec(v_ngen_2296_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2327_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; lean_object* v_env_2303_; lean_object* v_nextMacroScope_2304_; lean_object* v_auxDeclNGen_2305_; lean_object* v_traceState_2306_; lean_object* v_cache_2307_; lean_object* v_messages_2308_; lean_object* v_infoState_2309_; lean_object* v_snapshotTasks_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2325_; 
v___x_2302_ = lean_st_ref_take(v___y_2293_);
v_env_2303_ = lean_ctor_get(v___x_2302_, 0);
v_nextMacroScope_2304_ = lean_ctor_get(v___x_2302_, 1);
v_auxDeclNGen_2305_ = lean_ctor_get(v___x_2302_, 3);
v_traceState_2306_ = lean_ctor_get(v___x_2302_, 4);
v_cache_2307_ = lean_ctor_get(v___x_2302_, 5);
v_messages_2308_ = lean_ctor_get(v___x_2302_, 6);
v_infoState_2309_ = lean_ctor_get(v___x_2302_, 7);
v_snapshotTasks_2310_ = lean_ctor_get(v___x_2302_, 8);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; 
v_unused_2326_ = lean_ctor_get(v___x_2302_, 2);
lean_dec(v_unused_2326_);
v___x_2312_ = v___x_2302_;
v_isShared_2313_ = v_isSharedCheck_2325_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_snapshotTasks_2310_);
lean_inc(v_infoState_2309_);
lean_inc(v_messages_2308_);
lean_inc(v_cache_2307_);
lean_inc(v_traceState_2306_);
lean_inc(v_auxDeclNGen_2305_);
lean_inc(v_nextMacroScope_2304_);
lean_inc(v_env_2303_);
lean_dec(v___x_2302_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2325_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v_r_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2318_; 
lean_inc(v_idx_2298_);
lean_inc(v_namePrefix_2297_);
v_r_2314_ = l_Lean_Name_num___override(v_namePrefix_2297_, v_idx_2298_);
v___x_2315_ = lean_unsigned_to_nat(1u);
v___x_2316_ = lean_nat_add(v_idx_2298_, v___x_2315_);
lean_dec(v_idx_2298_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 1, v___x_2316_);
v___x_2318_ = v___x_2300_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_namePrefix_2297_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v___x_2316_);
v___x_2318_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
lean_object* v___x_2320_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 2, v___x_2318_);
v___x_2320_ = v___x_2312_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_env_2303_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_nextMacroScope_2304_);
lean_ctor_set(v_reuseFailAlloc_2323_, 2, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2323_, 3, v_auxDeclNGen_2305_);
lean_ctor_set(v_reuseFailAlloc_2323_, 4, v_traceState_2306_);
lean_ctor_set(v_reuseFailAlloc_2323_, 5, v_cache_2307_);
lean_ctor_set(v_reuseFailAlloc_2323_, 6, v_messages_2308_);
lean_ctor_set(v_reuseFailAlloc_2323_, 7, v_infoState_2309_);
lean_ctor_set(v_reuseFailAlloc_2323_, 8, v_snapshotTasks_2310_);
v___x_2320_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = lean_st_ref_set(v___y_2293_, v___x_2320_);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v_r_2314_);
return v___x_2322_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg___boxed(lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2328_);
lean_dec(v___y_2328_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v___x_2336_; lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
v___x_2336_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2334_);
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0___boxed(lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t v_pu_2354_, lean_object* v_binderName_2355_, lean_object* v_type_2356_, uint8_t v_borrow_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2387_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref(v___x_2363_);
v___x_2365_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_2366_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2355_, v___x_2365_, v_a_2359_);
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2369_ = v___x_2366_;
v_isShared_2370_ = v_isSharedCheck_2387_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2366_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2387_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v_lctx_2372_; lean_object* v_nextIdx_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2386_; 
v___x_2371_ = lean_st_ref_take(v_a_2359_);
v_lctx_2372_ = lean_ctor_get(v___x_2371_, 0);
v_nextIdx_2373_ = lean_ctor_get(v___x_2371_, 1);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2375_ = v___x_2371_;
v_isShared_2376_ = v_isSharedCheck_2386_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_nextIdx_2373_);
lean_inc(v_lctx_2372_);
lean_dec(v___x_2371_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2386_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2380_; 
v___x_2377_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2377_, 0, v_a_2364_);
lean_ctor_set(v___x_2377_, 1, v_a_2367_);
lean_ctor_set(v___x_2377_, 2, v_type_2356_);
lean_ctor_set_uint8(v___x_2377_, sizeof(void*)*3, v_borrow_2357_);
lean_inc_ref(v___x_2377_);
v___x_2378_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2354_, v_lctx_2372_, v___x_2377_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v___x_2378_);
v___x_2380_ = v___x_2375_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2378_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_nextIdx_2373_);
v___x_2380_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2381_ = lean_st_ref_set(v_a_2359_, v___x_2380_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v___x_2377_);
v___x_2383_ = v___x_2369_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2377_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
lean_dec_ref(v_type_2356_);
lean_dec(v_binderName_2355_);
v_a_2388_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2363_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2363_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam___boxed(lean_object* v_pu_2396_, lean_object* v_binderName_2397_, lean_object* v_type_2398_, lean_object* v_borrow_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
uint8_t v_pu_boxed_2405_; uint8_t v_borrow_boxed_2406_; lean_object* v_res_2407_; 
v_pu_boxed_2405_ = lean_unbox(v_pu_2396_);
v_borrow_boxed_2406_ = lean_unbox(v_borrow_2399_);
v_res_2407_ = l_Lean_Compiler_LCNF_mkParam(v_pu_boxed_2405_, v_binderName_2397_, v_type_2398_, v_borrow_boxed_2406_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2411_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___boxed(lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t v_pu_2423_, lean_object* v_binderName_2424_, lean_object* v_type_2425_, lean_object* v_value_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2456_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref(v___x_2432_);
v___x_2434_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2435_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2424_, v___x_2434_, v_a_2428_);
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2438_ = v___x_2435_;
v_isShared_2439_ = v_isSharedCheck_2456_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2435_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2456_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; lean_object* v_lctx_2441_; lean_object* v_nextIdx_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2455_; 
v___x_2440_ = lean_st_ref_take(v_a_2428_);
v_lctx_2441_ = lean_ctor_get(v___x_2440_, 0);
v_nextIdx_2442_ = lean_ctor_get(v___x_2440_, 1);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2444_ = v___x_2440_;
v_isShared_2445_ = v_isSharedCheck_2455_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_nextIdx_2442_);
lean_inc(v_lctx_2441_);
lean_dec(v___x_2440_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2455_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2446_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2446_, 0, v_a_2433_);
lean_ctor_set(v___x_2446_, 1, v_a_2436_);
lean_ctor_set(v___x_2446_, 2, v_type_2425_);
lean_ctor_set(v___x_2446_, 3, v_value_2426_);
lean_inc_ref(v___x_2446_);
v___x_2447_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2423_, v_lctx_2441_, v___x_2446_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 0, v___x_2447_);
v___x_2449_ = v___x_2444_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2447_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v_nextIdx_2442_);
v___x_2449_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2450_ = lean_st_ref_set(v_a_2428_, v___x_2449_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 0, v___x_2446_);
v___x_2452_ = v___x_2438_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2446_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec(v_value_2426_);
lean_dec_ref(v_type_2425_);
lean_dec(v_binderName_2424_);
v_a_2457_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2432_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2432_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl___boxed(lean_object* v_pu_2465_, lean_object* v_binderName_2466_, lean_object* v_type_2467_, lean_object* v_value_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_){
_start:
{
uint8_t v_pu_boxed_2474_; lean_object* v_res_2475_; 
v_pu_boxed_2474_ = lean_unbox(v_pu_2465_);
v_res_2475_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_boxed_2474_, v_binderName_2466_, v_type_2467_, v_value_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec(v_a_2470_);
lean_dec_ref(v_a_2469_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t v_pu_2479_, lean_object* v_binderName_2480_, lean_object* v_type_2481_, lean_object* v_params_2482_, lean_object* v_value_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2513_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2490_);
lean_dec_ref(v___x_2489_);
v___x_2491_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFunDecl___closed__1));
v___x_2492_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2480_, v___x_2491_, v_a_2485_);
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2495_ = v___x_2492_;
v_isShared_2496_ = v_isSharedCheck_2513_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2513_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; lean_object* v_lctx_2498_; lean_object* v_nextIdx_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2512_; 
v___x_2497_ = lean_st_ref_take(v_a_2485_);
v_lctx_2498_ = lean_ctor_get(v___x_2497_, 0);
v_nextIdx_2499_ = lean_ctor_get(v___x_2497_, 1);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2501_ = v___x_2497_;
v_isShared_2502_ = v_isSharedCheck_2512_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_nextIdx_2499_);
lean_inc(v_lctx_2498_);
lean_dec(v___x_2497_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2512_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2506_; 
v___x_2503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2503_, 0, v_a_2490_);
lean_ctor_set(v___x_2503_, 1, v_a_2493_);
lean_ctor_set(v___x_2503_, 2, v_params_2482_);
lean_ctor_set(v___x_2503_, 3, v_type_2481_);
lean_ctor_set(v___x_2503_, 4, v_value_2483_);
lean_inc_ref(v___x_2503_);
v___x_2504_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2479_, v_lctx_2498_, v___x_2503_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 0, v___x_2504_);
v___x_2506_ = v___x_2501_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_nextIdx_2499_);
v___x_2506_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2507_; lean_object* v___x_2509_; 
v___x_2507_ = lean_st_ref_set(v_a_2485_, v___x_2506_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v___x_2503_);
v___x_2509_ = v___x_2495_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2503_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec_ref(v_value_2483_);
lean_dec_ref(v_params_2482_);
lean_dec_ref(v_type_2481_);
lean_dec(v_binderName_2480_);
v_a_2514_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2489_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2489_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl___boxed(lean_object* v_pu_2522_, lean_object* v_binderName_2523_, lean_object* v_type_2524_, lean_object* v_params_2525_, lean_object* v_value_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_){
_start:
{
uint8_t v_pu_boxed_2532_; lean_object* v_res_2533_; 
v_pu_boxed_2532_ = lean_unbox(v_pu_2522_);
v_res_2533_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_boxed_2532_, v_binderName_2523_, v_type_2524_, v_params_2525_, v_value_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_);
lean_dec(v_a_2530_);
lean_dec_ref(v_a_2529_);
lean_dec(v_a_2528_);
lean_dec_ref(v_a_2527_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(uint8_t v_pu_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v_a_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2540_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2541_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2540_, v_a_2536_);
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref(v___x_2541_);
v___x_2543_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2544_ = lean_box(1);
v___x_2545_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2534_, v_a_2542_, v___x_2543_, v___x_2544_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased___boxed(lean_object* v_pu_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
uint8_t v_pu_boxed_2552_; lean_object* v_res_2553_; 
v_pu_boxed_2552_ = lean_unbox(v_pu_2546_);
v_res_2553_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_boxed_2552_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
lean_dec(v_a_2548_);
lean_dec_ref(v_a_2547_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t v_pu_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2571_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2563_ = v___x_2560_;
v_isShared_2564_ = v_isSharedCheck_2571_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2560_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2571_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v_fvarId_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2569_; 
v_fvarId_2565_ = lean_ctor_get(v_a_2561_, 0);
lean_inc(v_fvarId_2565_);
v___x_2566_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2566_, 0, v_fvarId_2565_);
v___x_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2567_, 0, v_a_2561_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 0, v___x_2567_);
v___x_2569_ = v___x_2563_;
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
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
v_a_2572_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2560_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2560_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased___boxed(lean_object* v_pu_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_){
_start:
{
uint8_t v_pu_boxed_2586_; lean_object* v_res_2587_; 
v_pu_boxed_2586_ = lean_unbox(v_pu_2580_);
v_res_2587_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_boxed_2586_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
lean_dec(v_a_2584_);
lean_dec_ref(v_a_2583_);
lean_dec(v_a_2582_);
lean_dec_ref(v_a_2581_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t v_pu_2588_, lean_object* v_p_2589_, lean_object* v_type_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v_fvarId_2593_; lean_object* v_binderName_2594_; lean_object* v_type_2595_; uint8_t v_borrow_2596_; size_t v___x_2597_; size_t v___x_2598_; uint8_t v___x_2599_; 
v_fvarId_2593_ = lean_ctor_get(v_p_2589_, 0);
v_binderName_2594_ = lean_ctor_get(v_p_2589_, 1);
v_type_2595_ = lean_ctor_get(v_p_2589_, 2);
v_borrow_2596_ = lean_ctor_get_uint8(v_p_2589_, sizeof(void*)*3);
v___x_2597_ = lean_ptr_addr(v_type_2590_);
v___x_2598_ = lean_ptr_addr(v_type_2595_);
v___x_2599_ = lean_usize_dec_eq(v___x_2597_, v___x_2598_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2619_; 
lean_inc(v_binderName_2594_);
lean_inc(v_fvarId_2593_);
v_isSharedCheck_2619_ = !lean_is_exclusive(v_p_2589_);
if (v_isSharedCheck_2619_ == 0)
{
lean_object* v_unused_2620_; lean_object* v_unused_2621_; lean_object* v_unused_2622_; 
v_unused_2620_ = lean_ctor_get(v_p_2589_, 2);
lean_dec(v_unused_2620_);
v_unused_2621_ = lean_ctor_get(v_p_2589_, 1);
lean_dec(v_unused_2621_);
v_unused_2622_ = lean_ctor_get(v_p_2589_, 0);
lean_dec(v_unused_2622_);
v___x_2601_ = v_p_2589_;
v_isShared_2602_ = v_isSharedCheck_2619_;
goto v_resetjp_2600_;
}
else
{
lean_dec(v_p_2589_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2619_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2603_; lean_object* v_lctx_2604_; lean_object* v_nextIdx_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2618_; 
v___x_2603_ = lean_st_ref_take(v_a_2591_);
v_lctx_2604_ = lean_ctor_get(v___x_2603_, 0);
v_nextIdx_2605_ = lean_ctor_get(v___x_2603_, 1);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2607_ = v___x_2603_;
v_isShared_2608_ = v_isSharedCheck_2618_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_nextIdx_2605_);
lean_inc(v_lctx_2604_);
lean_dec(v___x_2603_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2618_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v_p_2610_; 
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 2, v_type_2590_);
v_p_2610_ = v___x_2601_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_fvarId_2593_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v_binderName_2594_);
lean_ctor_set(v_reuseFailAlloc_2617_, 2, v_type_2590_);
lean_ctor_set_uint8(v_reuseFailAlloc_2617_, sizeof(void*)*3, v_borrow_2596_);
v_p_2610_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2611_; lean_object* v___x_2613_; 
lean_inc_ref(v_p_2610_);
v___x_2611_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2588_, v_lctx_2604_, v_p_2610_);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v___x_2611_);
v___x_2613_ = v___x_2607_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v_nextIdx_2605_);
v___x_2613_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = lean_st_ref_set(v_a_2591_, v___x_2613_);
v___x_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2615_, 0, v_p_2610_);
return v___x_2615_;
}
}
}
}
}
else
{
lean_object* v___x_2623_; 
lean_dec_ref(v_type_2590_);
v___x_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2623_, 0, v_p_2589_);
return v___x_2623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg___boxed(lean_object* v_pu_2624_, lean_object* v_p_2625_, lean_object* v_type_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
uint8_t v_pu_boxed_2629_; lean_object* v_res_2630_; 
v_pu_boxed_2629_ = lean_unbox(v_pu_2624_);
v_res_2630_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_boxed_2629_, v_p_2625_, v_type_2626_, v_a_2627_);
lean_dec(v_a_2627_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(uint8_t v_pu_2631_, lean_object* v_p_2632_, lean_object* v_type_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_2631_, v_p_2632_, v_type_2633_, v_a_2635_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(lean_object* v_pu_2640_, lean_object* v_p_2641_, lean_object* v_type_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
uint8_t v_pu_boxed_2648_; lean_object* v_res_2649_; 
v_pu_boxed_2648_ = lean_unbox(v_pu_2640_);
v_res_2649_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(v_pu_boxed_2648_, v_p_2641_, v_type_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t v_pu_2650_, lean_object* v_p_2651_, uint8_t v_borrow_2652_, lean_object* v_a_2653_){
_start:
{
lean_object* v_fvarId_2655_; lean_object* v_binderName_2656_; lean_object* v_type_2657_; uint8_t v_borrow_2658_; 
v_fvarId_2655_ = lean_ctor_get(v_p_2651_, 0);
v_binderName_2656_ = lean_ctor_get(v_p_2651_, 1);
v_type_2657_ = lean_ctor_get(v_p_2651_, 2);
v_borrow_2658_ = lean_ctor_get_uint8(v_p_2651_, sizeof(void*)*3);
if (v_borrow_2652_ == 0)
{
if (v_borrow_2658_ == 0)
{
lean_object* v___x_2674_; 
v___x_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2674_, 0, v_p_2651_);
return v___x_2674_;
}
else
{
lean_inc_ref(v_type_2657_);
lean_inc(v_binderName_2656_);
lean_inc(v_fvarId_2655_);
lean_dec_ref(v_p_2651_);
goto v___jp_2659_;
}
}
else
{
if (v_borrow_2658_ == 0)
{
lean_inc_ref(v_type_2657_);
lean_inc(v_binderName_2656_);
lean_inc(v_fvarId_2655_);
lean_dec_ref(v_p_2651_);
goto v___jp_2659_;
}
else
{
lean_object* v___x_2675_; 
v___x_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2675_, 0, v_p_2651_);
return v___x_2675_;
}
}
v___jp_2659_:
{
lean_object* v___x_2660_; lean_object* v_lctx_2661_; lean_object* v_nextIdx_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2673_; 
v___x_2660_ = lean_st_ref_take(v_a_2653_);
v_lctx_2661_ = lean_ctor_get(v___x_2660_, 0);
v_nextIdx_2662_ = lean_ctor_get(v___x_2660_, 1);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2664_ = v___x_2660_;
v_isShared_2665_ = v_isSharedCheck_2673_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_nextIdx_2662_);
lean_inc(v_lctx_2661_);
lean_dec(v___x_2660_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2673_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v_p_2666_; lean_object* v___x_2667_; lean_object* v___x_2669_; 
v_p_2666_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_p_2666_, 0, v_fvarId_2655_);
lean_ctor_set(v_p_2666_, 1, v_binderName_2656_);
lean_ctor_set(v_p_2666_, 2, v_type_2657_);
lean_ctor_set_uint8(v_p_2666_, sizeof(void*)*3, v_borrow_2652_);
lean_inc_ref(v_p_2666_);
v___x_2667_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2650_, v_lctx_2661_, v_p_2666_);
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v___x_2667_);
v___x_2669_ = v___x_2664_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v_nextIdx_2662_);
v___x_2669_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = lean_st_ref_set(v_a_2653_, v___x_2669_);
v___x_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2671_, 0, v_p_2666_);
return v___x_2671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg___boxed(lean_object* v_pu_2676_, lean_object* v_p_2677_, lean_object* v_borrow_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_){
_start:
{
uint8_t v_pu_boxed_2681_; uint8_t v_borrow_boxed_2682_; lean_object* v_res_2683_; 
v_pu_boxed_2681_ = lean_unbox(v_pu_2676_);
v_borrow_boxed_2682_ = lean_unbox(v_borrow_2678_);
v_res_2683_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_boxed_2681_, v_p_2677_, v_borrow_boxed_2682_, v_a_2679_);
lean_dec(v_a_2679_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(uint8_t v_pu_2684_, lean_object* v_p_2685_, uint8_t v_borrow_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_2684_, v_p_2685_, v_borrow_2686_, v_a_2688_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___boxed(lean_object* v_pu_2693_, lean_object* v_p_2694_, lean_object* v_borrow_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_){
_start:
{
uint8_t v_pu_boxed_2701_; uint8_t v_borrow_boxed_2702_; lean_object* v_res_2703_; 
v_pu_boxed_2701_ = lean_unbox(v_pu_2693_);
v_borrow_boxed_2702_ = lean_unbox(v_borrow_2695_);
v_res_2703_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(v_pu_boxed_2701_, v_p_2694_, v_borrow_boxed_2702_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t v_pu_2704_, lean_object* v_decl_2705_, lean_object* v_type_2706_, lean_object* v_value_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v_fvarId_2710_; lean_object* v_binderName_2711_; lean_object* v_type_2712_; lean_object* v_value_2713_; uint8_t v___y_2715_; size_t v___x_2741_; size_t v___x_2742_; uint8_t v___x_2743_; 
v_fvarId_2710_ = lean_ctor_get(v_decl_2705_, 0);
v_binderName_2711_ = lean_ctor_get(v_decl_2705_, 1);
v_type_2712_ = lean_ctor_get(v_decl_2705_, 2);
v_value_2713_ = lean_ctor_get(v_decl_2705_, 3);
v___x_2741_ = lean_ptr_addr(v_type_2706_);
v___x_2742_ = lean_ptr_addr(v_type_2712_);
v___x_2743_ = lean_usize_dec_eq(v___x_2741_, v___x_2742_);
if (v___x_2743_ == 0)
{
v___y_2715_ = v___x_2743_;
goto v___jp_2714_;
}
else
{
size_t v___x_2744_; size_t v___x_2745_; uint8_t v___x_2746_; 
v___x_2744_ = lean_ptr_addr(v_value_2707_);
v___x_2745_ = lean_ptr_addr(v_value_2713_);
v___x_2746_ = lean_usize_dec_eq(v___x_2744_, v___x_2745_);
v___y_2715_ = v___x_2746_;
goto v___jp_2714_;
}
v___jp_2714_:
{
if (v___y_2715_ == 0)
{
lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2735_; 
lean_inc(v_binderName_2711_);
lean_inc(v_fvarId_2710_);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_decl_2705_);
if (v_isSharedCheck_2735_ == 0)
{
lean_object* v_unused_2736_; lean_object* v_unused_2737_; lean_object* v_unused_2738_; lean_object* v_unused_2739_; 
v_unused_2736_ = lean_ctor_get(v_decl_2705_, 3);
lean_dec(v_unused_2736_);
v_unused_2737_ = lean_ctor_get(v_decl_2705_, 2);
lean_dec(v_unused_2737_);
v_unused_2738_ = lean_ctor_get(v_decl_2705_, 1);
lean_dec(v_unused_2738_);
v_unused_2739_ = lean_ctor_get(v_decl_2705_, 0);
lean_dec(v_unused_2739_);
v___x_2717_ = v_decl_2705_;
v_isShared_2718_ = v_isSharedCheck_2735_;
goto v_resetjp_2716_;
}
else
{
lean_dec(v_decl_2705_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2735_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2719_; lean_object* v_lctx_2720_; lean_object* v_nextIdx_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2734_; 
v___x_2719_ = lean_st_ref_take(v_a_2708_);
v_lctx_2720_ = lean_ctor_get(v___x_2719_, 0);
v_nextIdx_2721_ = lean_ctor_get(v___x_2719_, 1);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2723_ = v___x_2719_;
v_isShared_2724_ = v_isSharedCheck_2734_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_nextIdx_2721_);
lean_inc(v_lctx_2720_);
lean_dec(v___x_2719_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2734_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v_decl_2726_; 
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 3, v_value_2707_);
lean_ctor_set(v___x_2717_, 2, v_type_2706_);
v_decl_2726_ = v___x_2717_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_fvarId_2710_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_binderName_2711_);
lean_ctor_set(v_reuseFailAlloc_2733_, 2, v_type_2706_);
lean_ctor_set(v_reuseFailAlloc_2733_, 3, v_value_2707_);
v_decl_2726_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
lean_object* v___x_2727_; lean_object* v___x_2729_; 
lean_inc_ref(v_decl_2726_);
v___x_2727_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2704_, v_lctx_2720_, v_decl_2726_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v___x_2727_);
v___x_2729_ = v___x_2723_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2727_);
lean_ctor_set(v_reuseFailAlloc_2732_, 1, v_nextIdx_2721_);
v___x_2729_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2730_ = lean_st_ref_set(v_a_2708_, v___x_2729_);
v___x_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2731_, 0, v_decl_2726_);
return v___x_2731_;
}
}
}
}
}
else
{
lean_object* v___x_2740_; 
lean_dec(v_value_2707_);
lean_dec_ref(v_type_2706_);
v___x_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2740_, 0, v_decl_2705_);
return v___x_2740_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg___boxed(lean_object* v_pu_2747_, lean_object* v_decl_2748_, lean_object* v_type_2749_, lean_object* v_value_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_){
_start:
{
uint8_t v_pu_boxed_2753_; lean_object* v_res_2754_; 
v_pu_boxed_2753_ = lean_unbox(v_pu_2747_);
v_res_2754_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_boxed_2753_, v_decl_2748_, v_type_2749_, v_value_2750_, v_a_2751_);
lean_dec(v_a_2751_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(uint8_t v_pu_2755_, lean_object* v_decl_2756_, lean_object* v_type_2757_, lean_object* v_value_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2755_, v_decl_2756_, v_type_2757_, v_value_2758_, v_a_2760_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(lean_object* v_pu_2765_, lean_object* v_decl_2766_, lean_object* v_type_2767_, lean_object* v_value_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_){
_start:
{
uint8_t v_pu_boxed_2774_; lean_object* v_res_2775_; 
v_pu_boxed_2774_ = lean_unbox(v_pu_2765_);
v_res_2775_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(v_pu_boxed_2774_, v_decl_2766_, v_type_2767_, v_value_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
lean_dec(v_a_2772_);
lean_dec_ref(v_a_2771_);
lean_dec(v_a_2770_);
lean_dec_ref(v_a_2769_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t v_pu_2776_, lean_object* v_decl_2777_, lean_object* v_value_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v_type_2781_; lean_object* v___x_2782_; 
v_type_2781_ = lean_ctor_get(v_decl_2777_, 2);
lean_inc_ref(v_type_2781_);
v___x_2782_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2776_, v_decl_2777_, v_type_2781_, v_value_2778_, v_a_2779_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg___boxed(lean_object* v_pu_2783_, lean_object* v_decl_2784_, lean_object* v_value_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_){
_start:
{
uint8_t v_pu_boxed_2788_; lean_object* v_res_2789_; 
v_pu_boxed_2788_ = lean_unbox(v_pu_2783_);
v_res_2789_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_boxed_2788_, v_decl_2784_, v_value_2785_, v_a_2786_);
lean_dec(v_a_2786_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(uint8_t v_pu_2790_, lean_object* v_decl_2791_, lean_object* v_value_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_2790_, v_decl_2791_, v_value_2792_, v_a_2794_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___boxed(lean_object* v_pu_2799_, lean_object* v_decl_2800_, lean_object* v_value_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
uint8_t v_pu_boxed_2807_; lean_object* v_res_2808_; 
v_pu_boxed_2807_ = lean_unbox(v_pu_2799_);
v_res_2808_ = l_Lean_Compiler_LCNF_LetDecl_updateValue(v_pu_boxed_2807_, v_decl_2800_, v_value_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_);
lean_dec(v_a_2805_);
lean_dec_ref(v_a_2804_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t v_pu_2809_, lean_object* v_decl_2810_, lean_object* v_type_2811_, lean_object* v_params_2812_, lean_object* v_value_2813_, lean_object* v_a_2814_){
_start:
{
lean_object* v_fvarId_2816_; lean_object* v_binderName_2817_; lean_object* v_params_2818_; lean_object* v_type_2819_; lean_object* v_value_2820_; uint8_t v___y_2837_; size_t v___x_2842_; size_t v___x_2843_; uint8_t v___x_2844_; 
v_fvarId_2816_ = lean_ctor_get(v_decl_2810_, 0);
v_binderName_2817_ = lean_ctor_get(v_decl_2810_, 1);
v_params_2818_ = lean_ctor_get(v_decl_2810_, 2);
v_type_2819_ = lean_ctor_get(v_decl_2810_, 3);
v_value_2820_ = lean_ctor_get(v_decl_2810_, 4);
v___x_2842_ = lean_ptr_addr(v_type_2811_);
v___x_2843_ = lean_ptr_addr(v_type_2819_);
v___x_2844_ = lean_usize_dec_eq(v___x_2842_, v___x_2843_);
if (v___x_2844_ == 0)
{
v___y_2837_ = v___x_2844_;
goto v___jp_2836_;
}
else
{
size_t v___x_2845_; size_t v___x_2846_; uint8_t v___x_2847_; 
v___x_2845_ = lean_ptr_addr(v_params_2812_);
v___x_2846_ = lean_ptr_addr(v_params_2818_);
v___x_2847_ = lean_usize_dec_eq(v___x_2845_, v___x_2846_);
v___y_2837_ = v___x_2847_;
goto v___jp_2836_;
}
v___jp_2821_:
{
lean_object* v___x_2822_; lean_object* v_lctx_2823_; lean_object* v_nextIdx_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2835_; 
v___x_2822_ = lean_st_ref_take(v_a_2814_);
v_lctx_2823_ = lean_ctor_get(v___x_2822_, 0);
v_nextIdx_2824_ = lean_ctor_get(v___x_2822_, 1);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2826_ = v___x_2822_;
v_isShared_2827_ = v_isSharedCheck_2835_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_nextIdx_2824_);
lean_inc(v_lctx_2823_);
lean_dec(v___x_2822_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2835_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v_decl_2828_; lean_object* v___x_2829_; lean_object* v___x_2831_; 
v_decl_2828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_decl_2828_, 0, v_fvarId_2816_);
lean_ctor_set(v_decl_2828_, 1, v_binderName_2817_);
lean_ctor_set(v_decl_2828_, 2, v_params_2812_);
lean_ctor_set(v_decl_2828_, 3, v_type_2811_);
lean_ctor_set(v_decl_2828_, 4, v_value_2813_);
lean_inc_ref(v_decl_2828_);
v___x_2829_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2809_, v_lctx_2823_, v_decl_2828_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v___x_2829_);
v___x_2831_ = v___x_2826_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2829_);
lean_ctor_set(v_reuseFailAlloc_2834_, 1, v_nextIdx_2824_);
v___x_2831_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_st_ref_set(v_a_2814_, v___x_2831_);
v___x_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2833_, 0, v_decl_2828_);
return v___x_2833_;
}
}
}
v___jp_2836_:
{
if (v___y_2837_ == 0)
{
lean_inc(v_binderName_2817_);
lean_inc(v_fvarId_2816_);
lean_dec_ref(v_decl_2810_);
goto v___jp_2821_;
}
else
{
size_t v___x_2838_; size_t v___x_2839_; uint8_t v___x_2840_; 
v___x_2838_ = lean_ptr_addr(v_value_2813_);
v___x_2839_ = lean_ptr_addr(v_value_2820_);
v___x_2840_ = lean_usize_dec_eq(v___x_2838_, v___x_2839_);
if (v___x_2840_ == 0)
{
lean_inc(v_binderName_2817_);
lean_inc(v_fvarId_2816_);
lean_dec_ref(v_decl_2810_);
goto v___jp_2821_;
}
else
{
lean_object* v___x_2841_; 
lean_dec_ref(v_value_2813_);
lean_dec_ref(v_params_2812_);
lean_dec_ref(v_type_2811_);
v___x_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2841_, 0, v_decl_2810_);
return v___x_2841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg___boxed(lean_object* v_pu_2848_, lean_object* v_decl_2849_, lean_object* v_type_2850_, lean_object* v_params_2851_, lean_object* v_value_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_){
_start:
{
uint8_t v_pu_boxed_2855_; lean_object* v_res_2856_; 
v_pu_boxed_2855_ = lean_unbox(v_pu_2848_);
v_res_2856_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_boxed_2855_, v_decl_2849_, v_type_2850_, v_params_2851_, v_value_2852_, v_a_2853_);
lean_dec(v_a_2853_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(uint8_t v_pu_2857_, lean_object* v_decl_2858_, lean_object* v_type_2859_, lean_object* v_params_2860_, lean_object* v_value_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2857_, v_decl_2858_, v_type_2859_, v_params_2860_, v_value_2861_, v_a_2863_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(lean_object* v_pu_2868_, lean_object* v_decl_2869_, lean_object* v_type_2870_, lean_object* v_params_2871_, lean_object* v_value_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
uint8_t v_pu_boxed_2878_; lean_object* v_res_2879_; 
v_pu_boxed_2878_ = lean_unbox(v_pu_2868_);
v_res_2879_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(v_pu_boxed_2878_, v_decl_2869_, v_type_2870_, v_params_2871_, v_value_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
lean_dec(v_a_2876_);
lean_dec_ref(v_a_2875_);
lean_dec(v_a_2874_);
lean_dec_ref(v_a_2873_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(uint8_t v_pu_2880_, lean_object* v_decl_2881_, lean_object* v_type_2882_, lean_object* v_value_2883_, lean_object* v_a_2884_){
_start:
{
lean_object* v_params_2886_; lean_object* v___x_2887_; 
v_params_2886_ = lean_ctor_get(v_decl_2881_, 2);
lean_inc_ref(v_params_2886_);
v___x_2887_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2880_, v_decl_2881_, v_type_2882_, v_params_2886_, v_value_2883_, v_a_2884_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg___boxed(lean_object* v_pu_2888_, lean_object* v_decl_2889_, lean_object* v_type_2890_, lean_object* v_value_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_){
_start:
{
uint8_t v_pu_boxed_2894_; lean_object* v_res_2895_; 
v_pu_boxed_2894_ = lean_unbox(v_pu_2888_);
v_res_2895_ = l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(v_pu_boxed_2894_, v_decl_2889_, v_type_2890_, v_value_2891_, v_a_2892_);
lean_dec(v_a_2892_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27(uint8_t v_pu_2896_, lean_object* v_decl_2897_, lean_object* v_type_2898_, lean_object* v_value_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v_params_2905_; lean_object* v___x_2906_; 
v_params_2905_ = lean_ctor_get(v_decl_2897_, 2);
lean_inc_ref(v_params_2905_);
v___x_2906_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2896_, v_decl_2897_, v_type_2898_, v_params_2905_, v_value_2899_, v_a_2901_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___boxed(lean_object* v_pu_2907_, lean_object* v_decl_2908_, lean_object* v_type_2909_, lean_object* v_value_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_){
_start:
{
uint8_t v_pu_boxed_2916_; lean_object* v_res_2917_; 
v_pu_boxed_2916_ = lean_unbox(v_pu_2907_);
v_res_2917_ = l_Lean_Compiler_LCNF_FunDecl_update_x27(v_pu_boxed_2916_, v_decl_2908_, v_type_2909_, v_value_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(uint8_t v_pu_2918_, lean_object* v_decl_2919_, lean_object* v_value_2920_, lean_object* v_a_2921_){
_start:
{
lean_object* v_params_2923_; lean_object* v_type_2924_; lean_object* v___x_2925_; 
v_params_2923_ = lean_ctor_get(v_decl_2919_, 2);
lean_inc_ref(v_params_2923_);
v_type_2924_ = lean_ctor_get(v_decl_2919_, 3);
lean_inc_ref(v_type_2924_);
v___x_2925_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2918_, v_decl_2919_, v_type_2924_, v_params_2923_, v_value_2920_, v_a_2921_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg___boxed(lean_object* v_pu_2926_, lean_object* v_decl_2927_, lean_object* v_value_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_){
_start:
{
uint8_t v_pu_boxed_2931_; lean_object* v_res_2932_; 
v_pu_boxed_2931_ = lean_unbox(v_pu_2926_);
v_res_2932_ = l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(v_pu_boxed_2931_, v_decl_2927_, v_value_2928_, v_a_2929_);
lean_dec(v_a_2929_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue(uint8_t v_pu_2933_, lean_object* v_decl_2934_, lean_object* v_value_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_){
_start:
{
lean_object* v_params_2941_; lean_object* v_type_2942_; lean_object* v___x_2943_; 
v_params_2941_ = lean_ctor_get(v_decl_2934_, 2);
lean_inc_ref(v_params_2941_);
v_type_2942_ = lean_ctor_get(v_decl_2934_, 3);
lean_inc_ref(v_type_2942_);
v___x_2943_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2933_, v_decl_2934_, v_type_2942_, v_params_2941_, v_value_2935_, v_a_2937_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___boxed(lean_object* v_pu_2944_, lean_object* v_decl_2945_, lean_object* v_value_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_){
_start:
{
uint8_t v_pu_boxed_2952_; lean_object* v_res_2953_; 
v_pu_boxed_2952_ = lean_unbox(v_pu_2944_);
v_res_2953_ = l_Lean_Compiler_LCNF_FunDecl_updateValue(v_pu_boxed_2952_, v_decl_2945_, v_value_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_);
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0(uint8_t v_pu_2954_, lean_object* v_p_2955_, lean_object* v_inst_2956_, lean_object* v_____do__lift_2957_){
_start:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2958_ = lean_box(v_pu_2954_);
v___x_2959_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_2959_, 0, v___x_2958_);
lean_closure_set(v___x_2959_, 1, v_p_2955_);
lean_closure_set(v___x_2959_, 2, v_____do__lift_2957_);
v___x_2960_ = lean_apply_2(v_inst_2956_, lean_box(0), v___x_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed(lean_object* v_pu_2961_, lean_object* v_p_2962_, lean_object* v_inst_2963_, lean_object* v_____do__lift_2964_){
_start:
{
uint8_t v_pu_boxed_2965_; lean_object* v_res_2966_; 
v_pu_boxed_2965_ = lean_unbox(v_pu_2961_);
v_res_2966_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__0(v_pu_boxed_2965_, v_p_2962_, v_inst_2963_, v_____do__lift_2964_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1(uint8_t v_pu_2967_, uint8_t v_t_2968_, lean_object* v_type_2969_, lean_object* v_toPure_2970_, lean_object* v_____do__lift_2971_){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2967_, v_____do__lift_2971_, v_t_2968_, v_type_2969_);
v___x_2973_ = lean_apply_2(v_toPure_2970_, lean_box(0), v___x_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed(lean_object* v_pu_2974_, lean_object* v_t_2975_, lean_object* v_type_2976_, lean_object* v_toPure_2977_, lean_object* v_____do__lift_2978_){
_start:
{
uint8_t v_pu_boxed_2979_; uint8_t v_t_boxed_2980_; lean_object* v_res_2981_; 
v_pu_boxed_2979_ = lean_unbox(v_pu_2974_);
v_t_boxed_2980_ = lean_unbox(v_t_2975_);
v_res_2981_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__1(v_pu_boxed_2979_, v_t_boxed_2980_, v_type_2976_, v_toPure_2977_, v_____do__lift_2978_);
lean_dec_ref(v_____do__lift_2978_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg(uint8_t v_pu_2982_, uint8_t v_t_2983_, lean_object* v_inst_2984_, lean_object* v_inst_2985_, lean_object* v_inst_2986_, lean_object* v_p_2987_){
_start:
{
lean_object* v_toApplicative_2988_; lean_object* v_toBind_2989_; lean_object* v_type_2990_; lean_object* v_toPure_2991_; lean_object* v___x_2992_; lean_object* v___f_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___f_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v_toApplicative_2988_ = lean_ctor_get(v_inst_2985_, 0);
lean_inc_ref(v_toApplicative_2988_);
v_toBind_2989_ = lean_ctor_get(v_inst_2985_, 1);
lean_inc_n(v_toBind_2989_, 2);
lean_dec_ref(v_inst_2985_);
v_type_2990_ = lean_ctor_get(v_p_2987_, 2);
lean_inc_ref(v_type_2990_);
v_toPure_2991_ = lean_ctor_get(v_toApplicative_2988_, 1);
lean_inc(v_toPure_2991_);
lean_dec_ref(v_toApplicative_2988_);
v___x_2992_ = lean_box(v_pu_2982_);
v___f_2993_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2993_, 0, v___x_2992_);
lean_closure_set(v___f_2993_, 1, v_p_2987_);
lean_closure_set(v___f_2993_, 2, v_inst_2984_);
v___x_2994_ = lean_box(v_pu_2982_);
v___x_2995_ = lean_box(v_t_2983_);
v___f_2996_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2996_, 0, v___x_2994_);
lean_closure_set(v___f_2996_, 1, v___x_2995_);
lean_closure_set(v___f_2996_, 2, v_type_2990_);
lean_closure_set(v___f_2996_, 3, v_toPure_2991_);
v___x_2997_ = lean_apply_4(v_toBind_2989_, lean_box(0), lean_box(0), v_inst_2986_, v___f_2996_);
v___x_2998_ = lean_apply_4(v_toBind_2989_, lean_box(0), lean_box(0), v___x_2997_, v___f_2993_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___boxed(lean_object* v_pu_2999_, lean_object* v_t_3000_, lean_object* v_inst_3001_, lean_object* v_inst_3002_, lean_object* v_inst_3003_, lean_object* v_p_3004_){
_start:
{
uint8_t v_pu_boxed_3005_; uint8_t v_t_boxed_3006_; lean_object* v_res_3007_; 
v_pu_boxed_3005_ = lean_unbox(v_pu_2999_);
v_t_boxed_3006_ = lean_unbox(v_t_3000_);
v_res_3007_ = l_Lean_Compiler_LCNF_normParam___redArg(v_pu_boxed_3005_, v_t_boxed_3006_, v_inst_3001_, v_inst_3002_, v_inst_3003_, v_p_3004_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam(lean_object* v_m_3008_, uint8_t v_pu_3009_, uint8_t v_t_3010_, lean_object* v_inst_3011_, lean_object* v_inst_3012_, lean_object* v_inst_3013_, lean_object* v_p_3014_){
_start:
{
lean_object* v_toApplicative_3015_; lean_object* v_toBind_3016_; lean_object* v_type_3017_; lean_object* v_toPure_3018_; lean_object* v___x_3019_; lean_object* v___f_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___f_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v_toApplicative_3015_ = lean_ctor_get(v_inst_3012_, 0);
lean_inc_ref(v_toApplicative_3015_);
v_toBind_3016_ = lean_ctor_get(v_inst_3012_, 1);
lean_inc_n(v_toBind_3016_, 2);
lean_dec_ref(v_inst_3012_);
v_type_3017_ = lean_ctor_get(v_p_3014_, 2);
lean_inc_ref(v_type_3017_);
v_toPure_3018_ = lean_ctor_get(v_toApplicative_3015_, 1);
lean_inc(v_toPure_3018_);
lean_dec_ref(v_toApplicative_3015_);
v___x_3019_ = lean_box(v_pu_3009_);
v___f_3020_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3020_, 0, v___x_3019_);
lean_closure_set(v___f_3020_, 1, v_p_3014_);
lean_closure_set(v___f_3020_, 2, v_inst_3011_);
v___x_3021_ = lean_box(v_pu_3009_);
v___x_3022_ = lean_box(v_t_3010_);
v___f_3023_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3023_, 0, v___x_3021_);
lean_closure_set(v___f_3023_, 1, v___x_3022_);
lean_closure_set(v___f_3023_, 2, v_type_3017_);
lean_closure_set(v___f_3023_, 3, v_toPure_3018_);
v___x_3024_ = lean_apply_4(v_toBind_3016_, lean_box(0), lean_box(0), v_inst_3013_, v___f_3023_);
v___x_3025_ = lean_apply_4(v_toBind_3016_, lean_box(0), lean_box(0), v___x_3024_, v___f_3020_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___boxed(lean_object* v_m_3026_, lean_object* v_pu_3027_, lean_object* v_t_3028_, lean_object* v_inst_3029_, lean_object* v_inst_3030_, lean_object* v_inst_3031_, lean_object* v_p_3032_){
_start:
{
uint8_t v_pu_boxed_3033_; uint8_t v_t_boxed_3034_; lean_object* v_res_3035_; 
v_pu_boxed_3033_ = lean_unbox(v_pu_3027_);
v_t_boxed_3034_ = lean_unbox(v_t_3028_);
v_res_3035_ = l_Lean_Compiler_LCNF_normParam(v_m_3026_, v_pu_boxed_3033_, v_t_boxed_3034_, v_inst_3029_, v_inst_3030_, v_inst_3031_, v_p_3032_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg(uint8_t v_pu_3036_, uint8_t v_t_3037_, lean_object* v_inst_3038_, lean_object* v_inst_3039_, lean_object* v_inst_3040_, lean_object* v_ps_3041_){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3042_ = lean_box(v_pu_3036_);
v___x_3043_ = lean_box(v_t_3037_);
lean_inc_ref(v_inst_3039_);
v___x_3044_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___boxed), 7, 6);
lean_closure_set(v___x_3044_, 0, lean_box(0));
lean_closure_set(v___x_3044_, 1, v___x_3042_);
lean_closure_set(v___x_3044_, 2, v___x_3043_);
lean_closure_set(v___x_3044_, 3, v_inst_3038_);
lean_closure_set(v___x_3044_, 4, v_inst_3039_);
lean_closure_set(v___x_3044_, 5, v_inst_3040_);
v___x_3045_ = lean_unsigned_to_nat(0u);
v___x_3046_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_3039_, v___x_3044_, v___x_3045_, v_ps_3041_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg___boxed(lean_object* v_pu_3047_, lean_object* v_t_3048_, lean_object* v_inst_3049_, lean_object* v_inst_3050_, lean_object* v_inst_3051_, lean_object* v_ps_3052_){
_start:
{
uint8_t v_pu_boxed_3053_; uint8_t v_t_boxed_3054_; lean_object* v_res_3055_; 
v_pu_boxed_3053_ = lean_unbox(v_pu_3047_);
v_t_boxed_3054_ = lean_unbox(v_t_3048_);
v_res_3055_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_boxed_3053_, v_t_boxed_3054_, v_inst_3049_, v_inst_3050_, v_inst_3051_, v_ps_3052_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams(lean_object* v_m_3056_, uint8_t v_pu_3057_, uint8_t v_t_3058_, lean_object* v_inst_3059_, lean_object* v_inst_3060_, lean_object* v_inst_3061_, lean_object* v_ps_3062_){
_start:
{
lean_object* v___x_3063_; 
v___x_3063_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_3057_, v_t_3058_, v_inst_3059_, v_inst_3060_, v_inst_3061_, v_ps_3062_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___boxed(lean_object* v_m_3064_, lean_object* v_pu_3065_, lean_object* v_t_3066_, lean_object* v_inst_3067_, lean_object* v_inst_3068_, lean_object* v_inst_3069_, lean_object* v_ps_3070_){
_start:
{
uint8_t v_pu_boxed_3071_; uint8_t v_t_boxed_3072_; lean_object* v_res_3073_; 
v_pu_boxed_3071_ = lean_unbox(v_pu_3065_);
v_t_boxed_3072_ = lean_unbox(v_t_3066_);
v_res_3073_ = l_Lean_Compiler_LCNF_normParams(v_m_3064_, v_pu_boxed_3071_, v_t_boxed_3072_, v_inst_3067_, v_inst_3068_, v_inst_3069_, v_ps_3070_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(uint8_t v_pu_3074_, lean_object* v_decl_3075_, lean_object* v_____do__lift_3076_, lean_object* v_inst_3077_, lean_object* v_____do__lift_3078_){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = lean_box(v_pu_3074_);
v___x_3080_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_3080_, 0, v___x_3079_);
lean_closure_set(v___x_3080_, 1, v_decl_3075_);
lean_closure_set(v___x_3080_, 2, v_____do__lift_3076_);
lean_closure_set(v___x_3080_, 3, v_____do__lift_3078_);
v___x_3081_ = lean_apply_2(v_inst_3077_, lean_box(0), v___x_3080_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed(lean_object* v_pu_3082_, lean_object* v_decl_3083_, lean_object* v_____do__lift_3084_, lean_object* v_inst_3085_, lean_object* v_____do__lift_3086_){
_start:
{
uint8_t v_pu_boxed_3087_; lean_object* v_res_3088_; 
v_pu_boxed_3087_ = lean_unbox(v_pu_3082_);
v_res_3088_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(v_pu_boxed_3087_, v_decl_3083_, v_____do__lift_3084_, v_inst_3085_, v_____do__lift_3086_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(uint8_t v_pu_3089_, lean_object* v_value_3090_, uint8_t v_t_3091_, lean_object* v_toPure_3092_, lean_object* v_____do__lift_3093_){
_start:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3094_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3089_, v_____do__lift_3093_, v_value_3090_, v_t_3091_);
v___x_3095_ = lean_apply_2(v_toPure_3092_, lean_box(0), v___x_3094_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed(lean_object* v_pu_3096_, lean_object* v_value_3097_, lean_object* v_t_3098_, lean_object* v_toPure_3099_, lean_object* v_____do__lift_3100_){
_start:
{
uint8_t v_pu_boxed_3101_; uint8_t v_t_boxed_3102_; lean_object* v_res_3103_; 
v_pu_boxed_3101_ = lean_unbox(v_pu_3096_);
v_t_boxed_3102_ = lean_unbox(v_t_3098_);
v_res_3103_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(v_pu_boxed_3101_, v_value_3097_, v_t_boxed_3102_, v_toPure_3099_, v_____do__lift_3100_);
lean_dec_ref(v_____do__lift_3100_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(uint8_t v_pu_3104_, lean_object* v_decl_3105_, lean_object* v_inst_3106_, lean_object* v_value_3107_, uint8_t v_t_3108_, lean_object* v_toPure_3109_, lean_object* v_toBind_3110_, lean_object* v_inst_3111_, lean_object* v_____do__lift_3112_){
_start:
{
lean_object* v___x_3113_; lean_object* v___f_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___f_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3113_ = lean_box(v_pu_3104_);
v___f_3114_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3114_, 0, v___x_3113_);
lean_closure_set(v___f_3114_, 1, v_decl_3105_);
lean_closure_set(v___f_3114_, 2, v_____do__lift_3112_);
lean_closure_set(v___f_3114_, 3, v_inst_3106_);
v___x_3115_ = lean_box(v_pu_3104_);
v___x_3116_ = lean_box(v_t_3108_);
v___f_3117_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3117_, 0, v___x_3115_);
lean_closure_set(v___f_3117_, 1, v_value_3107_);
lean_closure_set(v___f_3117_, 2, v___x_3116_);
lean_closure_set(v___f_3117_, 3, v_toPure_3109_);
lean_inc(v_toBind_3110_);
v___x_3118_ = lean_apply_4(v_toBind_3110_, lean_box(0), lean_box(0), v_inst_3111_, v___f_3117_);
v___x_3119_ = lean_apply_4(v_toBind_3110_, lean_box(0), lean_box(0), v___x_3118_, v___f_3114_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed(lean_object* v_pu_3120_, lean_object* v_decl_3121_, lean_object* v_inst_3122_, lean_object* v_value_3123_, lean_object* v_t_3124_, lean_object* v_toPure_3125_, lean_object* v_toBind_3126_, lean_object* v_inst_3127_, lean_object* v_____do__lift_3128_){
_start:
{
uint8_t v_pu_boxed_3129_; uint8_t v_t_boxed_3130_; lean_object* v_res_3131_; 
v_pu_boxed_3129_ = lean_unbox(v_pu_3120_);
v_t_boxed_3130_ = lean_unbox(v_t_3124_);
v_res_3131_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(v_pu_boxed_3129_, v_decl_3121_, v_inst_3122_, v_value_3123_, v_t_boxed_3130_, v_toPure_3125_, v_toBind_3126_, v_inst_3127_, v_____do__lift_3128_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg(uint8_t v_pu_3132_, uint8_t v_t_3133_, lean_object* v_inst_3134_, lean_object* v_inst_3135_, lean_object* v_inst_3136_, lean_object* v_decl_3137_){
_start:
{
lean_object* v_toApplicative_3138_; lean_object* v_toBind_3139_; lean_object* v_type_3140_; lean_object* v_value_3141_; lean_object* v_toPure_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___f_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___f_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v_toApplicative_3138_ = lean_ctor_get(v_inst_3135_, 0);
lean_inc_ref(v_toApplicative_3138_);
v_toBind_3139_ = lean_ctor_get(v_inst_3135_, 1);
lean_inc_n(v_toBind_3139_, 3);
lean_dec_ref(v_inst_3135_);
v_type_3140_ = lean_ctor_get(v_decl_3137_, 2);
lean_inc_ref(v_type_3140_);
v_value_3141_ = lean_ctor_get(v_decl_3137_, 3);
lean_inc(v_value_3141_);
v_toPure_3142_ = lean_ctor_get(v_toApplicative_3138_, 1);
lean_inc_n(v_toPure_3142_, 2);
lean_dec_ref(v_toApplicative_3138_);
v___x_3143_ = lean_box(v_pu_3132_);
v___x_3144_ = lean_box(v_t_3133_);
lean_inc(v_inst_3136_);
v___f_3145_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_3145_, 0, v___x_3143_);
lean_closure_set(v___f_3145_, 1, v_decl_3137_);
lean_closure_set(v___f_3145_, 2, v_inst_3134_);
lean_closure_set(v___f_3145_, 3, v_value_3141_);
lean_closure_set(v___f_3145_, 4, v___x_3144_);
lean_closure_set(v___f_3145_, 5, v_toPure_3142_);
lean_closure_set(v___f_3145_, 6, v_toBind_3139_);
lean_closure_set(v___f_3145_, 7, v_inst_3136_);
v___x_3146_ = lean_box(v_pu_3132_);
v___x_3147_ = lean_box(v_t_3133_);
v___f_3148_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3148_, 0, v___x_3146_);
lean_closure_set(v___f_3148_, 1, v___x_3147_);
lean_closure_set(v___f_3148_, 2, v_type_3140_);
lean_closure_set(v___f_3148_, 3, v_toPure_3142_);
v___x_3149_ = lean_apply_4(v_toBind_3139_, lean_box(0), lean_box(0), v_inst_3136_, v___f_3148_);
v___x_3150_ = lean_apply_4(v_toBind_3139_, lean_box(0), lean_box(0), v___x_3149_, v___f_3145_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___boxed(lean_object* v_pu_3151_, lean_object* v_t_3152_, lean_object* v_inst_3153_, lean_object* v_inst_3154_, lean_object* v_inst_3155_, lean_object* v_decl_3156_){
_start:
{
uint8_t v_pu_boxed_3157_; uint8_t v_t_boxed_3158_; lean_object* v_res_3159_; 
v_pu_boxed_3157_ = lean_unbox(v_pu_3151_);
v_t_boxed_3158_ = lean_unbox(v_t_3152_);
v_res_3159_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_boxed_3157_, v_t_boxed_3158_, v_inst_3153_, v_inst_3154_, v_inst_3155_, v_decl_3156_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl(lean_object* v_m_3160_, uint8_t v_pu_3161_, uint8_t v_t_3162_, lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_inst_3165_, lean_object* v_decl_3166_){
_start:
{
lean_object* v___x_3167_; 
v___x_3167_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_3161_, v_t_3162_, v_inst_3163_, v_inst_3164_, v_inst_3165_, v_decl_3166_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___boxed(lean_object* v_m_3168_, lean_object* v_pu_3169_, lean_object* v_t_3170_, lean_object* v_inst_3171_, lean_object* v_inst_3172_, lean_object* v_inst_3173_, lean_object* v_decl_3174_){
_start:
{
uint8_t v_pu_boxed_3175_; uint8_t v_t_boxed_3176_; lean_object* v_res_3177_; 
v_pu_boxed_3175_ = lean_unbox(v_pu_3169_);
v_t_boxed_3176_ = lean_unbox(v_t_3170_);
v_res_3177_ = l_Lean_Compiler_LCNF_normLetDecl(v_m_3168_, v_pu_boxed_3175_, v_t_boxed_3176_, v_inst_3171_, v_inst_3172_, v_inst_3173_, v_decl_3174_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(uint8_t v_pu_3178_, uint8_t v_t_3179_){
_start:
{
lean_object* v___x_3180_; lean_object* v_toApplicative_3181_; lean_object* v_toFunctor_3182_; lean_object* v_toSeq_3183_; lean_object* v_toSeqLeft_3184_; lean_object* v_toSeqRight_3185_; lean_object* v___f_3186_; lean_object* v___f_3187_; lean_object* v___f_3188_; lean_object* v___f_3189_; lean_object* v___x_3190_; lean_object* v___f_3191_; lean_object* v___f_3192_; lean_object* v___f_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v_toApplicative_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3225_; 
v___x_3180_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_3181_ = lean_ctor_get(v___x_3180_, 0);
v_toFunctor_3182_ = lean_ctor_get(v_toApplicative_3181_, 0);
v_toSeq_3183_ = lean_ctor_get(v_toApplicative_3181_, 2);
v_toSeqLeft_3184_ = lean_ctor_get(v_toApplicative_3181_, 3);
v_toSeqRight_3185_ = lean_ctor_get(v_toApplicative_3181_, 4);
v___f_3186_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_3187_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_3182_, 2);
v___f_3188_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3188_, 0, v_toFunctor_3182_);
v___f_3189_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3189_, 0, v_toFunctor_3182_);
v___x_3190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3190_, 0, v___f_3188_);
lean_ctor_set(v___x_3190_, 1, v___f_3189_);
lean_inc(v_toSeqRight_3185_);
v___f_3191_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3191_, 0, v_toSeqRight_3185_);
lean_inc(v_toSeqLeft_3184_);
v___f_3192_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3192_, 0, v_toSeqLeft_3184_);
lean_inc(v_toSeq_3183_);
v___f_3193_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3193_, 0, v_toSeq_3183_);
v___x_3194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3190_);
lean_ctor_set(v___x_3194_, 1, v___f_3186_);
lean_ctor_set(v___x_3194_, 2, v___f_3193_);
lean_ctor_set(v___x_3194_, 3, v___f_3192_);
lean_ctor_set(v___x_3194_, 4, v___f_3191_);
v___x_3195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3194_);
lean_ctor_set(v___x_3195_, 1, v___f_3187_);
v___x_3196_ = l_StateRefT_x27_instMonad___redArg(v___x_3195_);
v_toApplicative_3197_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3225_ == 0)
{
lean_object* v_unused_3226_; 
v_unused_3226_ = lean_ctor_get(v___x_3196_, 1);
lean_dec(v_unused_3226_);
v___x_3199_ = v___x_3196_;
v_isShared_3200_ = v_isSharedCheck_3225_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_toApplicative_3197_);
lean_dec(v___x_3196_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3225_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v_toFunctor_3201_; lean_object* v_toSeq_3202_; lean_object* v_toSeqLeft_3203_; lean_object* v_toSeqRight_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3223_; 
v_toFunctor_3201_ = lean_ctor_get(v_toApplicative_3197_, 0);
v_toSeq_3202_ = lean_ctor_get(v_toApplicative_3197_, 2);
v_toSeqLeft_3203_ = lean_ctor_get(v_toApplicative_3197_, 3);
v_toSeqRight_3204_ = lean_ctor_get(v_toApplicative_3197_, 4);
v_isSharedCheck_3223_ = !lean_is_exclusive(v_toApplicative_3197_);
if (v_isSharedCheck_3223_ == 0)
{
lean_object* v_unused_3224_; 
v_unused_3224_ = lean_ctor_get(v_toApplicative_3197_, 1);
lean_dec(v_unused_3224_);
v___x_3206_ = v_toApplicative_3197_;
v_isShared_3207_ = v_isSharedCheck_3223_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_toSeqRight_3204_);
lean_inc(v_toSeqLeft_3203_);
lean_inc(v_toSeq_3202_);
lean_inc(v_toFunctor_3201_);
lean_dec(v_toApplicative_3197_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3223_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___f_3208_; lean_object* v___f_3209_; lean_object* v___f_3210_; lean_object* v___f_3211_; lean_object* v___x_3212_; lean_object* v___f_3213_; lean_object* v___f_3214_; lean_object* v___f_3215_; lean_object* v___x_3217_; 
v___f_3208_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_3209_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_3201_);
v___f_3210_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3210_, 0, v_toFunctor_3201_);
v___f_3211_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3211_, 0, v_toFunctor_3201_);
v___x_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___f_3210_);
lean_ctor_set(v___x_3212_, 1, v___f_3211_);
v___f_3213_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3213_, 0, v_toSeqRight_3204_);
v___f_3214_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3214_, 0, v_toSeqLeft_3203_);
v___f_3215_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3215_, 0, v_toSeq_3202_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 4, v___f_3213_);
lean_ctor_set(v___x_3206_, 3, v___f_3214_);
lean_ctor_set(v___x_3206_, 2, v___f_3215_);
lean_ctor_set(v___x_3206_, 1, v___f_3208_);
lean_ctor_set(v___x_3206_, 0, v___x_3212_);
v___x_3217_ = v___x_3206_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3212_);
lean_ctor_set(v_reuseFailAlloc_3222_, 1, v___f_3208_);
lean_ctor_set(v_reuseFailAlloc_3222_, 2, v___f_3215_);
lean_ctor_set(v_reuseFailAlloc_3222_, 3, v___f_3214_);
lean_ctor_set(v_reuseFailAlloc_3222_, 4, v___f_3213_);
v___x_3217_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
lean_object* v___x_3219_; 
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 1, v___f_3209_);
lean_ctor_set(v___x_3199_, 0, v___x_3217_);
v___x_3219_ = v___x_3199_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3217_);
lean_ctor_set(v_reuseFailAlloc_3221_, 1, v___f_3209_);
v___x_3219_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3220_; 
v___x_3220_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_3220_, 0, lean_box(0));
lean_closure_set(v___x_3220_, 1, lean_box(0));
lean_closure_set(v___x_3220_, 2, v___x_3219_);
return v___x_3220_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___boxed(lean_object* v_pu_3227_, lean_object* v_t_3228_){
_start:
{
uint8_t v_pu_boxed_3229_; uint8_t v_t_boxed_3230_; lean_object* v_res_3231_; 
v_pu_boxed_3229_ = lean_unbox(v_pu_3227_);
v_t_boxed_3230_ = lean_unbox(v_t_3228_);
v_res_3231_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(v_pu_boxed_3229_, v_t_boxed_3230_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg(uint8_t v_pu_3232_, lean_object* v_inst_3233_, lean_object* v_result_3234_, lean_object* v_x_3235_){
_start:
{
if (lean_obj_tag(v_result_3234_) == 0)
{
lean_object* v_fvarId_3236_; lean_object* v___x_3237_; 
lean_dec(v_inst_3233_);
v_fvarId_3236_ = lean_ctor_get(v_result_3234_, 0);
lean_inc(v_fvarId_3236_);
lean_dec_ref(v_result_3234_);
v___x_3237_ = lean_apply_1(v_x_3235_, v_fvarId_3236_);
return v___x_3237_;
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
lean_dec(v_x_3235_);
v___x_3238_ = lean_box(v_pu_3232_);
v___x_3239_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3239_, 0, v___x_3238_);
v___x_3240_ = lean_apply_2(v_inst_3233_, lean_box(0), v___x_3239_);
return v___x_3240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg___boxed(lean_object* v_pu_3241_, lean_object* v_inst_3242_, lean_object* v_result_3243_, lean_object* v_x_3244_){
_start:
{
uint8_t v_pu_boxed_3245_; lean_object* v_res_3246_; 
v_pu_boxed_3245_ = lean_unbox(v_pu_3241_);
v_res_3246_ = l_Lean_Compiler_LCNF_withNormFVarResult___redArg(v_pu_boxed_3245_, v_inst_3242_, v_result_3243_, v_x_3244_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult(lean_object* v_m_3247_, uint8_t v_pu_3248_, lean_object* v_inst_3249_, lean_object* v_inst_3250_, lean_object* v_result_3251_, lean_object* v_x_3252_){
_start:
{
if (lean_obj_tag(v_result_3251_) == 0)
{
lean_object* v_fvarId_3253_; lean_object* v___x_3254_; 
lean_dec(v_inst_3249_);
v_fvarId_3253_ = lean_ctor_get(v_result_3251_, 0);
lean_inc(v_fvarId_3253_);
lean_dec_ref(v_result_3251_);
v___x_3254_ = lean_apply_1(v_x_3252_, v_fvarId_3253_);
return v___x_3254_;
}
else
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
lean_dec(v_x_3252_);
v___x_3255_ = lean_box(v_pu_3248_);
v___x_3256_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3256_, 0, v___x_3255_);
v___x_3257_ = lean_apply_2(v_inst_3249_, lean_box(0), v___x_3256_);
return v___x_3257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___boxed(lean_object* v_m_3258_, lean_object* v_pu_3259_, lean_object* v_inst_3260_, lean_object* v_inst_3261_, lean_object* v_result_3262_, lean_object* v_x_3263_){
_start:
{
uint8_t v_pu_boxed_3264_; lean_object* v_res_3265_; 
v_pu_boxed_3264_ = lean_unbox(v_pu_3259_);
v_res_3265_ = l_Lean_Compiler_LCNF_withNormFVarResult(v_m_3258_, v_pu_boxed_3264_, v_inst_3260_, v_inst_3261_, v_result_3262_, v_x_3263_);
lean_dec_ref(v_inst_3261_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(uint8_t v_pu_3266_, uint8_t v_t_3267_, lean_object* v_args_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3271_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_3266_, v___y_3269_, v_args_3268_, v_t_3267_);
v___x_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg___boxed(lean_object* v_pu_3273_, lean_object* v_t_3274_, lean_object* v_args_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
uint8_t v_pu_boxed_3278_; uint8_t v_t_boxed_3279_; lean_object* v_res_3280_; 
v_pu_boxed_3278_ = lean_unbox(v_pu_3273_);
v_t_boxed_3279_ = lean_unbox(v_t_3274_);
v_res_3280_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_boxed_3278_, v_t_boxed_3279_, v_args_3275_, v___y_3276_);
lean_dec_ref(v___y_3276_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(uint8_t v_pu_3281_, uint8_t v_t_3282_, lean_object* v_i_3283_, lean_object* v_as_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v___x_3288_; uint8_t v___x_3289_; 
v___x_3288_ = lean_array_get_size(v_as_3284_);
v___x_3289_ = lean_nat_dec_lt(v_i_3283_, v___x_3288_);
if (v___x_3289_ == 0)
{
lean_object* v___x_3290_; 
lean_dec(v_i_3283_);
v___x_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3290_, 0, v_as_3284_);
return v___x_3290_;
}
else
{
lean_object* v_a_3291_; lean_object* v_type_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v_a_3291_ = lean_array_fget_borrowed(v_as_3284_, v_i_3283_);
v_type_3292_ = lean_ctor_get(v_a_3291_, 2);
lean_inc_ref(v_type_3292_);
v___x_3293_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3281_, v___y_3285_, v_t_3282_, v_type_3292_);
lean_inc(v_a_3291_);
v___x_3294_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_3281_, v_a_3291_, v___x_3293_, v___y_3286_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; size_t v___x_3296_; size_t v___x_3297_; uint8_t v___x_3298_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_a_3295_);
lean_dec_ref(v___x_3294_);
v___x_3296_ = lean_ptr_addr(v_a_3291_);
v___x_3297_ = lean_ptr_addr(v_a_3295_);
v___x_3298_ = lean_usize_dec_eq(v___x_3296_, v___x_3297_);
if (v___x_3298_ == 0)
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3299_ = lean_unsigned_to_nat(1u);
v___x_3300_ = lean_nat_add(v_i_3283_, v___x_3299_);
v___x_3301_ = lean_array_fset(v_as_3284_, v_i_3283_, v_a_3295_);
lean_dec(v_i_3283_);
v_i_3283_ = v___x_3300_;
v_as_3284_ = v___x_3301_;
goto _start;
}
else
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
lean_dec(v_a_3295_);
v___x_3303_ = lean_unsigned_to_nat(1u);
v___x_3304_ = lean_nat_add(v_i_3283_, v___x_3303_);
lean_dec(v_i_3283_);
v_i_3283_ = v___x_3304_;
goto _start;
}
}
else
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
lean_dec_ref(v_as_3284_);
lean_dec(v_i_3283_);
v_a_3306_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3294_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3294_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg___boxed(lean_object* v_pu_3314_, lean_object* v_t_3315_, lean_object* v_i_3316_, lean_object* v_as_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
uint8_t v_pu_boxed_3321_; uint8_t v_t_boxed_3322_; lean_object* v_res_3323_; 
v_pu_boxed_3321_ = lean_unbox(v_pu_3314_);
v_t_boxed_3322_ = lean_unbox(v_t_3315_);
v_res_3323_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_boxed_3321_, v_t_boxed_3322_, v_i_3316_, v_as_3317_, v___y_3318_, v___y_3319_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(uint8_t v_pu_3324_, uint8_t v_t_3325_, lean_object* v_ps_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = lean_unsigned_to_nat(0u);
v___x_3334_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_3324_, v_t_3325_, v___x_3333_, v_ps_3326_, v___y_3327_, v___y_3329_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg___boxed(lean_object* v_pu_3335_, lean_object* v_t_3336_, lean_object* v_ps_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
uint8_t v_pu_boxed_3344_; uint8_t v_t_boxed_3345_; lean_object* v_res_3346_; 
v_pu_boxed_3344_ = lean_unbox(v_pu_3335_);
v_t_boxed_3345_ = lean_unbox(v_t_3336_);
v_res_3346_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_boxed_3344_, v_t_boxed_3345_, v_ps_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec_ref(v___y_3338_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(uint8_t v_pu_3347_, uint8_t v_t_3348_, lean_object* v_decl_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v_type_3353_; lean_object* v_value_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v_type_3353_ = lean_ctor_get(v_decl_3349_, 2);
v_value_3354_ = lean_ctor_get(v_decl_3349_, 3);
lean_inc_ref(v_type_3353_);
v___x_3355_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3347_, v___y_3350_, v_t_3348_, v_type_3353_);
lean_inc(v_value_3354_);
v___x_3356_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3347_, v___y_3350_, v_value_3354_, v_t_3348_);
v___x_3357_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_3347_, v_decl_3349_, v___x_3355_, v___x_3356_, v___y_3351_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg___boxed(lean_object* v_pu_3358_, lean_object* v_t_3359_, lean_object* v_decl_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
uint8_t v_pu_boxed_3364_; uint8_t v_t_boxed_3365_; lean_object* v_res_3366_; 
v_pu_boxed_3364_ = lean_unbox(v_pu_3358_);
v_t_boxed_3365_ = lean_unbox(v_t_3359_);
v_res_3366_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_boxed_3364_, v_t_boxed_3365_, v_decl_3360_, v___y_3361_, v___y_3362_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(uint8_t v_pu_3367_, uint8_t v_t_3368_, lean_object* v_i_3369_, lean_object* v_as_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v___x_3377_; uint8_t v___x_3378_; 
v___x_3377_ = lean_array_get_size(v_as_3370_);
v___x_3378_ = lean_nat_dec_lt(v_i_3369_, v___x_3377_);
if (v___x_3378_ == 0)
{
lean_object* v___x_3379_; 
lean_dec(v_i_3369_);
v___x_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3379_, 0, v_as_3370_);
return v___x_3379_;
}
else
{
lean_object* v_a_3380_; lean_object* v_a_3382_; 
v_a_3380_ = lean_array_fget_borrowed(v_as_3370_, v_i_3369_);
switch(lean_obj_tag(v_a_3380_))
{
case 0:
{
lean_object* v_params_3393_; lean_object* v_code_3394_; lean_object* v___x_3395_; 
v_params_3393_ = lean_ctor_get(v_a_3380_, 1);
v_code_3394_ = lean_ctor_get(v_a_3380_, 2);
lean_inc_ref(v_params_3393_);
v___x_3395_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_3367_, v_t_3368_, v_params_3393_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; lean_object* v___x_3397_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_a_3396_);
lean_dec_ref(v___x_3395_);
lean_inc_ref(v_code_3394_);
v___x_3397_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3367_, v_t_3368_, v_code_3394_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; lean_object* v___x_3399_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_a_3398_);
lean_dec_ref(v___x_3397_);
lean_inc_ref(v_a_3380_);
v___x_3399_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_3367_, v_a_3380_, v_a_3396_, v_a_3398_);
v_a_3382_ = v___x_3399_;
goto v___jp_3381_;
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_dec(v_a_3396_);
lean_dec_ref(v_as_3370_);
lean_dec(v_i_3369_);
v_a_3400_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3397_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3397_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_dec_ref(v_as_3370_);
lean_dec(v_i_3369_);
v_a_3408_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3395_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3395_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
case 1:
{
lean_object* v_code_3416_; lean_object* v___x_3417_; 
v_code_3416_ = lean_ctor_get(v_a_3380_, 1);
lean_inc_ref(v_code_3416_);
v___x_3417_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3367_, v_t_3368_, v_code_3416_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_a_3418_; lean_object* v___x_3419_; 
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3418_);
lean_dec_ref(v___x_3417_);
lean_inc_ref(v_a_3380_);
v___x_3419_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3380_, v_a_3418_);
v_a_3382_ = v___x_3419_;
goto v___jp_3381_;
}
else
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
lean_dec_ref(v_as_3370_);
lean_dec(v_i_3369_);
v_a_3420_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3422_ = v___x_3417_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3417_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3420_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
}
default: 
{
lean_object* v_code_3428_; lean_object* v___x_3429_; 
v_code_3428_ = lean_ctor_get(v_a_3380_, 0);
lean_inc_ref(v_code_3428_);
v___x_3429_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3367_, v_t_3368_, v_code_3428_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; lean_object* v___x_3431_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_a_3430_);
lean_dec_ref(v___x_3429_);
lean_inc_ref(v_a_3380_);
v___x_3431_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3380_, v_a_3430_);
v_a_3382_ = v___x_3431_;
goto v___jp_3381_;
}
else
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
lean_dec_ref(v_as_3370_);
lean_dec(v_i_3369_);
v_a_3432_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3434_ = v___x_3429_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3429_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3432_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
}
v___jp_3381_:
{
size_t v___x_3383_; size_t v___x_3384_; uint8_t v___x_3385_; 
v___x_3383_ = lean_ptr_addr(v_a_3380_);
v___x_3384_ = lean_ptr_addr(v_a_3382_);
v___x_3385_ = lean_usize_dec_eq(v___x_3383_, v___x_3384_);
if (v___x_3385_ == 0)
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3386_ = lean_unsigned_to_nat(1u);
v___x_3387_ = lean_nat_add(v_i_3369_, v___x_3386_);
v___x_3388_ = lean_array_fset(v_as_3370_, v_i_3369_, v_a_3382_);
lean_dec(v_i_3369_);
v_i_3369_ = v___x_3387_;
v_as_3370_ = v___x_3388_;
goto _start;
}
else
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
lean_dec_ref(v_a_3382_);
v___x_3390_ = lean_unsigned_to_nat(1u);
v___x_3391_ = lean_nat_add(v_i_3369_, v___x_3390_);
lean_dec(v_i_3369_);
v_i_3369_ = v___x_3391_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp(uint8_t v_pu_3440_, uint8_t v_t_3441_, lean_object* v_code_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_){
_start:
{
switch(lean_obj_tag(v_code_3442_))
{
case 0:
{
lean_object* v_decl_3449_; lean_object* v_k_3450_; lean_object* v___x_3451_; 
v_decl_3449_ = lean_ctor_get(v_code_3442_, 0);
v_k_3450_ = lean_ctor_get(v_code_3442_, 1);
lean_inc_ref(v_decl_3449_);
v___x_3451_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_3440_, v_t_3441_, v_decl_3449_, v_a_3443_, v_a_3445_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; lean_object* v___x_3453_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3452_);
lean_dec_ref(v___x_3451_);
lean_inc_ref(v_k_3450_);
v___x_3453_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3440_, v_t_3441_, v_k_3450_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3481_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3456_ = v___x_3453_;
v_isShared_3457_ = v_isSharedCheck_3481_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3453_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3481_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
uint8_t v___y_3459_; size_t v___x_3475_; size_t v___x_3476_; uint8_t v___x_3477_; 
v___x_3475_ = lean_ptr_addr(v_k_3450_);
v___x_3476_ = lean_ptr_addr(v_a_3454_);
v___x_3477_ = lean_usize_dec_eq(v___x_3475_, v___x_3476_);
if (v___x_3477_ == 0)
{
v___y_3459_ = v___x_3477_;
goto v___jp_3458_;
}
else
{
size_t v___x_3478_; size_t v___x_3479_; uint8_t v___x_3480_; 
v___x_3478_ = lean_ptr_addr(v_decl_3449_);
v___x_3479_ = lean_ptr_addr(v_a_3452_);
v___x_3480_ = lean_usize_dec_eq(v___x_3478_, v___x_3479_);
v___y_3459_ = v___x_3480_;
goto v___jp_3458_;
}
v___jp_3458_:
{
if (v___y_3459_ == 0)
{
lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3469_; 
v_isSharedCheck_3469_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_3469_ == 0)
{
lean_object* v_unused_3470_; lean_object* v_unused_3471_; 
v_unused_3470_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_3470_);
v_unused_3471_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_3471_);
v___x_3461_ = v_code_3442_;
v_isShared_3462_ = v_isSharedCheck_3469_;
goto v_resetjp_3460_;
}
else
{
lean_dec(v_code_3442_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3469_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 1, v_a_3454_);
lean_ctor_set(v___x_3461_, 0, v_a_3452_);
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3452_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v_a_3454_);
v___x_3464_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
lean_object* v___x_3466_; 
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 0, v___x_3464_);
v___x_3466_ = v___x_3456_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3464_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
else
{
lean_object* v___x_3473_; 
lean_dec(v_a_3454_);
lean_dec(v_a_3452_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 0, v_code_3442_);
v___x_3473_ = v___x_3456_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_code_3442_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
}
else
{
lean_dec(v_a_3452_);
lean_dec_ref(v_code_3442_);
return v___x_3453_;
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref(v_code_3442_);
v_a_3482_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3451_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3451_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
case 1:
{
lean_object* v_decl_3490_; lean_object* v_k_3491_; lean_object* v___x_3492_; 
v_decl_3490_ = lean_ctor_get(v_code_3442_, 0);
v_k_3491_ = lean_ctor_get(v_code_3442_, 1);
lean_inc_ref(v_decl_3490_);
v___x_3492_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3440_, v_t_3441_, v_decl_3490_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3494_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref(v___x_3492_);
lean_inc_ref(v_k_3491_);
v___x_3494_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3440_, v_t_3441_, v_k_3491_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3522_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3497_ = v___x_3494_;
v_isShared_3498_ = v_isSharedCheck_3522_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3494_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3522_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
uint8_t v___y_3500_; size_t v___x_3516_; size_t v___x_3517_; uint8_t v___x_3518_; 
v___x_3516_ = lean_ptr_addr(v_k_3491_);
v___x_3517_ = lean_ptr_addr(v_a_3495_);
v___x_3518_ = lean_usize_dec_eq(v___x_3516_, v___x_3517_);
if (v___x_3518_ == 0)
{
v___y_3500_ = v___x_3518_;
goto v___jp_3499_;
}
else
{
size_t v___x_3519_; size_t v___x_3520_; uint8_t v___x_3521_; 
v___x_3519_ = lean_ptr_addr(v_decl_3490_);
v___x_3520_ = lean_ptr_addr(v_a_3493_);
v___x_3521_ = lean_usize_dec_eq(v___x_3519_, v___x_3520_);
v___y_3500_ = v___x_3521_;
goto v___jp_3499_;
}
v___jp_3499_:
{
if (v___y_3500_ == 0)
{
lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3510_; 
v_isSharedCheck_3510_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_3510_ == 0)
{
lean_object* v_unused_3511_; lean_object* v_unused_3512_; 
v_unused_3511_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_3511_);
v_unused_3512_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_3512_);
v___x_3502_ = v_code_3442_;
v_isShared_3503_ = v_isSharedCheck_3510_;
goto v_resetjp_3501_;
}
else
{
lean_dec(v_code_3442_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3510_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 1, v_a_3495_);
lean_ctor_set(v___x_3502_, 0, v_a_3493_);
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3493_);
lean_ctor_set(v_reuseFailAlloc_3509_, 1, v_a_3495_);
v___x_3505_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
lean_object* v___x_3507_; 
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v___x_3505_);
v___x_3507_ = v___x_3497_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
else
{
lean_object* v___x_3514_; 
lean_dec(v_a_3495_);
lean_dec(v_a_3493_);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v_code_3442_);
v___x_3514_ = v___x_3497_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_code_3442_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
}
else
{
lean_dec(v_a_3493_);
lean_dec_ref(v_code_3442_);
return v___x_3494_;
}
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_dec_ref(v_code_3442_);
v_a_3523_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3492_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3492_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
case 2:
{
lean_object* v_decl_3531_; lean_object* v_k_3532_; lean_object* v___x_3533_; 
v_decl_3531_ = lean_ctor_get(v_code_3442_, 0);
v_k_3532_ = lean_ctor_get(v_code_3442_, 1);
lean_inc_ref(v_decl_3531_);
v___x_3533_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3440_, v_t_3441_, v_decl_3531_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; lean_object* v___x_3535_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3534_);
lean_dec_ref(v___x_3533_);
lean_inc_ref(v_k_3532_);
v___x_3535_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3440_, v_t_3441_, v_k_3532_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3563_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3538_ = v___x_3535_;
v_isShared_3539_ = v_isSharedCheck_3563_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3535_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3563_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
uint8_t v___y_3541_; size_t v___x_3557_; size_t v___x_3558_; uint8_t v___x_3559_; 
v___x_3557_ = lean_ptr_addr(v_k_3532_);
v___x_3558_ = lean_ptr_addr(v_a_3536_);
v___x_3559_ = lean_usize_dec_eq(v___x_3557_, v___x_3558_);
if (v___x_3559_ == 0)
{
v___y_3541_ = v___x_3559_;
goto v___jp_3540_;
}
else
{
size_t v___x_3560_; size_t v___x_3561_; uint8_t v___x_3562_; 
v___x_3560_ = lean_ptr_addr(v_decl_3531_);
v___x_3561_ = lean_ptr_addr(v_a_3534_);
v___x_3562_ = lean_usize_dec_eq(v___x_3560_, v___x_3561_);
v___y_3541_ = v___x_3562_;
goto v___jp_3540_;
}
v___jp_3540_:
{
if (v___y_3541_ == 0)
{
lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3551_; 
v_isSharedCheck_3551_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_3551_ == 0)
{
lean_object* v_unused_3552_; lean_object* v_unused_3553_; 
v_unused_3552_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_3552_);
v_unused_3553_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_3553_);
v___x_3543_ = v_code_3442_;
v_isShared_3544_ = v_isSharedCheck_3551_;
goto v_resetjp_3542_;
}
else
{
lean_dec(v_code_3442_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3551_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
lean_ctor_set(v___x_3543_, 1, v_a_3536_);
lean_ctor_set(v___x_3543_, 0, v_a_3534_);
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3534_);
lean_ctor_set(v_reuseFailAlloc_3550_, 1, v_a_3536_);
v___x_3546_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
lean_object* v___x_3548_; 
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 0, v___x_3546_);
v___x_3548_ = v___x_3538_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v___x_3546_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
else
{
lean_object* v___x_3555_; 
lean_dec(v_a_3536_);
lean_dec(v_a_3534_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 0, v_code_3442_);
v___x_3555_ = v___x_3538_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_code_3442_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
}
}
else
{
lean_dec(v_a_3534_);
lean_dec_ref(v_code_3442_);
return v___x_3535_;
}
}
else
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3571_; 
lean_dec_ref(v_code_3442_);
v_a_3564_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3566_ = v___x_3533_;
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3533_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3564_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3572_; lean_object* v_args_3573_; lean_object* v___x_3574_; 
v_fvarId_3572_ = lean_ctor_get(v_code_3442_, 0);
v_args_3573_ = lean_ctor_get(v_code_3442_, 1);
lean_inc(v_fvarId_3572_);
v___x_3574_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3443_, v_fvarId_3572_, v_t_3441_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_fvarId_3575_; lean_object* v___x_3576_; 
v_fvarId_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_fvarId_3575_);
lean_dec_ref(v___x_3574_);
lean_inc_ref(v_args_3573_);
v___x_3576_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_3440_, v_t_3441_, v_args_3573_, v_a_3443_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3602_; 
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3579_ = v___x_3576_;
v_isShared_3580_ = v_isSharedCheck_3602_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3576_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3602_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
uint8_t v___y_3582_; uint8_t v___x_3598_; 
v___x_3598_ = l_Lean_instBEqFVarId_beq(v_fvarId_3572_, v_fvarId_3575_);
if (v___x_3598_ == 0)
{
v___y_3582_ = v___x_3598_;
goto v___jp_3581_;
}
else
{
size_t v___x_3599_; size_t v___x_3600_; uint8_t v___x_3601_; 
v___x_3599_ = lean_ptr_addr(v_args_3573_);
v___x_3600_ = lean_ptr_addr(v_a_3577_);
v___x_3601_ = lean_usize_dec_eq(v___x_3599_, v___x_3600_);
v___y_3582_ = v___x_3601_;
goto v___jp_3581_;
}
v___jp_3581_:
{
if (v___y_3582_ == 0)
{
lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3592_; 
v_isSharedCheck_3592_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_3592_ == 0)
{
lean_object* v_unused_3593_; lean_object* v_unused_3594_; 
v_unused_3593_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_3593_);
v_unused_3594_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_3594_);
v___x_3584_ = v_code_3442_;
v_isShared_3585_ = v_isSharedCheck_3592_;
goto v_resetjp_3583_;
}
else
{
lean_dec(v_code_3442_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3592_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 1, v_a_3577_);
lean_ctor_set(v___x_3584_, 0, v_fvarId_3575_);
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_fvarId_3575_);
lean_ctor_set(v_reuseFailAlloc_3591_, 1, v_a_3577_);
v___x_3587_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
lean_object* v___x_3589_; 
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v___x_3587_);
v___x_3589_ = v___x_3579_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
else
{
lean_object* v___x_3596_; 
lean_dec(v_a_3577_);
lean_dec(v_fvarId_3575_);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v_code_3442_);
v___x_3596_ = v___x_3579_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_code_3442_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
lean_dec(v_fvarId_3575_);
lean_dec_ref(v_code_3442_);
v_a_3603_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3576_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3576_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
else
{
lean_object* v___x_3611_; 
lean_dec_ref(v_code_3442_);
v___x_3611_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3440_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
return v___x_3611_;
}
}
case 4:
{
lean_object* v_cases_3612_; lean_object* v_typeName_3613_; lean_object* v_resultType_3614_; lean_object* v_discr_3615_; lean_object* v_alts_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3663_; 
v_cases_3612_ = lean_ctor_get(v_code_3442_, 0);
lean_inc_ref(v_cases_3612_);
v_typeName_3613_ = lean_ctor_get(v_cases_3612_, 0);
v_resultType_3614_ = lean_ctor_get(v_cases_3612_, 1);
v_discr_3615_ = lean_ctor_get(v_cases_3612_, 2);
v_alts_3616_ = lean_ctor_get(v_cases_3612_, 3);
v_isSharedCheck_3663_ = !lean_is_exclusive(v_cases_3612_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3618_ = v_cases_3612_;
v_isShared_3619_ = v_isSharedCheck_3663_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_alts_3616_);
lean_inc(v_discr_3615_);
lean_inc(v_resultType_3614_);
lean_inc(v_typeName_3613_);
lean_dec(v_cases_3612_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3663_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; 
lean_inc_ref(v_resultType_3614_);
v___x_3620_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3440_, v_a_3443_, v_t_3441_, v_resultType_3614_);
lean_inc(v_discr_3615_);
v___x_3621_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3443_, v_discr_3615_, v_t_3441_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_fvarId_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3661_; 
v_fvarId_3622_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3624_ = v___x_3621_;
v_isShared_3625_ = v_isSharedCheck_3661_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_fvarId_3622_);
lean_dec(v___x_3621_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3661_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3616_);
v___x_3627_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_3440_, v_t_3441_, v___x_3626_, v_alts_3616_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3652_; 
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3630_ = v___x_3627_;
v_isShared_3631_ = v_isSharedCheck_3652_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3627_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3652_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
uint8_t v___y_3643_; size_t v___x_3646_; size_t v___x_3647_; uint8_t v___x_3648_; 
v___x_3646_ = lean_ptr_addr(v_alts_3616_);
lean_dec_ref(v_alts_3616_);
v___x_3647_ = lean_ptr_addr(v_a_3628_);
v___x_3648_ = lean_usize_dec_eq(v___x_3646_, v___x_3647_);
if (v___x_3648_ == 0)
{
lean_dec_ref(v_resultType_3614_);
v___y_3643_ = v___x_3648_;
goto v___jp_3642_;
}
else
{
size_t v___x_3649_; size_t v___x_3650_; uint8_t v___x_3651_; 
v___x_3649_ = lean_ptr_addr(v_resultType_3614_);
lean_dec_ref(v_resultType_3614_);
v___x_3650_ = lean_ptr_addr(v___x_3620_);
v___x_3651_ = lean_usize_dec_eq(v___x_3649_, v___x_3650_);
v___y_3643_ = v___x_3651_;
goto v___jp_3642_;
}
v___jp_3632_:
{
lean_object* v___x_3634_; 
if (v_isShared_3619_ == 0)
{
lean_ctor_set(v___x_3618_, 3, v_a_3628_);
lean_ctor_set(v___x_3618_, 2, v_fvarId_3622_);
lean_ctor_set(v___x_3618_, 1, v___x_3620_);
v___x_3634_ = v___x_3618_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_typeName_3613_);
lean_ctor_set(v_reuseFailAlloc_3641_, 1, v___x_3620_);
lean_ctor_set(v_reuseFailAlloc_3641_, 2, v_fvarId_3622_);
lean_ctor_set(v_reuseFailAlloc_3641_, 3, v_a_3628_);
v___x_3634_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
lean_object* v___x_3636_; 
if (v_isShared_3625_ == 0)
{
lean_ctor_set_tag(v___x_3624_, 4);
lean_ctor_set(v___x_3624_, 0, v___x_3634_);
v___x_3636_ = v___x_3624_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3634_);
v___x_3636_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
lean_object* v___x_3638_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 0, v___x_3636_);
v___x_3638_ = v___x_3630_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3636_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
v___jp_3642_:
{
if (v___y_3643_ == 0)
{
lean_dec(v_discr_3615_);
lean_dec_ref(v_code_3442_);
goto v___jp_3632_;
}
else
{
uint8_t v___x_3644_; 
v___x_3644_ = l_Lean_instBEqFVarId_beq(v_discr_3615_, v_fvarId_3622_);
lean_dec(v_discr_3615_);
if (v___x_3644_ == 0)
{
lean_dec_ref(v_code_3442_);
goto v___jp_3632_;
}
else
{
lean_object* v___x_3645_; 
lean_del_object(v___x_3630_);
lean_dec(v_a_3628_);
lean_del_object(v___x_3624_);
lean_dec(v_fvarId_3622_);
lean_dec_ref(v___x_3620_);
lean_del_object(v___x_3618_);
lean_dec(v_typeName_3613_);
v___x_3645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3645_, 0, v_code_3442_);
return v___x_3645_;
}
}
}
}
}
else
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3660_; 
lean_del_object(v___x_3624_);
lean_dec(v_fvarId_3622_);
lean_dec_ref(v___x_3620_);
lean_del_object(v___x_3618_);
lean_dec_ref(v_alts_3616_);
lean_dec(v_discr_3615_);
lean_dec_ref(v_resultType_3614_);
lean_dec(v_typeName_3613_);
lean_dec_ref(v_code_3442_);
v_a_3653_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3655_ = v___x_3627_;
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3627_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
if (v_isShared_3656_ == 0)
{
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_a_3653_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
}
}
else
{
lean_object* v___x_3662_; 
lean_dec_ref(v___x_3620_);
lean_del_object(v___x_3618_);
lean_dec_ref(v_alts_3616_);
lean_dec(v_discr_3615_);
lean_dec_ref(v_resultType_3614_);
lean_dec(v_typeName_3613_);
lean_dec_ref(v_code_3442_);
v___x_3662_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3440_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
return v___x_3662_;
}
}
}
case 5:
{
lean_object* v_fvarId_3664_; lean_object* v___x_3665_; 
v_fvarId_3664_ = lean_ctor_get(v_code_3442_, 0);
lean_inc(v_fvarId_3664_);
v___x_3665_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3443_, v_fvarId_3664_, v_t_3441_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_fvarId_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3685_; 
v_fvarId_3666_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3668_ = v___x_3665_;
v_isShared_3669_ = v_isSharedCheck_3685_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_fvarId_3666_);
lean_dec(v___x_3665_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3685_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
uint8_t v___x_3670_; 
v___x_3670_ = l_Lean_instBEqFVarId_beq(v_fvarId_3664_, v_fvarId_3666_);
if (v___x_3670_ == 0)
{
lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3680_; 
v_isSharedCheck_3680_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_3680_ == 0)
{
lean_object* v_unused_3681_; 
v_unused_3681_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_3681_);
v___x_3672_ = v_code_3442_;
v_isShared_3673_ = v_isSharedCheck_3680_;
goto v_resetjp_3671_;
}
else
{
lean_dec(v_code_3442_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3680_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v_fvarId_3666_);
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_fvarId_3666_);
v___x_3675_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
lean_object* v___x_3677_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v___x_3675_);
v___x_3677_ = v___x_3668_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
else
{
lean_object* v___x_3683_; 
lean_dec(v_fvarId_3666_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v_code_3442_);
v___x_3683_ = v___x_3668_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_code_3442_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
else
{
lean_object* v___x_3686_; 
lean_dec_ref(v_code_3442_);
v___x_3686_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3440_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
return v___x_3686_;
}
}
case 6:
{
lean_object* v_type_3687_; lean_object* v___x_3688_; size_t v___x_3689_; size_t v___x_3690_; uint8_t v___x_3691_; 
v_type_3687_ = lean_ctor_get(v_code_3442_, 0);
lean_inc_ref(v_type_3687_);
v___x_3688_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3440_, v_a_3443_, v_t_3441_, v_type_3687_);
v___x_3689_ = lean_ptr_addr(v_type_3687_);
v___x_3690_ = lean_ptr_addr(v___x_3688_);
v___x_3691_ = lean_usize_dec_eq(v___x_3689_, v___x_3690_);
if (v___x_3691_ == 0)
{
lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3699_; 
v_isSharedCheck_3699_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_3699_ == 0)
{
lean_object* v_unused_3700_; 
v_unused_3700_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_3700_);
v___x_3693_ = v_code_3442_;
v_isShared_3694_ = v_isSharedCheck_3699_;
goto v_resetjp_3692_;
}
else
{
lean_dec(v_code_3442_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3699_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 0, v___x_3688_);
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3688_);
v___x_3696_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
lean_object* v___x_3697_; 
v___x_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3696_);
return v___x_3697_;
}
}
}
else
{
lean_object* v___x_3701_; 
lean_dec_ref(v___x_3688_);
v___x_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3701_, 0, v_code_3442_);
return v___x_3701_;
}
}
case 7:
{
lean_object* v_fvarId_3702_; lean_object* v_i_3703_; lean_object* v_y_3704_; lean_object* v_k_3705_; lean_object* v___x_3706_; 
v_fvarId_3702_ = lean_ctor_get(v_code_3442_, 0);
v_i_3703_ = lean_ctor_get(v_code_3442_, 1);
v_y_3704_ = lean_ctor_get(v_code_3442_, 2);
v_k_3705_ = lean_ctor_get(v_code_3442_, 3);
lean_inc(v_fvarId_3702_);
v___x_3706_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3443_, v_fvarId_3702_, v_t_3441_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_fvarId_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v_fvarId_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_fvarId_3707_);
lean_dec_ref(v___x_3706_);
lean_inc(v_y_3704_);
v___x_3708_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_3440_, v_a_3443_, v_y_3704_, v_t_3441_);
lean_inc_ref(v_k_3705_);
v___x_3709_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3440_, v_t_3441_, v_k_3705_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3771_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3712_ = v___x_3709_;
v_isShared_3713_ = v_isSharedCheck_3771_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3709_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3771_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
uint8_t v___y_3715_; size_t v___x_3767_; size_t v___x_3768_; uint8_t v___x_3769_; 
v___x_3767_ = lean_ptr_addr(v_fvarId_3702_);
v___x_3768_ = lean_ptr_addr(v_fvarId_3707_);
v___x_3769_ = lean_usize_dec_eq(v___x_3767_, v___x_3768_);
if (v___x_3769_ == 0)
{
v___y_3715_ = v___x_3769_;
goto v___jp_3714_;
}
else
{
uint8_t v___x_3770_; 
v___x_3770_ = lean_nat_dec_eq(v_i_3703_, v_i_3703_);
v___y_3715_ = v___x_3770_;
goto v___jp_3714_;
}
v___jp_3714_:
{
if (v___y_3715_ == 0)
{
lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3725_; 
lean_inc(v_i_3703_);
v_isSharedCheck_3725_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_3725_ == 0)
{
lean_object* v_unused_3726_; lean_object* v_unused_3727_; lean_object* v_unused_3728_; lean_object* v_unused_3729_; 
v_unused_3726_ = lean_ctor_get(v_code_3442_, 3);
lean_dec(v_unused_3726_);
v_unused_3727_ = lean_ctor_get(v_code_3442_, 2);
lean_dec(v_unused_3727_);
v_unused_3728_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_3728_);
v_unused_3729_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_3729_);
v___x_3717_ = v_code_3442_;
v_isShared_3718_ = v_isSharedCheck_3725_;
goto v_resetjp_3716_;
}
else
{
lean_dec(v_code_3442_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3725_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 3, v_a_3710_);
lean_ctor_set(v___x_3717_, 2, v___x_3708_);
lean_ctor_set(v___x_3717_, 0, v_fvarId_3707_);
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_fvarId_3707_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v_i_3703_);
lean_ctor_set(v_reuseFailAlloc_3724_, 2, v___x_3708_);
lean_ctor_set(v_reuseFailAlloc_3724_, 3, v_a_3710_);
v___x_3720_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
lean_object* v___x_3722_; 
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 0, v___x_3720_);
v___x_3722_ = v___x_3712_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3720_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
else
{
size_t v___x_3730_; size_t v___x_3731_; uint8_t v___x_3732_; 
v___x_3730_ = lean_ptr_addr(v_y_3704_);
v___x_3731_ = lean_ptr_addr(v___x_3708_);
v___x_3732_ = lean_usize_dec_eq(v___x_3730_, v___x_3731_);
if (v___x_3732_ == 0)
{
lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3742_; 
lean_inc(v_i_3703_);
v_isSharedCheck_3742_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_3742_ == 0)
{
lean_object* v_unused_3743_; lean_object* v_unused_3744_; lean_object* v_unused_3745_; lean_object* v_unused_3746_; 
v_unused_3743_ = lean_ctor_get(v_code_3442_, 3);
lean_dec(v_unused_3743_);
v_unused_3744_ = lean_ctor_get(v_code_3442_, 2);
lean_dec(v_unused_3744_);
v_unused_3745_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_3745_);
v_unused_3746_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_3746_);
v___x_3734_ = v_code_3442_;
v_isShared_3735_ = v_isSharedCheck_3742_;
goto v_resetjp_3733_;
}
else
{
lean_dec(v_code_3442_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3742_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 3, v_a_3710_);
lean_ctor_set(v___x_3734_, 2, v___x_3708_);
lean_ctor_set(v___x_3734_, 0, v_fvarId_3707_);
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_fvarId_3707_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v_i_3703_);
lean_ctor_set(v_reuseFailAlloc_3741_, 2, v___x_3708_);
lean_ctor_set(v_reuseFailAlloc_3741_, 3, v_a_3710_);
v___x_3737_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
lean_object* v___x_3739_; 
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 0, v___x_3737_);
v___x_3739_ = v___x_3712_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3737_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
else
{
size_t v___x_3747_; size_t v___x_3748_; uint8_t v___x_3749_; 
v___x_3747_ = lean_ptr_addr(v_k_3705_);
v___x_3748_ = lean_ptr_addr(v_a_3710_);
v___x_3749_ = lean_usize_dec_eq(v___x_3747_, v___x_3748_);
if (v___x_3749_ == 0)
{
lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3759_; 
lean_inc(v_i_3703_);
v_isSharedCheck_3759_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_3759_ == 0)
{
lean_object* v_unused_3760_; lean_object* v_unused_3761_; lean_object* v_unused_3762_; lean_object* v_unused_3763_; 
v_unused_3760_ = lean_ctor_get(v_code_3442_, 3);
lean_dec(v_unused_3760_);
v_unused_3761_ = lean_ctor_get(v_code_3442_, 2);
lean_dec(v_unused_3761_);
v_unused_3762_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_3762_);
v_unused_3763_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_3763_);
v___x_3751_ = v_code_3442_;
v_isShared_3752_ = v_isSharedCheck_3759_;
goto v_resetjp_3750_;
}
else
{
lean_dec(v_code_3442_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3759_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 3, v_a_3710_);
lean_ctor_set(v___x_3751_, 2, v___x_3708_);
lean_ctor_set(v___x_3751_, 0, v_fvarId_3707_);
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_fvarId_3707_);
lean_ctor_set(v_reuseFailAlloc_3758_, 1, v_i_3703_);
lean_ctor_set(v_reuseFailAlloc_3758_, 2, v___x_3708_);
lean_ctor_set(v_reuseFailAlloc_3758_, 3, v_a_3710_);
v___x_3754_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
lean_object* v___x_3756_; 
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 0, v___x_3754_);
v___x_3756_ = v___x_3712_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3754_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
else
{
lean_object* v___x_3765_; 
lean_dec(v_a_3710_);
lean_dec(v___x_3708_);
lean_dec(v_fvarId_3707_);
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 0, v_code_3442_);
v___x_3765_ = v___x_3712_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_code_3442_);
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
}
}
}
else
{
lean_dec(v___x_3708_);
lean_dec(v_fvarId_3707_);
lean_dec_ref(v_code_3442_);
return v___x_3709_;
}
}
else
{
lean_object* v___x_3772_; 
lean_dec_ref(v_code_3442_);
v___x_3772_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3440_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
return v___x_3772_;
}
}
case 8:
{
lean_object* v_fvarId_3773_; lean_object* v_i_3774_; lean_object* v_y_3775_; lean_object* v_k_3776_; lean_object* v___x_3777_; 
v_fvarId_3773_ = lean_ctor_get(v_code_3442_, 0);
v_i_3774_ = lean_ctor_get(v_code_3442_, 1);
v_y_3775_ = lean_ctor_get(v_code_3442_, 2);
v_k_3776_ = lean_ctor_get(v_code_3442_, 3);
lean_inc(v_fvarId_3773_);
v___x_3777_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3443_, v_fvarId_3773_, v_t_3441_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v_fvarId_3778_; lean_object* v___x_3779_; 
v_fvarId_3778_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_fvarId_3778_);
lean_dec_ref(v___x_3777_);
lean_inc(v_y_3775_);
v___x_3779_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3443_, v_y_3775_, v_t_3441_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_fvarId_3780_; lean_object* v___x_3781_; 
v_fvarId_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_fvarId_3780_);
lean_dec_ref(v___x_3779_);
lean_inc_ref(v_k_3776_);
v___x_3781_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3440_, v_t_3441_, v_k_3776_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3843_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3784_ = v___x_3781_;
v_isShared_3785_ = v_isSharedCheck_3843_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3781_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3843_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
uint8_t v___y_3787_; size_t v___x_3839_; size_t v___x_3840_; uint8_t v___x_3841_; 
v___x_3839_ = lean_ptr_addr(v_fvarId_3773_);
v___x_3840_ = lean_ptr_addr(v_fvarId_3778_);
v___x_3841_ = lean_usize_dec_eq(v___x_3839_, v___x_3840_);
if (v___x_3841_ == 0)
{
v___y_3787_ = v___x_3841_;
goto v___jp_3786_;
}
else
{
uint8_t v___x_3842_; 
v___x_3842_ = lean_nat_dec_eq(v_i_3774_, v_i_3774_);
v___y_3787_ = v___x_3842_;
goto v___jp_3786_;
}
v___jp_3786_:
{
if (v___y_3787_ == 0)
{
lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3797_; 
lean_inc(v_i_3774_);
v_isSharedCheck_3797_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_3797_ == 0)
{
lean_object* v_unused_3798_; lean_object* v_unused_3799_; lean_object* v_unused_3800_; lean_object* v_unused_3801_; 
v_unused_3798_ = lean_ctor_get(v_code_3442_, 3);
lean_dec(v_unused_3798_);
v_unused_3799_ = lean_ctor_get(v_code_3442_, 2);
lean_dec(v_unused_3799_);
v_unused_3800_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_3800_);
v_unused_3801_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_3801_);
v___x_3789_ = v_code_3442_;
v_isShared_3790_ = v_isSharedCheck_3797_;
goto v_resetjp_3788_;
}
else
{
lean_dec(v_code_3442_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3797_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 3, v_a_3782_);
lean_ctor_set(v___x_3789_, 2, v_fvarId_3780_);
lean_ctor_set(v___x_3789_, 0, v_fvarId_3778_);
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_fvarId_3778_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v_i_3774_);
lean_ctor_set(v_reuseFailAlloc_3796_, 2, v_fvarId_3780_);
lean_ctor_set(v_reuseFailAlloc_3796_, 3, v_a_3782_);
v___x_3792_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
lean_object* v___x_3794_; 
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 0, v___x_3792_);
v___x_3794_ = v___x_3784_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3792_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
else
{
size_t v___x_3802_; size_t v___x_3803_; uint8_t v___x_3804_; 
v___x_3802_ = lean_ptr_addr(v_y_3775_);
v___x_3803_ = lean_ptr_addr(v_fvarId_3780_);
v___x_3804_ = lean_usize_dec_eq(v___x_3802_, v___x_3803_);
if (v___x_3804_ == 0)
{
lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3814_; 
lean_inc(v_i_3774_);
v_isSharedCheck_3814_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_3814_ == 0)
{
lean_object* v_unused_3815_; lean_object* v_unused_3816_; lean_object* v_unused_3817_; lean_object* v_unused_3818_; 
v_unused_3815_ = lean_ctor_get(v_code_3442_, 3);
lean_dec(v_unused_3815_);
v_unused_3816_ = lean_ctor_get(v_code_3442_, 2);
lean_dec(v_unused_3816_);
v_unused_3817_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_3817_);
v_unused_3818_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_3818_);
v___x_3806_ = v_code_3442_;
v_isShared_3807_ = v_isSharedCheck_3814_;
goto v_resetjp_3805_;
}
else
{
lean_dec(v_code_3442_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3814_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3809_; 
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 3, v_a_3782_);
lean_ctor_set(v___x_3806_, 2, v_fvarId_3780_);
lean_ctor_set(v___x_3806_, 0, v_fvarId_3778_);
v___x_3809_ = v___x_3806_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_fvarId_3778_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v_i_3774_);
lean_ctor_set(v_reuseFailAlloc_3813_, 2, v_fvarId_3780_);
lean_ctor_set(v_reuseFailAlloc_3813_, 3, v_a_3782_);
v___x_3809_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
lean_object* v___x_3811_; 
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 0, v___x_3809_);
v___x_3811_ = v___x_3784_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3809_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
else
{
size_t v___x_3819_; size_t v___x_3820_; uint8_t v___x_3821_; 
v___x_3819_ = lean_ptr_addr(v_k_3776_);
v___x_3820_ = lean_ptr_addr(v_a_3782_);
v___x_3821_ = lean_usize_dec_eq(v___x_3819_, v___x_3820_);
if (v___x_3821_ == 0)
{
lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3831_; 
lean_inc(v_i_3774_);
v_isSharedCheck_3831_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_3831_ == 0)
{
lean_object* v_unused_3832_; lean_object* v_unused_3833_; lean_object* v_unused_3834_; lean_object* v_unused_3835_; 
v_unused_3832_ = lean_ctor_get(v_code_3442_, 3);
lean_dec(v_unused_3832_);
v_unused_3833_ = lean_ctor_get(v_code_3442_, 2);
lean_dec(v_unused_3833_);
v_unused_3834_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_3834_);
v_unused_3835_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_3835_);
v___x_3823_ = v_code_3442_;
v_isShared_3824_ = v_isSharedCheck_3831_;
goto v_resetjp_3822_;
}
else
{
lean_dec(v_code_3442_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3831_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
lean_ctor_set(v___x_3823_, 3, v_a_3782_);
lean_ctor_set(v___x_3823_, 2, v_fvarId_3780_);
lean_ctor_set(v___x_3823_, 0, v_fvarId_3778_);
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_fvarId_3778_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v_i_3774_);
lean_ctor_set(v_reuseFailAlloc_3830_, 2, v_fvarId_3780_);
lean_ctor_set(v_reuseFailAlloc_3830_, 3, v_a_3782_);
v___x_3826_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
lean_object* v___x_3828_; 
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 0, v___x_3826_);
v___x_3828_ = v___x_3784_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v___x_3826_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
else
{
lean_object* v___x_3837_; 
lean_dec(v_a_3782_);
lean_dec(v_fvarId_3780_);
lean_dec(v_fvarId_3778_);
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 0, v_code_3442_);
v___x_3837_ = v___x_3784_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_code_3442_);
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
}
}
}
else
{
lean_dec(v_fvarId_3780_);
lean_dec(v_fvarId_3778_);
lean_dec_ref(v_code_3442_);
return v___x_3781_;
}
}
else
{
lean_object* v___x_3844_; 
lean_dec(v_fvarId_3778_);
lean_dec_ref(v_code_3442_);
v___x_3844_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3440_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
return v___x_3844_;
}
}
else
{
lean_object* v___x_3845_; 
lean_dec_ref(v_code_3442_);
v___x_3845_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3440_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
return v___x_3845_;
}
}
case 9:
{
lean_object* v_fvarId_3846_; lean_object* v_i_3847_; lean_object* v_offset_3848_; lean_object* v_y_3849_; lean_object* v_ty_3850_; lean_object* v_k_3851_; lean_object* v___x_3852_; 
v_fvarId_3846_ = lean_ctor_get(v_code_3442_, 0);
v_i_3847_ = lean_ctor_get(v_code_3442_, 1);
v_offset_3848_ = lean_ctor_get(v_code_3442_, 2);
v_y_3849_ = lean_ctor_get(v_code_3442_, 3);
v_ty_3850_ = lean_ctor_get(v_code_3442_, 4);
v_k_3851_ = lean_ctor_get(v_code_3442_, 5);
lean_inc(v_fvarId_3846_);
v___x_3852_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3443_, v_fvarId_3846_, v_t_3441_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_fvarId_3853_; lean_object* v___x_3854_; 
v_fvarId_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_fvarId_3853_);
lean_dec_ref(v___x_3852_);
lean_inc(v_y_3849_);
v___x_3854_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3443_, v_y_3849_, v_t_3441_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_fvarId_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v_fvarId_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_fvarId_3855_);
lean_dec_ref(v___x_3854_);
lean_inc_ref(v_ty_3850_);
v___x_3856_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3440_, v_a_3443_, v_t_3441_, v_ty_3850_);
lean_inc_ref(v_k_3851_);
v___x_3857_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3440_, v_t_3441_, v_k_3851_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3961_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3860_ = v___x_3857_;
v_isShared_3861_ = v_isSharedCheck_3961_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3857_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3961_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
uint8_t v___y_3863_; size_t v___x_3957_; size_t v___x_3958_; uint8_t v___x_3959_; 
v___x_3957_ = lean_ptr_addr(v_fvarId_3846_);
v___x_3958_ = lean_ptr_addr(v_fvarId_3853_);
v___x_3959_ = lean_usize_dec_eq(v___x_3957_, v___x_3958_);
if (v___x_3959_ == 0)
{
v___y_3863_ = v___x_3959_;
goto v___jp_3862_;
}
else
{
uint8_t v___x_3960_; 
v___x_3960_ = lean_nat_dec_eq(v_i_3847_, v_i_3847_);
v___y_3863_ = v___x_3960_;
goto v___jp_3862_;
}
v___jp_3862_:
{
if (v___y_3863_ == 0)
{
lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3873_; 
lean_inc(v_offset_3848_);
lean_inc(v_i_3847_);
v_isSharedCheck_3873_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_3873_ == 0)
{
lean_object* v_unused_3874_; lean_object* v_unused_3875_; lean_object* v_unused_3876_; lean_object* v_unused_3877_; lean_object* v_unused_3878_; lean_object* v_unused_3879_; 
v_unused_3874_ = lean_ctor_get(v_code_3442_, 5);
lean_dec(v_unused_3874_);
v_unused_3875_ = lean_ctor_get(v_code_3442_, 4);
lean_dec(v_unused_3875_);
v_unused_3876_ = lean_ctor_get(v_code_3442_, 3);
lean_dec(v_unused_3876_);
v_unused_3877_ = lean_ctor_get(v_code_3442_, 2);
lean_dec(v_unused_3877_);
v_unused_3878_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_3878_);
v_unused_3879_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_3879_);
v___x_3865_ = v_code_3442_;
v_isShared_3866_ = v_isSharedCheck_3873_;
goto v_resetjp_3864_;
}
else
{
lean_dec(v_code_3442_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3873_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
lean_ctor_set(v___x_3865_, 5, v_a_3858_);
lean_ctor_set(v___x_3865_, 4, v___x_3856_);
lean_ctor_set(v___x_3865_, 3, v_fvarId_3855_);
lean_ctor_set(v___x_3865_, 0, v_fvarId_3853_);
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_fvarId_3853_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v_i_3847_);
lean_ctor_set(v_reuseFailAlloc_3872_, 2, v_offset_3848_);
lean_ctor_set(v_reuseFailAlloc_3872_, 3, v_fvarId_3855_);
lean_ctor_set(v_reuseFailAlloc_3872_, 4, v___x_3856_);
lean_ctor_set(v_reuseFailAlloc_3872_, 5, v_a_3858_);
v___x_3868_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
lean_object* v___x_3870_; 
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v___x_3868_);
v___x_3870_ = v___x_3860_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3868_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
else
{
uint8_t v___x_3880_; 
v___x_3880_ = lean_nat_dec_eq(v_offset_3848_, v_offset_3848_);
if (v___x_3880_ == 0)
{
lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3890_; 
lean_inc(v_offset_3848_);
lean_inc(v_i_3847_);
v_isSharedCheck_3890_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_3890_ == 0)
{
lean_object* v_unused_3891_; lean_object* v_unused_3892_; lean_object* v_unused_3893_; lean_object* v_unused_3894_; lean_object* v_unused_3895_; lean_object* v_unused_3896_; 
v_unused_3891_ = lean_ctor_get(v_code_3442_, 5);
lean_dec(v_unused_3891_);
v_unused_3892_ = lean_ctor_get(v_code_3442_, 4);
lean_dec(v_unused_3892_);
v_unused_3893_ = lean_ctor_get(v_code_3442_, 3);
lean_dec(v_unused_3893_);
v_unused_3894_ = lean_ctor_get(v_code_3442_, 2);
lean_dec(v_unused_3894_);
v_unused_3895_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_3895_);
v_unused_3896_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_3896_);
v___x_3882_ = v_code_3442_;
v_isShared_3883_ = v_isSharedCheck_3890_;
goto v_resetjp_3881_;
}
else
{
lean_dec(v_code_3442_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3890_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 5, v_a_3858_);
lean_ctor_set(v___x_3882_, 4, v___x_3856_);
lean_ctor_set(v___x_3882_, 3, v_fvarId_3855_);
lean_ctor_set(v___x_3882_, 0, v_fvarId_3853_);
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_fvarId_3853_);
lean_ctor_set(v_reuseFailAlloc_3889_, 1, v_i_3847_);
lean_ctor_set(v_reuseFailAlloc_3889_, 2, v_offset_3848_);
lean_ctor_set(v_reuseFailAlloc_3889_, 3, v_fvarId_3855_);
lean_ctor_set(v_reuseFailAlloc_3889_, 4, v___x_3856_);
lean_ctor_set(v_reuseFailAlloc_3889_, 5, v_a_3858_);
v___x_3885_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
lean_object* v___x_3887_; 
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v___x_3885_);
v___x_3887_ = v___x_3860_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3885_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
}
else
{
size_t v___x_3897_; size_t v___x_3898_; uint8_t v___x_3899_; 
v___x_3897_ = lean_ptr_addr(v_y_3849_);
v___x_3898_ = lean_ptr_addr(v_fvarId_3855_);
v___x_3899_ = lean_usize_dec_eq(v___x_3897_, v___x_3898_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3909_; 
lean_inc(v_offset_3848_);
lean_inc(v_i_3847_);
v_isSharedCheck_3909_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_3909_ == 0)
{
lean_object* v_unused_3910_; lean_object* v_unused_3911_; lean_object* v_unused_3912_; lean_object* v_unused_3913_; lean_object* v_unused_3914_; lean_object* v_unused_3915_; 
v_unused_3910_ = lean_ctor_get(v_code_3442_, 5);
lean_dec(v_unused_3910_);
v_unused_3911_ = lean_ctor_get(v_code_3442_, 4);
lean_dec(v_unused_3911_);
v_unused_3912_ = lean_ctor_get(v_code_3442_, 3);
lean_dec(v_unused_3912_);
v_unused_3913_ = lean_ctor_get(v_code_3442_, 2);
lean_dec(v_unused_3913_);
v_unused_3914_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_3914_);
v_unused_3915_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_3915_);
v___x_3901_ = v_code_3442_;
v_isShared_3902_ = v_isSharedCheck_3909_;
goto v_resetjp_3900_;
}
else
{
lean_dec(v_code_3442_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3909_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 5, v_a_3858_);
lean_ctor_set(v___x_3901_, 4, v___x_3856_);
lean_ctor_set(v___x_3901_, 3, v_fvarId_3855_);
lean_ctor_set(v___x_3901_, 0, v_fvarId_3853_);
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_fvarId_3853_);
lean_ctor_set(v_reuseFailAlloc_3908_, 1, v_i_3847_);
lean_ctor_set(v_reuseFailAlloc_3908_, 2, v_offset_3848_);
lean_ctor_set(v_reuseFailAlloc_3908_, 3, v_fvarId_3855_);
lean_ctor_set(v_reuseFailAlloc_3908_, 4, v___x_3856_);
lean_ctor_set(v_reuseFailAlloc_3908_, 5, v_a_3858_);
v___x_3904_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
lean_object* v___x_3906_; 
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v___x_3904_);
v___x_3906_ = v___x_3860_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3904_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
else
{
size_t v___x_3916_; size_t v___x_3917_; uint8_t v___x_3918_; 
v___x_3916_ = lean_ptr_addr(v_ty_3850_);
v___x_3917_ = lean_ptr_addr(v___x_3856_);
v___x_3918_ = lean_usize_dec_eq(v___x_3916_, v___x_3917_);
if (v___x_3918_ == 0)
{
lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3928_; 
lean_inc(v_offset_3848_);
lean_inc(v_i_3847_);
v_isSharedCheck_3928_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_3928_ == 0)
{
lean_object* v_unused_3929_; lean_object* v_unused_3930_; lean_object* v_unused_3931_; lean_object* v_unused_3932_; lean_object* v_unused_3933_; lean_object* v_unused_3934_; 
v_unused_3929_ = lean_ctor_get(v_code_3442_, 5);
lean_dec(v_unused_3929_);
v_unused_3930_ = lean_ctor_get(v_code_3442_, 4);
lean_dec(v_unused_3930_);
v_unused_3931_ = lean_ctor_get(v_code_3442_, 3);
lean_dec(v_unused_3931_);
v_unused_3932_ = lean_ctor_get(v_code_3442_, 2);
lean_dec(v_unused_3932_);
v_unused_3933_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_3933_);
v_unused_3934_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_3934_);
v___x_3920_ = v_code_3442_;
v_isShared_3921_ = v_isSharedCheck_3928_;
goto v_resetjp_3919_;
}
else
{
lean_dec(v_code_3442_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3928_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 5, v_a_3858_);
lean_ctor_set(v___x_3920_, 4, v___x_3856_);
lean_ctor_set(v___x_3920_, 3, v_fvarId_3855_);
lean_ctor_set(v___x_3920_, 0, v_fvarId_3853_);
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_fvarId_3853_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v_i_3847_);
lean_ctor_set(v_reuseFailAlloc_3927_, 2, v_offset_3848_);
lean_ctor_set(v_reuseFailAlloc_3927_, 3, v_fvarId_3855_);
lean_ctor_set(v_reuseFailAlloc_3927_, 4, v___x_3856_);
lean_ctor_set(v_reuseFailAlloc_3927_, 5, v_a_3858_);
v___x_3923_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
lean_object* v___x_3925_; 
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v___x_3923_);
v___x_3925_ = v___x_3860_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3923_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
else
{
size_t v___x_3935_; size_t v___x_3936_; uint8_t v___x_3937_; 
v___x_3935_ = lean_ptr_addr(v_k_3851_);
v___x_3936_ = lean_ptr_addr(v_a_3858_);
v___x_3937_ = lean_usize_dec_eq(v___x_3935_, v___x_3936_);
if (v___x_3937_ == 0)
{
lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3947_; 
lean_inc(v_offset_3848_);
lean_inc(v_i_3847_);
v_isSharedCheck_3947_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_3947_ == 0)
{
lean_object* v_unused_3948_; lean_object* v_unused_3949_; lean_object* v_unused_3950_; lean_object* v_unused_3951_; lean_object* v_unused_3952_; lean_object* v_unused_3953_; 
v_unused_3948_ = lean_ctor_get(v_code_3442_, 5);
lean_dec(v_unused_3948_);
v_unused_3949_ = lean_ctor_get(v_code_3442_, 4);
lean_dec(v_unused_3949_);
v_unused_3950_ = lean_ctor_get(v_code_3442_, 3);
lean_dec(v_unused_3950_);
v_unused_3951_ = lean_ctor_get(v_code_3442_, 2);
lean_dec(v_unused_3951_);
v_unused_3952_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_3952_);
v_unused_3953_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_3953_);
v___x_3939_ = v_code_3442_;
v_isShared_3940_ = v_isSharedCheck_3947_;
goto v_resetjp_3938_;
}
else
{
lean_dec(v_code_3442_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3947_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
lean_ctor_set(v___x_3939_, 5, v_a_3858_);
lean_ctor_set(v___x_3939_, 4, v___x_3856_);
lean_ctor_set(v___x_3939_, 3, v_fvarId_3855_);
lean_ctor_set(v___x_3939_, 0, v_fvarId_3853_);
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_fvarId_3853_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v_i_3847_);
lean_ctor_set(v_reuseFailAlloc_3946_, 2, v_offset_3848_);
lean_ctor_set(v_reuseFailAlloc_3946_, 3, v_fvarId_3855_);
lean_ctor_set(v_reuseFailAlloc_3946_, 4, v___x_3856_);
lean_ctor_set(v_reuseFailAlloc_3946_, 5, v_a_3858_);
v___x_3942_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
lean_object* v___x_3944_; 
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v___x_3942_);
v___x_3944_ = v___x_3860_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v___x_3942_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
}
else
{
lean_object* v___x_3955_; 
lean_dec(v_a_3858_);
lean_dec_ref(v___x_3856_);
lean_dec(v_fvarId_3855_);
lean_dec(v_fvarId_3853_);
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v_code_3442_);
v___x_3955_ = v___x_3860_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_code_3442_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
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
lean_dec_ref(v___x_3856_);
lean_dec(v_fvarId_3855_);
lean_dec(v_fvarId_3853_);
lean_dec_ref(v_code_3442_);
return v___x_3857_;
}
}
else
{
lean_object* v___x_3962_; 
lean_dec(v_fvarId_3853_);
lean_dec_ref(v_code_3442_);
v___x_3962_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3440_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
return v___x_3962_;
}
}
else
{
lean_object* v___x_3963_; 
lean_dec_ref(v_code_3442_);
v___x_3963_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3440_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
return v___x_3963_;
}
}
case 10:
{
lean_object* v_fvarId_3964_; lean_object* v_cidx_3965_; lean_object* v_k_3966_; lean_object* v___x_3967_; 
v_fvarId_3964_ = lean_ctor_get(v_code_3442_, 0);
v_cidx_3965_ = lean_ctor_get(v_code_3442_, 1);
v_k_3966_ = lean_ctor_get(v_code_3442_, 2);
lean_inc(v_fvarId_3964_);
v___x_3967_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3443_, v_fvarId_3964_, v_t_3441_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v_fvarId_3968_; lean_object* v___x_3969_; 
v_fvarId_3968_ = lean_ctor_get(v___x_3967_, 0);
lean_inc(v_fvarId_3968_);
lean_dec_ref(v___x_3967_);
lean_inc_ref(v_k_3966_);
v___x_3969_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3440_, v_t_3441_, v_k_3966_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_4012_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_3972_ = v___x_3969_;
v_isShared_3973_ = v_isSharedCheck_4012_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3969_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_4012_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
uint8_t v___y_3975_; size_t v___x_4008_; size_t v___x_4009_; uint8_t v___x_4010_; 
v___x_4008_ = lean_ptr_addr(v_fvarId_3964_);
v___x_4009_ = lean_ptr_addr(v_fvarId_3968_);
v___x_4010_ = lean_usize_dec_eq(v___x_4008_, v___x_4009_);
if (v___x_4010_ == 0)
{
v___y_3975_ = v___x_4010_;
goto v___jp_3974_;
}
else
{
uint8_t v___x_4011_; 
v___x_4011_ = lean_nat_dec_eq(v_cidx_3965_, v_cidx_3965_);
v___y_3975_ = v___x_4011_;
goto v___jp_3974_;
}
v___jp_3974_:
{
if (v___y_3975_ == 0)
{
lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3985_; 
lean_inc(v_cidx_3965_);
v_isSharedCheck_3985_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_3985_ == 0)
{
lean_object* v_unused_3986_; lean_object* v_unused_3987_; lean_object* v_unused_3988_; 
v_unused_3986_ = lean_ctor_get(v_code_3442_, 2);
lean_dec(v_unused_3986_);
v_unused_3987_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_3987_);
v_unused_3988_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_3988_);
v___x_3977_ = v_code_3442_;
v_isShared_3978_ = v_isSharedCheck_3985_;
goto v_resetjp_3976_;
}
else
{
lean_dec(v_code_3442_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3985_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3980_; 
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 2, v_a_3970_);
lean_ctor_set(v___x_3977_, 0, v_fvarId_3968_);
v___x_3980_ = v___x_3977_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_fvarId_3968_);
lean_ctor_set(v_reuseFailAlloc_3984_, 1, v_cidx_3965_);
lean_ctor_set(v_reuseFailAlloc_3984_, 2, v_a_3970_);
v___x_3980_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
lean_object* v___x_3982_; 
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 0, v___x_3980_);
v___x_3982_ = v___x_3972_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v___x_3980_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
else
{
size_t v___x_3989_; size_t v___x_3990_; uint8_t v___x_3991_; 
v___x_3989_ = lean_ptr_addr(v_k_3966_);
v___x_3990_ = lean_ptr_addr(v_a_3970_);
v___x_3991_ = lean_usize_dec_eq(v___x_3989_, v___x_3990_);
if (v___x_3991_ == 0)
{
lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_4001_; 
lean_inc(v_cidx_3965_);
v_isSharedCheck_4001_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_4001_ == 0)
{
lean_object* v_unused_4002_; lean_object* v_unused_4003_; lean_object* v_unused_4004_; 
v_unused_4002_ = lean_ctor_get(v_code_3442_, 2);
lean_dec(v_unused_4002_);
v_unused_4003_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_4003_);
v_unused_4004_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_4004_);
v___x_3993_ = v_code_3442_;
v_isShared_3994_ = v_isSharedCheck_4001_;
goto v_resetjp_3992_;
}
else
{
lean_dec(v_code_3442_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_4001_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3996_; 
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 2, v_a_3970_);
lean_ctor_set(v___x_3993_, 0, v_fvarId_3968_);
v___x_3996_ = v___x_3993_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_fvarId_3968_);
lean_ctor_set(v_reuseFailAlloc_4000_, 1, v_cidx_3965_);
lean_ctor_set(v_reuseFailAlloc_4000_, 2, v_a_3970_);
v___x_3996_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
lean_object* v___x_3998_; 
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 0, v___x_3996_);
v___x_3998_ = v___x_3972_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3996_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
else
{
lean_object* v___x_4006_; 
lean_dec(v_a_3970_);
lean_dec(v_fvarId_3968_);
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 0, v_code_3442_);
v___x_4006_ = v___x_3972_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_code_3442_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_3968_);
lean_dec_ref(v_code_3442_);
return v___x_3969_;
}
}
else
{
lean_object* v___x_4013_; 
lean_dec_ref(v_code_3442_);
v___x_4013_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3440_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
return v___x_4013_;
}
}
case 11:
{
lean_object* v_fvarId_4014_; lean_object* v_n_4015_; uint8_t v_check_4016_; uint8_t v_persistent_4017_; lean_object* v_k_4018_; lean_object* v___x_4019_; 
v_fvarId_4014_ = lean_ctor_get(v_code_3442_, 0);
v_n_4015_ = lean_ctor_get(v_code_3442_, 1);
v_check_4016_ = lean_ctor_get_uint8(v_code_3442_, sizeof(void*)*3);
v_persistent_4017_ = lean_ctor_get_uint8(v_code_3442_, sizeof(void*)*3 + 1);
v_k_4018_ = lean_ctor_get(v_code_3442_, 2);
lean_inc(v_fvarId_4014_);
v___x_4019_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3443_, v_fvarId_4014_, v_t_3441_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v_fvarId_4020_; lean_object* v___x_4021_; 
v_fvarId_4020_ = lean_ctor_get(v___x_4019_, 0);
lean_inc(v_fvarId_4020_);
lean_dec_ref(v___x_4019_);
lean_inc_ref(v_k_4018_);
v___x_4021_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3440_, v_t_3441_, v_k_4018_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4064_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4024_ = v___x_4021_;
v_isShared_4025_ = v_isSharedCheck_4064_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_4021_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4064_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
uint8_t v___y_4027_; size_t v___x_4060_; size_t v___x_4061_; uint8_t v___x_4062_; 
v___x_4060_ = lean_ptr_addr(v_fvarId_4014_);
v___x_4061_ = lean_ptr_addr(v_fvarId_4020_);
v___x_4062_ = lean_usize_dec_eq(v___x_4060_, v___x_4061_);
if (v___x_4062_ == 0)
{
v___y_4027_ = v___x_4062_;
goto v___jp_4026_;
}
else
{
uint8_t v___x_4063_; 
v___x_4063_ = lean_nat_dec_eq(v_n_4015_, v_n_4015_);
v___y_4027_ = v___x_4063_;
goto v___jp_4026_;
}
v___jp_4026_:
{
if (v___y_4027_ == 0)
{
lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4037_; 
lean_inc(v_n_4015_);
v_isSharedCheck_4037_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_4037_ == 0)
{
lean_object* v_unused_4038_; lean_object* v_unused_4039_; lean_object* v_unused_4040_; 
v_unused_4038_ = lean_ctor_get(v_code_3442_, 2);
lean_dec(v_unused_4038_);
v_unused_4039_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_4039_);
v_unused_4040_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_4040_);
v___x_4029_ = v_code_3442_;
v_isShared_4030_ = v_isSharedCheck_4037_;
goto v_resetjp_4028_;
}
else
{
lean_dec(v_code_3442_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4037_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4032_; 
if (v_isShared_4030_ == 0)
{
lean_ctor_set(v___x_4029_, 2, v_a_4022_);
lean_ctor_set(v___x_4029_, 0, v_fvarId_4020_);
v___x_4032_ = v___x_4029_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_fvarId_4020_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v_n_4015_);
lean_ctor_set(v_reuseFailAlloc_4036_, 2, v_a_4022_);
lean_ctor_set_uint8(v_reuseFailAlloc_4036_, sizeof(void*)*3, v_check_4016_);
lean_ctor_set_uint8(v_reuseFailAlloc_4036_, sizeof(void*)*3 + 1, v_persistent_4017_);
v___x_4032_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
lean_object* v___x_4034_; 
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 0, v___x_4032_);
v___x_4034_ = v___x_4024_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v___x_4032_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
else
{
size_t v___x_4041_; size_t v___x_4042_; uint8_t v___x_4043_; 
v___x_4041_ = lean_ptr_addr(v_k_4018_);
v___x_4042_ = lean_ptr_addr(v_a_4022_);
v___x_4043_ = lean_usize_dec_eq(v___x_4041_, v___x_4042_);
if (v___x_4043_ == 0)
{
lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4053_; 
lean_inc(v_n_4015_);
v_isSharedCheck_4053_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_4053_ == 0)
{
lean_object* v_unused_4054_; lean_object* v_unused_4055_; lean_object* v_unused_4056_; 
v_unused_4054_ = lean_ctor_get(v_code_3442_, 2);
lean_dec(v_unused_4054_);
v_unused_4055_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_4055_);
v_unused_4056_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_4056_);
v___x_4045_ = v_code_3442_;
v_isShared_4046_ = v_isSharedCheck_4053_;
goto v_resetjp_4044_;
}
else
{
lean_dec(v_code_3442_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4053_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
lean_ctor_set(v___x_4045_, 2, v_a_4022_);
lean_ctor_set(v___x_4045_, 0, v_fvarId_4020_);
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_fvarId_4020_);
lean_ctor_set(v_reuseFailAlloc_4052_, 1, v_n_4015_);
lean_ctor_set(v_reuseFailAlloc_4052_, 2, v_a_4022_);
lean_ctor_set_uint8(v_reuseFailAlloc_4052_, sizeof(void*)*3, v_check_4016_);
lean_ctor_set_uint8(v_reuseFailAlloc_4052_, sizeof(void*)*3 + 1, v_persistent_4017_);
v___x_4048_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
lean_object* v___x_4050_; 
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 0, v___x_4048_);
v___x_4050_ = v___x_4024_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v___x_4048_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
else
{
lean_object* v___x_4058_; 
lean_dec(v_a_4022_);
lean_dec(v_fvarId_4020_);
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 0, v_code_3442_);
v___x_4058_ = v___x_4024_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_code_3442_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4020_);
lean_dec_ref(v_code_3442_);
return v___x_4021_;
}
}
else
{
lean_object* v___x_4065_; 
lean_dec_ref(v_code_3442_);
v___x_4065_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3440_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
return v___x_4065_;
}
}
case 12:
{
lean_object* v_fvarId_4066_; lean_object* v_n_4067_; uint8_t v_check_4068_; uint8_t v_persistent_4069_; lean_object* v_k_4070_; lean_object* v___x_4071_; 
v_fvarId_4066_ = lean_ctor_get(v_code_3442_, 0);
v_n_4067_ = lean_ctor_get(v_code_3442_, 1);
v_check_4068_ = lean_ctor_get_uint8(v_code_3442_, sizeof(void*)*3);
v_persistent_4069_ = lean_ctor_get_uint8(v_code_3442_, sizeof(void*)*3 + 1);
v_k_4070_ = lean_ctor_get(v_code_3442_, 2);
lean_inc(v_fvarId_4066_);
v___x_4071_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3443_, v_fvarId_4066_, v_t_3441_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_fvarId_4072_; lean_object* v___x_4073_; 
v_fvarId_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_fvarId_4072_);
lean_dec_ref(v___x_4071_);
lean_inc_ref(v_k_4070_);
v___x_4073_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3440_, v_t_3441_, v_k_4070_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4116_; 
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4076_ = v___x_4073_;
v_isShared_4077_ = v_isSharedCheck_4116_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4073_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4116_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
uint8_t v___y_4079_; size_t v___x_4112_; size_t v___x_4113_; uint8_t v___x_4114_; 
v___x_4112_ = lean_ptr_addr(v_fvarId_4066_);
v___x_4113_ = lean_ptr_addr(v_fvarId_4072_);
v___x_4114_ = lean_usize_dec_eq(v___x_4112_, v___x_4113_);
if (v___x_4114_ == 0)
{
v___y_4079_ = v___x_4114_;
goto v___jp_4078_;
}
else
{
uint8_t v___x_4115_; 
v___x_4115_ = lean_nat_dec_eq(v_n_4067_, v_n_4067_);
v___y_4079_ = v___x_4115_;
goto v___jp_4078_;
}
v___jp_4078_:
{
if (v___y_4079_ == 0)
{
lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4089_; 
lean_inc(v_n_4067_);
v_isSharedCheck_4089_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_4089_ == 0)
{
lean_object* v_unused_4090_; lean_object* v_unused_4091_; lean_object* v_unused_4092_; 
v_unused_4090_ = lean_ctor_get(v_code_3442_, 2);
lean_dec(v_unused_4090_);
v_unused_4091_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_4091_);
v_unused_4092_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_4092_);
v___x_4081_ = v_code_3442_;
v_isShared_4082_ = v_isSharedCheck_4089_;
goto v_resetjp_4080_;
}
else
{
lean_dec(v_code_3442_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4089_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
lean_ctor_set(v___x_4081_, 2, v_a_4074_);
lean_ctor_set(v___x_4081_, 0, v_fvarId_4072_);
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_fvarId_4072_);
lean_ctor_set(v_reuseFailAlloc_4088_, 1, v_n_4067_);
lean_ctor_set(v_reuseFailAlloc_4088_, 2, v_a_4074_);
lean_ctor_set_uint8(v_reuseFailAlloc_4088_, sizeof(void*)*3, v_check_4068_);
lean_ctor_set_uint8(v_reuseFailAlloc_4088_, sizeof(void*)*3 + 1, v_persistent_4069_);
v___x_4084_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
lean_object* v___x_4086_; 
if (v_isShared_4077_ == 0)
{
lean_ctor_set(v___x_4076_, 0, v___x_4084_);
v___x_4086_ = v___x_4076_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v___x_4084_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
else
{
size_t v___x_4093_; size_t v___x_4094_; uint8_t v___x_4095_; 
v___x_4093_ = lean_ptr_addr(v_k_4070_);
v___x_4094_ = lean_ptr_addr(v_a_4074_);
v___x_4095_ = lean_usize_dec_eq(v___x_4093_, v___x_4094_);
if (v___x_4095_ == 0)
{
lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4105_; 
lean_inc(v_n_4067_);
v_isSharedCheck_4105_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_4105_ == 0)
{
lean_object* v_unused_4106_; lean_object* v_unused_4107_; lean_object* v_unused_4108_; 
v_unused_4106_ = lean_ctor_get(v_code_3442_, 2);
lean_dec(v_unused_4106_);
v_unused_4107_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_4107_);
v_unused_4108_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_4108_);
v___x_4097_ = v_code_3442_;
v_isShared_4098_ = v_isSharedCheck_4105_;
goto v_resetjp_4096_;
}
else
{
lean_dec(v_code_3442_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4105_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4100_; 
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 2, v_a_4074_);
lean_ctor_set(v___x_4097_, 0, v_fvarId_4072_);
v___x_4100_ = v___x_4097_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_fvarId_4072_);
lean_ctor_set(v_reuseFailAlloc_4104_, 1, v_n_4067_);
lean_ctor_set(v_reuseFailAlloc_4104_, 2, v_a_4074_);
lean_ctor_set_uint8(v_reuseFailAlloc_4104_, sizeof(void*)*3, v_check_4068_);
lean_ctor_set_uint8(v_reuseFailAlloc_4104_, sizeof(void*)*3 + 1, v_persistent_4069_);
v___x_4100_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
lean_object* v___x_4102_; 
if (v_isShared_4077_ == 0)
{
lean_ctor_set(v___x_4076_, 0, v___x_4100_);
v___x_4102_ = v___x_4076_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v___x_4100_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
}
else
{
lean_object* v___x_4110_; 
lean_dec(v_a_4074_);
lean_dec(v_fvarId_4072_);
if (v_isShared_4077_ == 0)
{
lean_ctor_set(v___x_4076_, 0, v_code_3442_);
v___x_4110_ = v___x_4076_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_code_3442_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4072_);
lean_dec_ref(v_code_3442_);
return v___x_4073_;
}
}
else
{
lean_object* v___x_4117_; 
lean_dec_ref(v_code_3442_);
v___x_4117_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3440_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
return v___x_4117_;
}
}
default: 
{
lean_object* v_fvarId_4118_; lean_object* v_k_4119_; lean_object* v___x_4120_; 
v_fvarId_4118_ = lean_ctor_get(v_code_3442_, 0);
v_k_4119_ = lean_ctor_get(v_code_3442_, 1);
lean_inc(v_fvarId_4118_);
v___x_4120_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3443_, v_fvarId_4118_, v_t_3441_);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_object* v_fvarId_4121_; lean_object* v___x_4122_; 
v_fvarId_4121_ = lean_ctor_get(v___x_4120_, 0);
lean_inc(v_fvarId_4121_);
lean_dec_ref(v___x_4120_);
lean_inc_ref(v_k_4119_);
v___x_4122_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3440_, v_t_3441_, v_k_4119_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4150_; 
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4125_ = v___x_4122_;
v_isShared_4126_ = v_isSharedCheck_4150_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4122_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4150_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
uint8_t v___y_4128_; size_t v___x_4144_; size_t v___x_4145_; uint8_t v___x_4146_; 
v___x_4144_ = lean_ptr_addr(v_fvarId_4118_);
v___x_4145_ = lean_ptr_addr(v_fvarId_4121_);
v___x_4146_ = lean_usize_dec_eq(v___x_4144_, v___x_4145_);
if (v___x_4146_ == 0)
{
v___y_4128_ = v___x_4146_;
goto v___jp_4127_;
}
else
{
size_t v___x_4147_; size_t v___x_4148_; uint8_t v___x_4149_; 
v___x_4147_ = lean_ptr_addr(v_k_4119_);
v___x_4148_ = lean_ptr_addr(v_a_4123_);
v___x_4149_ = lean_usize_dec_eq(v___x_4147_, v___x_4148_);
v___y_4128_ = v___x_4149_;
goto v___jp_4127_;
}
v___jp_4127_:
{
if (v___y_4128_ == 0)
{
lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4138_; 
v_isSharedCheck_4138_ = !lean_is_exclusive(v_code_3442_);
if (v_isSharedCheck_4138_ == 0)
{
lean_object* v_unused_4139_; lean_object* v_unused_4140_; 
v_unused_4139_ = lean_ctor_get(v_code_3442_, 1);
lean_dec(v_unused_4139_);
v_unused_4140_ = lean_ctor_get(v_code_3442_, 0);
lean_dec(v_unused_4140_);
v___x_4130_ = v_code_3442_;
v_isShared_4131_ = v_isSharedCheck_4138_;
goto v_resetjp_4129_;
}
else
{
lean_dec(v_code_3442_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4138_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4133_; 
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 1, v_a_4123_);
lean_ctor_set(v___x_4130_, 0, v_fvarId_4121_);
v___x_4133_ = v___x_4130_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_fvarId_4121_);
lean_ctor_set(v_reuseFailAlloc_4137_, 1, v_a_4123_);
v___x_4133_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
lean_object* v___x_4135_; 
if (v_isShared_4126_ == 0)
{
lean_ctor_set(v___x_4125_, 0, v___x_4133_);
v___x_4135_ = v___x_4125_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v___x_4133_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
else
{
lean_object* v___x_4142_; 
lean_dec(v_a_4123_);
lean_dec(v_fvarId_4121_);
if (v_isShared_4126_ == 0)
{
lean_ctor_set(v___x_4125_, 0, v_code_3442_);
v___x_4142_ = v___x_4125_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_code_3442_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_4121_);
lean_dec_ref(v_code_3442_);
return v___x_4122_;
}
}
else
{
lean_object* v___x_4151_; 
lean_dec_ref(v_code_3442_);
v___x_4151_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3440_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
return v___x_4151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t v_pu_4152_, uint8_t v_t_4153_, lean_object* v_decl_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_){
_start:
{
lean_object* v_params_4161_; lean_object* v_type_4162_; lean_object* v_value_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v_params_4161_ = lean_ctor_get(v_decl_4154_, 2);
v_type_4162_ = lean_ctor_get(v_decl_4154_, 3);
v_value_4163_ = lean_ctor_get(v_decl_4154_, 4);
lean_inc_ref(v_type_4162_);
v___x_4164_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4152_, v_a_4155_, v_t_4153_, v_type_4162_);
lean_inc_ref(v_params_4161_);
v___x_4165_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4152_, v_t_4153_, v_params_4161_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; lean_object* v___x_4167_; 
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_a_4166_);
lean_dec_ref(v___x_4165_);
lean_inc_ref(v_value_4163_);
v___x_4167_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4152_, v_t_4153_, v_value_4163_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_object* v_a_4168_; lean_object* v___x_4169_; 
v_a_4168_ = lean_ctor_get(v___x_4167_, 0);
lean_inc(v_a_4168_);
lean_dec_ref(v___x_4167_);
v___x_4169_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_4152_, v_decl_4154_, v___x_4164_, v_a_4166_, v_a_4168_, v_a_4157_);
return v___x_4169_;
}
else
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4177_; 
lean_dec(v_a_4166_);
lean_dec_ref(v___x_4164_);
lean_dec_ref(v_decl_4154_);
v_a_4170_ = lean_ctor_get(v___x_4167_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4172_ = v___x_4167_;
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_4167_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4175_; 
if (v_isShared_4173_ == 0)
{
v___x_4175_ = v___x_4172_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_a_4170_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
}
else
{
lean_object* v_a_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4185_; 
lean_dec_ref(v___x_4164_);
lean_dec_ref(v_decl_4154_);
v_a_4178_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4180_ = v___x_4165_;
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_a_4178_);
lean_dec(v___x_4165_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v___x_4183_; 
if (v_isShared_4181_ == 0)
{
v___x_4183_ = v___x_4180_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v_a_4178_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp___boxed(lean_object* v_pu_4186_, lean_object* v_t_4187_, lean_object* v_decl_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_){
_start:
{
uint8_t v_pu_boxed_4195_; uint8_t v_t_boxed_4196_; lean_object* v_res_4197_; 
v_pu_boxed_4195_ = lean_unbox(v_pu_4186_);
v_t_boxed_4196_ = lean_unbox(v_t_4187_);
v_res_4197_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_boxed_4195_, v_t_boxed_4196_, v_decl_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_);
lean_dec(v_a_4193_);
lean_dec_ref(v_a_4192_);
lean_dec(v_a_4191_);
lean_dec_ref(v_a_4190_);
lean_dec_ref(v_a_4189_);
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4___boxed(lean_object* v_pu_4198_, lean_object* v_t_4199_, lean_object* v_i_4200_, lean_object* v_as_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
uint8_t v_pu_boxed_4208_; uint8_t v_t_boxed_4209_; lean_object* v_res_4210_; 
v_pu_boxed_4208_ = lean_unbox(v_pu_4198_);
v_t_boxed_4209_ = lean_unbox(v_t_4199_);
v_res_4210_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_boxed_4208_, v_t_boxed_4209_, v_i_4200_, v_as_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
lean_dec(v___y_4206_);
lean_dec_ref(v___y_4205_);
lean_dec(v___y_4204_);
lean_dec_ref(v___y_4203_);
lean_dec_ref(v___y_4202_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp___boxed(lean_object* v_pu_4211_, lean_object* v_t_4212_, lean_object* v_code_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_){
_start:
{
uint8_t v_pu_boxed_4220_; uint8_t v_t_boxed_4221_; lean_object* v_res_4222_; 
v_pu_boxed_4220_ = lean_unbox(v_pu_4211_);
v_t_boxed_4221_ = lean_unbox(v_t_4212_);
v_res_4222_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_boxed_4220_, v_t_boxed_4221_, v_code_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_);
lean_dec(v_a_4218_);
lean_dec_ref(v_a_4217_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec_ref(v_a_4214_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(uint8_t v_pu_4223_, uint8_t v_t_4224_, uint8_t v_pu_4225_, uint8_t v_t_4226_, lean_object* v_decl_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v___x_4234_; 
v___x_4234_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_4225_, v_t_4226_, v_decl_4227_, v___y_4228_, v___y_4230_);
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___boxed(lean_object* v_pu_4235_, lean_object* v_t_4236_, lean_object* v_pu_4237_, lean_object* v_t_4238_, lean_object* v_decl_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
uint8_t v_pu_boxed_4246_; uint8_t v_t_boxed_4247_; uint8_t v_pu_boxed_4248_; uint8_t v_t_boxed_4249_; lean_object* v_res_4250_; 
v_pu_boxed_4246_ = lean_unbox(v_pu_4235_);
v_t_boxed_4247_ = lean_unbox(v_t_4236_);
v_pu_boxed_4248_ = lean_unbox(v_pu_4237_);
v_t_boxed_4249_ = lean_unbox(v_t_4238_);
v_res_4250_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(v_pu_boxed_4246_, v_t_boxed_4247_, v_pu_boxed_4248_, v_t_boxed_4249_, v_decl_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
lean_dec(v___y_4244_);
lean_dec_ref(v___y_4243_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
lean_dec_ref(v___y_4240_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(uint8_t v_pu_4251_, uint8_t v_t_4252_, uint8_t v_pu_4253_, uint8_t v_t_4254_, lean_object* v_args_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
lean_object* v___x_4262_; 
v___x_4262_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_4253_, v_t_4254_, v_args_4255_, v___y_4256_);
return v___x_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___boxed(lean_object* v_pu_4263_, lean_object* v_t_4264_, lean_object* v_pu_4265_, lean_object* v_t_4266_, lean_object* v_args_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
uint8_t v_pu_boxed_4274_; uint8_t v_t_boxed_4275_; uint8_t v_pu_boxed_4276_; uint8_t v_t_boxed_4277_; lean_object* v_res_4278_; 
v_pu_boxed_4274_ = lean_unbox(v_pu_4263_);
v_t_boxed_4275_ = lean_unbox(v_t_4264_);
v_pu_boxed_4276_ = lean_unbox(v_pu_4265_);
v_t_boxed_4277_ = lean_unbox(v_t_4266_);
v_res_4278_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(v_pu_boxed_4274_, v_t_boxed_4275_, v_pu_boxed_4276_, v_t_boxed_4277_, v_args_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec_ref(v___y_4268_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(uint8_t v_pu_4279_, uint8_t v_t_4280_, uint8_t v_pu_4281_, uint8_t v_t_4282_, lean_object* v_ps_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_){
_start:
{
lean_object* v___x_4290_; 
v___x_4290_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4281_, v_t_4282_, v_ps_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___boxed(lean_object* v_pu_4291_, lean_object* v_t_4292_, lean_object* v_pu_4293_, lean_object* v_t_4294_, lean_object* v_ps_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
uint8_t v_pu_boxed_4302_; uint8_t v_t_boxed_4303_; uint8_t v_pu_boxed_4304_; uint8_t v_t_boxed_4305_; lean_object* v_res_4306_; 
v_pu_boxed_4302_ = lean_unbox(v_pu_4291_);
v_t_boxed_4303_ = lean_unbox(v_t_4292_);
v_pu_boxed_4304_ = lean_unbox(v_pu_4293_);
v_t_boxed_4305_ = lean_unbox(v_t_4294_);
v_res_4306_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(v_pu_boxed_4302_, v_t_boxed_4303_, v_pu_boxed_4304_, v_t_boxed_4305_, v_ps_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
lean_dec(v___y_4300_);
lean_dec_ref(v___y_4299_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec_ref(v___y_4296_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(uint8_t v_pu_4307_, uint8_t v_t_4308_, lean_object* v_i_4309_, lean_object* v_as_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_){
_start:
{
lean_object* v___x_4317_; 
v___x_4317_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_4307_, v_t_4308_, v_i_4309_, v_as_4310_, v___y_4311_, v___y_4313_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___boxed(lean_object* v_pu_4318_, lean_object* v_t_4319_, lean_object* v_i_4320_, lean_object* v_as_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_){
_start:
{
uint8_t v_pu_boxed_4328_; uint8_t v_t_boxed_4329_; lean_object* v_res_4330_; 
v_pu_boxed_4328_ = lean_unbox(v_pu_4318_);
v_t_boxed_4329_ = lean_unbox(v_t_4319_);
v_res_4330_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(v_pu_boxed_4328_, v_t_boxed_4329_, v_i_4320_, v_as_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec_ref(v___y_4322_);
return v_res_4330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(uint8_t v_pu_4331_, uint8_t v_t_4332_, lean_object* v_decl_4333_, lean_object* v_inst_4334_, lean_object* v_____do__lift_4335_){
_start:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4336_ = lean_box(v_pu_4331_);
v___x_4337_ = lean_box(v_t_4332_);
v___x_4338_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDeclImp___boxed), 9, 4);
lean_closure_set(v___x_4338_, 0, v___x_4336_);
lean_closure_set(v___x_4338_, 1, v___x_4337_);
lean_closure_set(v___x_4338_, 2, v_decl_4333_);
lean_closure_set(v___x_4338_, 3, v_____do__lift_4335_);
v___x_4339_ = lean_apply_2(v_inst_4334_, lean_box(0), v___x_4338_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed(lean_object* v_pu_4340_, lean_object* v_t_4341_, lean_object* v_decl_4342_, lean_object* v_inst_4343_, lean_object* v_____do__lift_4344_){
_start:
{
uint8_t v_pu_boxed_4345_; uint8_t v_t_boxed_4346_; lean_object* v_res_4347_; 
v_pu_boxed_4345_ = lean_unbox(v_pu_4340_);
v_t_boxed_4346_ = lean_unbox(v_t_4341_);
v_res_4347_ = l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(v_pu_boxed_4345_, v_t_boxed_4346_, v_decl_4342_, v_inst_4343_, v_____do__lift_4344_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg(uint8_t v_pu_4348_, uint8_t v_t_4349_, lean_object* v_inst_4350_, lean_object* v_inst_4351_, lean_object* v_inst_4352_, lean_object* v_decl_4353_){
_start:
{
lean_object* v_toBind_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___f_4357_; lean_object* v___x_4358_; 
v_toBind_4354_ = lean_ctor_get(v_inst_4351_, 1);
lean_inc(v_toBind_4354_);
lean_dec_ref(v_inst_4351_);
v___x_4355_ = lean_box(v_pu_4348_);
v___x_4356_ = lean_box(v_t_4349_);
v___f_4357_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4357_, 0, v___x_4355_);
lean_closure_set(v___f_4357_, 1, v___x_4356_);
lean_closure_set(v___f_4357_, 2, v_decl_4353_);
lean_closure_set(v___f_4357_, 3, v_inst_4350_);
v___x_4358_ = lean_apply_4(v_toBind_4354_, lean_box(0), lean_box(0), v_inst_4352_, v___f_4357_);
return v___x_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___boxed(lean_object* v_pu_4359_, lean_object* v_t_4360_, lean_object* v_inst_4361_, lean_object* v_inst_4362_, lean_object* v_inst_4363_, lean_object* v_decl_4364_){
_start:
{
uint8_t v_pu_boxed_4365_; uint8_t v_t_boxed_4366_; lean_object* v_res_4367_; 
v_pu_boxed_4365_ = lean_unbox(v_pu_4359_);
v_t_boxed_4366_ = lean_unbox(v_t_4360_);
v_res_4367_ = l_Lean_Compiler_LCNF_normFunDecl___redArg(v_pu_boxed_4365_, v_t_boxed_4366_, v_inst_4361_, v_inst_4362_, v_inst_4363_, v_decl_4364_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl(lean_object* v_m_4368_, uint8_t v_pu_4369_, uint8_t v_t_4370_, lean_object* v_inst_4371_, lean_object* v_inst_4372_, lean_object* v_inst_4373_, lean_object* v_decl_4374_){
_start:
{
lean_object* v_toBind_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___f_4378_; lean_object* v___x_4379_; 
v_toBind_4375_ = lean_ctor_get(v_inst_4372_, 1);
lean_inc(v_toBind_4375_);
lean_dec_ref(v_inst_4372_);
v___x_4376_ = lean_box(v_pu_4369_);
v___x_4377_ = lean_box(v_t_4370_);
v___f_4378_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4378_, 0, v___x_4376_);
lean_closure_set(v___f_4378_, 1, v___x_4377_);
lean_closure_set(v___f_4378_, 2, v_decl_4374_);
lean_closure_set(v___f_4378_, 3, v_inst_4371_);
v___x_4379_ = lean_apply_4(v_toBind_4375_, lean_box(0), lean_box(0), v_inst_4373_, v___f_4378_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___boxed(lean_object* v_m_4380_, lean_object* v_pu_4381_, lean_object* v_t_4382_, lean_object* v_inst_4383_, lean_object* v_inst_4384_, lean_object* v_inst_4385_, lean_object* v_decl_4386_){
_start:
{
uint8_t v_pu_boxed_4387_; uint8_t v_t_boxed_4388_; lean_object* v_res_4389_; 
v_pu_boxed_4387_ = lean_unbox(v_pu_4381_);
v_t_boxed_4388_ = lean_unbox(v_t_4382_);
v_res_4389_ = l_Lean_Compiler_LCNF_normFunDecl(v_m_4380_, v_pu_boxed_4387_, v_t_boxed_4388_, v_inst_4383_, v_inst_4384_, v_inst_4385_, v_decl_4386_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0(uint8_t v_pu_4390_, uint8_t v_t_4391_, lean_object* v_code_4392_, lean_object* v_inst_4393_, lean_object* v_____do__lift_4394_){
_start:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4395_ = lean_box(v_pu_4390_);
v___x_4396_ = lean_box(v_t_4391_);
v___x_4397_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCodeImp___boxed), 9, 4);
lean_closure_set(v___x_4397_, 0, v___x_4395_);
lean_closure_set(v___x_4397_, 1, v___x_4396_);
lean_closure_set(v___x_4397_, 2, v_code_4392_);
lean_closure_set(v___x_4397_, 3, v_____do__lift_4394_);
v___x_4398_ = lean_apply_2(v_inst_4393_, lean_box(0), v___x_4397_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed(lean_object* v_pu_4399_, lean_object* v_t_4400_, lean_object* v_code_4401_, lean_object* v_inst_4402_, lean_object* v_____do__lift_4403_){
_start:
{
uint8_t v_pu_boxed_4404_; uint8_t v_t_boxed_4405_; lean_object* v_res_4406_; 
v_pu_boxed_4404_ = lean_unbox(v_pu_4399_);
v_t_boxed_4405_ = lean_unbox(v_t_4400_);
v_res_4406_ = l_Lean_Compiler_LCNF_normCode___redArg___lam__0(v_pu_boxed_4404_, v_t_boxed_4405_, v_code_4401_, v_inst_4402_, v_____do__lift_4403_);
return v_res_4406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg(uint8_t v_pu_4407_, uint8_t v_t_4408_, lean_object* v_inst_4409_, lean_object* v_inst_4410_, lean_object* v_inst_4411_, lean_object* v_code_4412_){
_start:
{
lean_object* v_toBind_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___f_4416_; lean_object* v___x_4417_; 
v_toBind_4413_ = lean_ctor_get(v_inst_4410_, 1);
lean_inc(v_toBind_4413_);
lean_dec_ref(v_inst_4410_);
v___x_4414_ = lean_box(v_pu_4407_);
v___x_4415_ = lean_box(v_t_4408_);
v___f_4416_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4416_, 0, v___x_4414_);
lean_closure_set(v___f_4416_, 1, v___x_4415_);
lean_closure_set(v___f_4416_, 2, v_code_4412_);
lean_closure_set(v___f_4416_, 3, v_inst_4409_);
v___x_4417_ = lean_apply_4(v_toBind_4413_, lean_box(0), lean_box(0), v_inst_4411_, v___f_4416_);
return v___x_4417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___boxed(lean_object* v_pu_4418_, lean_object* v_t_4419_, lean_object* v_inst_4420_, lean_object* v_inst_4421_, lean_object* v_inst_4422_, lean_object* v_code_4423_){
_start:
{
uint8_t v_pu_boxed_4424_; uint8_t v_t_boxed_4425_; lean_object* v_res_4426_; 
v_pu_boxed_4424_ = lean_unbox(v_pu_4418_);
v_t_boxed_4425_ = lean_unbox(v_t_4419_);
v_res_4426_ = l_Lean_Compiler_LCNF_normCode___redArg(v_pu_boxed_4424_, v_t_boxed_4425_, v_inst_4420_, v_inst_4421_, v_inst_4422_, v_code_4423_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode(lean_object* v_m_4427_, uint8_t v_pu_4428_, uint8_t v_t_4429_, lean_object* v_inst_4430_, lean_object* v_inst_4431_, lean_object* v_inst_4432_, lean_object* v_code_4433_){
_start:
{
lean_object* v_toBind_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___f_4437_; lean_object* v___x_4438_; 
v_toBind_4434_ = lean_ctor_get(v_inst_4431_, 1);
lean_inc(v_toBind_4434_);
lean_dec_ref(v_inst_4431_);
v___x_4435_ = lean_box(v_pu_4428_);
v___x_4436_ = lean_box(v_t_4429_);
v___f_4437_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4437_, 0, v___x_4435_);
lean_closure_set(v___f_4437_, 1, v___x_4436_);
lean_closure_set(v___f_4437_, 2, v_code_4433_);
lean_closure_set(v___f_4437_, 3, v_inst_4430_);
v___x_4438_ = lean_apply_4(v_toBind_4434_, lean_box(0), lean_box(0), v_inst_4432_, v___f_4437_);
return v___x_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___boxed(lean_object* v_m_4439_, lean_object* v_pu_4440_, lean_object* v_t_4441_, lean_object* v_inst_4442_, lean_object* v_inst_4443_, lean_object* v_inst_4444_, lean_object* v_code_4445_){
_start:
{
uint8_t v_pu_boxed_4446_; uint8_t v_t_boxed_4447_; lean_object* v_res_4448_; 
v_pu_boxed_4446_ = lean_unbox(v_pu_4440_);
v_t_boxed_4447_ = lean_unbox(v_t_4441_);
v_res_4448_ = l_Lean_Compiler_LCNF_normCode(v_m_4439_, v_pu_boxed_4446_, v_t_boxed_4447_, v_inst_4442_, v_inst_4443_, v_inst_4444_, v_code_4445_);
return v_res_4448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t v_pu_4449_, lean_object* v_e_4450_, lean_object* v_s_4451_, uint8_t v_translator_4452_){
_start:
{
lean_object* v___x_4454_; lean_object* v___x_4455_; 
v___x_4454_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4449_, v_s_4451_, v_translator_4452_, v_e_4450_);
v___x_4455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4455_, 0, v___x_4454_);
return v___x_4455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg___boxed(lean_object* v_pu_4456_, lean_object* v_e_4457_, lean_object* v_s_4458_, lean_object* v_translator_4459_, lean_object* v_a_4460_){
_start:
{
uint8_t v_pu_boxed_4461_; uint8_t v_translator_boxed_4462_; lean_object* v_res_4463_; 
v_pu_boxed_4461_ = lean_unbox(v_pu_4456_);
v_translator_boxed_4462_ = lean_unbox(v_translator_4459_);
v_res_4463_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_boxed_4461_, v_e_4457_, v_s_4458_, v_translator_boxed_4462_);
lean_dec_ref(v_s_4458_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(uint8_t v_pu_4464_, lean_object* v_e_4465_, lean_object* v_s_4466_, uint8_t v_translator_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_){
_start:
{
lean_object* v___x_4473_; 
v___x_4473_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_4464_, v_e_4465_, v_s_4466_, v_translator_4467_);
return v___x_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___boxed(lean_object* v_pu_4474_, lean_object* v_e_4475_, lean_object* v_s_4476_, lean_object* v_translator_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_){
_start:
{
uint8_t v_pu_boxed_4483_; uint8_t v_translator_boxed_4484_; lean_object* v_res_4485_; 
v_pu_boxed_4483_ = lean_unbox(v_pu_4474_);
v_translator_boxed_4484_ = lean_unbox(v_translator_4477_);
v_res_4485_ = l_Lean_Compiler_LCNF_replaceExprFVars(v_pu_boxed_4483_, v_e_4475_, v_s_4476_, v_translator_boxed_4484_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_);
lean_dec(v_a_4481_);
lean_dec_ref(v_a_4480_);
lean_dec(v_a_4479_);
lean_dec_ref(v_a_4478_);
lean_dec_ref(v_s_4476_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t v_pu_4486_, lean_object* v_code_4487_, lean_object* v_s_4488_, uint8_t v_translator_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_){
_start:
{
lean_object* v___x_4495_; 
v___x_4495_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4486_, v_translator_4489_, v_code_4487_, v_s_4488_, v_a_4490_, v_a_4491_, v_a_4492_, v_a_4493_);
return v___x_4495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars___boxed(lean_object* v_pu_4496_, lean_object* v_code_4497_, lean_object* v_s_4498_, lean_object* v_translator_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_){
_start:
{
uint8_t v_pu_boxed_4505_; uint8_t v_translator_boxed_4506_; lean_object* v_res_4507_; 
v_pu_boxed_4505_ = lean_unbox(v_pu_4496_);
v_translator_boxed_4506_ = lean_unbox(v_translator_4499_);
v_res_4507_ = l_Lean_Compiler_LCNF_replaceFVars(v_pu_boxed_4505_, v_code_4497_, v_s_4498_, v_translator_boxed_4506_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_);
lean_dec(v_a_4503_);
lean_dec_ref(v_a_4502_);
lean_dec(v_a_4501_);
lean_dec_ref(v_a_4500_);
lean_dec_ref(v_s_4498_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg(lean_object* v_a_4511_){
_start:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___x_4513_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1));
v___x_4514_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4513_, v_a_4511_);
return v___x_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___boxed(lean_object* v_a_4515_, lean_object* v_a_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4515_);
lean_dec(v_a_4515_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName(lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_){
_start:
{
lean_object* v___x_4523_; 
v___x_4523_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4519_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___boxed(lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_){
_start:
{
lean_object* v_res_4529_; 
v_res_4529_ = l_Lean_Compiler_LCNF_mkFreshJpName(v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_);
lean_dec(v_a_4527_);
lean_dec_ref(v_a_4526_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t v_pu_4530_, lean_object* v_type_4531_, uint8_t v_borrow_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_){
_start:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v_a_4540_; lean_object* v___x_4541_; 
v___x_4538_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_4539_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4538_, v_a_4534_);
v_a_4540_ = lean_ctor_get(v___x_4539_, 0);
lean_inc(v_a_4540_);
lean_dec_ref(v___x_4539_);
v___x_4541_ = l_Lean_Compiler_LCNF_mkParam(v_pu_4530_, v_a_4540_, v_type_4531_, v_borrow_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_);
return v___x_4541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam___boxed(lean_object* v_pu_4542_, lean_object* v_type_4543_, lean_object* v_borrow_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_){
_start:
{
uint8_t v_pu_boxed_4550_; uint8_t v_borrow_boxed_4551_; lean_object* v_res_4552_; 
v_pu_boxed_4550_ = lean_unbox(v_pu_4542_);
v_borrow_boxed_4551_ = lean_unbox(v_borrow_4544_);
v_res_4552_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_boxed_4550_, v_type_4543_, v_borrow_boxed_4551_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_);
lean_dec(v_a_4548_);
lean_dec_ref(v_a_4547_);
lean_dec(v_a_4546_);
lean_dec_ref(v_a_4545_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object* v_a_4553_){
_start:
{
lean_object* v_config_4555_; lean_object* v___x_4556_; 
v_config_4555_ = lean_ctor_get(v_a_4553_, 0);
lean_inc_ref(v_config_4555_);
v___x_4556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4556_, 0, v_config_4555_);
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg___boxed(lean_object* v_a_4557_, lean_object* v_a_4558_){
_start:
{
lean_object* v_res_4559_; 
v_res_4559_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4557_);
lean_dec_ref(v_a_4557_);
return v_res_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig(lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_){
_start:
{
lean_object* v___x_4565_; 
v___x_4565_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4560_);
return v___x_4565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___boxed(lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l_Lean_Compiler_LCNF_getConfig(v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_);
lean_dec(v_a_4569_);
lean_dec_ref(v_a_4568_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object* v_x_4572_, lean_object* v_s_4573_, uint8_t v_phase_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_){
_start:
{
lean_object* v___x_4578_; lean_object* v_options_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; 
v___x_4578_ = lean_st_mk_ref(v_s_4573_);
v_options_4579_ = lean_ctor_get(v_a_4575_, 2);
v___x_4580_ = l_Lean_Compiler_LCNF_toConfigOptions(v_options_4579_);
v___x_4581_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4581_, 0, v___x_4580_);
lean_ctor_set_uint8(v___x_4581_, sizeof(void*)*1, v_phase_4574_);
lean_inc(v_a_4576_);
lean_inc_ref(v_a_4575_);
lean_inc(v___x_4578_);
v___x_4582_ = lean_apply_5(v_x_4572_, v___x_4581_, v___x_4578_, v_a_4575_, v_a_4576_, lean_box(0));
if (lean_obj_tag(v___x_4582_) == 0)
{
lean_object* v_a_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4591_; 
v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4585_ = v___x_4582_;
v_isShared_4586_ = v_isSharedCheck_4591_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_a_4583_);
lean_dec(v___x_4582_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4591_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4587_; lean_object* v___x_4589_; 
v___x_4587_ = lean_st_ref_get(v___x_4578_);
lean_dec(v___x_4578_);
lean_dec(v___x_4587_);
if (v_isShared_4586_ == 0)
{
v___x_4589_ = v___x_4585_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_a_4583_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
}
else
{
lean_dec(v___x_4578_);
return v___x_4582_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg___boxed(lean_object* v_x_4592_, lean_object* v_s_4593_, lean_object* v_phase_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_){
_start:
{
uint8_t v_phase_boxed_4598_; lean_object* v_res_4599_; 
v_phase_boxed_4598_ = lean_unbox(v_phase_4594_);
v_res_4599_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4592_, v_s_4593_, v_phase_boxed_4598_, v_a_4595_, v_a_4596_);
lean_dec(v_a_4596_);
lean_dec_ref(v_a_4595_);
return v_res_4599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run(lean_object* v_00_u03b1_4600_, lean_object* v_x_4601_, lean_object* v_s_4602_, uint8_t v_phase_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_){
_start:
{
lean_object* v___x_4607_; 
v___x_4607_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4601_, v_s_4602_, v_phase_4603_, v_a_4604_, v_a_4605_);
return v___x_4607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___boxed(lean_object* v_00_u03b1_4608_, lean_object* v_x_4609_, lean_object* v_s_4610_, lean_object* v_phase_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_){
_start:
{
uint8_t v_phase_boxed_4615_; lean_object* v_res_4616_; 
v_phase_boxed_4615_ = lean_unbox(v_phase_4611_);
v_res_4616_ = l_Lean_Compiler_LCNF_CompilerM_run(v_00_u03b1_4608_, v_x_4609_, v_s_4610_, v_phase_boxed_4615_, v_a_4612_, v_a_4613_);
lean_dec(v_a_4613_);
lean_dec_ref(v_a_4612_);
return v_res_4616_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0(void){
_start:
{
lean_object* v___x_4617_; 
v___x_4617_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_){
_start:
{
lean_object* v___x_4622_; 
v___x_4622_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_){
_start:
{
lean_object* v_res_4627_; 
v_res_4627_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_);
lean_dec_ref(v_a_4626_);
lean_dec_ref(v_a_4625_);
return v_res_4627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension(lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_){
_start:
{
lean_object* v___x_4632_; 
v___x_4632_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___boxed(lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_){
_start:
{
lean_object* v_res_4637_; 
v_res_4637_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension(v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_);
lean_dec_ref(v_a_4636_);
lean_dec_ref(v_a_4635_);
return v_res_4637_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4641_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2));
v___x_4642_ = lean_unsigned_to_nat(14u);
v___x_4643_ = lean_unsigned_to_nat(177u);
v___x_4644_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1));
v___x_4645_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0));
v___x_4646_ = l_mkPanicMessageWithDecl(v___x_4645_, v___x_4644_, v___x_4643_, v___x_4642_, v___x_4641_);
return v___x_4646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(lean_object* v_inst_4647_, lean_object* v_inst_4648_, lean_object* v_snd_4649_, lean_object* v_inst_4650_, lean_object* v_s_4651_, lean_object* v_e_4652_){
_start:
{
lean_object* v_fst_4653_; lean_object* v_snd_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4669_; 
v_fst_4653_ = lean_ctor_get(v_s_4651_, 0);
v_snd_4654_ = lean_ctor_get(v_s_4651_, 1);
v_isSharedCheck_4669_ = !lean_is_exclusive(v_s_4651_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4656_ = v_s_4651_;
v_isShared_4657_ = v_isSharedCheck_4669_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_snd_4654_);
lean_inc(v_fst_4653_);
lean_dec(v_s_4651_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4669_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4658_; lean_object* v___y_4660_; lean_object* v___x_4665_; 
lean_inc_n(v_e_4652_, 2);
v___x_4658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4658_, 0, v_e_4652_);
lean_ctor_set(v___x_4658_, 1, v_fst_4653_);
lean_inc_ref(v_inst_4648_);
lean_inc_ref(v_inst_4647_);
v___x_4665_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4647_, v_inst_4648_, v_snd_4649_, v_e_4652_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4666_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3);
v___x_4667_ = l_panic___redArg(v_inst_4650_, v___x_4666_);
v___y_4660_ = v___x_4667_;
goto v___jp_4659_;
}
else
{
lean_object* v_val_4668_; 
v_val_4668_ = lean_ctor_get(v___x_4665_, 0);
lean_inc(v_val_4668_);
lean_dec_ref(v___x_4665_);
v___y_4660_ = v_val_4668_;
goto v___jp_4659_;
}
v___jp_4659_:
{
lean_object* v___x_4661_; lean_object* v___x_4663_; 
v___x_4661_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4647_, v_inst_4648_, v_snd_4654_, v_e_4652_, v___y_4660_);
if (v_isShared_4657_ == 0)
{
lean_ctor_set(v___x_4656_, 1, v___x_4661_);
lean_ctor_set(v___x_4656_, 0, v___x_4658_);
v___x_4663_ = v___x_4656_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v___x_4658_);
lean_ctor_set(v_reuseFailAlloc_4664_, 1, v___x_4661_);
v___x_4663_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
return v___x_4663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed(lean_object* v_inst_4670_, lean_object* v_inst_4671_, lean_object* v_snd_4672_, lean_object* v_inst_4673_, lean_object* v_s_4674_, lean_object* v_e_4675_){
_start:
{
lean_object* v_res_4676_; 
v_res_4676_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(v_inst_4670_, v_inst_4671_, v_snd_4672_, v_inst_4673_, v_s_4674_, v_e_4675_);
lean_dec(v_inst_4673_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(lean_object* v_inst_4679_, lean_object* v_inst_4680_, lean_object* v_inst_4681_, lean_object* v_oldState_4682_, lean_object* v_newState_4683_, lean_object* v_x_4684_, lean_object* v_s_4685_){
_start:
{
lean_object* v_fst_4686_; lean_object* v_snd_4687_; lean_object* v_fst_4688_; lean_object* v___f_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v_newEntries_4694_; lean_object* v___x_4695_; 
v_fst_4686_ = lean_ctor_get(v_newState_4683_, 0);
lean_inc_n(v_fst_4686_, 2);
v_snd_4687_ = lean_ctor_get(v_newState_4683_, 1);
lean_inc(v_snd_4687_);
lean_dec_ref(v_newState_4683_);
v_fst_4688_ = lean_ctor_get(v_oldState_4682_, 0);
v___f_4689_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_4689_, 0, v_inst_4679_);
lean_closure_set(v___f_4689_, 1, v_inst_4680_);
lean_closure_set(v___f_4689_, 2, v_snd_4687_);
lean_closure_set(v___f_4689_, 3, v_inst_4681_);
v___x_4690_ = l_List_lengthTR___redArg(v_fst_4686_);
v___x_4691_ = l_List_lengthTR___redArg(v_fst_4688_);
v___x_4692_ = lean_nat_sub(v___x_4690_, v___x_4691_);
lean_dec(v___x_4691_);
lean_dec(v___x_4690_);
v___x_4693_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0));
v_newEntries_4694_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_fst_4686_, v_fst_4686_, v___x_4692_, v___x_4693_);
lean_dec(v_fst_4686_);
v___x_4695_ = l_List_foldl___redArg(v___f_4689_, v_s_4685_, v_newEntries_4694_);
return v___x_4695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(lean_object* v_inst_4696_, lean_object* v_inst_4697_, lean_object* v_inst_4698_, lean_object* v_oldState_4699_, lean_object* v_newState_4700_, lean_object* v_x_4701_, lean_object* v_s_4702_){
_start:
{
lean_object* v_res_4703_; 
v_res_4703_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(v_inst_4696_, v_inst_4697_, v_inst_4698_, v_oldState_4699_, v_newState_4700_, v_x_4701_, v_s_4702_);
lean_dec(v_x_4701_);
lean_dec_ref(v_oldState_4699_);
return v_res_4703_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0(void){
_start:
{
lean_object* v___x_4704_; 
v___x_4704_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4704_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1(void){
_start:
{
lean_object* v___x_4705_; lean_object* v___x_4706_; 
v___x_4705_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0);
v___x_4706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4706_, 0, v___x_4705_);
return v___x_4706_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2(void){
_start:
{
lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; 
v___x_4707_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1);
v___x_4708_ = lean_box(0);
v___x_4709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4708_);
lean_ctor_set(v___x_4709_, 1, v___x_4707_);
return v___x_4709_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3(void){
_start:
{
lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4710_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2);
v___x_4711_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_4711_, 0, lean_box(0));
lean_closure_set(v___x_4711_, 1, lean_box(0));
lean_closure_set(v___x_4711_, 2, v___x_4710_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object* v_inst_4712_, lean_object* v_inst_4713_, lean_object* v_inst_4714_){
_start:
{
lean_object* v___f_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; 
v___f_4716_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4716_, 0, v_inst_4712_);
lean_closure_set(v___f_4716_, 1, v_inst_4713_);
lean_closure_set(v___f_4716_, 2, v_inst_4714_);
v___x_4717_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3);
v___x_4718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4718_, 0, v___f_4716_);
v___x_4719_ = lean_box(0);
v___x_4720_ = l_Lean_registerEnvExtension___redArg(v___x_4717_, v___x_4718_, v___x_4719_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4728_; 
v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4723_ = v___x_4720_;
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v___x_4720_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4726_; 
if (v_isShared_4724_ == 0)
{
v___x_4726_ = v___x_4723_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_a_4721_);
v___x_4726_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
return v___x_4726_;
}
}
}
else
{
lean_object* v_a_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4736_; 
v_a_4729_ = lean_ctor_get(v___x_4720_, 0);
v_isSharedCheck_4736_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4736_ == 0)
{
v___x_4731_ = v___x_4720_;
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_a_4729_);
lean_dec(v___x_4720_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4734_; 
if (v_isShared_4732_ == 0)
{
v___x_4734_ = v___x_4731_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4735_; 
v_reuseFailAlloc_4735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_a_4729_);
v___x_4734_ = v_reuseFailAlloc_4735_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
return v___x_4734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object* v_inst_4737_, lean_object* v_inst_4738_, lean_object* v_inst_4739_, lean_object* v_a_4740_){
_start:
{
lean_object* v_res_4741_; 
v_res_4741_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4737_, v_inst_4738_, v_inst_4739_);
return v_res_4741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object* v_00_u03b1_4742_, lean_object* v_00_u03b2_4743_, lean_object* v_inst_4744_, lean_object* v_inst_4745_, lean_object* v_inst_4746_){
_start:
{
lean_object* v___x_4748_; 
v___x_4748_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4744_, v_inst_4745_, v_inst_4746_);
return v___x_4748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object* v_00_u03b1_4749_, lean_object* v_00_u03b2_4750_, lean_object* v_inst_4751_, lean_object* v_inst_4752_, lean_object* v_inst_4753_, lean_object* v_a_4754_){
_start:
{
lean_object* v_res_4755_; 
v_res_4755_ = l_Lean_Compiler_LCNF_CacheExtension_register(v_00_u03b1_4749_, v_00_u03b2_4750_, v_inst_4751_, v_inst_4752_, v_inst_4753_);
return v_res_4755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object* v_a_4756_, lean_object* v_inst_4757_, lean_object* v_inst_4758_, lean_object* v_b_4759_, lean_object* v_x_4760_){
_start:
{
lean_object* v_fst_4761_; lean_object* v_snd_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4771_; 
v_fst_4761_ = lean_ctor_get(v_x_4760_, 0);
v_snd_4762_ = lean_ctor_get(v_x_4760_, 1);
v_isSharedCheck_4771_ = !lean_is_exclusive(v_x_4760_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4764_ = v_x_4760_;
v_isShared_4765_ = v_isSharedCheck_4771_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_snd_4762_);
lean_inc(v_fst_4761_);
lean_dec(v_x_4760_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4771_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4769_; 
lean_inc(v_a_4756_);
v___x_4766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4766_, 0, v_a_4756_);
lean_ctor_set(v___x_4766_, 1, v_fst_4761_);
v___x_4767_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4757_, v_inst_4758_, v_snd_4762_, v_a_4756_, v_b_4759_);
if (v_isShared_4765_ == 0)
{
lean_ctor_set(v___x_4764_, 1, v___x_4767_);
lean_ctor_set(v___x_4764_, 0, v___x_4766_);
v___x_4769_ = v___x_4764_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v___x_4766_);
lean_ctor_set(v_reuseFailAlloc_4770_, 1, v___x_4767_);
v___x_4769_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
return v___x_4769_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_4772_; 
v___x_4772_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4772_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4773_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0);
v___x_4774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4773_);
return v___x_4774_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2(void){
_start:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; 
v___x_4775_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1);
v___x_4776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4776_, 0, v___x_4775_);
lean_ctor_set(v___x_4776_, 1, v___x_4775_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object* v_inst_4777_, lean_object* v_inst_4778_, lean_object* v_ext_4779_, lean_object* v_a_4780_, lean_object* v_b_4781_, lean_object* v_a_4782_){
_start:
{
lean_object* v___x_4784_; lean_object* v_env_4785_; lean_object* v_nextMacroScope_4786_; lean_object* v_ngen_4787_; lean_object* v_auxDeclNGen_4788_; lean_object* v_traceState_4789_; lean_object* v_messages_4790_; lean_object* v_infoState_4791_; lean_object* v_snapshotTasks_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4807_; 
v___x_4784_ = lean_st_ref_take(v_a_4782_);
v_env_4785_ = lean_ctor_get(v___x_4784_, 0);
v_nextMacroScope_4786_ = lean_ctor_get(v___x_4784_, 1);
v_ngen_4787_ = lean_ctor_get(v___x_4784_, 2);
v_auxDeclNGen_4788_ = lean_ctor_get(v___x_4784_, 3);
v_traceState_4789_ = lean_ctor_get(v___x_4784_, 4);
v_messages_4790_ = lean_ctor_get(v___x_4784_, 6);
v_infoState_4791_ = lean_ctor_get(v___x_4784_, 7);
v_snapshotTasks_4792_ = lean_ctor_get(v___x_4784_, 8);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4807_ == 0)
{
lean_object* v_unused_4808_; 
v_unused_4808_ = lean_ctor_get(v___x_4784_, 5);
lean_dec(v_unused_4808_);
v___x_4794_ = v___x_4784_;
v_isShared_4795_ = v_isSharedCheck_4807_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_snapshotTasks_4792_);
lean_inc(v_infoState_4791_);
lean_inc(v_messages_4790_);
lean_inc(v_traceState_4789_);
lean_inc(v_auxDeclNGen_4788_);
lean_inc(v_ngen_4787_);
lean_inc(v_nextMacroScope_4786_);
lean_inc(v_env_4785_);
lean_dec(v___x_4784_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4807_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v_asyncMode_4796_; lean_object* v___f_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4802_; 
v_asyncMode_4796_ = lean_ctor_get(v_ext_4779_, 2);
lean_inc(v_asyncMode_4796_);
v___f_4797_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4797_, 0, v_a_4780_);
lean_closure_set(v___f_4797_, 1, v_inst_4777_);
lean_closure_set(v___f_4797_, 2, v_inst_4778_);
lean_closure_set(v___f_4797_, 3, v_b_4781_);
v___x_4798_ = lean_box(0);
v___x_4799_ = l_Lean_EnvExtension_modifyState___redArg(v_ext_4779_, v_env_4785_, v___f_4797_, v_asyncMode_4796_, v___x_4798_);
lean_dec(v_asyncMode_4796_);
v___x_4800_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2);
if (v_isShared_4795_ == 0)
{
lean_ctor_set(v___x_4794_, 5, v___x_4800_);
lean_ctor_set(v___x_4794_, 0, v___x_4799_);
v___x_4802_ = v___x_4794_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4799_);
lean_ctor_set(v_reuseFailAlloc_4806_, 1, v_nextMacroScope_4786_);
lean_ctor_set(v_reuseFailAlloc_4806_, 2, v_ngen_4787_);
lean_ctor_set(v_reuseFailAlloc_4806_, 3, v_auxDeclNGen_4788_);
lean_ctor_set(v_reuseFailAlloc_4806_, 4, v_traceState_4789_);
lean_ctor_set(v_reuseFailAlloc_4806_, 5, v___x_4800_);
lean_ctor_set(v_reuseFailAlloc_4806_, 6, v_messages_4790_);
lean_ctor_set(v_reuseFailAlloc_4806_, 7, v_infoState_4791_);
lean_ctor_set(v_reuseFailAlloc_4806_, 8, v_snapshotTasks_4792_);
v___x_4802_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; 
v___x_4803_ = lean_st_ref_set(v_a_4782_, v___x_4802_);
v___x_4804_ = lean_box(0);
v___x_4805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4805_, 0, v___x_4804_);
return v___x_4805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object* v_inst_4809_, lean_object* v_inst_4810_, lean_object* v_ext_4811_, lean_object* v_a_4812_, lean_object* v_b_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_){
_start:
{
lean_object* v_res_4816_; 
v_res_4816_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4809_, v_inst_4810_, v_ext_4811_, v_a_4812_, v_b_4813_, v_a_4814_);
lean_dec(v_a_4814_);
return v_res_4816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object* v_00_u03b1_4817_, lean_object* v_00_u03b2_4818_, lean_object* v_inst_4819_, lean_object* v_inst_4820_, lean_object* v_inst_4821_, lean_object* v_ext_4822_, lean_object* v_a_4823_, lean_object* v_b_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_){
_start:
{
lean_object* v___x_4828_; 
v___x_4828_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4819_, v_inst_4820_, v_ext_4822_, v_a_4823_, v_b_4824_, v_a_4826_);
return v___x_4828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object* v_00_u03b1_4829_, lean_object* v_00_u03b2_4830_, lean_object* v_inst_4831_, lean_object* v_inst_4832_, lean_object* v_inst_4833_, lean_object* v_ext_4834_, lean_object* v_a_4835_, lean_object* v_b_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_){
_start:
{
lean_object* v_res_4840_; 
v_res_4840_ = l_Lean_Compiler_LCNF_CacheExtension_insert(v_00_u03b1_4829_, v_00_u03b2_4830_, v_inst_4831_, v_inst_4832_, v_inst_4833_, v_ext_4834_, v_a_4835_, v_b_4836_, v_a_4837_, v_a_4838_);
lean_dec(v_a_4838_);
lean_dec_ref(v_a_4837_);
lean_dec(v_inst_4833_);
return v_res_4840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(lean_object* v_inst_4841_, lean_object* v_inst_4842_, lean_object* v_ext_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_){
_start:
{
lean_object* v___x_4847_; lean_object* v_env_4848_; lean_object* v_asyncMode_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v_snd_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; 
v___x_4847_ = lean_st_ref_get(v_a_4845_);
v_env_4848_ = lean_ctor_get(v___x_4847_, 0);
lean_inc_ref(v_env_4848_);
lean_dec(v___x_4847_);
v_asyncMode_4849_ = lean_ctor_get(v_ext_4843_, 2);
v___x_4850_ = lean_box(0);
v___x_4851_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v_inst_4841_, v_inst_4842_);
v___x_4852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4852_, 0, v___x_4850_);
lean_ctor_set(v___x_4852_, 1, v___x_4851_);
v___x_4853_ = lean_box(0);
v___x_4854_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4852_, v_ext_4843_, v_env_4848_, v_asyncMode_4849_, v___x_4853_);
lean_dec_ref(v___x_4852_);
v_snd_4855_ = lean_ctor_get(v___x_4854_, 1);
lean_inc(v_snd_4855_);
lean_dec(v___x_4854_);
v___x_4856_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4841_, v_inst_4842_, v_snd_4855_, v_a_4844_);
v___x_4857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4857_, 0, v___x_4856_);
return v___x_4857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(lean_object* v_inst_4858_, lean_object* v_inst_4859_, lean_object* v_ext_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_){
_start:
{
lean_object* v_res_4864_; 
v_res_4864_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4858_, v_inst_4859_, v_ext_4860_, v_a_4861_, v_a_4862_);
lean_dec(v_a_4862_);
lean_dec_ref(v_ext_4860_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_object* v_00_u03b1_4865_, lean_object* v_00_u03b2_4866_, lean_object* v_inst_4867_, lean_object* v_inst_4868_, lean_object* v_inst_4869_, lean_object* v_ext_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_){
_start:
{
lean_object* v___x_4875_; 
v___x_4875_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4867_, v_inst_4868_, v_ext_4870_, v_a_4871_, v_a_4873_);
return v___x_4875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(lean_object* v_00_u03b1_4876_, lean_object* v_00_u03b2_4877_, lean_object* v_inst_4878_, lean_object* v_inst_4879_, lean_object* v_inst_4880_, lean_object* v_ext_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_){
_start:
{
lean_object* v_res_4886_; 
v_res_4886_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f(v_00_u03b1_4876_, v_00_u03b2_4877_, v_inst_4878_, v_inst_4879_, v_inst_4880_, v_ext_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
lean_dec(v_a_4884_);
lean_dec_ref(v_a_4883_);
lean_dec_ref(v_ext_4881_);
lean_dec(v_inst_4880_);
return v_res_4886_;
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
l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default = _init_l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default);
l_Lean_Compiler_LCNF_instInhabitedNormFVarResult = _init_l_Lean_Compiler_LCNF_instInhabitedNormFVarResult();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedNormFVarResult);
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
