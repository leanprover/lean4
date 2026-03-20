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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParam(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(uint8_t, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
lean_object* l_ReaderT_read(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__2___boxed(lean_object*, lean_object*);
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
v___x_135_ = lean_apply_6(v___y_127_, v_a_134_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, lean_box(0));
return v___x_135_;
}
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
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
return v_res_153_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0(void){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_154_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0);
v___x_156_ = l_ReaderT_instMonad___redArg(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM(void){
_start:
{
lean_object* v___x_161_; lean_object* v_toApplicative_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_219_; 
v___x_161_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_219_ == 0)
{
lean_object* v_unused_220_; 
v_unused_220_ = lean_ctor_get(v___x_161_, 1);
lean_dec(v_unused_220_);
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_219_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_toApplicative_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_219_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v_toFunctor_166_; lean_object* v_toSeq_167_; lean_object* v_toSeqLeft_168_; lean_object* v_toSeqRight_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_217_; 
v_toFunctor_166_ = lean_ctor_get(v_toApplicative_162_, 0);
v_toSeq_167_ = lean_ctor_get(v_toApplicative_162_, 2);
v_toSeqLeft_168_ = lean_ctor_get(v_toApplicative_162_, 3);
v_toSeqRight_169_ = lean_ctor_get(v_toApplicative_162_, 4);
v_isSharedCheck_217_ = !lean_is_exclusive(v_toApplicative_162_);
if (v_isSharedCheck_217_ == 0)
{
lean_object* v_unused_218_; 
v_unused_218_ = lean_ctor_get(v_toApplicative_162_, 1);
lean_dec(v_unused_218_);
v___x_171_ = v_toApplicative_162_;
v_isShared_172_ = v_isSharedCheck_217_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_toSeqRight_169_);
lean_inc(v_toSeqLeft_168_);
lean_inc(v_toSeq_167_);
lean_inc(v_toFunctor_166_);
lean_dec(v_toApplicative_162_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_217_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___f_173_; lean_object* v___f_174_; lean_object* v___f_175_; lean_object* v___f_176_; lean_object* v___x_177_; lean_object* v___f_178_; lean_object* v___f_179_; lean_object* v___f_180_; lean_object* v___x_182_; 
v___f_173_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_174_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref(v_toFunctor_166_);
v___f_175_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_175_, 0, v_toFunctor_166_);
v___f_176_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_176_, 0, v_toFunctor_166_);
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v___f_175_);
lean_ctor_set(v___x_177_, 1, v___f_176_);
v___f_178_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_178_, 0, v_toSeqRight_169_);
v___f_179_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_179_, 0, v_toSeqLeft_168_);
v___f_180_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_180_, 0, v_toSeq_167_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 4, v___f_178_);
lean_ctor_set(v___x_171_, 3, v___f_179_);
lean_ctor_set(v___x_171_, 2, v___f_180_);
lean_ctor_set(v___x_171_, 1, v___f_173_);
lean_ctor_set(v___x_171_, 0, v___x_177_);
v___x_182_ = v___x_171_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v___f_173_);
lean_ctor_set(v_reuseFailAlloc_216_, 2, v___f_180_);
lean_ctor_set(v_reuseFailAlloc_216_, 3, v___f_179_);
lean_ctor_set(v_reuseFailAlloc_216_, 4, v___f_178_);
v___x_182_ = v_reuseFailAlloc_216_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_184_; 
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 1, v___f_174_);
lean_ctor_set(v___x_164_, 0, v___x_182_);
v___x_184_ = v___x_164_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___f_174_);
v___x_184_ = v_reuseFailAlloc_215_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; lean_object* v_toApplicative_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_213_; 
v___x_185_ = l_ReaderT_instMonad___redArg(v___x_184_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg(uint8_t v_phase_221_, lean_object* v_x_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_config_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_236_; 
v_config_228_ = lean_ctor_get(v_a_223_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v_a_223_);
if (v_isSharedCheck_236_ == 0)
{
v___x_230_ = v_a_223_;
v_isShared_231_ = v_isSharedCheck_236_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_config_228_);
lean_dec(v_a_223_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_236_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_config_228_);
v___x_233_ = v_reuseFailAlloc_235_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; 
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*1, v_phase_221_);
v___x_234_ = lean_apply_5(v_x_222_, v___x_233_, v_a_224_, v_a_225_, v_a_226_, lean_box(0));
return v___x_234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg___boxed(lean_object* v_phase_237_, lean_object* v_x_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
uint8_t v_phase_boxed_244_; lean_object* v_res_245_; 
v_phase_boxed_244_ = lean_unbox(v_phase_237_);
v_res_245_ = l_Lean_Compiler_LCNF_withPhase___redArg(v_phase_boxed_244_, v_x_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase(lean_object* v_00_u03b1_246_, uint8_t v_phase_247_, lean_object* v_x_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_config_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_262_; 
v_config_254_ = lean_ctor_get(v_a_249_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v_a_249_);
if (v_isSharedCheck_262_ == 0)
{
v___x_256_ = v_a_249_;
v_isShared_257_ = v_isSharedCheck_262_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_config_254_);
lean_dec(v_a_249_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_262_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_config_254_);
v___x_259_ = v_reuseFailAlloc_261_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; 
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*1, v_phase_247_);
v___x_260_ = lean_apply_5(v_x_248_, v___x_259_, v_a_250_, v_a_251_, v_a_252_, lean_box(0));
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___boxed(lean_object* v_00_u03b1_263_, lean_object* v_phase_264_, lean_object* v_x_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
uint8_t v_phase_boxed_271_; lean_object* v_res_272_; 
v_phase_boxed_271_ = lean_unbox(v_phase_264_);
v_res_272_ = l_Lean_Compiler_LCNF_withPhase(v_00_u03b1_263_, v_phase_boxed_271_, v_x_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object* v_a_273_){
_start:
{
uint8_t v_phase_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_phase_275_ = lean_ctor_get_uint8(v_a_273_, sizeof(void*)*1);
v___x_276_ = lean_box(v_phase_275_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg___boxed(lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_278_);
lean_dec_ref(v_a_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase(lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_281_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___boxed(lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Compiler_LCNF_getPhase(v_a_287_, v_a_288_, v_a_289_, v_a_290_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object* v_a_293_){
_start:
{
lean_object* v___x_295_; lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_306_; 
v___x_295_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_293_);
v_a_296_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_306_ == 0)
{
v___x_298_ = v___x_295_;
v_isShared_299_ = v_isSharedCheck_306_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_295_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_306_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
uint8_t v___x_300_; uint8_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_300_ = lean_unbox(v_a_296_);
lean_dec(v_a_296_);
v___x_301_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_300_);
v___x_302_ = lean_box(v___x_301_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v___x_302_);
v___x_304_ = v___x_298_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg___boxed(lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_307_);
lean_dec_ref(v_a_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity(lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_310_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___boxed(lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Compiler_LCNF_getPurity(v_a_316_, v_a_317_, v_a_318_, v_a_319_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg(lean_object* v_a_322_){
_start:
{
lean_object* v___x_324_; lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_340_; 
v___x_324_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_322_);
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_340_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_340_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_340_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
uint8_t v___x_329_; 
v___x_329_ = lean_unbox(v_a_325_);
lean_dec(v_a_325_);
if (v___x_329_ == 0)
{
uint8_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_330_ = 1;
v___x_331_ = lean_box(v___x_330_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_331_);
v___x_333_ = v___x_327_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
else
{
uint8_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_335_ = 0;
v___x_336_ = lean_box(v___x_335_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_336_);
v___x_338_ = v___x_327_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg___boxed(lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_341_);
lean_dec_ref(v_a_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase(lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_344_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___boxed(lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Compiler_LCNF_inBasePhase(v_a_350_, v_a_351_, v_a_352_, v_a_353_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
return v_res_355_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0(void){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_356_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1);
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
lean_ctor_set(v___x_361_, 2, v___x_360_);
lean_ctor_set(v___x_361_, 3, v___x_359_);
lean_ctor_set(v___x_361_, 4, v___x_359_);
lean_ctor_set(v___x_361_, 5, v___x_359_);
lean_ctor_set(v___x_361_, 6, v___x_359_);
lean_ctor_set(v___x_361_, 7, v___x_359_);
lean_ctor_set(v___x_361_, 8, v___x_359_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(lean_object* v_msgData_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = lean_st_ref_get(v___y_366_);
v___x_369_ = lean_st_ref_get(v___y_364_);
v___x_370_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_363_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_393_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_393_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_393_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_393_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v_env_375_; lean_object* v_lctx_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_391_; 
v_env_375_ = lean_ctor_get(v___x_368_, 0);
lean_inc_ref(v_env_375_);
lean_dec(v___x_368_);
v_lctx_376_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v___x_369_, 1);
lean_dec(v_unused_392_);
v___x_378_ = v___x_369_;
v_isShared_379_ = v_isSharedCheck_391_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_lctx_376_);
lean_dec(v___x_369_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_391_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v_options_380_; uint8_t v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v_options_380_ = lean_ctor_get(v___y_365_, 2);
v___x_381_ = lean_unbox(v_a_371_);
lean_dec(v_a_371_);
v___x_382_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_376_, v___x_381_);
lean_dec_ref(v_lctx_376_);
v___x_383_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_380_);
v___x_384_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_384_, 0, v_env_375_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
lean_ctor_set(v___x_384_, 2, v___x_382_);
lean_ctor_set(v___x_384_, 3, v_options_380_);
if (v_isShared_379_ == 0)
{
lean_ctor_set_tag(v___x_378_, 3);
lean_ctor_set(v___x_378_, 1, v_msgData_362_);
lean_ctor_set(v___x_378_, 0, v___x_384_);
v___x_386_ = v___x_378_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_msgData_362_);
v___x_386_ = v_reuseFailAlloc_390_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_388_; 
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_386_);
v___x_388_ = v___x_373_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec(v___x_369_);
lean_dec(v___x_368_);
lean_dec_ref(v_msgData_362_);
v_a_394_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_370_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_370_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed(lean_object* v_msgData_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(v_msgData_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(lean_object* v_msg_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_options_417_; lean_object* v_ref_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_options_417_ = lean_ctor_get(v___y_414_, 2);
v_ref_418_ = lean_ctor_get(v___y_414_, 5);
v___x_419_ = lean_st_ref_get(v___y_415_);
v___x_420_ = lean_st_ref_get(v___y_413_);
v___x_421_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_412_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_444_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_444_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_444_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_444_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v_env_426_; lean_object* v_lctx_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_442_; 
v_env_426_ = lean_ctor_get(v___x_419_, 0);
lean_inc_ref(v_env_426_);
lean_dec(v___x_419_);
v_lctx_427_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; 
v_unused_443_ = lean_ctor_get(v___x_420_, 1);
lean_dec(v_unused_443_);
v___x_429_ = v___x_420_;
v_isShared_430_ = v_isSharedCheck_442_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_lctx_427_);
lean_dec(v___x_420_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_442_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
uint8_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_431_ = lean_unbox(v_a_422_);
lean_dec(v_a_422_);
v___x_432_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_427_, v___x_431_);
lean_dec_ref(v_lctx_427_);
v___x_433_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_417_);
v___x_434_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_434_, 0, v_env_426_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
lean_ctor_set(v___x_434_, 2, v___x_432_);
lean_ctor_set(v___x_434_, 3, v_options_417_);
if (v_isShared_430_ == 0)
{
lean_ctor_set_tag(v___x_429_, 3);
lean_ctor_set(v___x_429_, 1, v_msg_411_);
lean_ctor_set(v___x_429_, 0, v___x_434_);
v___x_436_ = v___x_429_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_msg_411_);
v___x_436_ = v_reuseFailAlloc_441_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_437_; lean_object* v___x_439_; 
lean_inc(v_ref_418_);
v___x_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_437_, 0, v_ref_418_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 1);
lean_ctor_set(v___x_424_, 0, v___x_437_);
v___x_439_ = v___x_424_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec(v___x_420_);
lean_dec(v___x_419_);
lean_dec_ref(v_msg_411_);
v_a_445_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_421_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_421_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg___boxed(lean_object* v_msg_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(lean_object* v_00_u03b1_460_, lean_object* v_msg_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___boxed(lean_object* v_00_u03b1_468_, lean_object* v_msg_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(v_00_u03b1_468_, v_msg_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(lean_object* v_a_476_, lean_object* v_x_477_){
_start:
{
if (lean_obj_tag(v_x_477_) == 0)
{
lean_object* v___x_478_; 
v___x_478_ = lean_box(0);
return v___x_478_;
}
else
{
lean_object* v_key_479_; lean_object* v_value_480_; lean_object* v_tail_481_; uint8_t v___x_482_; 
v_key_479_ = lean_ctor_get(v_x_477_, 0);
v_value_480_ = lean_ctor_get(v_x_477_, 1);
v_tail_481_ = lean_ctor_get(v_x_477_, 2);
v___x_482_ = l_Lean_instBEqFVarId_beq(v_key_479_, v_a_476_);
if (v___x_482_ == 0)
{
v_x_477_ = v_tail_481_;
goto _start;
}
else
{
lean_object* v___x_484_; 
lean_inc(v_value_480_);
v___x_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_484_, 0, v_value_480_);
return v___x_484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg___boxed(lean_object* v_a_485_, lean_object* v_x_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_485_, v_x_486_);
lean_dec(v_x_486_);
lean_dec(v_a_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object* v_m_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_buckets_490_; lean_object* v___x_491_; uint64_t v___x_492_; uint64_t v___x_493_; uint64_t v___x_494_; uint64_t v_fold_495_; uint64_t v___x_496_; uint64_t v___x_497_; uint64_t v___x_498_; size_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; size_t v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_buckets_490_ = lean_ctor_get(v_m_488_, 1);
v___x_491_ = lean_array_get_size(v_buckets_490_);
v___x_492_ = l_Lean_instHashableFVarId_hash(v_a_489_);
v___x_493_ = 32ULL;
v___x_494_ = lean_uint64_shift_right(v___x_492_, v___x_493_);
v_fold_495_ = lean_uint64_xor(v___x_492_, v___x_494_);
v___x_496_ = 16ULL;
v___x_497_ = lean_uint64_shift_right(v_fold_495_, v___x_496_);
v___x_498_ = lean_uint64_xor(v_fold_495_, v___x_497_);
v___x_499_ = lean_uint64_to_usize(v___x_498_);
v___x_500_ = lean_usize_of_nat(v___x_491_);
v___x_501_ = ((size_t)1ULL);
v___x_502_ = lean_usize_sub(v___x_500_, v___x_501_);
v___x_503_ = lean_usize_land(v___x_499_, v___x_502_);
v___x_504_ = lean_array_uget_borrowed(v_buckets_490_, v___x_503_);
v___x_505_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_489_, v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg___boxed(lean_object* v_m_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_506_, v_a_507_);
lean_dec(v_a_507_);
lean_dec_ref(v_m_506_);
return v_res_508_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getType___closed__1(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = ((lean_object*)(l_Lean_Compiler_LCNF_getType___closed__0));
v___x_511_ = l_Lean_stringToMessageData(v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType(lean_object* v_fvarId_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_st_ref_get(v_a_514_);
v___x_519_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_513_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_570_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_570_ == 0)
{
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_570_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_570_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___y_525_; lean_object* v_lctx_536_; lean_object* v___y_538_; lean_object* v___y_553_; uint8_t v___x_567_; 
v_lctx_536_ = lean_ctor_get(v___x_518_, 0);
lean_inc_ref(v_lctx_536_);
lean_dec(v___x_518_);
v___x_567_ = lean_unbox(v_a_520_);
if (v___x_567_ == 0)
{
lean_object* v_letDeclsPure_568_; 
v_letDeclsPure_568_ = lean_ctor_get(v_lctx_536_, 2);
lean_inc_ref(v_letDeclsPure_568_);
v___y_553_ = v_letDeclsPure_568_;
goto v___jp_552_;
}
else
{
lean_object* v_letDeclsImpure_569_; 
v_letDeclsImpure_569_ = lean_ctor_get(v_lctx_536_, 3);
lean_inc_ref(v_letDeclsImpure_569_);
v___y_553_ = v_letDeclsImpure_569_;
goto v___jp_552_;
}
v___jp_524_:
{
lean_object* v___x_526_; 
v___x_526_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_525_, v_fvarId_512_);
lean_dec_ref(v___y_525_);
if (lean_obj_tag(v___x_526_) == 1)
{
lean_object* v_val_527_; lean_object* v_type_528_; lean_object* v___x_530_; 
lean_dec(v_fvarId_512_);
v_val_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_val_527_);
lean_dec_ref(v___x_526_);
v_type_528_ = lean_ctor_get(v_val_527_, 3);
lean_inc_ref(v_type_528_);
lean_dec(v_val_527_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v_type_528_);
v___x_530_ = v___x_522_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_type_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
lean_dec(v___x_526_);
lean_del_object(v___x_522_);
v___x_532_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_533_ = l_Lean_MessageData_ofName(v_fvarId_512_);
v___x_534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_534_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
return v___x_535_;
}
}
v___jp_537_:
{
lean_object* v___x_539_; 
v___x_539_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_538_, v_fvarId_512_);
lean_dec_ref(v___y_538_);
if (lean_obj_tag(v___x_539_) == 1)
{
lean_object* v_val_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_548_; 
lean_dec_ref(v_lctx_536_);
lean_del_object(v___x_522_);
lean_dec(v_a_520_);
lean_dec(v_fvarId_512_);
v_val_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_548_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_548_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_val_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_548_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v_type_544_; lean_object* v___x_546_; 
v_type_544_ = lean_ctor_get(v_val_540_, 2);
lean_inc_ref(v_type_544_);
lean_dec(v_val_540_);
if (v_isShared_543_ == 0)
{
lean_ctor_set_tag(v___x_542_, 0);
lean_ctor_set(v___x_542_, 0, v_type_544_);
v___x_546_ = v___x_542_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_type_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
uint8_t v___x_549_; 
lean_dec(v___x_539_);
v___x_549_ = lean_unbox(v_a_520_);
lean_dec(v_a_520_);
if (v___x_549_ == 0)
{
lean_object* v_funDeclsPure_550_; 
v_funDeclsPure_550_ = lean_ctor_get(v_lctx_536_, 4);
lean_inc_ref(v_funDeclsPure_550_);
lean_dec_ref(v_lctx_536_);
v___y_525_ = v_funDeclsPure_550_;
goto v___jp_524_;
}
else
{
lean_object* v_funDeclsImpure_551_; 
v_funDeclsImpure_551_ = lean_ctor_get(v_lctx_536_, 5);
lean_inc_ref(v_funDeclsImpure_551_);
lean_dec_ref(v_lctx_536_);
v___y_525_ = v_funDeclsImpure_551_;
goto v___jp_524_;
}
}
}
v___jp_552_:
{
lean_object* v___x_554_; 
v___x_554_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_553_, v_fvarId_512_);
lean_dec_ref(v___y_553_);
if (lean_obj_tag(v___x_554_) == 1)
{
lean_object* v_val_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_563_; 
lean_dec_ref(v_lctx_536_);
lean_del_object(v___x_522_);
lean_dec(v_a_520_);
lean_dec(v_fvarId_512_);
v_val_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_563_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_val_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v_type_559_; lean_object* v___x_561_; 
v_type_559_ = lean_ctor_get(v_val_555_, 2);
lean_inc_ref(v_type_559_);
lean_dec(v_val_555_);
if (v_isShared_558_ == 0)
{
lean_ctor_set_tag(v___x_557_, 0);
lean_ctor_set(v___x_557_, 0, v_type_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_type_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
else
{
uint8_t v___x_564_; 
lean_dec(v___x_554_);
v___x_564_ = lean_unbox(v_a_520_);
if (v___x_564_ == 0)
{
lean_object* v_paramsPure_565_; 
v_paramsPure_565_ = lean_ctor_get(v_lctx_536_, 0);
lean_inc_ref(v_paramsPure_565_);
v___y_538_ = v_paramsPure_565_;
goto v___jp_537_;
}
else
{
lean_object* v_paramsImpure_566_; 
v_paramsImpure_566_ = lean_ctor_get(v_lctx_536_, 1);
lean_inc_ref(v_paramsImpure_566_);
v___y_538_ = v_paramsImpure_566_;
goto v___jp_537_;
}
}
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_dec(v___x_518_);
lean_dec(v_fvarId_512_);
v_a_571_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_519_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_519_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType___boxed(lean_object* v_fvarId_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_Compiler_LCNF_getType(v_fvarId_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(lean_object* v_00_u03b2_586_, lean_object* v_m_587_, lean_object* v_a_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_587_, v_a_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___boxed(lean_object* v_00_u03b2_590_, lean_object* v_m_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(v_00_u03b2_590_, v_m_591_, v_a_592_);
lean_dec(v_a_592_);
lean_dec_ref(v_m_591_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(lean_object* v_00_u03b2_594_, lean_object* v_a_595_, lean_object* v_x_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_595_, v_x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_598_, lean_object* v_a_599_, lean_object* v_x_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(v_00_u03b2_598_, v_a_599_, v_x_600_);
lean_dec(v_x_600_);
lean_dec(v_a_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object* v_fvarId_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_st_ref_get(v_a_604_);
v___x_609_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_603_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_660_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_660_ == 0)
{
v___x_612_ = v___x_609_;
v_isShared_613_ = v_isSharedCheck_660_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_609_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_660_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___y_615_; lean_object* v_lctx_626_; lean_object* v___y_628_; lean_object* v___y_643_; uint8_t v___x_657_; 
v_lctx_626_ = lean_ctor_get(v___x_608_, 0);
lean_inc_ref(v_lctx_626_);
lean_dec(v___x_608_);
v___x_657_ = lean_unbox(v_a_610_);
if (v___x_657_ == 0)
{
lean_object* v_letDeclsPure_658_; 
v_letDeclsPure_658_ = lean_ctor_get(v_lctx_626_, 2);
lean_inc_ref(v_letDeclsPure_658_);
v___y_643_ = v_letDeclsPure_658_;
goto v___jp_642_;
}
else
{
lean_object* v_letDeclsImpure_659_; 
v_letDeclsImpure_659_ = lean_ctor_get(v_lctx_626_, 3);
lean_inc_ref(v_letDeclsImpure_659_);
v___y_643_ = v_letDeclsImpure_659_;
goto v___jp_642_;
}
v___jp_614_:
{
lean_object* v___x_616_; 
v___x_616_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_615_, v_fvarId_602_);
lean_dec_ref(v___y_615_);
if (lean_obj_tag(v___x_616_) == 1)
{
lean_object* v_val_617_; lean_object* v_binderName_618_; lean_object* v___x_620_; 
lean_dec(v_fvarId_602_);
v_val_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_val_617_);
lean_dec_ref(v___x_616_);
v_binderName_618_ = lean_ctor_get(v_val_617_, 1);
lean_inc(v_binderName_618_);
lean_dec(v_val_617_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v_binderName_618_);
v___x_620_ = v___x_612_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_binderName_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec(v___x_616_);
lean_del_object(v___x_612_);
v___x_622_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_623_ = l_Lean_MessageData_ofName(v_fvarId_602_);
v___x_624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_624_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
return v___x_625_;
}
}
v___jp_627_:
{
lean_object* v___x_629_; 
v___x_629_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_628_, v_fvarId_602_);
lean_dec_ref(v___y_628_);
if (lean_obj_tag(v___x_629_) == 1)
{
lean_object* v_val_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_638_; 
lean_dec_ref(v_lctx_626_);
lean_del_object(v___x_612_);
lean_dec(v_a_610_);
lean_dec(v_fvarId_602_);
v_val_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_638_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_val_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v_binderName_634_; lean_object* v___x_636_; 
v_binderName_634_ = lean_ctor_get(v_val_630_, 1);
lean_inc(v_binderName_634_);
lean_dec(v_val_630_);
if (v_isShared_633_ == 0)
{
lean_ctor_set_tag(v___x_632_, 0);
lean_ctor_set(v___x_632_, 0, v_binderName_634_);
v___x_636_ = v___x_632_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_binderName_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
else
{
uint8_t v___x_639_; 
lean_dec(v___x_629_);
v___x_639_ = lean_unbox(v_a_610_);
lean_dec(v_a_610_);
if (v___x_639_ == 0)
{
lean_object* v_funDeclsPure_640_; 
v_funDeclsPure_640_ = lean_ctor_get(v_lctx_626_, 4);
lean_inc_ref(v_funDeclsPure_640_);
lean_dec_ref(v_lctx_626_);
v___y_615_ = v_funDeclsPure_640_;
goto v___jp_614_;
}
else
{
lean_object* v_funDeclsImpure_641_; 
v_funDeclsImpure_641_ = lean_ctor_get(v_lctx_626_, 5);
lean_inc_ref(v_funDeclsImpure_641_);
lean_dec_ref(v_lctx_626_);
v___y_615_ = v_funDeclsImpure_641_;
goto v___jp_614_;
}
}
}
v___jp_642_:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_643_, v_fvarId_602_);
lean_dec_ref(v___y_643_);
if (lean_obj_tag(v___x_644_) == 1)
{
lean_object* v_val_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_653_; 
lean_dec_ref(v_lctx_626_);
lean_del_object(v___x_612_);
lean_dec(v_a_610_);
lean_dec(v_fvarId_602_);
v_val_645_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_653_ == 0)
{
v___x_647_ = v___x_644_;
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_val_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v_binderName_649_; lean_object* v___x_651_; 
v_binderName_649_ = lean_ctor_get(v_val_645_, 1);
lean_inc(v_binderName_649_);
lean_dec(v_val_645_);
if (v_isShared_648_ == 0)
{
lean_ctor_set_tag(v___x_647_, 0);
lean_ctor_set(v___x_647_, 0, v_binderName_649_);
v___x_651_ = v___x_647_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_binderName_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
else
{
uint8_t v___x_654_; 
lean_dec(v___x_644_);
v___x_654_ = lean_unbox(v_a_610_);
if (v___x_654_ == 0)
{
lean_object* v_paramsPure_655_; 
v_paramsPure_655_ = lean_ctor_get(v_lctx_626_, 0);
lean_inc_ref(v_paramsPure_655_);
v___y_628_ = v_paramsPure_655_;
goto v___jp_627_;
}
else
{
lean_object* v_paramsImpure_656_; 
v_paramsImpure_656_ = lean_ctor_get(v_lctx_626_, 1);
lean_inc_ref(v_paramsImpure_656_);
v___y_628_ = v_paramsImpure_656_;
goto v___jp_627_;
}
}
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec(v___x_608_);
lean_dec(v_fvarId_602_);
v_a_661_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_609_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_609_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName___boxed(lean_object* v_fvarId_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t v_pu_676_, lean_object* v_fvarId_677_, lean_object* v_a_678_){
_start:
{
lean_object* v___x_680_; lean_object* v___y_682_; 
v___x_680_ = lean_st_ref_get(v_a_678_);
if (v_pu_676_ == 0)
{
lean_object* v_lctx_685_; lean_object* v_paramsPure_686_; 
v_lctx_685_ = lean_ctor_get(v___x_680_, 0);
lean_inc_ref(v_lctx_685_);
lean_dec(v___x_680_);
v_paramsPure_686_ = lean_ctor_get(v_lctx_685_, 0);
lean_inc_ref(v_paramsPure_686_);
lean_dec_ref(v_lctx_685_);
v___y_682_ = v_paramsPure_686_;
goto v___jp_681_;
}
else
{
lean_object* v_lctx_687_; lean_object* v_paramsImpure_688_; 
v_lctx_687_ = lean_ctor_get(v___x_680_, 0);
lean_inc_ref(v_lctx_687_);
lean_dec(v___x_680_);
v_paramsImpure_688_ = lean_ctor_get(v_lctx_687_, 1);
lean_inc_ref(v_paramsImpure_688_);
lean_dec_ref(v_lctx_687_);
v___y_682_ = v_paramsImpure_688_;
goto v___jp_681_;
}
v___jp_681_:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_682_, v_fvarId_677_);
lean_dec_ref(v___y_682_);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg___boxed(lean_object* v_pu_689_, lean_object* v_fvarId_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
uint8_t v_pu_boxed_693_; lean_object* v_res_694_; 
v_pu_boxed_693_ = lean_unbox(v_pu_689_);
v_res_694_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_boxed_693_, v_fvarId_690_, v_a_691_);
lean_dec(v_a_691_);
lean_dec(v_fvarId_690_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f(uint8_t v_pu_695_, lean_object* v_fvarId_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_695_, v_fvarId_696_, v_a_698_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___boxed(lean_object* v_pu_703_, lean_object* v_fvarId_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
uint8_t v_pu_boxed_710_; lean_object* v_res_711_; 
v_pu_boxed_710_ = lean_unbox(v_pu_703_);
v_res_711_ = l_Lean_Compiler_LCNF_findParam_x3f(v_pu_boxed_710_, v_fvarId_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_fvarId_704_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t v_pu_712_, lean_object* v_fvarId_713_, lean_object* v_a_714_){
_start:
{
lean_object* v___x_716_; lean_object* v___y_718_; 
v___x_716_ = lean_st_ref_get(v_a_714_);
if (v_pu_712_ == 0)
{
lean_object* v_lctx_721_; lean_object* v_letDeclsPure_722_; 
v_lctx_721_ = lean_ctor_get(v___x_716_, 0);
lean_inc_ref(v_lctx_721_);
lean_dec(v___x_716_);
v_letDeclsPure_722_ = lean_ctor_get(v_lctx_721_, 2);
lean_inc_ref(v_letDeclsPure_722_);
lean_dec_ref(v_lctx_721_);
v___y_718_ = v_letDeclsPure_722_;
goto v___jp_717_;
}
else
{
lean_object* v_lctx_723_; lean_object* v_letDeclsImpure_724_; 
v_lctx_723_ = lean_ctor_get(v___x_716_, 0);
lean_inc_ref(v_lctx_723_);
lean_dec(v___x_716_);
v_letDeclsImpure_724_ = lean_ctor_get(v_lctx_723_, 3);
lean_inc_ref(v_letDeclsImpure_724_);
lean_dec_ref(v_lctx_723_);
v___y_718_ = v_letDeclsImpure_724_;
goto v___jp_717_;
}
v___jp_717_:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_718_, v_fvarId_713_);
lean_dec_ref(v___y_718_);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg___boxed(lean_object* v_pu_725_, lean_object* v_fvarId_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
uint8_t v_pu_boxed_729_; lean_object* v_res_730_; 
v_pu_boxed_729_ = lean_unbox(v_pu_725_);
v_res_730_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_boxed_729_, v_fvarId_726_, v_a_727_);
lean_dec(v_a_727_);
lean_dec(v_fvarId_726_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(uint8_t v_pu_731_, lean_object* v_fvarId_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_731_, v_fvarId_732_, v_a_734_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___boxed(lean_object* v_pu_739_, lean_object* v_fvarId_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
uint8_t v_pu_boxed_746_; lean_object* v_res_747_; 
v_pu_boxed_746_ = lean_unbox(v_pu_739_);
v_res_747_ = l_Lean_Compiler_LCNF_findLetDecl_x3f(v_pu_boxed_746_, v_fvarId_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_fvarId_740_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t v_pu_748_, lean_object* v_fvarId_749_, lean_object* v_a_750_){
_start:
{
lean_object* v___x_752_; lean_object* v___y_754_; 
v___x_752_ = lean_st_ref_get(v_a_750_);
if (v_pu_748_ == 0)
{
lean_object* v_lctx_757_; lean_object* v_funDeclsPure_758_; 
v_lctx_757_ = lean_ctor_get(v___x_752_, 0);
lean_inc_ref(v_lctx_757_);
lean_dec(v___x_752_);
v_funDeclsPure_758_ = lean_ctor_get(v_lctx_757_, 4);
lean_inc_ref(v_funDeclsPure_758_);
lean_dec_ref(v_lctx_757_);
v___y_754_ = v_funDeclsPure_758_;
goto v___jp_753_;
}
else
{
lean_object* v_lctx_759_; lean_object* v_funDeclsImpure_760_; 
v_lctx_759_ = lean_ctor_get(v___x_752_, 0);
lean_inc_ref(v_lctx_759_);
lean_dec(v___x_752_);
v_funDeclsImpure_760_ = lean_ctor_get(v_lctx_759_, 5);
lean_inc_ref(v_funDeclsImpure_760_);
lean_dec_ref(v_lctx_759_);
v___y_754_ = v_funDeclsImpure_760_;
goto v___jp_753_;
}
v___jp_753_:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_754_, v_fvarId_749_);
lean_dec_ref(v___y_754_);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg___boxed(lean_object* v_pu_761_, lean_object* v_fvarId_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
uint8_t v_pu_boxed_765_; lean_object* v_res_766_; 
v_pu_boxed_765_ = lean_unbox(v_pu_761_);
v_res_766_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_boxed_765_, v_fvarId_762_, v_a_763_);
lean_dec(v_a_763_);
lean_dec(v_fvarId_762_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(uint8_t v_pu_767_, lean_object* v_fvarId_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_767_, v_fvarId_768_, v_a_770_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___boxed(lean_object* v_pu_775_, lean_object* v_fvarId_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
uint8_t v_pu_boxed_782_; lean_object* v_res_783_; 
v_pu_boxed_782_ = lean_unbox(v_pu_775_);
v_res_783_ = l_Lean_Compiler_LCNF_findFunDecl_x3f(v_pu_boxed_782_, v_fvarId_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_fvarId_776_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t v_pu_784_, lean_object* v_fvarId_785_, lean_object* v_a_786_){
_start:
{
lean_object* v___x_788_; lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_809_; 
v___x_788_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_784_, v_fvarId_785_, v_a_786_);
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_809_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_809_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_809_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
if (lean_obj_tag(v_a_789_) == 1)
{
lean_object* v_val_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_804_; 
v_val_793_ = lean_ctor_get(v_a_789_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v_a_789_);
if (v_isSharedCheck_804_ == 0)
{
v___x_795_ = v_a_789_;
v_isShared_796_ = v_isSharedCheck_804_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_val_793_);
lean_dec(v_a_789_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_804_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_value_797_; lean_object* v___x_799_; 
v_value_797_ = lean_ctor_get(v_val_793_, 3);
lean_inc(v_value_797_);
lean_dec(v_val_793_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v_value_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_value_797_);
v___x_799_ = v_reuseFailAlloc_803_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_801_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_799_);
v___x_801_ = v___x_791_;
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
lean_object* v___x_805_; lean_object* v___x_807_; 
lean_dec(v_a_789_);
v___x_805_ = lean_box(0);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_805_);
v___x_807_ = v___x_791_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg___boxed(lean_object* v_pu_810_, lean_object* v_fvarId_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
uint8_t v_pu_boxed_814_; lean_object* v_res_815_; 
v_pu_boxed_814_ = lean_unbox(v_pu_810_);
v_res_815_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_boxed_814_, v_fvarId_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec(v_fvarId_811_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f(uint8_t v_pu_816_, lean_object* v_fvarId_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_816_, v_fvarId_817_, v_a_819_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___boxed(lean_object* v_pu_824_, lean_object* v_fvarId_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
uint8_t v_pu_boxed_831_; lean_object* v_res_832_; 
v_pu_boxed_831_ = lean_unbox(v_pu_824_);
v_res_832_ = l_Lean_Compiler_LCNF_findLetValue_x3f(v_pu_boxed_831_, v_fvarId_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec(v_fvarId_825_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg(lean_object* v_fvarId_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
uint8_t v___x_837_; lean_object* v___x_838_; 
v___x_837_ = 0;
v___x_838_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_837_, v_fvarId_833_, v_a_834_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_882_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_882_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_882_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_882_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
if (lean_obj_tag(v_a_839_) == 1)
{
lean_object* v_val_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_881_; 
v_val_849_ = lean_ctor_get(v_a_839_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v_a_839_);
if (v_isSharedCheck_881_ == 0)
{
v___x_851_ = v_a_839_;
v_isShared_852_ = v_isSharedCheck_881_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_val_849_);
lean_dec(v_a_839_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_881_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
if (lean_obj_tag(v_val_849_) == 3)
{
lean_object* v_declName_853_; lean_object* v___x_854_; lean_object* v_env_855_; uint8_t v___x_856_; lean_object* v___x_857_; 
lean_del_object(v___x_841_);
v_declName_853_ = lean_ctor_get(v_val_849_, 0);
lean_inc(v_declName_853_);
lean_dec_ref(v_val_849_);
v___x_854_ = lean_st_ref_get(v_a_835_);
v_env_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc_ref(v_env_855_);
lean_dec(v___x_854_);
v___x_856_ = 0;
v___x_857_ = l_Lean_Environment_find_x3f(v_env_855_, v_declName_853_, v___x_856_);
if (lean_obj_tag(v___x_857_) == 1)
{
lean_object* v_val_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_876_; 
lean_del_object(v___x_851_);
v_val_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_876_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_876_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_val_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_876_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
if (lean_obj_tag(v_val_858_) == 6)
{
lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_870_; 
lean_del_object(v___x_860_);
v_isSharedCheck_870_ = !lean_is_exclusive(v_val_858_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; 
v_unused_871_ = lean_ctor_get(v_val_858_, 0);
lean_dec(v_unused_871_);
v___x_863_ = v_val_858_;
v_isShared_864_ = v_isSharedCheck_870_;
goto v_resetjp_862_;
}
else
{
lean_dec(v_val_858_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_870_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
uint8_t v___x_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
v___x_865_ = 1;
v___x_866_ = lean_box(v___x_865_);
if (v_isShared_864_ == 0)
{
lean_ctor_set_tag(v___x_863_, 0);
lean_ctor_set(v___x_863_, 0, v___x_866_);
v___x_868_ = v___x_863_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
else
{
lean_object* v___x_872_; lean_object* v___x_874_; 
lean_dec(v_val_858_);
v___x_872_ = lean_box(v___x_856_);
if (v_isShared_861_ == 0)
{
lean_ctor_set_tag(v___x_860_, 0);
lean_ctor_set(v___x_860_, 0, v___x_872_);
v___x_874_ = v___x_860_;
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
}
}
else
{
lean_object* v___x_877_; lean_object* v___x_879_; 
lean_dec(v___x_857_);
v___x_877_ = lean_box(v___x_856_);
if (v_isShared_852_ == 0)
{
lean_ctor_set_tag(v___x_851_, 0);
lean_ctor_set(v___x_851_, 0, v___x_877_);
v___x_879_ = v___x_851_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
else
{
lean_del_object(v___x_851_);
lean_dec(v_val_849_);
goto v___jp_843_;
}
}
}
else
{
lean_dec(v_a_839_);
goto v___jp_843_;
}
v___jp_843_:
{
uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_844_ = 0;
v___x_845_ = lean_box(v___x_844_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_845_);
v___x_847_ = v___x_841_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
v_a_883_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_838_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_838_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg___boxed(lean_object* v_fvarId_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_891_, v_a_892_, v_a_893_);
lean_dec(v_a_893_);
lean_dec(v_a_892_);
lean_dec(v_fvarId_891_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp(lean_object* v_fvarId_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_896_, v_a_898_, v_a_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___boxed(lean_object* v_fvarId_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_Compiler_LCNF_isConstructorApp(v_fvarId_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
lean_dec(v_fvarId_903_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(lean_object* v_arg_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
if (lean_obj_tag(v_arg_910_) == 1)
{
lean_object* v_fvarId_914_; lean_object* v___x_915_; 
v_fvarId_914_ = lean_ctor_get(v_arg_910_, 0);
v___x_915_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_914_, v_a_911_, v_a_912_);
return v___x_915_;
}
else
{
uint8_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = 0;
v___x_917_ = lean_box(v___x_916_);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg___boxed(lean_object* v_arg_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_919_, v_a_920_, v_a_921_);
lean_dec(v_a_921_);
lean_dec(v_a_920_);
lean_dec(v_arg_919_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp(uint8_t v_pu_924_, lean_object* v_arg_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_925_, v_a_927_, v_a_929_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___boxed(lean_object* v_pu_932_, lean_object* v_arg_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
uint8_t v_pu_boxed_939_; lean_object* v_res_940_; 
v_pu_boxed_939_ = lean_unbox(v_pu_932_);
v_res_940_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp(v_pu_boxed_939_, v_arg_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_arg_933_);
return v_res_940_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getParam___closed__1(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParam___closed__0));
v___x_943_ = l_Lean_stringToMessageData(v___x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam(uint8_t v_pu_944_, lean_object* v_fvarId_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___x_951_; lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_964_; 
v___x_951_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_944_, v_fvarId_945_, v_a_947_);
v_a_952_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_964_ == 0)
{
v___x_954_ = v___x_951_;
v_isShared_955_ = v_isSharedCheck_964_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_964_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
if (lean_obj_tag(v_a_952_) == 1)
{
lean_object* v_val_956_; lean_object* v___x_958_; 
lean_dec(v_fvarId_945_);
v_val_956_ = lean_ctor_get(v_a_952_, 0);
lean_inc(v_val_956_);
lean_dec_ref(v_a_952_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v_val_956_);
v___x_958_ = v___x_954_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_val_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
lean_del_object(v___x_954_);
lean_dec(v_a_952_);
v___x_960_ = lean_obj_once(&l_Lean_Compiler_LCNF_getParam___closed__1, &l_Lean_Compiler_LCNF_getParam___closed__1_once, _init_l_Lean_Compiler_LCNF_getParam___closed__1);
v___x_961_ = l_Lean_MessageData_ofName(v_fvarId_945_);
v___x_962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_962_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
return v___x_963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam___boxed(lean_object* v_pu_965_, lean_object* v_fvarId_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
uint8_t v_pu_boxed_972_; lean_object* v_res_973_; 
v_pu_boxed_972_ = lean_unbox(v_pu_965_);
v_res_973_ = l_Lean_Compiler_LCNF_getParam(v_pu_boxed_972_, v_fvarId_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
return v_res_973_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = ((lean_object*)(l_Lean_Compiler_LCNF_getLetDecl___closed__0));
v___x_976_ = l_Lean_stringToMessageData(v___x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl(uint8_t v_pu_977_, lean_object* v_fvarId_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v___x_984_; lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_997_; 
v___x_984_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_977_, v_fvarId_978_, v_a_980_);
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_997_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_997_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_997_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
if (lean_obj_tag(v_a_985_) == 1)
{
lean_object* v_val_989_; lean_object* v___x_991_; 
lean_dec(v_fvarId_978_);
v_val_989_ = lean_ctor_get(v_a_985_, 0);
lean_inc(v_val_989_);
lean_dec_ref(v_a_985_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v_val_989_);
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_val_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
lean_del_object(v___x_987_);
lean_dec(v_a_985_);
v___x_993_ = lean_obj_once(&l_Lean_Compiler_LCNF_getLetDecl___closed__1, &l_Lean_Compiler_LCNF_getLetDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1);
v___x_994_ = l_Lean_MessageData_ofName(v_fvarId_978_);
v___x_995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_995_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
return v___x_996_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl___boxed(lean_object* v_pu_998_, lean_object* v_fvarId_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
uint8_t v_pu_boxed_1005_; lean_object* v_res_1006_; 
v_pu_boxed_1005_ = lean_unbox(v_pu_998_);
v_res_1006_ = l_Lean_Compiler_LCNF_getLetDecl(v_pu_boxed_1005_, v_fvarId_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
return v_res_1006_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l_Lean_Compiler_LCNF_getFunDecl___closed__0));
v___x_1009_ = l_Lean_stringToMessageData(v___x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t v_pu_1010_, lean_object* v_fvarId_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v___x_1017_; lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1030_; 
v___x_1017_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_1010_, v_fvarId_1011_, v_a_1013_);
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1020_ = v___x_1017_;
v_isShared_1021_ = v_isSharedCheck_1030_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1017_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1030_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
if (lean_obj_tag(v_a_1018_) == 1)
{
lean_object* v_val_1022_; lean_object* v___x_1024_; 
lean_dec(v_fvarId_1011_);
v_val_1022_ = lean_ctor_get(v_a_1018_, 0);
lean_inc(v_val_1022_);
lean_dec_ref(v_a_1018_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v_val_1022_);
v___x_1024_ = v___x_1020_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_val_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_del_object(v___x_1020_);
lean_dec(v_a_1018_);
v___x_1026_ = lean_obj_once(&l_Lean_Compiler_LCNF_getFunDecl___closed__1, &l_Lean_Compiler_LCNF_getFunDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1);
v___x_1027_ = l_Lean_MessageData_ofName(v_fvarId_1011_);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_1028_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_);
return v___x_1029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl___boxed(lean_object* v_pu_1031_, lean_object* v_fvarId_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
uint8_t v_pu_boxed_1038_; lean_object* v_res_1039_; 
v_pu_boxed_1038_ = lean_unbox(v_pu_1031_);
v_res_1039_ = l_Lean_Compiler_LCNF_getFunDecl(v_pu_boxed_1038_, v_fvarId_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg(lean_object* v_f_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1043_; lean_object* v_lctx_1044_; lean_object* v_nextIdx_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1056_; 
v___x_1043_ = lean_st_ref_take(v_a_1041_);
v_lctx_1044_ = lean_ctor_get(v___x_1043_, 0);
v_nextIdx_1045_ = lean_ctor_get(v___x_1043_, 1);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1047_ = v___x_1043_;
v_isShared_1048_ = v_isSharedCheck_1056_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_nextIdx_1045_);
lean_inc(v_lctx_1044_);
lean_dec(v___x_1043_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1056_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1049_ = lean_apply_1(v_f_1040_, v_lctx_1044_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1049_);
v___x_1051_ = v___x_1047_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_nextIdx_1045_);
v___x_1051_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = lean_st_ref_set(v_a_1041_, v___x_1051_);
v___x_1053_ = lean_box(0);
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg___boxed(lean_object* v_f_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Compiler_LCNF_modifyLCtx___redArg(v_f_1057_, v_a_1058_);
lean_dec(v_a_1058_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx(lean_object* v_f_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v___x_1067_; lean_object* v_lctx_1068_; lean_object* v_nextIdx_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1080_; 
v___x_1067_ = lean_st_ref_take(v_a_1063_);
v_lctx_1068_ = lean_ctor_get(v___x_1067_, 0);
v_nextIdx_1069_ = lean_ctor_get(v___x_1067_, 1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1071_ = v___x_1067_;
v_isShared_1072_ = v_isSharedCheck_1080_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_nextIdx_1069_);
lean_inc(v_lctx_1068_);
lean_dec(v___x_1067_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1080_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1073_ = lean_apply_1(v_f_1061_, v_lctx_1068_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v___x_1073_);
v___x_1075_ = v___x_1071_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_nextIdx_1069_);
v___x_1075_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1076_ = lean_st_ref_set(v_a_1063_, v___x_1075_);
v___x_1077_ = lean_box(0);
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___boxed(lean_object* v_f_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_Compiler_LCNF_modifyLCtx(v_f_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t v_pu_1088_, lean_object* v_decl_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v___x_1092_; lean_object* v_lctx_1093_; lean_object* v_nextIdx_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1105_; 
v___x_1092_ = lean_st_ref_take(v_a_1090_);
v_lctx_1093_ = lean_ctor_get(v___x_1092_, 0);
v_nextIdx_1094_ = lean_ctor_get(v___x_1092_, 1);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1096_ = v___x_1092_;
v_isShared_1097_ = v_isSharedCheck_1105_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_nextIdx_1094_);
lean_inc(v_lctx_1093_);
lean_dec(v___x_1092_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1105_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1098_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_1088_, v_lctx_1093_, v_decl_1089_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v___x_1098_);
v___x_1100_ = v___x_1096_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_nextIdx_1094_);
v___x_1100_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = lean_st_ref_set(v_a_1090_, v___x_1100_);
v___x_1102_ = lean_box(0);
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
return v___x_1103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg___boxed(lean_object* v_pu_1106_, lean_object* v_decl_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
uint8_t v_pu_boxed_1110_; lean_object* v_res_1111_; 
v_pu_boxed_1110_ = lean_unbox(v_pu_1106_);
v_res_1111_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_boxed_1110_, v_decl_1107_, v_a_1108_);
lean_dec(v_a_1108_);
lean_dec_ref(v_decl_1107_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(uint8_t v_pu_1112_, lean_object* v_decl_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1112_, v_decl_1113_, v_a_1115_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___boxed(lean_object* v_pu_1120_, lean_object* v_decl_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
uint8_t v_pu_boxed_1127_; lean_object* v_res_1128_; 
v_pu_boxed_1127_ = lean_unbox(v_pu_1120_);
v_res_1128_ = l_Lean_Compiler_LCNF_eraseLetDecl(v_pu_boxed_1127_, v_decl_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec_ref(v_decl_1121_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t v_pu_1129_, lean_object* v_decl_1130_, uint8_t v_recursive_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v___x_1134_; lean_object* v_lctx_1135_; lean_object* v_nextIdx_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1147_; 
v___x_1134_ = lean_st_ref_take(v_a_1132_);
v_lctx_1135_ = lean_ctor_get(v___x_1134_, 0);
v_nextIdx_1136_ = lean_ctor_get(v___x_1134_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1138_ = v___x_1134_;
v_isShared_1139_ = v_isSharedCheck_1147_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_nextIdx_1136_);
lean_inc(v_lctx_1135_);
lean_dec(v___x_1134_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1147_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1140_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_1129_, v_lctx_1135_, v_decl_1130_, v_recursive_1131_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1140_);
v___x_1142_ = v___x_1138_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_nextIdx_1136_);
v___x_1142_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = lean_st_ref_set(v_a_1132_, v___x_1142_);
v___x_1144_ = lean_box(0);
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
return v___x_1145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg___boxed(lean_object* v_pu_1148_, lean_object* v_decl_1149_, lean_object* v_recursive_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
uint8_t v_pu_boxed_1153_; uint8_t v_recursive_boxed_1154_; lean_object* v_res_1155_; 
v_pu_boxed_1153_ = lean_unbox(v_pu_1148_);
v_recursive_boxed_1154_ = lean_unbox(v_recursive_1150_);
v_res_1155_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_boxed_1153_, v_decl_1149_, v_recursive_boxed_1154_, v_a_1151_);
lean_dec(v_a_1151_);
lean_dec_ref(v_decl_1149_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(uint8_t v_pu_1156_, lean_object* v_decl_1157_, uint8_t v_recursive_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1156_, v_decl_1157_, v_recursive_1158_, v_a_1160_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___boxed(lean_object* v_pu_1165_, lean_object* v_decl_1166_, lean_object* v_recursive_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
uint8_t v_pu_boxed_1173_; uint8_t v_recursive_boxed_1174_; lean_object* v_res_1175_; 
v_pu_boxed_1173_ = lean_unbox(v_pu_1165_);
v_recursive_boxed_1174_ = lean_unbox(v_recursive_1167_);
v_res_1175_ = l_Lean_Compiler_LCNF_eraseFunDecl(v_pu_boxed_1173_, v_decl_1166_, v_recursive_boxed_1174_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec_ref(v_decl_1166_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t v_pu_1176_, lean_object* v_code_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v___x_1180_; lean_object* v_lctx_1181_; lean_object* v_nextIdx_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1193_; 
v___x_1180_ = lean_st_ref_take(v_a_1178_);
v_lctx_1181_ = lean_ctor_get(v___x_1180_, 0);
v_nextIdx_1182_ = lean_ctor_get(v___x_1180_, 1);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1184_ = v___x_1180_;
v_isShared_1185_ = v_isSharedCheck_1193_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_nextIdx_1182_);
lean_inc(v_lctx_1181_);
lean_dec(v___x_1180_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1193_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1186_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_1176_, v_code_1177_, v_lctx_1181_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1186_);
v___x_1188_ = v___x_1184_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_nextIdx_1182_);
v___x_1188_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1189_ = lean_st_ref_set(v_a_1178_, v___x_1188_);
v___x_1190_ = lean_box(0);
v___x_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
return v___x_1191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg___boxed(lean_object* v_pu_1194_, lean_object* v_code_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
uint8_t v_pu_boxed_1198_; lean_object* v_res_1199_; 
v_pu_boxed_1198_ = lean_unbox(v_pu_1194_);
v_res_1199_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_boxed_1198_, v_code_1195_, v_a_1196_);
lean_dec(v_a_1196_);
lean_dec_ref(v_code_1195_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode(uint8_t v_pu_1200_, lean_object* v_code_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_1200_, v_code_1201_, v_a_1203_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___boxed(lean_object* v_pu_1208_, lean_object* v_code_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
uint8_t v_pu_boxed_1215_; lean_object* v_res_1216_; 
v_pu_boxed_1215_ = lean_unbox(v_pu_1208_);
v_res_1216_ = l_Lean_Compiler_LCNF_eraseCode(v_pu_boxed_1215_, v_code_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec_ref(v_code_1209_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t v_pu_1217_, lean_object* v_param_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v___x_1221_; lean_object* v_lctx_1222_; lean_object* v_nextIdx_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1234_; 
v___x_1221_ = lean_st_ref_take(v_a_1219_);
v_lctx_1222_ = lean_ctor_get(v___x_1221_, 0);
v_nextIdx_1223_ = lean_ctor_get(v___x_1221_, 1);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1225_ = v___x_1221_;
v_isShared_1226_ = v_isSharedCheck_1234_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_nextIdx_1223_);
lean_inc(v_lctx_1222_);
lean_dec(v___x_1221_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1234_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1227_ = l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_1217_, v_lctx_1222_, v_param_1218_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1227_);
v___x_1229_ = v___x_1225_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_nextIdx_1223_);
v___x_1229_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1230_ = lean_st_ref_set(v_a_1219_, v___x_1229_);
v___x_1231_ = lean_box(0);
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
return v___x_1232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg___boxed(lean_object* v_pu_1235_, lean_object* v_param_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_){
_start:
{
uint8_t v_pu_boxed_1239_; lean_object* v_res_1240_; 
v_pu_boxed_1239_ = lean_unbox(v_pu_1235_);
v_res_1240_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_boxed_1239_, v_param_1236_, v_a_1237_);
lean_dec(v_a_1237_);
lean_dec_ref(v_param_1236_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam(uint8_t v_pu_1241_, lean_object* v_param_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_1241_, v_param_1242_, v_a_1244_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___boxed(lean_object* v_pu_1249_, lean_object* v_param_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
uint8_t v_pu_boxed_1256_; lean_object* v_res_1257_; 
v_pu_boxed_1256_ = lean_unbox(v_pu_1249_);
v_res_1257_ = l_Lean_Compiler_LCNF_eraseParam(v_pu_boxed_1256_, v_param_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
lean_dec_ref(v_param_1250_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t v_pu_1258_, lean_object* v_params_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v___x_1262_; lean_object* v_lctx_1263_; lean_object* v_nextIdx_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1275_; 
v___x_1262_ = lean_st_ref_take(v_a_1260_);
v_lctx_1263_ = lean_ctor_get(v___x_1262_, 0);
v_nextIdx_1264_ = lean_ctor_get(v___x_1262_, 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1266_ = v___x_1262_;
v_isShared_1267_ = v_isSharedCheck_1275_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_nextIdx_1264_);
lean_inc(v_lctx_1263_);
lean_dec(v___x_1262_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1275_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1268_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_1258_, v_lctx_1263_, v_params_1259_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1268_);
v___x_1270_ = v___x_1266_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_nextIdx_1264_);
v___x_1270_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = lean_st_ref_set(v_a_1260_, v___x_1270_);
v___x_1272_ = lean_box(0);
v___x_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
return v___x_1273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg___boxed(lean_object* v_pu_1276_, lean_object* v_params_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
uint8_t v_pu_boxed_1280_; lean_object* v_res_1281_; 
v_pu_boxed_1280_ = lean_unbox(v_pu_1276_);
v_res_1281_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_boxed_1280_, v_params_1277_, v_a_1278_);
lean_dec(v_a_1278_);
lean_dec_ref(v_params_1277_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams(uint8_t v_pu_1282_, lean_object* v_params_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1282_, v_params_1283_, v_a_1285_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___boxed(lean_object* v_pu_1290_, lean_object* v_params_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
uint8_t v_pu_boxed_1297_; lean_object* v_res_1298_; 
v_pu_boxed_1297_ = lean_unbox(v_pu_1290_);
v_res_1298_ = l_Lean_Compiler_LCNF_eraseParams(v_pu_boxed_1297_, v_params_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec_ref(v_params_1291_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t v_pu_1299_, lean_object* v_decl_1300_, lean_object* v_a_1301_){
_start:
{
switch(lean_obj_tag(v_decl_1300_))
{
case 0:
{
lean_object* v_decl_1303_; lean_object* v___x_1304_; 
v_decl_1303_ = lean_ctor_get(v_decl_1300_, 0);
v___x_1304_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1299_, v_decl_1303_, v_a_1301_);
return v___x_1304_;
}
case 1:
{
lean_object* v_decl_1305_; uint8_t v___x_1306_; lean_object* v___x_1307_; 
v_decl_1305_ = lean_ctor_get(v_decl_1300_, 0);
v___x_1306_ = 1;
v___x_1307_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1299_, v_decl_1305_, v___x_1306_, v_a_1301_);
return v___x_1307_;
}
case 2:
{
lean_object* v_decl_1308_; uint8_t v___x_1309_; lean_object* v___x_1310_; 
v_decl_1308_ = lean_ctor_get(v_decl_1300_, 0);
v___x_1309_ = 1;
v___x_1310_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1299_, v_decl_1308_, v___x_1309_, v_a_1301_);
return v___x_1310_;
}
default: 
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_box(0);
v___x_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
return v___x_1312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg___boxed(lean_object* v_pu_1313_, lean_object* v_decl_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
uint8_t v_pu_boxed_1317_; lean_object* v_res_1318_; 
v_pu_boxed_1317_ = lean_unbox(v_pu_1313_);
v_res_1318_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_boxed_1317_, v_decl_1314_, v_a_1315_);
lean_dec(v_a_1315_);
lean_dec_ref(v_decl_1314_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl(uint8_t v_pu_1319_, lean_object* v_decl_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1319_, v_decl_1320_, v_a_1322_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___boxed(lean_object* v_pu_1327_, lean_object* v_decl_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
uint8_t v_pu_boxed_1334_; lean_object* v_res_1335_; 
v_pu_boxed_1334_ = lean_unbox(v_pu_1327_);
v_res_1335_ = l_Lean_Compiler_LCNF_eraseCodeDecl(v_pu_boxed_1334_, v_decl_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
lean_dec(v_a_1332_);
lean_dec_ref(v_a_1331_);
lean_dec(v_a_1330_);
lean_dec_ref(v_a_1329_);
lean_dec_ref(v_decl_1328_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(uint8_t v_pu_1336_, lean_object* v_as_1337_, size_t v_i_1338_, size_t v_stop_1339_, lean_object* v_b_1340_, lean_object* v___y_1341_){
_start:
{
uint8_t v___x_1343_; 
v___x_1343_ = lean_usize_dec_eq(v_i_1338_, v_stop_1339_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = lean_array_uget_borrowed(v_as_1337_, v_i_1338_);
v___x_1345_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1336_, v___x_1344_, v___y_1341_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; size_t v___x_1347_; size_t v___x_1348_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref(v___x_1345_);
v___x_1347_ = ((size_t)1ULL);
v___x_1348_ = lean_usize_add(v_i_1338_, v___x_1347_);
v_i_1338_ = v___x_1348_;
v_b_1340_ = v_a_1346_;
goto _start;
}
else
{
return v___x_1345_;
}
}
else
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v_b_1340_);
return v___x_1350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg___boxed(lean_object* v_pu_1351_, lean_object* v_as_1352_, lean_object* v_i_1353_, lean_object* v_stop_1354_, lean_object* v_b_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
uint8_t v_pu_boxed_1358_; size_t v_i_boxed_1359_; size_t v_stop_boxed_1360_; lean_object* v_res_1361_; 
v_pu_boxed_1358_ = lean_unbox(v_pu_1351_);
v_i_boxed_1359_ = lean_unbox_usize(v_i_1353_);
lean_dec(v_i_1353_);
v_stop_boxed_1360_ = lean_unbox_usize(v_stop_1354_);
lean_dec(v_stop_1354_);
v_res_1361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_boxed_1358_, v_as_1352_, v_i_boxed_1359_, v_stop_boxed_1360_, v_b_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v_as_1352_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls(uint8_t v_pu_1362_, lean_object* v_decls_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1369_ = lean_unsigned_to_nat(0u);
v___x_1370_ = lean_array_get_size(v_decls_1363_);
v___x_1371_ = lean_box(0);
v___x_1372_ = lean_nat_dec_lt(v___x_1369_, v___x_1370_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1371_);
return v___x_1373_;
}
else
{
uint8_t v___x_1374_; 
v___x_1374_ = lean_nat_dec_le(v___x_1370_, v___x_1370_);
if (v___x_1374_ == 0)
{
if (v___x_1372_ == 0)
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1371_);
return v___x_1375_;
}
else
{
size_t v___x_1376_; size_t v___x_1377_; lean_object* v___x_1378_; 
v___x_1376_ = ((size_t)0ULL);
v___x_1377_ = lean_usize_of_nat(v___x_1370_);
v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1362_, v_decls_1363_, v___x_1376_, v___x_1377_, v___x_1371_, v_a_1365_);
return v___x_1378_;
}
}
else
{
size_t v___x_1379_; size_t v___x_1380_; lean_object* v___x_1381_; 
v___x_1379_ = ((size_t)0ULL);
v___x_1380_ = lean_usize_of_nat(v___x_1370_);
v___x_1381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1362_, v_decls_1363_, v___x_1379_, v___x_1380_, v___x_1371_, v_a_1365_);
return v___x_1381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls___boxed(lean_object* v_pu_1382_, lean_object* v_decls_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
uint8_t v_pu_boxed_1389_; lean_object* v_res_1390_; 
v_pu_boxed_1389_ = lean_unbox(v_pu_1382_);
v_res_1390_ = l_Lean_Compiler_LCNF_eraseCodeDecls(v_pu_boxed_1389_, v_decls_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec_ref(v_decls_1383_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(uint8_t v_pu_1391_, lean_object* v_as_1392_, size_t v_i_1393_, size_t v_stop_1394_, lean_object* v_b_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1391_, v_as_1392_, v_i_1393_, v_stop_1394_, v_b_1395_, v___y_1397_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___boxed(lean_object* v_pu_1402_, lean_object* v_as_1403_, lean_object* v_i_1404_, lean_object* v_stop_1405_, lean_object* v_b_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
uint8_t v_pu_boxed_1412_; size_t v_i_boxed_1413_; size_t v_stop_boxed_1414_; lean_object* v_res_1415_; 
v_pu_boxed_1412_ = lean_unbox(v_pu_1402_);
v_i_boxed_1413_ = lean_unbox_usize(v_i_1404_);
lean_dec(v_i_1404_);
v_stop_boxed_1414_ = lean_unbox_usize(v_stop_1405_);
lean_dec(v_stop_1405_);
v_res_1415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(v_pu_boxed_1412_, v_as_1403_, v_i_boxed_1413_, v_stop_boxed_1414_, v_b_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec_ref(v_as_1403_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(lean_object* v_f_1416_, lean_object* v_v_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
if (lean_obj_tag(v_v_1417_) == 0)
{
lean_object* v_code_1423_; lean_object* v___x_1424_; 
v_code_1423_ = lean_ctor_get(v_v_1417_, 0);
lean_inc_ref(v_code_1423_);
lean_dec_ref(v_v_1417_);
v___x_1424_ = lean_apply_6(v_f_1416_, v_code_1423_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, lean_box(0));
return v___x_1424_;
}
else
{
lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1432_; 
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec_ref(v_f_1416_);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_v_1417_);
if (v_isSharedCheck_1432_ == 0)
{
lean_object* v_unused_1433_; 
v_unused_1433_ = lean_ctor_get(v_v_1417_, 0);
lean_dec(v_unused_1433_);
v___x_1426_ = v_v_1417_;
v_isShared_1427_ = v_isSharedCheck_1432_;
goto v_resetjp_1425_;
}
else
{
lean_dec(v_v_1417_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1432_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1428_ = lean_box(0);
if (v_isShared_1427_ == 0)
{
lean_ctor_set_tag(v___x_1426_, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1428_);
v___x_1430_ = v___x_1426_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg___boxed(lean_object* v_f_1434_, lean_object* v_v_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1434_, v_v_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(uint8_t v_pu_1442_, lean_object* v_f_1443_, lean_object* v_v_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1443_, v_v_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___boxed(lean_object* v_pu_1451_, lean_object* v_f_1452_, lean_object* v_v_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
uint8_t v_pu_boxed_1459_; lean_object* v_res_1460_; 
v_pu_boxed_1459_ = lean_unbox(v_pu_1451_);
v_res_1460_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(v_pu_boxed_1459_, v_f_1452_, v_v_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t v_pu_1461_, lean_object* v_decl_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v_toSignature_1468_; lean_object* v_value_1469_; lean_object* v_params_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v_toSignature_1468_ = lean_ctor_get(v_decl_1462_, 0);
lean_inc_ref(v_toSignature_1468_);
v_value_1469_ = lean_ctor_get(v_decl_1462_, 1);
lean_inc_ref(v_value_1469_);
lean_dec_ref(v_decl_1462_);
v_params_1470_ = lean_ctor_get(v_toSignature_1468_, 3);
lean_inc_ref(v_params_1470_);
lean_dec_ref(v_toSignature_1468_);
v___x_1471_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1461_, v_params_1470_, v_a_1464_);
lean_dec_ref(v_params_1470_);
lean_dec_ref(v___x_1471_);
v___x_1472_ = lean_box(v_pu_1461_);
v___x_1473_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_eraseCode___boxed), 7, 1);
lean_closure_set(v___x_1473_, 0, v___x_1472_);
v___x_1474_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v___x_1473_, v_value_1469_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl___boxed(lean_object* v_pu_1475_, lean_object* v_decl_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
uint8_t v_pu_boxed_1482_; lean_object* v_res_1483_; 
v_pu_boxed_1482_ = lean_unbox(v_pu_1475_);
v_res_1483_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_boxed_1482_, v_decl_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase(uint8_t v_pu_1484_, lean_object* v_decl_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_1484_, v_decl_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase___boxed(lean_object* v_pu_1492_, lean_object* v_decl_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
uint8_t v_pu_boxed_1499_; lean_object* v_res_1500_; 
v_pu_boxed_1499_ = lean_unbox(v_pu_1492_);
v_res_1500_ = l_Lean_Compiler_LCNF_Decl_erase(v_pu_boxed_1499_, v_decl_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(lean_object* v_msg_1501_){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = l_Lean_instInhabitedExpr;
v___x_1503_ = lean_panic_fn(v___x_1502_, v_msg_1501_);
return v___x_1503_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1507_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2));
v___x_1508_ = lean_unsigned_to_nat(20u);
v___x_1509_ = lean_unsigned_to_nat(215u);
v___x_1510_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1));
v___x_1511_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0));
v___x_1512_ = l_mkPanicMessageWithDecl(v___x_1511_, v___x_1510_, v___x_1509_, v___x_1508_, v___x_1507_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t v_pu_1513_, lean_object* v_s_1514_, uint8_t v_translator_1515_, lean_object* v_e_1516_){
_start:
{
uint8_t v___x_1517_; 
v___x_1517_ = l_Lean_Expr_hasFVar(v_e_1516_);
if (v___x_1517_ == 0)
{
return v_e_1516_;
}
else
{
switch(lean_obj_tag(v_e_1516_))
{
case 1:
{
lean_object* v_fvarId_1518_; lean_object* v___x_1519_; 
v_fvarId_1518_ = lean_ctor_get(v_e_1516_, 0);
v___x_1519_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1514_, v_fvarId_1518_);
if (lean_obj_tag(v___x_1519_) == 0)
{
return v_e_1516_;
}
else
{
lean_object* v_val_1520_; 
lean_dec_ref(v_e_1516_);
v_val_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_val_1520_);
lean_dec_ref(v___x_1519_);
switch(lean_obj_tag(v_val_1520_))
{
case 0:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_Compiler_LCNF_erasedExpr;
return v___x_1521_;
}
case 1:
{
if (v_translator_1515_ == 0)
{
lean_object* v_fvarId_1522_; lean_object* v___x_1523_; 
v_fvarId_1522_ = lean_ctor_get(v_val_1520_, 0);
lean_inc(v_fvarId_1522_);
lean_dec_ref(v_val_1520_);
v___x_1523_ = l_Lean_Expr_fvar___override(v_fvarId_1522_);
v_e_1516_ = v___x_1523_;
goto _start;
}
else
{
lean_object* v_fvarId_1525_; lean_object* v___x_1526_; 
v_fvarId_1525_ = lean_ctor_get(v_val_1520_, 0);
lean_inc(v_fvarId_1525_);
lean_dec_ref(v_val_1520_);
v___x_1526_ = l_Lean_Expr_fvar___override(v_fvarId_1525_);
return v___x_1526_;
}
}
default: 
{
if (v_translator_1515_ == 0)
{
lean_object* v_expr_1527_; 
v_expr_1527_ = lean_ctor_get(v_val_1520_, 0);
lean_inc_ref(v_expr_1527_);
lean_dec_ref(v_val_1520_);
v_e_1516_ = v_expr_1527_;
goto _start;
}
else
{
lean_object* v_expr_1529_; 
v_expr_1529_ = lean_ctor_get(v_val_1520_, 0);
lean_inc_ref(v_expr_1529_);
lean_dec_ref(v_val_1520_);
return v_expr_1529_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_1530_; lean_object* v_arg_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___y_1535_; size_t v___x_1539_; size_t v___x_1540_; uint8_t v___x_1541_; 
v_fn_1530_ = lean_ctor_get(v_e_1516_, 0);
v_arg_1531_ = lean_ctor_get(v_e_1516_, 1);
lean_inc_ref(v_fn_1530_);
v___x_1532_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1513_, v_s_1514_, v_translator_1515_, v_fn_1530_);
lean_inc_ref(v_arg_1531_);
v___x_1533_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1513_, v_s_1514_, v_translator_1515_, v_arg_1531_);
v___x_1539_ = lean_ptr_addr(v_fn_1530_);
v___x_1540_ = lean_ptr_addr(v___x_1532_);
v___x_1541_ = lean_usize_dec_eq(v___x_1539_, v___x_1540_);
if (v___x_1541_ == 0)
{
v___y_1535_ = v___x_1541_;
goto v___jp_1534_;
}
else
{
size_t v___x_1542_; size_t v___x_1543_; uint8_t v___x_1544_; 
v___x_1542_ = lean_ptr_addr(v_arg_1531_);
v___x_1543_ = lean_ptr_addr(v___x_1533_);
v___x_1544_ = lean_usize_dec_eq(v___x_1542_, v___x_1543_);
v___y_1535_ = v___x_1544_;
goto v___jp_1534_;
}
v___jp_1534_:
{
if (v___y_1535_ == 0)
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec_ref(v_e_1516_);
v___x_1536_ = l_Lean_Expr_app___override(v___x_1532_, v___x_1533_);
v___x_1537_ = l_Lean_Expr_headBeta(v___x_1536_);
return v___x_1537_;
}
else
{
lean_object* v___x_1538_; 
lean_dec_ref(v___x_1533_);
lean_dec_ref(v___x_1532_);
v___x_1538_ = l_Lean_Expr_headBeta(v_e_1516_);
return v___x_1538_;
}
}
}
case 6:
{
lean_object* v_binderName_1545_; lean_object* v_binderType_1546_; lean_object* v_body_1547_; uint8_t v_binderInfo_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___y_1552_; size_t v___x_1556_; size_t v___x_1557_; uint8_t v___x_1558_; 
v_binderName_1545_ = lean_ctor_get(v_e_1516_, 0);
v_binderType_1546_ = lean_ctor_get(v_e_1516_, 1);
v_body_1547_ = lean_ctor_get(v_e_1516_, 2);
v_binderInfo_1548_ = lean_ctor_get_uint8(v_e_1516_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1546_);
v___x_1549_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1513_, v_s_1514_, v_translator_1515_, v_binderType_1546_);
lean_inc_ref(v_body_1547_);
v___x_1550_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1513_, v_s_1514_, v_translator_1515_, v_body_1547_);
v___x_1556_ = lean_ptr_addr(v_binderType_1546_);
v___x_1557_ = lean_ptr_addr(v___x_1549_);
v___x_1558_ = lean_usize_dec_eq(v___x_1556_, v___x_1557_);
if (v___x_1558_ == 0)
{
v___y_1552_ = v___x_1558_;
goto v___jp_1551_;
}
else
{
size_t v___x_1559_; size_t v___x_1560_; uint8_t v___x_1561_; 
v___x_1559_ = lean_ptr_addr(v_body_1547_);
v___x_1560_ = lean_ptr_addr(v___x_1550_);
v___x_1561_ = lean_usize_dec_eq(v___x_1559_, v___x_1560_);
v___y_1552_ = v___x_1561_;
goto v___jp_1551_;
}
v___jp_1551_:
{
if (v___y_1552_ == 0)
{
lean_object* v___x_1553_; 
lean_inc(v_binderName_1545_);
lean_dec_ref(v_e_1516_);
v___x_1553_ = l_Lean_Expr_lam___override(v_binderName_1545_, v___x_1549_, v___x_1550_, v_binderInfo_1548_);
return v___x_1553_;
}
else
{
uint8_t v___x_1554_; 
v___x_1554_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1548_, v_binderInfo_1548_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; 
lean_inc(v_binderName_1545_);
lean_dec_ref(v_e_1516_);
v___x_1555_ = l_Lean_Expr_lam___override(v_binderName_1545_, v___x_1549_, v___x_1550_, v_binderInfo_1548_);
return v___x_1555_;
}
else
{
lean_dec_ref(v___x_1550_);
lean_dec_ref(v___x_1549_);
return v_e_1516_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1562_; lean_object* v_binderType_1563_; lean_object* v_body_1564_; uint8_t v_binderInfo_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; uint8_t v___y_1569_; size_t v___x_1573_; size_t v___x_1574_; uint8_t v___x_1575_; 
v_binderName_1562_ = lean_ctor_get(v_e_1516_, 0);
v_binderType_1563_ = lean_ctor_get(v_e_1516_, 1);
v_body_1564_ = lean_ctor_get(v_e_1516_, 2);
v_binderInfo_1565_ = lean_ctor_get_uint8(v_e_1516_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1563_);
v___x_1566_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1513_, v_s_1514_, v_translator_1515_, v_binderType_1563_);
lean_inc_ref(v_body_1564_);
v___x_1567_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1513_, v_s_1514_, v_translator_1515_, v_body_1564_);
v___x_1573_ = lean_ptr_addr(v_binderType_1563_);
v___x_1574_ = lean_ptr_addr(v___x_1566_);
v___x_1575_ = lean_usize_dec_eq(v___x_1573_, v___x_1574_);
if (v___x_1575_ == 0)
{
v___y_1569_ = v___x_1575_;
goto v___jp_1568_;
}
else
{
size_t v___x_1576_; size_t v___x_1577_; uint8_t v___x_1578_; 
v___x_1576_ = lean_ptr_addr(v_body_1564_);
v___x_1577_ = lean_ptr_addr(v___x_1567_);
v___x_1578_ = lean_usize_dec_eq(v___x_1576_, v___x_1577_);
v___y_1569_ = v___x_1578_;
goto v___jp_1568_;
}
v___jp_1568_:
{
if (v___y_1569_ == 0)
{
lean_object* v___x_1570_; 
lean_inc(v_binderName_1562_);
lean_dec_ref(v_e_1516_);
v___x_1570_ = l_Lean_Expr_forallE___override(v_binderName_1562_, v___x_1566_, v___x_1567_, v_binderInfo_1565_);
return v___x_1570_;
}
else
{
uint8_t v___x_1571_; 
v___x_1571_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1565_, v_binderInfo_1565_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; 
lean_inc(v_binderName_1562_);
lean_dec_ref(v_e_1516_);
v___x_1572_ = l_Lean_Expr_forallE___override(v_binderName_1562_, v___x_1566_, v___x_1567_, v_binderInfo_1565_);
return v___x_1572_;
}
else
{
lean_dec_ref(v___x_1567_);
lean_dec_ref(v___x_1566_);
return v_e_1516_;
}
}
}
}
case 8:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_dec_ref(v_e_1516_);
v___x_1579_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3, &l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3);
v___x_1580_ = l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(v___x_1579_);
return v___x_1580_;
}
case 10:
{
lean_object* v_data_1581_; lean_object* v_expr_1582_; lean_object* v___x_1583_; size_t v___x_1584_; size_t v___x_1585_; uint8_t v___x_1586_; 
v_data_1581_ = lean_ctor_get(v_e_1516_, 0);
v_expr_1582_ = lean_ctor_get(v_e_1516_, 1);
lean_inc_ref(v_expr_1582_);
v___x_1583_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1513_, v_s_1514_, v_translator_1515_, v_expr_1582_);
v___x_1584_ = lean_ptr_addr(v_expr_1582_);
v___x_1585_ = lean_ptr_addr(v___x_1583_);
v___x_1586_ = lean_usize_dec_eq(v___x_1584_, v___x_1585_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; 
lean_inc(v_data_1581_);
lean_dec_ref(v_e_1516_);
v___x_1587_ = l_Lean_Expr_mdata___override(v_data_1581_, v___x_1583_);
return v___x_1587_;
}
else
{
lean_dec_ref(v___x_1583_);
return v_e_1516_;
}
}
case 11:
{
lean_object* v_typeName_1588_; lean_object* v_idx_1589_; lean_object* v_struct_1590_; lean_object* v___x_1591_; size_t v___x_1592_; size_t v___x_1593_; uint8_t v___x_1594_; 
v_typeName_1588_ = lean_ctor_get(v_e_1516_, 0);
v_idx_1589_ = lean_ctor_get(v_e_1516_, 1);
v_struct_1590_ = lean_ctor_get(v_e_1516_, 2);
lean_inc_ref(v_struct_1590_);
v___x_1591_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1513_, v_s_1514_, v_translator_1515_, v_struct_1590_);
v___x_1592_ = lean_ptr_addr(v_struct_1590_);
v___x_1593_ = lean_ptr_addr(v___x_1591_);
v___x_1594_ = lean_usize_dec_eq(v___x_1592_, v___x_1593_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; 
lean_inc(v_idx_1589_);
lean_inc(v_typeName_1588_);
lean_dec_ref(v_e_1516_);
v___x_1595_ = l_Lean_Expr_proj___override(v_typeName_1588_, v_idx_1589_, v___x_1591_);
return v___x_1595_;
}
else
{
lean_dec_ref(v___x_1591_);
return v_e_1516_;
}
}
default: 
{
return v_e_1516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(uint8_t v_pu_1596_, lean_object* v_s_1597_, uint8_t v_translator_1598_, lean_object* v_e_1599_){
_start:
{
if (lean_obj_tag(v_e_1599_) == 5)
{
lean_object* v_fn_1600_; lean_object* v_arg_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; uint8_t v___y_1605_; size_t v___x_1607_; size_t v___x_1608_; uint8_t v___x_1609_; 
v_fn_1600_ = lean_ctor_get(v_e_1599_, 0);
v_arg_1601_ = lean_ctor_get(v_e_1599_, 1);
lean_inc_ref(v_fn_1600_);
v___x_1602_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1596_, v_s_1597_, v_translator_1598_, v_fn_1600_);
lean_inc_ref(v_arg_1601_);
v___x_1603_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1596_, v_s_1597_, v_translator_1598_, v_arg_1601_);
v___x_1607_ = lean_ptr_addr(v_fn_1600_);
v___x_1608_ = lean_ptr_addr(v___x_1602_);
v___x_1609_ = lean_usize_dec_eq(v___x_1607_, v___x_1608_);
if (v___x_1609_ == 0)
{
v___y_1605_ = v___x_1609_;
goto v___jp_1604_;
}
else
{
size_t v___x_1610_; size_t v___x_1611_; uint8_t v___x_1612_; 
v___x_1610_ = lean_ptr_addr(v_arg_1601_);
v___x_1611_ = lean_ptr_addr(v___x_1603_);
v___x_1612_ = lean_usize_dec_eq(v___x_1610_, v___x_1611_);
v___y_1605_ = v___x_1612_;
goto v___jp_1604_;
}
v___jp_1604_:
{
if (v___y_1605_ == 0)
{
lean_object* v___x_1606_; 
lean_dec_ref(v_e_1599_);
v___x_1606_ = l_Lean_Expr_app___override(v___x_1602_, v___x_1603_);
return v___x_1606_;
}
else
{
lean_dec_ref(v___x_1603_);
lean_dec_ref(v___x_1602_);
return v_e_1599_;
}
}
}
else
{
lean_object* v___x_1613_; 
v___x_1613_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1596_, v_s_1597_, v_translator_1598_, v_e_1599_);
return v___x_1613_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(lean_object* v_pu_1614_, lean_object* v_s_1615_, lean_object* v_translator_1616_, lean_object* v_e_1617_){
_start:
{
uint8_t v_pu_boxed_1618_; uint8_t v_translator_boxed_1619_; lean_object* v_res_1620_; 
v_pu_boxed_1618_ = lean_unbox(v_pu_1614_);
v_translator_boxed_1619_ = lean_unbox(v_translator_1616_);
v_res_1620_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_boxed_1618_, v_s_1615_, v_translator_boxed_1619_, v_e_1617_);
lean_dec_ref(v_s_1615_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(lean_object* v_pu_1621_, lean_object* v_s_1622_, lean_object* v_translator_1623_, lean_object* v_e_1624_){
_start:
{
uint8_t v_pu_boxed_1625_; uint8_t v_translator_boxed_1626_; lean_object* v_res_1627_; 
v_pu_boxed_1625_ = lean_unbox(v_pu_1621_);
v_translator_boxed_1626_ = lean_unbox(v_translator_1623_);
v_res_1627_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_boxed_1625_, v_s_1622_, v_translator_boxed_1626_, v_e_1624_);
lean_dec_ref(v_s_1622_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(uint8_t v_pu_1628_, lean_object* v_s_1629_, lean_object* v_e_1630_, uint8_t v_translator_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1628_, v_s_1629_, v_translator_1631_, v_e_1630_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(lean_object* v_pu_1633_, lean_object* v_s_1634_, lean_object* v_e_1635_, lean_object* v_translator_1636_){
_start:
{
uint8_t v_pu_boxed_1637_; uint8_t v_translator_boxed_1638_; lean_object* v_res_1639_; 
v_pu_boxed_1637_ = lean_unbox(v_pu_1633_);
v_translator_boxed_1638_ = lean_unbox(v_translator_1636_);
v_res_1639_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(v_pu_boxed_1637_, v_s_1634_, v_e_1635_, v_translator_boxed_1638_);
lean_dec_ref(v_s_1634_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(lean_object* v_x_1640_){
_start:
{
if (lean_obj_tag(v_x_1640_) == 0)
{
lean_object* v___x_1641_; 
v___x_1641_ = lean_unsigned_to_nat(0u);
return v___x_1641_;
}
else
{
lean_object* v___x_1642_; 
v___x_1642_ = lean_unsigned_to_nat(1u);
return v___x_1642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___boxed(lean_object* v_x_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(v_x_1643_);
lean_dec(v_x_1643_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(lean_object* v_t_1645_, lean_object* v_k_1646_){
_start:
{
if (lean_obj_tag(v_t_1645_) == 0)
{
lean_object* v_fvarId_1647_; lean_object* v___x_1648_; 
v_fvarId_1647_ = lean_ctor_get(v_t_1645_, 0);
lean_inc(v_fvarId_1647_);
lean_dec_ref(v_t_1645_);
v___x_1648_ = lean_apply_1(v_k_1646_, v_fvarId_1647_);
return v___x_1648_;
}
else
{
return v_k_1646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(lean_object* v_motive_1649_, lean_object* v_ctorIdx_1650_, lean_object* v_t_1651_, lean_object* v_h_1652_, lean_object* v_k_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1651_, v_k_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___boxed(lean_object* v_motive_1655_, lean_object* v_ctorIdx_1656_, lean_object* v_t_1657_, lean_object* v_h_1658_, lean_object* v_k_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(v_motive_1655_, v_ctorIdx_1656_, v_t_1657_, v_h_1658_, v_k_1659_);
lean_dec(v_ctorIdx_1656_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim___redArg(lean_object* v_t_1661_, lean_object* v_fvar_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1661_, v_fvar_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim(lean_object* v_motive_1664_, lean_object* v_t_1665_, lean_object* v_h_1666_, lean_object* v_fvar_1667_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1665_, v_fvar_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim___redArg(lean_object* v_t_1669_, lean_object* v_erased_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1669_, v_erased_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim(lean_object* v_motive_1672_, lean_object* v_t_1673_, lean_object* v_h_1674_, lean_object* v_erased_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1673_, v_erased_1675_);
return v___x_1676_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = l_Lean_instInhabitedFVarId_default;
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
return v___x_1678_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default(void){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0);
return v___x_1679_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedNormFVarResult(void){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default;
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object* v_s_1681_, lean_object* v_fvarId_1682_, uint8_t v_translator_1683_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1681_, v_fvarId_1682_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1685_, 0, v_fvarId_1682_);
return v___x_1685_;
}
else
{
lean_object* v_val_1686_; 
lean_dec(v_fvarId_1682_);
v_val_1686_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_val_1686_);
lean_dec_ref(v___x_1684_);
if (lean_obj_tag(v_val_1686_) == 1)
{
if (v_translator_1683_ == 0)
{
lean_object* v_fvarId_1687_; 
v_fvarId_1687_ = lean_ctor_get(v_val_1686_, 0);
lean_inc(v_fvarId_1687_);
lean_dec_ref(v_val_1686_);
v_fvarId_1682_ = v_fvarId_1687_;
goto _start;
}
else
{
lean_object* v_fvarId_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
v_fvarId_1689_ = lean_ctor_get(v_val_1686_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_val_1686_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v_val_1686_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_fvarId_1689_);
lean_dec(v_val_1686_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
lean_ctor_set_tag(v___x_1691_, 0);
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_fvarId_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
else
{
lean_object* v___x_1697_; 
lean_dec(v_val_1686_);
v___x_1697_ = lean_box(1);
return v___x_1697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg___boxed(lean_object* v_s_1698_, lean_object* v_fvarId_1699_, lean_object* v_translator_1700_){
_start:
{
uint8_t v_translator_boxed_1701_; lean_object* v_res_1702_; 
v_translator_boxed_1701_ = lean_unbox(v_translator_1700_);
v_res_1702_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1698_, v_fvarId_1699_, v_translator_boxed_1701_);
lean_dec_ref(v_s_1698_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp(uint8_t v_pu_1703_, lean_object* v_s_1704_, lean_object* v_fvarId_1705_, uint8_t v_translator_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1704_, v_fvarId_1705_, v_translator_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___boxed(lean_object* v_pu_1708_, lean_object* v_s_1709_, lean_object* v_fvarId_1710_, lean_object* v_translator_1711_){
_start:
{
uint8_t v_pu_boxed_1712_; uint8_t v_translator_boxed_1713_; lean_object* v_res_1714_; 
v_pu_boxed_1712_ = lean_unbox(v_pu_1708_);
v_translator_boxed_1713_ = lean_unbox(v_translator_1711_);
v_res_1714_ = l_Lean_Compiler_LCNF_normFVarImp(v_pu_boxed_1712_, v_s_1709_, v_fvarId_1710_, v_translator_boxed_1713_);
lean_dec_ref(v_s_1709_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t v_pu_1715_, lean_object* v_s_1716_, lean_object* v_arg_1717_, uint8_t v_translator_1718_){
_start:
{
switch(lean_obj_tag(v_arg_1717_))
{
case 0:
{
return v_arg_1717_;
}
case 1:
{
lean_object* v_fvarId_1719_; lean_object* v___x_1720_; 
v_fvarId_1719_ = lean_ctor_get(v_arg_1717_, 0);
v___x_1720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1716_, v_fvarId_1719_);
if (lean_obj_tag(v___x_1720_) == 0)
{
return v_arg_1717_;
}
else
{
lean_object* v_val_1721_; 
lean_dec_ref(v_arg_1717_);
v_val_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_val_1721_);
lean_dec_ref(v___x_1720_);
switch(lean_obj_tag(v_val_1721_))
{
case 0:
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_box(0);
return v___x_1722_;
}
case 1:
{
lean_object* v_fvarId_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1731_; 
v_fvarId_1723_ = lean_ctor_get(v_val_1721_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_val_1721_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1725_ = v_val_1721_;
v_isShared_1726_ = v_isSharedCheck_1731_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_fvarId_1723_);
lean_dec(v_val_1721_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1731_;
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
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_fvarId_1723_);
v___x_1728_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
if (v_translator_1718_ == 0)
{
v_arg_1717_ = v___x_1728_;
goto _start;
}
else
{
return v___x_1728_;
}
}
}
}
default: 
{
lean_object* v_expr_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
v_expr_1732_ = lean_ctor_get(v_val_1721_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_val_1721_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v_val_1721_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_expr_1732_);
lean_dec(v_val_1721_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_expr_1732_);
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
}
}
default: 
{
lean_object* v_expr_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v_expr_1740_ = lean_ctor_get(v_arg_1717_, 0);
lean_inc_ref(v_expr_1740_);
v___x_1741_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1715_, v_s_1716_, v_translator_1718_, v_expr_1740_);
v___x_1742_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1715_, v_arg_1717_, v___x_1741_);
return v___x_1742_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp___boxed(lean_object* v_pu_1743_, lean_object* v_s_1744_, lean_object* v_arg_1745_, lean_object* v_translator_1746_){
_start:
{
uint8_t v_pu_boxed_1747_; uint8_t v_translator_boxed_1748_; lean_object* v_res_1749_; 
v_pu_boxed_1747_ = lean_unbox(v_pu_1743_);
v_translator_boxed_1748_ = lean_unbox(v_translator_1746_);
v_res_1749_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_boxed_1747_, v_s_1744_, v_arg_1745_, v_translator_boxed_1748_);
lean_dec_ref(v_s_1744_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(uint8_t v_pu_1750_, lean_object* v_s_1751_, uint8_t v_translator_1752_, lean_object* v_i_1753_, lean_object* v_as_1754_){
_start:
{
lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1755_ = lean_array_get_size(v_as_1754_);
v___x_1756_ = lean_nat_dec_lt(v_i_1753_, v___x_1755_);
if (v___x_1756_ == 0)
{
lean_dec(v_i_1753_);
return v_as_1754_;
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1758_; size_t v___x_1759_; size_t v___x_1760_; uint8_t v___x_1761_; 
v_a_1757_ = lean_array_fget_borrowed(v_as_1754_, v_i_1753_);
lean_inc(v_a_1757_);
v___x_1758_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1750_, v_s_1751_, v_a_1757_, v_translator_1752_);
v___x_1759_ = lean_ptr_addr(v_a_1757_);
v___x_1760_ = lean_ptr_addr(v___x_1758_);
v___x_1761_ = lean_usize_dec_eq(v___x_1759_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1762_ = lean_unsigned_to_nat(1u);
v___x_1763_ = lean_nat_add(v_i_1753_, v___x_1762_);
v___x_1764_ = lean_array_fset(v_as_1754_, v_i_1753_, v___x_1758_);
lean_dec(v_i_1753_);
v_i_1753_ = v___x_1763_;
v_as_1754_ = v___x_1764_;
goto _start;
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_dec(v___x_1758_);
v___x_1766_ = lean_unsigned_to_nat(1u);
v___x_1767_ = lean_nat_add(v_i_1753_, v___x_1766_);
lean_dec(v_i_1753_);
v_i_1753_ = v___x_1767_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0___boxed(lean_object* v_pu_1769_, lean_object* v_s_1770_, lean_object* v_translator_1771_, lean_object* v_i_1772_, lean_object* v_as_1773_){
_start:
{
uint8_t v_pu_boxed_1774_; uint8_t v_translator_boxed_1775_; lean_object* v_res_1776_; 
v_pu_boxed_1774_ = lean_unbox(v_pu_1769_);
v_translator_boxed_1775_ = lean_unbox(v_translator_1771_);
v_res_1776_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_boxed_1774_, v_s_1770_, v_translator_boxed_1775_, v_i_1772_, v_as_1773_);
lean_dec_ref(v_s_1770_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t v_pu_1777_, lean_object* v_s_1778_, lean_object* v_args_1779_, uint8_t v_translator_1780_){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = lean_unsigned_to_nat(0u);
v___x_1782_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_1777_, v_s_1778_, v_translator_1780_, v___x_1781_, v_args_1779_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp___boxed(lean_object* v_pu_1783_, lean_object* v_s_1784_, lean_object* v_args_1785_, lean_object* v_translator_1786_){
_start:
{
uint8_t v_pu_boxed_1787_; uint8_t v_translator_boxed_1788_; lean_object* v_res_1789_; 
v_pu_boxed_1787_ = lean_unbox(v_pu_1783_);
v_translator_boxed_1788_ = lean_unbox(v_translator_1786_);
v_res_1789_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_boxed_1787_, v_s_1784_, v_args_1785_, v_translator_boxed_1788_);
lean_dec_ref(v_s_1784_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t v_pu_1790_, lean_object* v_s_1791_, lean_object* v_e_1792_, uint8_t v_translator_1793_){
_start:
{
lean_object* v_fvarId_1795_; lean_object* v_args_1801_; 
switch(lean_obj_tag(v_e_1792_))
{
case 2:
{
lean_object* v_struct_1804_; lean_object* v___x_1805_; 
v_struct_1804_ = lean_ctor_get(v_e_1792_, 2);
lean_inc(v_struct_1804_);
v___x_1805_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1791_, v_struct_1804_, v_translator_1793_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_fvarId_1806_; lean_object* v___x_1807_; 
v_fvarId_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_fvarId_1806_);
lean_dec_ref(v___x_1805_);
v___x_1807_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1790_, v_e_1792_, v_fvarId_1806_);
return v___x_1807_;
}
else
{
lean_object* v___x_1808_; 
lean_dec_ref(v_e_1792_);
v___x_1808_ = lean_box(1);
return v___x_1808_;
}
}
case 3:
{
lean_object* v_args_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v_args_1809_ = lean_ctor_get(v_e_1792_, 2);
lean_inc_ref(v_args_1809_);
v___x_1810_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1790_, v_s_1791_, v_args_1809_, v_translator_1793_);
v___x_1811_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1790_, v_e_1792_, v___x_1810_);
return v___x_1811_;
}
case 4:
{
lean_object* v_fvarId_1812_; lean_object* v_args_1813_; lean_object* v___x_1814_; 
v_fvarId_1812_ = lean_ctor_get(v_e_1792_, 0);
v_args_1813_ = lean_ctor_get(v_e_1792_, 1);
lean_inc(v_fvarId_1812_);
v___x_1814_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1791_, v_fvarId_1812_, v_translator_1793_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_fvarId_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v_fvarId_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_fvarId_1815_);
lean_dec_ref(v___x_1814_);
lean_inc_ref(v_args_1813_);
v___x_1816_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1790_, v_s_1791_, v_args_1813_, v_translator_1793_);
v___x_1817_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_1790_, v_e_1792_, v_fvarId_1815_, v___x_1816_);
lean_dec_ref(v_e_1792_);
return v___x_1817_;
}
else
{
lean_object* v___x_1818_; 
lean_dec_ref(v_e_1792_);
v___x_1818_ = lean_box(1);
return v___x_1818_;
}
}
case 5:
{
lean_object* v_args_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v_args_1819_ = lean_ctor_get(v_e_1792_, 1);
lean_inc_ref(v_args_1819_);
v___x_1820_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1790_, v_s_1791_, v_args_1819_, v_translator_1793_);
v___x_1821_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1790_, v_e_1792_, v___x_1820_);
return v___x_1821_;
}
case 6:
{
lean_object* v_var_1822_; 
v_var_1822_ = lean_ctor_get(v_e_1792_, 1);
lean_inc(v_var_1822_);
v_fvarId_1795_ = v_var_1822_;
goto v___jp_1794_;
}
case 7:
{
lean_object* v_var_1823_; 
v_var_1823_ = lean_ctor_get(v_e_1792_, 1);
lean_inc(v_var_1823_);
v_fvarId_1795_ = v_var_1823_;
goto v___jp_1794_;
}
case 8:
{
lean_object* v_var_1824_; lean_object* v___x_1825_; 
v_var_1824_ = lean_ctor_get(v_e_1792_, 2);
lean_inc(v_var_1824_);
v___x_1825_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1791_, v_var_1824_, v_translator_1793_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_fvarId_1826_; lean_object* v___x_1827_; 
v_fvarId_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_fvarId_1826_);
lean_dec_ref(v___x_1825_);
v___x_1827_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1790_, v_e_1792_, v_fvarId_1826_);
return v___x_1827_;
}
else
{
lean_object* v___x_1828_; 
lean_dec_ref(v_e_1792_);
v___x_1828_ = lean_box(1);
return v___x_1828_;
}
}
case 9:
{
lean_object* v_args_1829_; 
v_args_1829_ = lean_ctor_get(v_e_1792_, 1);
lean_inc_ref(v_args_1829_);
v_args_1801_ = v_args_1829_;
goto v___jp_1800_;
}
case 10:
{
lean_object* v_args_1830_; 
v_args_1830_ = lean_ctor_get(v_e_1792_, 1);
lean_inc_ref(v_args_1830_);
v_args_1801_ = v_args_1830_;
goto v___jp_1800_;
}
case 11:
{
lean_object* v_n_1831_; lean_object* v_var_1832_; lean_object* v___x_1833_; 
v_n_1831_ = lean_ctor_get(v_e_1792_, 0);
lean_inc(v_n_1831_);
v_var_1832_ = lean_ctor_get(v_e_1792_, 1);
lean_inc(v_var_1832_);
v___x_1833_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1791_, v_var_1832_, v_translator_1793_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_fvarId_1834_; lean_object* v___x_1835_; 
v_fvarId_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_fvarId_1834_);
lean_dec_ref(v___x_1833_);
v___x_1835_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_1790_, v_e_1792_, v_n_1831_, v_fvarId_1834_);
lean_dec_ref(v_e_1792_);
return v___x_1835_;
}
else
{
lean_object* v___x_1836_; 
lean_dec(v_n_1831_);
lean_dec_ref(v_e_1792_);
v___x_1836_ = lean_box(1);
return v___x_1836_;
}
}
case 12:
{
lean_object* v_var_1837_; lean_object* v_i_1838_; uint8_t v_updateHeader_1839_; lean_object* v_args_1840_; lean_object* v___x_1841_; 
v_var_1837_ = lean_ctor_get(v_e_1792_, 0);
v_i_1838_ = lean_ctor_get(v_e_1792_, 1);
lean_inc_ref(v_i_1838_);
v_updateHeader_1839_ = lean_ctor_get_uint8(v_e_1792_, sizeof(void*)*3);
v_args_1840_ = lean_ctor_get(v_e_1792_, 2);
lean_inc(v_var_1837_);
v___x_1841_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1791_, v_var_1837_, v_translator_1793_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_fvarId_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v_fvarId_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_fvarId_1842_);
lean_dec_ref(v___x_1841_);
lean_inc_ref(v_args_1840_);
v___x_1843_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1790_, v_s_1791_, v_args_1840_, v_translator_1793_);
v___x_1844_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_1790_, v_e_1792_, v_fvarId_1842_, v_i_1838_, v_updateHeader_1839_, v___x_1843_);
return v___x_1844_;
}
else
{
lean_object* v___x_1845_; 
lean_dec_ref(v_i_1838_);
lean_dec_ref(v_e_1792_);
v___x_1845_ = lean_box(1);
return v___x_1845_;
}
}
case 13:
{
lean_object* v_ty_1846_; lean_object* v_fvarId_1847_; lean_object* v___x_1848_; 
v_ty_1846_ = lean_ctor_get(v_e_1792_, 0);
lean_inc_ref(v_ty_1846_);
v_fvarId_1847_ = lean_ctor_get(v_e_1792_, 1);
lean_inc(v_fvarId_1847_);
v___x_1848_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1791_, v_fvarId_1847_, v_translator_1793_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_fvarId_1849_; lean_object* v___x_1850_; 
v_fvarId_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_fvarId_1849_);
lean_dec_ref(v___x_1848_);
v___x_1850_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_1790_, v_e_1792_, v_ty_1846_, v_fvarId_1849_);
lean_dec_ref(v_e_1792_);
return v___x_1850_;
}
else
{
lean_object* v___x_1851_; 
lean_dec_ref(v_ty_1846_);
lean_dec_ref(v_e_1792_);
v___x_1851_ = lean_box(1);
return v___x_1851_;
}
}
case 14:
{
lean_object* v_fvarId_1852_; lean_object* v___x_1853_; 
v_fvarId_1852_ = lean_ctor_get(v_e_1792_, 0);
lean_inc(v_fvarId_1852_);
v___x_1853_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1791_, v_fvarId_1852_, v_translator_1793_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_fvarId_1854_; lean_object* v___x_1855_; 
v_fvarId_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_fvarId_1854_);
lean_dec_ref(v___x_1853_);
v___x_1855_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_1790_, v_e_1792_, v_fvarId_1854_);
return v___x_1855_;
}
else
{
lean_object* v___x_1856_; 
lean_dec_ref(v_e_1792_);
v___x_1856_ = lean_box(1);
return v___x_1856_;
}
}
case 15:
{
lean_object* v_fvarId_1857_; lean_object* v___x_1858_; 
v_fvarId_1857_ = lean_ctor_get(v_e_1792_, 0);
lean_inc(v_fvarId_1857_);
v___x_1858_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1791_, v_fvarId_1857_, v_translator_1793_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_fvarId_1859_; lean_object* v___x_1860_; 
v_fvarId_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_fvarId_1859_);
lean_dec_ref(v___x_1858_);
v___x_1860_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_1790_, v_e_1792_, v_fvarId_1859_);
return v___x_1860_;
}
else
{
lean_object* v___x_1861_; 
lean_dec_ref(v_e_1792_);
v___x_1861_ = lean_box(1);
return v___x_1861_;
}
}
default: 
{
return v_e_1792_;
}
}
v___jp_1794_:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1791_, v_fvarId_1795_, v_translator_1793_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_fvarId_1797_; lean_object* v___x_1798_; 
v_fvarId_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_fvarId_1797_);
lean_dec_ref(v___x_1796_);
v___x_1798_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1790_, v_e_1792_, v_fvarId_1797_);
return v___x_1798_;
}
else
{
lean_object* v___x_1799_; 
lean_dec(v_e_1792_);
v___x_1799_ = lean_box(1);
return v___x_1799_;
}
}
v___jp_1800_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1790_, v_s_1791_, v_args_1801_, v_translator_1793_);
v___x_1803_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1790_, v_e_1792_, v___x_1802_);
return v___x_1803_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp___boxed(lean_object* v_pu_1862_, lean_object* v_s_1863_, lean_object* v_e_1864_, lean_object* v_translator_1865_){
_start:
{
uint8_t v_pu_boxed_1866_; uint8_t v_translator_boxed_1867_; lean_object* v_res_1868_; 
v_pu_boxed_1866_ = lean_unbox(v_pu_1862_);
v_translator_boxed_1867_ = lean_unbox(v_translator_1865_);
v_res_1868_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_boxed_1866_, v_s_1863_, v_e_1864_, v_translator_boxed_1867_);
lean_dec_ref(v_s_1863_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___redArg(lean_object* v_inst_1869_, lean_object* v_inst_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = lean_apply_2(v_inst_1869_, lean_box(0), v_inst_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(uint8_t v_pu_1872_, uint8_t v_t_1873_, lean_object* v_m_1874_, lean_object* v_n_1875_, lean_object* v_inst_1876_, lean_object* v_inst_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_apply_2(v_inst_1876_, lean_box(0), v_inst_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___boxed(lean_object* v_pu_1879_, lean_object* v_t_1880_, lean_object* v_m_1881_, lean_object* v_n_1882_, lean_object* v_inst_1883_, lean_object* v_inst_1884_){
_start:
{
uint8_t v_pu_boxed_1885_; uint8_t v_t_boxed_1886_; lean_object* v_res_1887_; 
v_pu_boxed_1885_ = lean_unbox(v_pu_1879_);
v_t_boxed_1886_ = lean_unbox(v_t_1880_);
v_res_1887_ = l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(v_pu_boxed_1885_, v_t_boxed_1886_, v_m_1881_, v_n_1882_, v_inst_1883_, v_inst_1884_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0(lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v_f_1890_){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_apply_1(v_inst_1888_, v_f_1890_);
v___x_1892_ = lean_apply_2(v_inst_1889_, lean_box(0), v___x_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg(lean_object* v_inst_1893_, lean_object* v_inst_1894_){
_start:
{
lean_object* v___f_1895_; 
v___f_1895_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1895_, 0, v_inst_1894_);
lean_closure_set(v___f_1895_, 1, v_inst_1893_);
return v___f_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(uint8_t v_pu_1896_, lean_object* v_m_1897_, lean_object* v_n_1898_, lean_object* v_inst_1899_, lean_object* v_inst_1900_){
_start:
{
lean_object* v___f_1901_; 
v___f_1901_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1901_, 0, v_inst_1900_);
lean_closure_set(v___f_1901_, 1, v_inst_1899_);
return v___f_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___boxed(lean_object* v_pu_1902_, lean_object* v_m_1903_, lean_object* v_n_1904_, lean_object* v_inst_1905_, lean_object* v_inst_1906_){
_start:
{
uint8_t v_pu_boxed_1907_; lean_object* v_res_1908_; 
v_pu_boxed_1907_ = lean_unbox(v_pu_1902_);
v_res_1908_ = l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(v_pu_boxed_1907_, v_m_1903_, v_n_1904_, v_inst_1905_, v_inst_1906_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___lam__0(lean_object* v___x_1909_, lean_object* v___x_1910_, lean_object* v_fvarId_1911_, lean_object* v_arg_1912_, lean_object* v_s_1913_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1909_, v___x_1910_, v_s_1913_, v_fvarId_1911_, v_arg_1912_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg(lean_object* v_inst_1917_, lean_object* v_fvarId_1918_, lean_object* v_arg_1919_){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___f_1922_; lean_object* v___x_1923_; 
v___x_1920_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1921_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1922_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1922_, 0, v___x_1920_);
lean_closure_set(v___f_1922_, 1, v___x_1921_);
lean_closure_set(v___f_1922_, 2, v_fvarId_1918_);
lean_closure_set(v___f_1922_, 3, v_arg_1919_);
v___x_1923_ = lean_apply_1(v_inst_1917_, v___f_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst(lean_object* v_m_1924_, uint8_t v_pu_1925_, lean_object* v_inst_1926_, lean_object* v_fvarId_1927_, lean_object* v_arg_1928_){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___f_1931_; lean_object* v___x_1932_; 
v___x_1929_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1930_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1931_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1931_, 0, v___x_1929_);
lean_closure_set(v___f_1931_, 1, v___x_1930_);
lean_closure_set(v___f_1931_, 2, v_fvarId_1927_);
lean_closure_set(v___f_1931_, 3, v_arg_1928_);
v___x_1932_ = lean_apply_1(v_inst_1926_, v___f_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___boxed(lean_object* v_m_1933_, lean_object* v_pu_1934_, lean_object* v_inst_1935_, lean_object* v_fvarId_1936_, lean_object* v_arg_1937_){
_start:
{
uint8_t v_pu_boxed_1938_; lean_object* v_res_1939_; 
v_pu_boxed_1938_ = lean_unbox(v_pu_1934_);
v_res_1939_ = l_Lean_Compiler_LCNF_addSubst(v_m_1933_, v_pu_boxed_1938_, v_inst_1935_, v_fvarId_1936_, v_arg_1937_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0(lean_object* v_fvarId_x27_1940_, lean_object* v___x_1941_, lean_object* v___x_1942_, lean_object* v_fvarId_1943_, lean_object* v_s_1944_){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1945_, 0, v_fvarId_x27_1940_);
v___x_1946_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1941_, v___x_1942_, v_s_1944_, v_fvarId_1943_, v___x_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg(lean_object* v_inst_1947_, lean_object* v_fvarId_1948_, lean_object* v_fvarId_x27_1949_){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___f_1952_; lean_object* v___x_1953_; 
v___x_1950_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1951_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1952_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1952_, 0, v_fvarId_x27_1949_);
lean_closure_set(v___f_1952_, 1, v___x_1950_);
lean_closure_set(v___f_1952_, 2, v___x_1951_);
lean_closure_set(v___f_1952_, 3, v_fvarId_1948_);
v___x_1953_ = lean_apply_1(v_inst_1947_, v___f_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst(lean_object* v_m_1954_, uint8_t v_ph_1955_, lean_object* v_inst_1956_, lean_object* v_fvarId_1957_, lean_object* v_fvarId_x27_1958_){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___f_1961_; lean_object* v___x_1962_; 
v___x_1959_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1960_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1961_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1961_, 0, v_fvarId_x27_1958_);
lean_closure_set(v___f_1961_, 1, v___x_1959_);
lean_closure_set(v___f_1961_, 2, v___x_1960_);
lean_closure_set(v___f_1961_, 3, v_fvarId_1957_);
v___x_1962_ = lean_apply_1(v_inst_1956_, v___f_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___boxed(lean_object* v_m_1963_, lean_object* v_ph_1964_, lean_object* v_inst_1965_, lean_object* v_fvarId_1966_, lean_object* v_fvarId_x27_1967_){
_start:
{
uint8_t v_ph_boxed_1968_; lean_object* v_res_1969_; 
v_ph_boxed_1968_ = lean_unbox(v_ph_1964_);
v_res_1969_ = l_Lean_Compiler_LCNF_addFVarSubst(v_m_1963_, v_ph_boxed_1968_, v_inst_1965_, v_fvarId_1966_, v_fvarId_x27_1967_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(lean_object* v_fvarId_1970_, uint8_t v_t_1971_, lean_object* v_toPure_1972_, lean_object* v_____do__lift_1973_){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_____do__lift_1973_, v_fvarId_1970_, v_t_1971_);
v___x_1975_ = lean_apply_2(v_toPure_1972_, lean_box(0), v___x_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed(lean_object* v_fvarId_1976_, lean_object* v_t_1977_, lean_object* v_toPure_1978_, lean_object* v_____do__lift_1979_){
_start:
{
uint8_t v_t_boxed_1980_; lean_object* v_res_1981_; 
v_t_boxed_1980_ = lean_unbox(v_t_1977_);
v_res_1981_ = l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(v_fvarId_1976_, v_t_boxed_1980_, v_toPure_1978_, v_____do__lift_1979_);
lean_dec_ref(v_____do__lift_1979_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg(uint8_t v_t_1982_, lean_object* v_inst_1983_, lean_object* v_inst_1984_, lean_object* v_fvarId_1985_){
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___boxed(lean_object* v_t_1992_, lean_object* v_inst_1993_, lean_object* v_inst_1994_, lean_object* v_fvarId_1995_){
_start:
{
uint8_t v_t_boxed_1996_; lean_object* v_res_1997_; 
v_t_boxed_1996_ = lean_unbox(v_t_1992_);
v_res_1997_ = l_Lean_Compiler_LCNF_normFVar___redArg(v_t_boxed_1996_, v_inst_1993_, v_inst_1994_, v_fvarId_1995_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar(lean_object* v_m_1998_, uint8_t v_pu_1999_, uint8_t v_t_2000_, lean_object* v_inst_2001_, lean_object* v_inst_2002_, lean_object* v_fvarId_2003_){
_start:
{
lean_object* v_toApplicative_2004_; lean_object* v_toBind_2005_; lean_object* v_toPure_2006_; lean_object* v___x_2007_; lean_object* v___f_2008_; lean_object* v___x_2009_; 
v_toApplicative_2004_ = lean_ctor_get(v_inst_2002_, 0);
lean_inc_ref(v_toApplicative_2004_);
v_toBind_2005_ = lean_ctor_get(v_inst_2002_, 1);
lean_inc(v_toBind_2005_);
lean_dec_ref(v_inst_2002_);
v_toPure_2006_ = lean_ctor_get(v_toApplicative_2004_, 1);
lean_inc(v_toPure_2006_);
lean_dec_ref(v_toApplicative_2004_);
v___x_2007_ = lean_box(v_t_2000_);
v___f_2008_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2008_, 0, v_fvarId_2003_);
lean_closure_set(v___f_2008_, 1, v___x_2007_);
lean_closure_set(v___f_2008_, 2, v_toPure_2006_);
v___x_2009_ = lean_apply_4(v_toBind_2005_, lean_box(0), lean_box(0), v_inst_2001_, v___f_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___boxed(lean_object* v_m_2010_, lean_object* v_pu_2011_, lean_object* v_t_2012_, lean_object* v_inst_2013_, lean_object* v_inst_2014_, lean_object* v_fvarId_2015_){
_start:
{
uint8_t v_pu_boxed_2016_; uint8_t v_t_boxed_2017_; lean_object* v_res_2018_; 
v_pu_boxed_2016_ = lean_unbox(v_pu_2011_);
v_t_boxed_2017_ = lean_unbox(v_t_2012_);
v_res_2018_ = l_Lean_Compiler_LCNF_normFVar(v_m_2010_, v_pu_boxed_2016_, v_t_boxed_2017_, v_inst_2013_, v_inst_2014_, v_fvarId_2015_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(uint8_t v_pu_2019_, uint8_t v_t_2020_, lean_object* v_e_2021_, lean_object* v_toPure_2022_, lean_object* v_____do__lift_2023_){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2019_, v_____do__lift_2023_, v_t_2020_, v_e_2021_);
v___x_2025_ = lean_apply_2(v_toPure_2022_, lean_box(0), v___x_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed(lean_object* v_pu_2026_, lean_object* v_t_2027_, lean_object* v_e_2028_, lean_object* v_toPure_2029_, lean_object* v_____do__lift_2030_){
_start:
{
uint8_t v_pu_boxed_2031_; uint8_t v_t_boxed_2032_; lean_object* v_res_2033_; 
v_pu_boxed_2031_ = lean_unbox(v_pu_2026_);
v_t_boxed_2032_ = lean_unbox(v_t_2027_);
v_res_2033_ = l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(v_pu_boxed_2031_, v_t_boxed_2032_, v_e_2028_, v_toPure_2029_, v_____do__lift_2030_);
lean_dec_ref(v_____do__lift_2030_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg(uint8_t v_pu_2034_, uint8_t v_t_2035_, lean_object* v_inst_2036_, lean_object* v_inst_2037_, lean_object* v_e_2038_){
_start:
{
lean_object* v_toApplicative_2039_; lean_object* v_toBind_2040_; lean_object* v_toPure_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___f_2044_; lean_object* v___x_2045_; 
v_toApplicative_2039_ = lean_ctor_get(v_inst_2037_, 0);
lean_inc_ref(v_toApplicative_2039_);
v_toBind_2040_ = lean_ctor_get(v_inst_2037_, 1);
lean_inc(v_toBind_2040_);
lean_dec_ref(v_inst_2037_);
v_toPure_2041_ = lean_ctor_get(v_toApplicative_2039_, 1);
lean_inc(v_toPure_2041_);
lean_dec_ref(v_toApplicative_2039_);
v___x_2042_ = lean_box(v_pu_2034_);
v___x_2043_ = lean_box(v_t_2035_);
v___f_2044_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2044_, 0, v___x_2042_);
lean_closure_set(v___f_2044_, 1, v___x_2043_);
lean_closure_set(v___f_2044_, 2, v_e_2038_);
lean_closure_set(v___f_2044_, 3, v_toPure_2041_);
v___x_2045_ = lean_apply_4(v_toBind_2040_, lean_box(0), lean_box(0), v_inst_2036_, v___f_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___boxed(lean_object* v_pu_2046_, lean_object* v_t_2047_, lean_object* v_inst_2048_, lean_object* v_inst_2049_, lean_object* v_e_2050_){
_start:
{
uint8_t v_pu_boxed_2051_; uint8_t v_t_boxed_2052_; lean_object* v_res_2053_; 
v_pu_boxed_2051_ = lean_unbox(v_pu_2046_);
v_t_boxed_2052_ = lean_unbox(v_t_2047_);
v_res_2053_ = l_Lean_Compiler_LCNF_normExpr___redArg(v_pu_boxed_2051_, v_t_boxed_2052_, v_inst_2048_, v_inst_2049_, v_e_2050_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr(lean_object* v_m_2054_, uint8_t v_pu_2055_, uint8_t v_t_2056_, lean_object* v_inst_2057_, lean_object* v_inst_2058_, lean_object* v_e_2059_){
_start:
{
lean_object* v_toApplicative_2060_; lean_object* v_toBind_2061_; lean_object* v_toPure_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___f_2065_; lean_object* v___x_2066_; 
v_toApplicative_2060_ = lean_ctor_get(v_inst_2058_, 0);
lean_inc_ref(v_toApplicative_2060_);
v_toBind_2061_ = lean_ctor_get(v_inst_2058_, 1);
lean_inc(v_toBind_2061_);
lean_dec_ref(v_inst_2058_);
v_toPure_2062_ = lean_ctor_get(v_toApplicative_2060_, 1);
lean_inc(v_toPure_2062_);
lean_dec_ref(v_toApplicative_2060_);
v___x_2063_ = lean_box(v_pu_2055_);
v___x_2064_ = lean_box(v_t_2056_);
v___f_2065_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2065_, 0, v___x_2063_);
lean_closure_set(v___f_2065_, 1, v___x_2064_);
lean_closure_set(v___f_2065_, 2, v_e_2059_);
lean_closure_set(v___f_2065_, 3, v_toPure_2062_);
v___x_2066_ = lean_apply_4(v_toBind_2061_, lean_box(0), lean_box(0), v_inst_2057_, v___f_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___boxed(lean_object* v_m_2067_, lean_object* v_pu_2068_, lean_object* v_t_2069_, lean_object* v_inst_2070_, lean_object* v_inst_2071_, lean_object* v_e_2072_){
_start:
{
uint8_t v_pu_boxed_2073_; uint8_t v_t_boxed_2074_; lean_object* v_res_2075_; 
v_pu_boxed_2073_ = lean_unbox(v_pu_2068_);
v_t_boxed_2074_ = lean_unbox(v_t_2069_);
v_res_2075_ = l_Lean_Compiler_LCNF_normExpr(v_m_2067_, v_pu_boxed_2073_, v_t_boxed_2074_, v_inst_2070_, v_inst_2071_, v_e_2072_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0(uint8_t v_pu_2076_, lean_object* v_arg_2077_, uint8_t v_t_2078_, lean_object* v_toPure_2079_, lean_object* v_____do__lift_2080_){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2076_, v_____do__lift_2080_, v_arg_2077_, v_t_2078_);
v___x_2082_ = lean_apply_2(v_toPure_2079_, lean_box(0), v___x_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed(lean_object* v_pu_2083_, lean_object* v_arg_2084_, lean_object* v_t_2085_, lean_object* v_toPure_2086_, lean_object* v_____do__lift_2087_){
_start:
{
uint8_t v_pu_boxed_2088_; uint8_t v_t_boxed_2089_; lean_object* v_res_2090_; 
v_pu_boxed_2088_ = lean_unbox(v_pu_2083_);
v_t_boxed_2089_ = lean_unbox(v_t_2085_);
v_res_2090_ = l_Lean_Compiler_LCNF_normArg___redArg___lam__0(v_pu_boxed_2088_, v_arg_2084_, v_t_boxed_2089_, v_toPure_2086_, v_____do__lift_2087_);
lean_dec_ref(v_____do__lift_2087_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg(uint8_t v_pu_2091_, uint8_t v_t_2092_, lean_object* v_inst_2093_, lean_object* v_inst_2094_, lean_object* v_arg_2095_){
_start:
{
lean_object* v_toApplicative_2096_; lean_object* v_toBind_2097_; lean_object* v_toPure_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___f_2101_; lean_object* v___x_2102_; 
v_toApplicative_2096_ = lean_ctor_get(v_inst_2094_, 0);
lean_inc_ref(v_toApplicative_2096_);
v_toBind_2097_ = lean_ctor_get(v_inst_2094_, 1);
lean_inc(v_toBind_2097_);
lean_dec_ref(v_inst_2094_);
v_toPure_2098_ = lean_ctor_get(v_toApplicative_2096_, 1);
lean_inc(v_toPure_2098_);
lean_dec_ref(v_toApplicative_2096_);
v___x_2099_ = lean_box(v_pu_2091_);
v___x_2100_ = lean_box(v_t_2092_);
v___f_2101_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2101_, 0, v___x_2099_);
lean_closure_set(v___f_2101_, 1, v_arg_2095_);
lean_closure_set(v___f_2101_, 2, v___x_2100_);
lean_closure_set(v___f_2101_, 3, v_toPure_2098_);
v___x_2102_ = lean_apply_4(v_toBind_2097_, lean_box(0), lean_box(0), v_inst_2093_, v___f_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___boxed(lean_object* v_pu_2103_, lean_object* v_t_2104_, lean_object* v_inst_2105_, lean_object* v_inst_2106_, lean_object* v_arg_2107_){
_start:
{
uint8_t v_pu_boxed_2108_; uint8_t v_t_boxed_2109_; lean_object* v_res_2110_; 
v_pu_boxed_2108_ = lean_unbox(v_pu_2103_);
v_t_boxed_2109_ = lean_unbox(v_t_2104_);
v_res_2110_ = l_Lean_Compiler_LCNF_normArg___redArg(v_pu_boxed_2108_, v_t_boxed_2109_, v_inst_2105_, v_inst_2106_, v_arg_2107_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg(lean_object* v_m_2111_, uint8_t v_pu_2112_, uint8_t v_t_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_arg_2116_){
_start:
{
lean_object* v_toApplicative_2117_; lean_object* v_toBind_2118_; lean_object* v_toPure_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___f_2122_; lean_object* v___x_2123_; 
v_toApplicative_2117_ = lean_ctor_get(v_inst_2115_, 0);
lean_inc_ref(v_toApplicative_2117_);
v_toBind_2118_ = lean_ctor_get(v_inst_2115_, 1);
lean_inc(v_toBind_2118_);
lean_dec_ref(v_inst_2115_);
v_toPure_2119_ = lean_ctor_get(v_toApplicative_2117_, 1);
lean_inc(v_toPure_2119_);
lean_dec_ref(v_toApplicative_2117_);
v___x_2120_ = lean_box(v_pu_2112_);
v___x_2121_ = lean_box(v_t_2113_);
v___f_2122_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2122_, 0, v___x_2120_);
lean_closure_set(v___f_2122_, 1, v_arg_2116_);
lean_closure_set(v___f_2122_, 2, v___x_2121_);
lean_closure_set(v___f_2122_, 3, v_toPure_2119_);
v___x_2123_ = lean_apply_4(v_toBind_2118_, lean_box(0), lean_box(0), v_inst_2114_, v___f_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___boxed(lean_object* v_m_2124_, lean_object* v_pu_2125_, lean_object* v_t_2126_, lean_object* v_inst_2127_, lean_object* v_inst_2128_, lean_object* v_arg_2129_){
_start:
{
uint8_t v_pu_boxed_2130_; uint8_t v_t_boxed_2131_; lean_object* v_res_2132_; 
v_pu_boxed_2130_ = lean_unbox(v_pu_2125_);
v_t_boxed_2131_ = lean_unbox(v_t_2126_);
v_res_2132_ = l_Lean_Compiler_LCNF_normArg(v_m_2124_, v_pu_boxed_2130_, v_t_boxed_2131_, v_inst_2127_, v_inst_2128_, v_arg_2129_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(uint8_t v_pu_2133_, lean_object* v_e_2134_, uint8_t v_t_2135_, lean_object* v_toPure_2136_, lean_object* v_____do__lift_2137_){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_2133_, v_____do__lift_2137_, v_e_2134_, v_t_2135_);
v___x_2139_ = lean_apply_2(v_toPure_2136_, lean_box(0), v___x_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed(lean_object* v_pu_2140_, lean_object* v_e_2141_, lean_object* v_t_2142_, lean_object* v_toPure_2143_, lean_object* v_____do__lift_2144_){
_start:
{
uint8_t v_pu_boxed_2145_; uint8_t v_t_boxed_2146_; lean_object* v_res_2147_; 
v_pu_boxed_2145_ = lean_unbox(v_pu_2140_);
v_t_boxed_2146_ = lean_unbox(v_t_2142_);
v_res_2147_ = l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(v_pu_boxed_2145_, v_e_2141_, v_t_boxed_2146_, v_toPure_2143_, v_____do__lift_2144_);
lean_dec_ref(v_____do__lift_2144_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg(uint8_t v_pu_2148_, uint8_t v_t_2149_, lean_object* v_inst_2150_, lean_object* v_inst_2151_, lean_object* v_e_2152_){
_start:
{
lean_object* v_toApplicative_2153_; lean_object* v_toBind_2154_; lean_object* v_toPure_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___f_2158_; lean_object* v___x_2159_; 
v_toApplicative_2153_ = lean_ctor_get(v_inst_2151_, 0);
lean_inc_ref(v_toApplicative_2153_);
v_toBind_2154_ = lean_ctor_get(v_inst_2151_, 1);
lean_inc(v_toBind_2154_);
lean_dec_ref(v_inst_2151_);
v_toPure_2155_ = lean_ctor_get(v_toApplicative_2153_, 1);
lean_inc(v_toPure_2155_);
lean_dec_ref(v_toApplicative_2153_);
v___x_2156_ = lean_box(v_pu_2148_);
v___x_2157_ = lean_box(v_t_2149_);
v___f_2158_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2158_, 0, v___x_2156_);
lean_closure_set(v___f_2158_, 1, v_e_2152_);
lean_closure_set(v___f_2158_, 2, v___x_2157_);
lean_closure_set(v___f_2158_, 3, v_toPure_2155_);
v___x_2159_ = lean_apply_4(v_toBind_2154_, lean_box(0), lean_box(0), v_inst_2150_, v___f_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___boxed(lean_object* v_pu_2160_, lean_object* v_t_2161_, lean_object* v_inst_2162_, lean_object* v_inst_2163_, lean_object* v_e_2164_){
_start:
{
uint8_t v_pu_boxed_2165_; uint8_t v_t_boxed_2166_; lean_object* v_res_2167_; 
v_pu_boxed_2165_ = lean_unbox(v_pu_2160_);
v_t_boxed_2166_ = lean_unbox(v_t_2161_);
v_res_2167_ = l_Lean_Compiler_LCNF_normLetValue___redArg(v_pu_boxed_2165_, v_t_boxed_2166_, v_inst_2162_, v_inst_2163_, v_e_2164_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue(lean_object* v_m_2168_, uint8_t v_pu_2169_, uint8_t v_t_2170_, lean_object* v_inst_2171_, lean_object* v_inst_2172_, lean_object* v_e_2173_){
_start:
{
lean_object* v_toApplicative_2174_; lean_object* v_toBind_2175_; lean_object* v_toPure_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___f_2179_; lean_object* v___x_2180_; 
v_toApplicative_2174_ = lean_ctor_get(v_inst_2172_, 0);
lean_inc_ref(v_toApplicative_2174_);
v_toBind_2175_ = lean_ctor_get(v_inst_2172_, 1);
lean_inc(v_toBind_2175_);
lean_dec_ref(v_inst_2172_);
v_toPure_2176_ = lean_ctor_get(v_toApplicative_2174_, 1);
lean_inc(v_toPure_2176_);
lean_dec_ref(v_toApplicative_2174_);
v___x_2177_ = lean_box(v_pu_2169_);
v___x_2178_ = lean_box(v_t_2170_);
v___f_2179_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2179_, 0, v___x_2177_);
lean_closure_set(v___f_2179_, 1, v_e_2173_);
lean_closure_set(v___f_2179_, 2, v___x_2178_);
lean_closure_set(v___f_2179_, 3, v_toPure_2176_);
v___x_2180_ = lean_apply_4(v_toBind_2175_, lean_box(0), lean_box(0), v_inst_2171_, v___f_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___boxed(lean_object* v_m_2181_, lean_object* v_pu_2182_, lean_object* v_t_2183_, lean_object* v_inst_2184_, lean_object* v_inst_2185_, lean_object* v_e_2186_){
_start:
{
uint8_t v_pu_boxed_2187_; uint8_t v_t_boxed_2188_; lean_object* v_res_2189_; 
v_pu_boxed_2187_ = lean_unbox(v_pu_2182_);
v_t_boxed_2188_ = lean_unbox(v_t_2183_);
v_res_2189_ = l_Lean_Compiler_LCNF_normLetValue(v_m_2181_, v_pu_boxed_2187_, v_t_boxed_2188_, v_inst_2184_, v_inst_2185_, v_e_2186_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore(uint8_t v_pu_2190_, lean_object* v_s_2191_, lean_object* v_e_2192_, uint8_t v_translator_2193_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2190_, v_s_2191_, v_translator_2193_, v_e_2192_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore___boxed(lean_object* v_pu_2195_, lean_object* v_s_2196_, lean_object* v_e_2197_, lean_object* v_translator_2198_){
_start:
{
uint8_t v_pu_boxed_2199_; uint8_t v_translator_boxed_2200_; lean_object* v_res_2201_; 
v_pu_boxed_2199_ = lean_unbox(v_pu_2195_);
v_translator_boxed_2200_ = lean_unbox(v_translator_2198_);
v_res_2201_ = l_Lean_Compiler_LCNF_normExprCore(v_pu_boxed_2199_, v_s_2196_, v_e_2197_, v_translator_boxed_2200_);
lean_dec_ref(v_s_2196_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(uint8_t v_pu_2202_, lean_object* v_args_2203_, uint8_t v_t_2204_, lean_object* v_toPure_2205_, lean_object* v_____do__lift_2206_){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_2202_, v_____do__lift_2206_, v_args_2203_, v_t_2204_);
v___x_2208_ = lean_apply_2(v_toPure_2205_, lean_box(0), v___x_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed(lean_object* v_pu_2209_, lean_object* v_args_2210_, lean_object* v_t_2211_, lean_object* v_toPure_2212_, lean_object* v_____do__lift_2213_){
_start:
{
uint8_t v_pu_boxed_2214_; uint8_t v_t_boxed_2215_; lean_object* v_res_2216_; 
v_pu_boxed_2214_ = lean_unbox(v_pu_2209_);
v_t_boxed_2215_ = lean_unbox(v_t_2211_);
v_res_2216_ = l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(v_pu_boxed_2214_, v_args_2210_, v_t_boxed_2215_, v_toPure_2212_, v_____do__lift_2213_);
lean_dec_ref(v_____do__lift_2213_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg(uint8_t v_pu_2217_, uint8_t v_t_2218_, lean_object* v_inst_2219_, lean_object* v_inst_2220_, lean_object* v_args_2221_){
_start:
{
lean_object* v_toApplicative_2222_; lean_object* v_toBind_2223_; lean_object* v_toPure_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___f_2227_; lean_object* v___x_2228_; 
v_toApplicative_2222_ = lean_ctor_get(v_inst_2220_, 0);
lean_inc_ref(v_toApplicative_2222_);
v_toBind_2223_ = lean_ctor_get(v_inst_2220_, 1);
lean_inc(v_toBind_2223_);
lean_dec_ref(v_inst_2220_);
v_toPure_2224_ = lean_ctor_get(v_toApplicative_2222_, 1);
lean_inc(v_toPure_2224_);
lean_dec_ref(v_toApplicative_2222_);
v___x_2225_ = lean_box(v_pu_2217_);
v___x_2226_ = lean_box(v_t_2218_);
v___f_2227_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2227_, 0, v___x_2225_);
lean_closure_set(v___f_2227_, 1, v_args_2221_);
lean_closure_set(v___f_2227_, 2, v___x_2226_);
lean_closure_set(v___f_2227_, 3, v_toPure_2224_);
v___x_2228_ = lean_apply_4(v_toBind_2223_, lean_box(0), lean_box(0), v_inst_2219_, v___f_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___boxed(lean_object* v_pu_2229_, lean_object* v_t_2230_, lean_object* v_inst_2231_, lean_object* v_inst_2232_, lean_object* v_args_2233_){
_start:
{
uint8_t v_pu_boxed_2234_; uint8_t v_t_boxed_2235_; lean_object* v_res_2236_; 
v_pu_boxed_2234_ = lean_unbox(v_pu_2229_);
v_t_boxed_2235_ = lean_unbox(v_t_2230_);
v_res_2236_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_boxed_2234_, v_t_boxed_2235_, v_inst_2231_, v_inst_2232_, v_args_2233_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs(lean_object* v_m_2237_, uint8_t v_pu_2238_, uint8_t v_t_2239_, lean_object* v_inst_2240_, lean_object* v_inst_2241_, lean_object* v_args_2242_){
_start:
{
lean_object* v___x_2243_; 
v___x_2243_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_2238_, v_t_2239_, v_inst_2240_, v_inst_2241_, v_args_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___boxed(lean_object* v_m_2244_, lean_object* v_pu_2245_, lean_object* v_t_2246_, lean_object* v_inst_2247_, lean_object* v_inst_2248_, lean_object* v_args_2249_){
_start:
{
uint8_t v_pu_boxed_2250_; uint8_t v_t_boxed_2251_; lean_object* v_res_2252_; 
v_pu_boxed_2250_ = lean_unbox(v_pu_2245_);
v_t_boxed_2251_ = lean_unbox(v_t_2246_);
v_res_2252_ = l_Lean_Compiler_LCNF_normArgs(v_m_2244_, v_pu_boxed_2250_, v_t_boxed_2251_, v_inst_2247_, v_inst_2248_, v_args_2249_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object* v_binderName_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v_lctx_2258_; lean_object* v_nextIdx_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2272_; 
v___x_2256_ = lean_st_ref_get(v_a_2254_);
v___x_2257_ = lean_st_ref_take(v_a_2254_);
v_lctx_2258_ = lean_ctor_get(v___x_2257_, 0);
v_nextIdx_2259_ = lean_ctor_get(v___x_2257_, 1);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2261_ = v___x_2257_;
v_isShared_2262_ = v_isSharedCheck_2272_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_nextIdx_2259_);
lean_inc(v_lctx_2258_);
lean_dec(v___x_2257_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2272_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2266_; 
v___x_2263_ = lean_unsigned_to_nat(1u);
v___x_2264_ = lean_nat_add(v_nextIdx_2259_, v___x_2263_);
lean_dec(v_nextIdx_2259_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 1, v___x_2264_);
v___x_2266_ = v___x_2261_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_lctx_2258_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v___x_2264_);
v___x_2266_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2267_; lean_object* v_nextIdx_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2267_ = lean_st_ref_set(v_a_2254_, v___x_2266_);
v_nextIdx_2268_ = lean_ctor_get(v___x_2256_, 1);
lean_inc(v_nextIdx_2268_);
lean_dec(v___x_2256_);
v___x_2269_ = l_Lean_Name_num___override(v_binderName_2253_, v_nextIdx_2268_);
v___x_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
return v___x_2270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg___boxed(lean_object* v_binderName_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2273_, v_a_2274_);
lean_dec(v_a_2274_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object* v_binderName_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2277_, v_a_2279_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___boxed(lean_object* v_binderName_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_Compiler_LCNF_mkFreshBinderName(v_binderName_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(lean_object* v_binderName_2291_, lean_object* v_baseName_2292_, lean_object* v_a_2293_){
_start:
{
uint8_t v___x_2295_; 
v___x_2295_ = l_Lean_Name_isAnonymous(v_binderName_2291_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; 
lean_dec(v_baseName_2292_);
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v_binderName_2291_);
return v___x_2296_;
}
else
{
lean_object* v___x_2297_; 
lean_dec(v_binderName_2291_);
v___x_2297_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_baseName_2292_, v_a_2293_);
return v___x_2297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg___boxed(lean_object* v_binderName_2298_, lean_object* v_baseName_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2298_, v_baseName_2299_, v_a_2300_);
lean_dec(v_a_2300_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous(lean_object* v_binderName_2303_, lean_object* v_baseName_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2303_, v_baseName_2304_, v_a_2306_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___boxed(lean_object* v_binderName_2311_, lean_object* v_baseName_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lean_Compiler_LCNF_ensureNotAnonymous(v_binderName_2311_, v_baseName_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(lean_object* v___y_2319_){
_start:
{
lean_object* v___x_2321_; lean_object* v_ngen_2322_; lean_object* v_namePrefix_2323_; lean_object* v_idx_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2353_; 
v___x_2321_ = lean_st_ref_get(v___y_2319_);
v_ngen_2322_ = lean_ctor_get(v___x_2321_, 2);
lean_inc_ref(v_ngen_2322_);
lean_dec(v___x_2321_);
v_namePrefix_2323_ = lean_ctor_get(v_ngen_2322_, 0);
v_idx_2324_ = lean_ctor_get(v_ngen_2322_, 1);
v_isSharedCheck_2353_ = !lean_is_exclusive(v_ngen_2322_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2326_ = v_ngen_2322_;
v_isShared_2327_ = v_isSharedCheck_2353_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_idx_2324_);
lean_inc(v_namePrefix_2323_);
lean_dec(v_ngen_2322_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2353_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2328_; lean_object* v_env_2329_; lean_object* v_nextMacroScope_2330_; lean_object* v_auxDeclNGen_2331_; lean_object* v_traceState_2332_; lean_object* v_cache_2333_; lean_object* v_messages_2334_; lean_object* v_infoState_2335_; lean_object* v_snapshotTasks_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2351_; 
v___x_2328_ = lean_st_ref_take(v___y_2319_);
v_env_2329_ = lean_ctor_get(v___x_2328_, 0);
v_nextMacroScope_2330_ = lean_ctor_get(v___x_2328_, 1);
v_auxDeclNGen_2331_ = lean_ctor_get(v___x_2328_, 3);
v_traceState_2332_ = lean_ctor_get(v___x_2328_, 4);
v_cache_2333_ = lean_ctor_get(v___x_2328_, 5);
v_messages_2334_ = lean_ctor_get(v___x_2328_, 6);
v_infoState_2335_ = lean_ctor_get(v___x_2328_, 7);
v_snapshotTasks_2336_ = lean_ctor_get(v___x_2328_, 8);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2351_ == 0)
{
lean_object* v_unused_2352_; 
v_unused_2352_ = lean_ctor_get(v___x_2328_, 2);
lean_dec(v_unused_2352_);
v___x_2338_ = v___x_2328_;
v_isShared_2339_ = v_isSharedCheck_2351_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_snapshotTasks_2336_);
lean_inc(v_infoState_2335_);
lean_inc(v_messages_2334_);
lean_inc(v_cache_2333_);
lean_inc(v_traceState_2332_);
lean_inc(v_auxDeclNGen_2331_);
lean_inc(v_nextMacroScope_2330_);
lean_inc(v_env_2329_);
lean_dec(v___x_2328_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2351_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v_r_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2344_; 
lean_inc(v_idx_2324_);
lean_inc(v_namePrefix_2323_);
v_r_2340_ = l_Lean_Name_num___override(v_namePrefix_2323_, v_idx_2324_);
v___x_2341_ = lean_unsigned_to_nat(1u);
v___x_2342_ = lean_nat_add(v_idx_2324_, v___x_2341_);
lean_dec(v_idx_2324_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 1, v___x_2342_);
v___x_2344_ = v___x_2326_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_namePrefix_2323_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v___x_2342_);
v___x_2344_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2346_; 
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 2, v___x_2344_);
v___x_2346_ = v___x_2338_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_env_2329_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_nextMacroScope_2330_);
lean_ctor_set(v_reuseFailAlloc_2349_, 2, v___x_2344_);
lean_ctor_set(v_reuseFailAlloc_2349_, 3, v_auxDeclNGen_2331_);
lean_ctor_set(v_reuseFailAlloc_2349_, 4, v_traceState_2332_);
lean_ctor_set(v_reuseFailAlloc_2349_, 5, v_cache_2333_);
lean_ctor_set(v_reuseFailAlloc_2349_, 6, v_messages_2334_);
lean_ctor_set(v_reuseFailAlloc_2349_, 7, v_infoState_2335_);
lean_ctor_set(v_reuseFailAlloc_2349_, 8, v_snapshotTasks_2336_);
v___x_2346_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = lean_st_ref_set(v___y_2319_, v___x_2346_);
v___x_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2348_, 0, v_r_2340_);
return v___x_2348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg___boxed(lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2354_);
lean_dec(v___y_2354_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___x_2362_; lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
v___x_2362_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2360_);
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2362_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0___boxed(lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t v_pu_2380_, lean_object* v_binderName_2381_, lean_object* v_type_2382_, uint8_t v_borrow_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2413_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2390_);
lean_dec_ref(v___x_2389_);
v___x_2391_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_2392_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2381_, v___x_2391_, v_a_2385_);
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2395_ = v___x_2392_;
v_isShared_2396_ = v_isSharedCheck_2413_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2413_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2397_; lean_object* v_lctx_2398_; lean_object* v_nextIdx_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2412_; 
v___x_2397_ = lean_st_ref_take(v_a_2385_);
v_lctx_2398_ = lean_ctor_get(v___x_2397_, 0);
v_nextIdx_2399_ = lean_ctor_get(v___x_2397_, 1);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2401_ = v___x_2397_;
v_isShared_2402_ = v_isSharedCheck_2412_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_nextIdx_2399_);
lean_inc(v_lctx_2398_);
lean_dec(v___x_2397_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2412_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2406_; 
v___x_2403_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2403_, 0, v_a_2390_);
lean_ctor_set(v___x_2403_, 1, v_a_2393_);
lean_ctor_set(v___x_2403_, 2, v_type_2382_);
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*3, v_borrow_2383_);
lean_inc_ref(v___x_2403_);
v___x_2404_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2380_, v_lctx_2398_, v___x_2403_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 0, v___x_2404_);
v___x_2406_ = v___x_2401_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2404_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v_nextIdx_2399_);
v___x_2406_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2407_ = lean_st_ref_set(v_a_2385_, v___x_2406_);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2403_);
v___x_2409_ = v___x_2395_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2403_);
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
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_dec_ref(v_type_2382_);
lean_dec(v_binderName_2381_);
v_a_2414_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2389_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2389_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam___boxed(lean_object* v_pu_2422_, lean_object* v_binderName_2423_, lean_object* v_type_2424_, lean_object* v_borrow_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
uint8_t v_pu_boxed_2431_; uint8_t v_borrow_boxed_2432_; lean_object* v_res_2433_; 
v_pu_boxed_2431_ = lean_unbox(v_pu_2422_);
v_borrow_boxed_2432_ = lean_unbox(v_borrow_2425_);
v_res_2433_ = l_Lean_Compiler_LCNF_mkParam(v_pu_boxed_2431_, v_binderName_2423_, v_type_2424_, v_borrow_boxed_2432_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec_ref(v_a_2426_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2437_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___boxed(lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t v_pu_2449_, lean_object* v_binderName_2450_, lean_object* v_type_2451_, lean_object* v_value_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2482_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref(v___x_2458_);
v___x_2460_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2461_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2450_, v___x_2460_, v_a_2454_);
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2482_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2482_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2466_; lean_object* v_lctx_2467_; lean_object* v_nextIdx_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2481_; 
v___x_2466_ = lean_st_ref_take(v_a_2454_);
v_lctx_2467_ = lean_ctor_get(v___x_2466_, 0);
v_nextIdx_2468_ = lean_ctor_get(v___x_2466_, 1);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2470_ = v___x_2466_;
v_isShared_2471_ = v_isSharedCheck_2481_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_nextIdx_2468_);
lean_inc(v_lctx_2467_);
lean_dec(v___x_2466_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2481_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2472_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2472_, 0, v_a_2459_);
lean_ctor_set(v___x_2472_, 1, v_a_2462_);
lean_ctor_set(v___x_2472_, 2, v_type_2451_);
lean_ctor_set(v___x_2472_, 3, v_value_2452_);
lean_inc_ref(v___x_2472_);
v___x_2473_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2449_, v_lctx_2467_, v___x_2472_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 0, v___x_2473_);
v___x_2475_ = v___x_2470_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_nextIdx_2468_);
v___x_2475_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; lean_object* v___x_2478_; 
v___x_2476_ = lean_st_ref_set(v_a_2454_, v___x_2475_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2472_);
v___x_2478_ = v___x_2464_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2472_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec(v_value_2452_);
lean_dec_ref(v_type_2451_);
lean_dec(v_binderName_2450_);
v_a_2483_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2458_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2458_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl___boxed(lean_object* v_pu_2491_, lean_object* v_binderName_2492_, lean_object* v_type_2493_, lean_object* v_value_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
uint8_t v_pu_boxed_2500_; lean_object* v_res_2501_; 
v_pu_boxed_2500_ = lean_unbox(v_pu_2491_);
v_res_2501_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_boxed_2500_, v_binderName_2492_, v_type_2493_, v_value_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t v_pu_2505_, lean_object* v_binderName_2506_, lean_object* v_type_2507_, lean_object* v_params_2508_, lean_object* v_value_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2539_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref(v___x_2515_);
v___x_2517_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFunDecl___closed__1));
v___x_2518_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2506_, v___x_2517_, v_a_2511_);
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2521_ = v___x_2518_;
v_isShared_2522_ = v_isSharedCheck_2539_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2518_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2539_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; lean_object* v_lctx_2524_; lean_object* v_nextIdx_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2538_; 
v___x_2523_ = lean_st_ref_take(v_a_2511_);
v_lctx_2524_ = lean_ctor_get(v___x_2523_, 0);
v_nextIdx_2525_ = lean_ctor_get(v___x_2523_, 1);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2527_ = v___x_2523_;
v_isShared_2528_ = v_isSharedCheck_2538_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_nextIdx_2525_);
lean_inc(v_lctx_2524_);
lean_dec(v___x_2523_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2538_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2529_, 0, v_a_2516_);
lean_ctor_set(v___x_2529_, 1, v_a_2519_);
lean_ctor_set(v___x_2529_, 2, v_params_2508_);
lean_ctor_set(v___x_2529_, 3, v_type_2507_);
lean_ctor_set(v___x_2529_, 4, v_value_2509_);
lean_inc_ref(v___x_2529_);
v___x_2530_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2505_, v_lctx_2524_, v___x_2529_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v___x_2530_);
v___x_2532_ = v___x_2527_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2530_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_nextIdx_2525_);
v___x_2532_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2533_ = lean_st_ref_set(v_a_2511_, v___x_2532_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v___x_2529_);
v___x_2535_ = v___x_2521_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2529_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_dec_ref(v_value_2509_);
lean_dec_ref(v_params_2508_);
lean_dec_ref(v_type_2507_);
lean_dec(v_binderName_2506_);
v_a_2540_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2515_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2515_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl___boxed(lean_object* v_pu_2548_, lean_object* v_binderName_2549_, lean_object* v_type_2550_, lean_object* v_params_2551_, lean_object* v_value_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
uint8_t v_pu_boxed_2558_; lean_object* v_res_2559_; 
v_pu_boxed_2558_ = lean_unbox(v_pu_2548_);
v_res_2559_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_boxed_2558_, v_binderName_2549_, v_type_2550_, v_params_2551_, v_value_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
lean_dec(v_a_2556_);
lean_dec_ref(v_a_2555_);
lean_dec(v_a_2554_);
lean_dec_ref(v_a_2553_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(uint8_t v_pu_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v_a_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2566_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2567_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2566_, v_a_2562_);
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_a_2568_);
lean_dec_ref(v___x_2567_);
v___x_2569_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2570_ = lean_box(1);
v___x_2571_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2560_, v_a_2568_, v___x_2569_, v___x_2570_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased___boxed(lean_object* v_pu_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_){
_start:
{
uint8_t v_pu_boxed_2578_; lean_object* v_res_2579_; 
v_pu_boxed_2578_ = lean_unbox(v_pu_2572_);
v_res_2579_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_boxed_2578_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_);
lean_dec(v_a_2576_);
lean_dec_ref(v_a_2575_);
lean_dec(v_a_2574_);
lean_dec_ref(v_a_2573_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t v_pu_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2597_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2597_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2597_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v_fvarId_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2595_; 
v_fvarId_2591_ = lean_ctor_get(v_a_2587_, 0);
lean_inc(v_fvarId_2591_);
v___x_2592_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2592_, 0, v_fvarId_2591_);
v___x_2593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2593_, 0, v_a_2587_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___x_2593_);
v___x_2595_ = v___x_2589_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
v_a_2598_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2586_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2586_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased___boxed(lean_object* v_pu_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_){
_start:
{
uint8_t v_pu_boxed_2612_; lean_object* v_res_2613_; 
v_pu_boxed_2612_ = lean_unbox(v_pu_2606_);
v_res_2613_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_boxed_2612_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
lean_dec(v_a_2610_);
lean_dec_ref(v_a_2609_);
lean_dec(v_a_2608_);
lean_dec_ref(v_a_2607_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t v_pu_2614_, lean_object* v_p_2615_, lean_object* v_type_2616_, lean_object* v_a_2617_){
_start:
{
lean_object* v_fvarId_2619_; lean_object* v_binderName_2620_; lean_object* v_type_2621_; uint8_t v_borrow_2622_; size_t v___x_2623_; size_t v___x_2624_; uint8_t v___x_2625_; 
v_fvarId_2619_ = lean_ctor_get(v_p_2615_, 0);
v_binderName_2620_ = lean_ctor_get(v_p_2615_, 1);
v_type_2621_ = lean_ctor_get(v_p_2615_, 2);
v_borrow_2622_ = lean_ctor_get_uint8(v_p_2615_, sizeof(void*)*3);
v___x_2623_ = lean_ptr_addr(v_type_2616_);
v___x_2624_ = lean_ptr_addr(v_type_2621_);
v___x_2625_ = lean_usize_dec_eq(v___x_2623_, v___x_2624_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2645_; 
lean_inc(v_binderName_2620_);
lean_inc(v_fvarId_2619_);
v_isSharedCheck_2645_ = !lean_is_exclusive(v_p_2615_);
if (v_isSharedCheck_2645_ == 0)
{
lean_object* v_unused_2646_; lean_object* v_unused_2647_; lean_object* v_unused_2648_; 
v_unused_2646_ = lean_ctor_get(v_p_2615_, 2);
lean_dec(v_unused_2646_);
v_unused_2647_ = lean_ctor_get(v_p_2615_, 1);
lean_dec(v_unused_2647_);
v_unused_2648_ = lean_ctor_get(v_p_2615_, 0);
lean_dec(v_unused_2648_);
v___x_2627_ = v_p_2615_;
v_isShared_2628_ = v_isSharedCheck_2645_;
goto v_resetjp_2626_;
}
else
{
lean_dec(v_p_2615_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2645_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2629_; lean_object* v_lctx_2630_; lean_object* v_nextIdx_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2644_; 
v___x_2629_ = lean_st_ref_take(v_a_2617_);
v_lctx_2630_ = lean_ctor_get(v___x_2629_, 0);
v_nextIdx_2631_ = lean_ctor_get(v___x_2629_, 1);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2633_ = v___x_2629_;
v_isShared_2634_ = v_isSharedCheck_2644_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_nextIdx_2631_);
lean_inc(v_lctx_2630_);
lean_dec(v___x_2629_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2644_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v_p_2636_; 
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 2, v_type_2616_);
v_p_2636_ = v___x_2627_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_fvarId_2619_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_binderName_2620_);
lean_ctor_set(v_reuseFailAlloc_2643_, 2, v_type_2616_);
lean_ctor_set_uint8(v_reuseFailAlloc_2643_, sizeof(void*)*3, v_borrow_2622_);
v_p_2636_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
lean_object* v___x_2637_; lean_object* v___x_2639_; 
lean_inc_ref(v_p_2636_);
v___x_2637_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2614_, v_lctx_2630_, v_p_2636_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v___x_2637_);
v___x_2639_ = v___x_2633_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_nextIdx_2631_);
v___x_2639_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = lean_st_ref_set(v_a_2617_, v___x_2639_);
v___x_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2641_, 0, v_p_2636_);
return v___x_2641_;
}
}
}
}
}
else
{
lean_object* v___x_2649_; 
lean_dec_ref(v_type_2616_);
v___x_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2649_, 0, v_p_2615_);
return v___x_2649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg___boxed(lean_object* v_pu_2650_, lean_object* v_p_2651_, lean_object* v_type_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_){
_start:
{
uint8_t v_pu_boxed_2655_; lean_object* v_res_2656_; 
v_pu_boxed_2655_ = lean_unbox(v_pu_2650_);
v_res_2656_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_boxed_2655_, v_p_2651_, v_type_2652_, v_a_2653_);
lean_dec(v_a_2653_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(uint8_t v_pu_2657_, lean_object* v_p_2658_, lean_object* v_type_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_2657_, v_p_2658_, v_type_2659_, v_a_2661_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(lean_object* v_pu_2666_, lean_object* v_p_2667_, lean_object* v_type_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_){
_start:
{
uint8_t v_pu_boxed_2674_; lean_object* v_res_2675_; 
v_pu_boxed_2674_ = lean_unbox(v_pu_2666_);
v_res_2675_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(v_pu_boxed_2674_, v_p_2667_, v_type_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t v_pu_2676_, lean_object* v_p_2677_, uint8_t v_borrow_2678_, lean_object* v_a_2679_){
_start:
{
lean_object* v_fvarId_2681_; lean_object* v_binderName_2682_; lean_object* v_type_2683_; uint8_t v_borrow_2684_; 
v_fvarId_2681_ = lean_ctor_get(v_p_2677_, 0);
v_binderName_2682_ = lean_ctor_get(v_p_2677_, 1);
v_type_2683_ = lean_ctor_get(v_p_2677_, 2);
v_borrow_2684_ = lean_ctor_get_uint8(v_p_2677_, sizeof(void*)*3);
if (v_borrow_2678_ == 0)
{
if (v_borrow_2684_ == 0)
{
lean_object* v___x_2700_; 
v___x_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2700_, 0, v_p_2677_);
return v___x_2700_;
}
else
{
lean_inc_ref(v_type_2683_);
lean_inc(v_binderName_2682_);
lean_inc(v_fvarId_2681_);
lean_dec_ref(v_p_2677_);
goto v___jp_2685_;
}
}
else
{
if (v_borrow_2684_ == 0)
{
lean_inc_ref(v_type_2683_);
lean_inc(v_binderName_2682_);
lean_inc(v_fvarId_2681_);
lean_dec_ref(v_p_2677_);
goto v___jp_2685_;
}
else
{
lean_object* v___x_2701_; 
v___x_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2701_, 0, v_p_2677_);
return v___x_2701_;
}
}
v___jp_2685_:
{
lean_object* v___x_2686_; lean_object* v_lctx_2687_; lean_object* v_nextIdx_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2699_; 
v___x_2686_ = lean_st_ref_take(v_a_2679_);
v_lctx_2687_ = lean_ctor_get(v___x_2686_, 0);
v_nextIdx_2688_ = lean_ctor_get(v___x_2686_, 1);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2690_ = v___x_2686_;
v_isShared_2691_ = v_isSharedCheck_2699_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_nextIdx_2688_);
lean_inc(v_lctx_2687_);
lean_dec(v___x_2686_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2699_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v_p_2692_; lean_object* v___x_2693_; lean_object* v___x_2695_; 
v_p_2692_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_p_2692_, 0, v_fvarId_2681_);
lean_ctor_set(v_p_2692_, 1, v_binderName_2682_);
lean_ctor_set(v_p_2692_, 2, v_type_2683_);
lean_ctor_set_uint8(v_p_2692_, sizeof(void*)*3, v_borrow_2678_);
lean_inc_ref(v_p_2692_);
v___x_2693_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2676_, v_lctx_2687_, v_p_2692_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v___x_2693_);
v___x_2695_ = v___x_2690_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2693_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_nextIdx_2688_);
v___x_2695_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2696_ = lean_st_ref_set(v_a_2679_, v___x_2695_);
v___x_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2697_, 0, v_p_2692_);
return v___x_2697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg___boxed(lean_object* v_pu_2702_, lean_object* v_p_2703_, lean_object* v_borrow_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_){
_start:
{
uint8_t v_pu_boxed_2707_; uint8_t v_borrow_boxed_2708_; lean_object* v_res_2709_; 
v_pu_boxed_2707_ = lean_unbox(v_pu_2702_);
v_borrow_boxed_2708_ = lean_unbox(v_borrow_2704_);
v_res_2709_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_boxed_2707_, v_p_2703_, v_borrow_boxed_2708_, v_a_2705_);
lean_dec(v_a_2705_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(uint8_t v_pu_2710_, lean_object* v_p_2711_, uint8_t v_borrow_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_2710_, v_p_2711_, v_borrow_2712_, v_a_2714_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___boxed(lean_object* v_pu_2719_, lean_object* v_p_2720_, lean_object* v_borrow_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
uint8_t v_pu_boxed_2727_; uint8_t v_borrow_boxed_2728_; lean_object* v_res_2729_; 
v_pu_boxed_2727_ = lean_unbox(v_pu_2719_);
v_borrow_boxed_2728_ = lean_unbox(v_borrow_2721_);
v_res_2729_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(v_pu_boxed_2727_, v_p_2720_, v_borrow_boxed_2728_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t v_pu_2730_, lean_object* v_decl_2731_, lean_object* v_type_2732_, lean_object* v_value_2733_, lean_object* v_a_2734_){
_start:
{
lean_object* v_fvarId_2736_; lean_object* v_binderName_2737_; lean_object* v_type_2738_; lean_object* v_value_2739_; uint8_t v___y_2741_; size_t v___x_2767_; size_t v___x_2768_; uint8_t v___x_2769_; 
v_fvarId_2736_ = lean_ctor_get(v_decl_2731_, 0);
v_binderName_2737_ = lean_ctor_get(v_decl_2731_, 1);
v_type_2738_ = lean_ctor_get(v_decl_2731_, 2);
v_value_2739_ = lean_ctor_get(v_decl_2731_, 3);
v___x_2767_ = lean_ptr_addr(v_type_2732_);
v___x_2768_ = lean_ptr_addr(v_type_2738_);
v___x_2769_ = lean_usize_dec_eq(v___x_2767_, v___x_2768_);
if (v___x_2769_ == 0)
{
v___y_2741_ = v___x_2769_;
goto v___jp_2740_;
}
else
{
size_t v___x_2770_; size_t v___x_2771_; uint8_t v___x_2772_; 
v___x_2770_ = lean_ptr_addr(v_value_2733_);
v___x_2771_ = lean_ptr_addr(v_value_2739_);
v___x_2772_ = lean_usize_dec_eq(v___x_2770_, v___x_2771_);
v___y_2741_ = v___x_2772_;
goto v___jp_2740_;
}
v___jp_2740_:
{
if (v___y_2741_ == 0)
{
lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2761_; 
lean_inc(v_binderName_2737_);
lean_inc(v_fvarId_2736_);
v_isSharedCheck_2761_ = !lean_is_exclusive(v_decl_2731_);
if (v_isSharedCheck_2761_ == 0)
{
lean_object* v_unused_2762_; lean_object* v_unused_2763_; lean_object* v_unused_2764_; lean_object* v_unused_2765_; 
v_unused_2762_ = lean_ctor_get(v_decl_2731_, 3);
lean_dec(v_unused_2762_);
v_unused_2763_ = lean_ctor_get(v_decl_2731_, 2);
lean_dec(v_unused_2763_);
v_unused_2764_ = lean_ctor_get(v_decl_2731_, 1);
lean_dec(v_unused_2764_);
v_unused_2765_ = lean_ctor_get(v_decl_2731_, 0);
lean_dec(v_unused_2765_);
v___x_2743_ = v_decl_2731_;
v_isShared_2744_ = v_isSharedCheck_2761_;
goto v_resetjp_2742_;
}
else
{
lean_dec(v_decl_2731_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2761_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2745_; lean_object* v_lctx_2746_; lean_object* v_nextIdx_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2760_; 
v___x_2745_ = lean_st_ref_take(v_a_2734_);
v_lctx_2746_ = lean_ctor_get(v___x_2745_, 0);
v_nextIdx_2747_ = lean_ctor_get(v___x_2745_, 1);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2749_ = v___x_2745_;
v_isShared_2750_ = v_isSharedCheck_2760_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_nextIdx_2747_);
lean_inc(v_lctx_2746_);
lean_dec(v___x_2745_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2760_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v_decl_2752_; 
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 3, v_value_2733_);
lean_ctor_set(v___x_2743_, 2, v_type_2732_);
v_decl_2752_ = v___x_2743_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_fvarId_2736_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v_binderName_2737_);
lean_ctor_set(v_reuseFailAlloc_2759_, 2, v_type_2732_);
lean_ctor_set(v_reuseFailAlloc_2759_, 3, v_value_2733_);
v_decl_2752_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; lean_object* v___x_2755_; 
lean_inc_ref(v_decl_2752_);
v___x_2753_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2730_, v_lctx_2746_, v_decl_2752_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2753_);
v___x_2755_ = v___x_2749_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2753_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v_nextIdx_2747_);
v___x_2755_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = lean_st_ref_set(v_a_2734_, v___x_2755_);
v___x_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2757_, 0, v_decl_2752_);
return v___x_2757_;
}
}
}
}
}
else
{
lean_object* v___x_2766_; 
lean_dec(v_value_2733_);
lean_dec_ref(v_type_2732_);
v___x_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2766_, 0, v_decl_2731_);
return v___x_2766_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg___boxed(lean_object* v_pu_2773_, lean_object* v_decl_2774_, lean_object* v_type_2775_, lean_object* v_value_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
uint8_t v_pu_boxed_2779_; lean_object* v_res_2780_; 
v_pu_boxed_2779_ = lean_unbox(v_pu_2773_);
v_res_2780_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_boxed_2779_, v_decl_2774_, v_type_2775_, v_value_2776_, v_a_2777_);
lean_dec(v_a_2777_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(uint8_t v_pu_2781_, lean_object* v_decl_2782_, lean_object* v_type_2783_, lean_object* v_value_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2781_, v_decl_2782_, v_type_2783_, v_value_2784_, v_a_2786_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(lean_object* v_pu_2791_, lean_object* v_decl_2792_, lean_object* v_type_2793_, lean_object* v_value_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
uint8_t v_pu_boxed_2800_; lean_object* v_res_2801_; 
v_pu_boxed_2800_ = lean_unbox(v_pu_2791_);
v_res_2801_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(v_pu_boxed_2800_, v_decl_2792_, v_type_2793_, v_value_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2796_);
lean_dec_ref(v_a_2795_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t v_pu_2802_, lean_object* v_decl_2803_, lean_object* v_value_2804_, lean_object* v_a_2805_){
_start:
{
lean_object* v_type_2807_; lean_object* v___x_2808_; 
v_type_2807_ = lean_ctor_get(v_decl_2803_, 2);
lean_inc_ref(v_type_2807_);
v___x_2808_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2802_, v_decl_2803_, v_type_2807_, v_value_2804_, v_a_2805_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg___boxed(lean_object* v_pu_2809_, lean_object* v_decl_2810_, lean_object* v_value_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_){
_start:
{
uint8_t v_pu_boxed_2814_; lean_object* v_res_2815_; 
v_pu_boxed_2814_ = lean_unbox(v_pu_2809_);
v_res_2815_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_boxed_2814_, v_decl_2810_, v_value_2811_, v_a_2812_);
lean_dec(v_a_2812_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(uint8_t v_pu_2816_, lean_object* v_decl_2817_, lean_object* v_value_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_2816_, v_decl_2817_, v_value_2818_, v_a_2820_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___boxed(lean_object* v_pu_2825_, lean_object* v_decl_2826_, lean_object* v_value_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_){
_start:
{
uint8_t v_pu_boxed_2833_; lean_object* v_res_2834_; 
v_pu_boxed_2833_ = lean_unbox(v_pu_2825_);
v_res_2834_ = l_Lean_Compiler_LCNF_LetDecl_updateValue(v_pu_boxed_2833_, v_decl_2826_, v_value_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
lean_dec(v_a_2829_);
lean_dec_ref(v_a_2828_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t v_pu_2835_, lean_object* v_decl_2836_, lean_object* v_type_2837_, lean_object* v_params_2838_, lean_object* v_value_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v_fvarId_2842_; lean_object* v_binderName_2843_; lean_object* v_params_2844_; lean_object* v_type_2845_; lean_object* v_value_2846_; uint8_t v___y_2863_; size_t v___x_2868_; size_t v___x_2869_; uint8_t v___x_2870_; 
v_fvarId_2842_ = lean_ctor_get(v_decl_2836_, 0);
v_binderName_2843_ = lean_ctor_get(v_decl_2836_, 1);
v_params_2844_ = lean_ctor_get(v_decl_2836_, 2);
v_type_2845_ = lean_ctor_get(v_decl_2836_, 3);
v_value_2846_ = lean_ctor_get(v_decl_2836_, 4);
v___x_2868_ = lean_ptr_addr(v_type_2837_);
v___x_2869_ = lean_ptr_addr(v_type_2845_);
v___x_2870_ = lean_usize_dec_eq(v___x_2868_, v___x_2869_);
if (v___x_2870_ == 0)
{
v___y_2863_ = v___x_2870_;
goto v___jp_2862_;
}
else
{
size_t v___x_2871_; size_t v___x_2872_; uint8_t v___x_2873_; 
v___x_2871_ = lean_ptr_addr(v_params_2838_);
v___x_2872_ = lean_ptr_addr(v_params_2844_);
v___x_2873_ = lean_usize_dec_eq(v___x_2871_, v___x_2872_);
v___y_2863_ = v___x_2873_;
goto v___jp_2862_;
}
v___jp_2847_:
{
lean_object* v___x_2848_; lean_object* v_lctx_2849_; lean_object* v_nextIdx_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2861_; 
v___x_2848_ = lean_st_ref_take(v_a_2840_);
v_lctx_2849_ = lean_ctor_get(v___x_2848_, 0);
v_nextIdx_2850_ = lean_ctor_get(v___x_2848_, 1);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2852_ = v___x_2848_;
v_isShared_2853_ = v_isSharedCheck_2861_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_nextIdx_2850_);
lean_inc(v_lctx_2849_);
lean_dec(v___x_2848_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2861_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v_decl_2854_; lean_object* v___x_2855_; lean_object* v___x_2857_; 
v_decl_2854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_decl_2854_, 0, v_fvarId_2842_);
lean_ctor_set(v_decl_2854_, 1, v_binderName_2843_);
lean_ctor_set(v_decl_2854_, 2, v_params_2838_);
lean_ctor_set(v_decl_2854_, 3, v_type_2837_);
lean_ctor_set(v_decl_2854_, 4, v_value_2839_);
lean_inc_ref(v_decl_2854_);
v___x_2855_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2835_, v_lctx_2849_, v_decl_2854_);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 0, v___x_2855_);
v___x_2857_ = v___x_2852_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2855_);
lean_ctor_set(v_reuseFailAlloc_2860_, 1, v_nextIdx_2850_);
v___x_2857_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2858_ = lean_st_ref_set(v_a_2840_, v___x_2857_);
v___x_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2859_, 0, v_decl_2854_);
return v___x_2859_;
}
}
}
v___jp_2862_:
{
if (v___y_2863_ == 0)
{
lean_inc(v_binderName_2843_);
lean_inc(v_fvarId_2842_);
lean_dec_ref(v_decl_2836_);
goto v___jp_2847_;
}
else
{
size_t v___x_2864_; size_t v___x_2865_; uint8_t v___x_2866_; 
v___x_2864_ = lean_ptr_addr(v_value_2839_);
v___x_2865_ = lean_ptr_addr(v_value_2846_);
v___x_2866_ = lean_usize_dec_eq(v___x_2864_, v___x_2865_);
if (v___x_2866_ == 0)
{
lean_inc(v_binderName_2843_);
lean_inc(v_fvarId_2842_);
lean_dec_ref(v_decl_2836_);
goto v___jp_2847_;
}
else
{
lean_object* v___x_2867_; 
lean_dec_ref(v_value_2839_);
lean_dec_ref(v_params_2838_);
lean_dec_ref(v_type_2837_);
v___x_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2867_, 0, v_decl_2836_);
return v___x_2867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg___boxed(lean_object* v_pu_2874_, lean_object* v_decl_2875_, lean_object* v_type_2876_, lean_object* v_params_2877_, lean_object* v_value_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_){
_start:
{
uint8_t v_pu_boxed_2881_; lean_object* v_res_2882_; 
v_pu_boxed_2881_ = lean_unbox(v_pu_2874_);
v_res_2882_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_boxed_2881_, v_decl_2875_, v_type_2876_, v_params_2877_, v_value_2878_, v_a_2879_);
lean_dec(v_a_2879_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(uint8_t v_pu_2883_, lean_object* v_decl_2884_, lean_object* v_type_2885_, lean_object* v_params_2886_, lean_object* v_value_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2883_, v_decl_2884_, v_type_2885_, v_params_2886_, v_value_2887_, v_a_2889_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(lean_object* v_pu_2894_, lean_object* v_decl_2895_, lean_object* v_type_2896_, lean_object* v_params_2897_, lean_object* v_value_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_){
_start:
{
uint8_t v_pu_boxed_2904_; lean_object* v_res_2905_; 
v_pu_boxed_2904_ = lean_unbox(v_pu_2894_);
v_res_2905_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(v_pu_boxed_2904_, v_decl_2895_, v_type_2896_, v_params_2897_, v_value_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(uint8_t v_pu_2906_, lean_object* v_decl_2907_, lean_object* v_type_2908_, lean_object* v_value_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v_params_2912_; lean_object* v___x_2913_; 
v_params_2912_ = lean_ctor_get(v_decl_2907_, 2);
lean_inc_ref(v_params_2912_);
v___x_2913_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2906_, v_decl_2907_, v_type_2908_, v_params_2912_, v_value_2909_, v_a_2910_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg___boxed(lean_object* v_pu_2914_, lean_object* v_decl_2915_, lean_object* v_type_2916_, lean_object* v_value_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_){
_start:
{
uint8_t v_pu_boxed_2920_; lean_object* v_res_2921_; 
v_pu_boxed_2920_ = lean_unbox(v_pu_2914_);
v_res_2921_ = l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(v_pu_boxed_2920_, v_decl_2915_, v_type_2916_, v_value_2917_, v_a_2918_);
lean_dec(v_a_2918_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27(uint8_t v_pu_2922_, lean_object* v_decl_2923_, lean_object* v_type_2924_, lean_object* v_value_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_){
_start:
{
lean_object* v_params_2931_; lean_object* v___x_2932_; 
v_params_2931_ = lean_ctor_get(v_decl_2923_, 2);
lean_inc_ref(v_params_2931_);
v___x_2932_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2922_, v_decl_2923_, v_type_2924_, v_params_2931_, v_value_2925_, v_a_2927_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___boxed(lean_object* v_pu_2933_, lean_object* v_decl_2934_, lean_object* v_type_2935_, lean_object* v_value_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
uint8_t v_pu_boxed_2942_; lean_object* v_res_2943_; 
v_pu_boxed_2942_ = lean_unbox(v_pu_2933_);
v_res_2943_ = l_Lean_Compiler_LCNF_FunDecl_update_x27(v_pu_boxed_2942_, v_decl_2934_, v_type_2935_, v_value_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
lean_dec(v_a_2938_);
lean_dec_ref(v_a_2937_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(uint8_t v_pu_2944_, lean_object* v_decl_2945_, lean_object* v_value_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v_params_2949_; lean_object* v_type_2950_; lean_object* v___x_2951_; 
v_params_2949_ = lean_ctor_get(v_decl_2945_, 2);
lean_inc_ref(v_params_2949_);
v_type_2950_ = lean_ctor_get(v_decl_2945_, 3);
lean_inc_ref(v_type_2950_);
v___x_2951_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2944_, v_decl_2945_, v_type_2950_, v_params_2949_, v_value_2946_, v_a_2947_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg___boxed(lean_object* v_pu_2952_, lean_object* v_decl_2953_, lean_object* v_value_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_){
_start:
{
uint8_t v_pu_boxed_2957_; lean_object* v_res_2958_; 
v_pu_boxed_2957_ = lean_unbox(v_pu_2952_);
v_res_2958_ = l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(v_pu_boxed_2957_, v_decl_2953_, v_value_2954_, v_a_2955_);
lean_dec(v_a_2955_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue(uint8_t v_pu_2959_, lean_object* v_decl_2960_, lean_object* v_value_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v_params_2967_; lean_object* v_type_2968_; lean_object* v___x_2969_; 
v_params_2967_ = lean_ctor_get(v_decl_2960_, 2);
lean_inc_ref(v_params_2967_);
v_type_2968_ = lean_ctor_get(v_decl_2960_, 3);
lean_inc_ref(v_type_2968_);
v___x_2969_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2959_, v_decl_2960_, v_type_2968_, v_params_2967_, v_value_2961_, v_a_2963_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___boxed(lean_object* v_pu_2970_, lean_object* v_decl_2971_, lean_object* v_value_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_){
_start:
{
uint8_t v_pu_boxed_2978_; lean_object* v_res_2979_; 
v_pu_boxed_2978_ = lean_unbox(v_pu_2970_);
v_res_2979_ = l_Lean_Compiler_LCNF_FunDecl_updateValue(v_pu_boxed_2978_, v_decl_2971_, v_value_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
lean_dec(v_a_2976_);
lean_dec_ref(v_a_2975_);
lean_dec(v_a_2974_);
lean_dec_ref(v_a_2973_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0(uint8_t v_pu_2980_, lean_object* v_p_2981_, lean_object* v_inst_2982_, lean_object* v_____do__lift_2983_){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2984_ = lean_box(v_pu_2980_);
v___x_2985_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_2985_, 0, v___x_2984_);
lean_closure_set(v___x_2985_, 1, v_p_2981_);
lean_closure_set(v___x_2985_, 2, v_____do__lift_2983_);
v___x_2986_ = lean_apply_2(v_inst_2982_, lean_box(0), v___x_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed(lean_object* v_pu_2987_, lean_object* v_p_2988_, lean_object* v_inst_2989_, lean_object* v_____do__lift_2990_){
_start:
{
uint8_t v_pu_boxed_2991_; lean_object* v_res_2992_; 
v_pu_boxed_2991_ = lean_unbox(v_pu_2987_);
v_res_2992_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__0(v_pu_boxed_2991_, v_p_2988_, v_inst_2989_, v_____do__lift_2990_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1(uint8_t v_pu_2993_, uint8_t v_t_2994_, lean_object* v_type_2995_, lean_object* v_toPure_2996_, lean_object* v_____do__lift_2997_){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2993_, v_____do__lift_2997_, v_t_2994_, v_type_2995_);
v___x_2999_ = lean_apply_2(v_toPure_2996_, lean_box(0), v___x_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed(lean_object* v_pu_3000_, lean_object* v_t_3001_, lean_object* v_type_3002_, lean_object* v_toPure_3003_, lean_object* v_____do__lift_3004_){
_start:
{
uint8_t v_pu_boxed_3005_; uint8_t v_t_boxed_3006_; lean_object* v_res_3007_; 
v_pu_boxed_3005_ = lean_unbox(v_pu_3000_);
v_t_boxed_3006_ = lean_unbox(v_t_3001_);
v_res_3007_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__1(v_pu_boxed_3005_, v_t_boxed_3006_, v_type_3002_, v_toPure_3003_, v_____do__lift_3004_);
lean_dec_ref(v_____do__lift_3004_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg(uint8_t v_pu_3008_, uint8_t v_t_3009_, lean_object* v_inst_3010_, lean_object* v_inst_3011_, lean_object* v_inst_3012_, lean_object* v_p_3013_){
_start:
{
lean_object* v_toApplicative_3014_; lean_object* v_toBind_3015_; lean_object* v_type_3016_; lean_object* v_toPure_3017_; lean_object* v___x_3018_; lean_object* v___f_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___f_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_toApplicative_3014_ = lean_ctor_get(v_inst_3011_, 0);
lean_inc_ref(v_toApplicative_3014_);
v_toBind_3015_ = lean_ctor_get(v_inst_3011_, 1);
lean_inc(v_toBind_3015_);
lean_dec_ref(v_inst_3011_);
v_type_3016_ = lean_ctor_get(v_p_3013_, 2);
lean_inc_ref(v_type_3016_);
v_toPure_3017_ = lean_ctor_get(v_toApplicative_3014_, 1);
lean_inc(v_toPure_3017_);
lean_dec_ref(v_toApplicative_3014_);
v___x_3018_ = lean_box(v_pu_3008_);
v___f_3019_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3019_, 0, v___x_3018_);
lean_closure_set(v___f_3019_, 1, v_p_3013_);
lean_closure_set(v___f_3019_, 2, v_inst_3010_);
v___x_3020_ = lean_box(v_pu_3008_);
v___x_3021_ = lean_box(v_t_3009_);
v___f_3022_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3022_, 0, v___x_3020_);
lean_closure_set(v___f_3022_, 1, v___x_3021_);
lean_closure_set(v___f_3022_, 2, v_type_3016_);
lean_closure_set(v___f_3022_, 3, v_toPure_3017_);
lean_inc(v_toBind_3015_);
v___x_3023_ = lean_apply_4(v_toBind_3015_, lean_box(0), lean_box(0), v_inst_3012_, v___f_3022_);
v___x_3024_ = lean_apply_4(v_toBind_3015_, lean_box(0), lean_box(0), v___x_3023_, v___f_3019_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___boxed(lean_object* v_pu_3025_, lean_object* v_t_3026_, lean_object* v_inst_3027_, lean_object* v_inst_3028_, lean_object* v_inst_3029_, lean_object* v_p_3030_){
_start:
{
uint8_t v_pu_boxed_3031_; uint8_t v_t_boxed_3032_; lean_object* v_res_3033_; 
v_pu_boxed_3031_ = lean_unbox(v_pu_3025_);
v_t_boxed_3032_ = lean_unbox(v_t_3026_);
v_res_3033_ = l_Lean_Compiler_LCNF_normParam___redArg(v_pu_boxed_3031_, v_t_boxed_3032_, v_inst_3027_, v_inst_3028_, v_inst_3029_, v_p_3030_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam(lean_object* v_m_3034_, uint8_t v_pu_3035_, uint8_t v_t_3036_, lean_object* v_inst_3037_, lean_object* v_inst_3038_, lean_object* v_inst_3039_, lean_object* v_p_3040_){
_start:
{
lean_object* v_toApplicative_3041_; lean_object* v_toBind_3042_; lean_object* v_type_3043_; lean_object* v_toPure_3044_; lean_object* v___x_3045_; lean_object* v___f_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___f_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v_toApplicative_3041_ = lean_ctor_get(v_inst_3038_, 0);
lean_inc_ref(v_toApplicative_3041_);
v_toBind_3042_ = lean_ctor_get(v_inst_3038_, 1);
lean_inc(v_toBind_3042_);
lean_dec_ref(v_inst_3038_);
v_type_3043_ = lean_ctor_get(v_p_3040_, 2);
lean_inc_ref(v_type_3043_);
v_toPure_3044_ = lean_ctor_get(v_toApplicative_3041_, 1);
lean_inc(v_toPure_3044_);
lean_dec_ref(v_toApplicative_3041_);
v___x_3045_ = lean_box(v_pu_3035_);
v___f_3046_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3046_, 0, v___x_3045_);
lean_closure_set(v___f_3046_, 1, v_p_3040_);
lean_closure_set(v___f_3046_, 2, v_inst_3037_);
v___x_3047_ = lean_box(v_pu_3035_);
v___x_3048_ = lean_box(v_t_3036_);
v___f_3049_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3049_, 0, v___x_3047_);
lean_closure_set(v___f_3049_, 1, v___x_3048_);
lean_closure_set(v___f_3049_, 2, v_type_3043_);
lean_closure_set(v___f_3049_, 3, v_toPure_3044_);
lean_inc(v_toBind_3042_);
v___x_3050_ = lean_apply_4(v_toBind_3042_, lean_box(0), lean_box(0), v_inst_3039_, v___f_3049_);
v___x_3051_ = lean_apply_4(v_toBind_3042_, lean_box(0), lean_box(0), v___x_3050_, v___f_3046_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___boxed(lean_object* v_m_3052_, lean_object* v_pu_3053_, lean_object* v_t_3054_, lean_object* v_inst_3055_, lean_object* v_inst_3056_, lean_object* v_inst_3057_, lean_object* v_p_3058_){
_start:
{
uint8_t v_pu_boxed_3059_; uint8_t v_t_boxed_3060_; lean_object* v_res_3061_; 
v_pu_boxed_3059_ = lean_unbox(v_pu_3053_);
v_t_boxed_3060_ = lean_unbox(v_t_3054_);
v_res_3061_ = l_Lean_Compiler_LCNF_normParam(v_m_3052_, v_pu_boxed_3059_, v_t_boxed_3060_, v_inst_3055_, v_inst_3056_, v_inst_3057_, v_p_3058_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg(uint8_t v_pu_3062_, uint8_t v_t_3063_, lean_object* v_inst_3064_, lean_object* v_inst_3065_, lean_object* v_inst_3066_, lean_object* v_ps_3067_){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3068_ = lean_box(v_pu_3062_);
v___x_3069_ = lean_box(v_t_3063_);
lean_inc_ref(v_inst_3065_);
v___x_3070_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___boxed), 7, 6);
lean_closure_set(v___x_3070_, 0, lean_box(0));
lean_closure_set(v___x_3070_, 1, v___x_3068_);
lean_closure_set(v___x_3070_, 2, v___x_3069_);
lean_closure_set(v___x_3070_, 3, v_inst_3064_);
lean_closure_set(v___x_3070_, 4, v_inst_3065_);
lean_closure_set(v___x_3070_, 5, v_inst_3066_);
v___x_3071_ = lean_unsigned_to_nat(0u);
v___x_3072_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_3065_, v___x_3070_, v___x_3071_, v_ps_3067_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg___boxed(lean_object* v_pu_3073_, lean_object* v_t_3074_, lean_object* v_inst_3075_, lean_object* v_inst_3076_, lean_object* v_inst_3077_, lean_object* v_ps_3078_){
_start:
{
uint8_t v_pu_boxed_3079_; uint8_t v_t_boxed_3080_; lean_object* v_res_3081_; 
v_pu_boxed_3079_ = lean_unbox(v_pu_3073_);
v_t_boxed_3080_ = lean_unbox(v_t_3074_);
v_res_3081_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_boxed_3079_, v_t_boxed_3080_, v_inst_3075_, v_inst_3076_, v_inst_3077_, v_ps_3078_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams(lean_object* v_m_3082_, uint8_t v_pu_3083_, uint8_t v_t_3084_, lean_object* v_inst_3085_, lean_object* v_inst_3086_, lean_object* v_inst_3087_, lean_object* v_ps_3088_){
_start:
{
lean_object* v___x_3089_; 
v___x_3089_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_3083_, v_t_3084_, v_inst_3085_, v_inst_3086_, v_inst_3087_, v_ps_3088_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___boxed(lean_object* v_m_3090_, lean_object* v_pu_3091_, lean_object* v_t_3092_, lean_object* v_inst_3093_, lean_object* v_inst_3094_, lean_object* v_inst_3095_, lean_object* v_ps_3096_){
_start:
{
uint8_t v_pu_boxed_3097_; uint8_t v_t_boxed_3098_; lean_object* v_res_3099_; 
v_pu_boxed_3097_ = lean_unbox(v_pu_3091_);
v_t_boxed_3098_ = lean_unbox(v_t_3092_);
v_res_3099_ = l_Lean_Compiler_LCNF_normParams(v_m_3090_, v_pu_boxed_3097_, v_t_boxed_3098_, v_inst_3093_, v_inst_3094_, v_inst_3095_, v_ps_3096_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(uint8_t v_pu_3100_, lean_object* v_decl_3101_, lean_object* v_____do__lift_3102_, lean_object* v_inst_3103_, lean_object* v_____do__lift_3104_){
_start:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3105_ = lean_box(v_pu_3100_);
v___x_3106_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_3106_, 0, v___x_3105_);
lean_closure_set(v___x_3106_, 1, v_decl_3101_);
lean_closure_set(v___x_3106_, 2, v_____do__lift_3102_);
lean_closure_set(v___x_3106_, 3, v_____do__lift_3104_);
v___x_3107_ = lean_apply_2(v_inst_3103_, lean_box(0), v___x_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed(lean_object* v_pu_3108_, lean_object* v_decl_3109_, lean_object* v_____do__lift_3110_, lean_object* v_inst_3111_, lean_object* v_____do__lift_3112_){
_start:
{
uint8_t v_pu_boxed_3113_; lean_object* v_res_3114_; 
v_pu_boxed_3113_ = lean_unbox(v_pu_3108_);
v_res_3114_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(v_pu_boxed_3113_, v_decl_3109_, v_____do__lift_3110_, v_inst_3111_, v_____do__lift_3112_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(uint8_t v_pu_3115_, lean_object* v_value_3116_, uint8_t v_t_3117_, lean_object* v_toPure_3118_, lean_object* v_____do__lift_3119_){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3120_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3115_, v_____do__lift_3119_, v_value_3116_, v_t_3117_);
v___x_3121_ = lean_apply_2(v_toPure_3118_, lean_box(0), v___x_3120_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed(lean_object* v_pu_3122_, lean_object* v_value_3123_, lean_object* v_t_3124_, lean_object* v_toPure_3125_, lean_object* v_____do__lift_3126_){
_start:
{
uint8_t v_pu_boxed_3127_; uint8_t v_t_boxed_3128_; lean_object* v_res_3129_; 
v_pu_boxed_3127_ = lean_unbox(v_pu_3122_);
v_t_boxed_3128_ = lean_unbox(v_t_3124_);
v_res_3129_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(v_pu_boxed_3127_, v_value_3123_, v_t_boxed_3128_, v_toPure_3125_, v_____do__lift_3126_);
lean_dec_ref(v_____do__lift_3126_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(uint8_t v_pu_3130_, lean_object* v_decl_3131_, lean_object* v_inst_3132_, lean_object* v_value_3133_, uint8_t v_t_3134_, lean_object* v_toPure_3135_, lean_object* v_toBind_3136_, lean_object* v_inst_3137_, lean_object* v_____do__lift_3138_){
_start:
{
lean_object* v___x_3139_; lean_object* v___f_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___f_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3139_ = lean_box(v_pu_3130_);
v___f_3140_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3140_, 0, v___x_3139_);
lean_closure_set(v___f_3140_, 1, v_decl_3131_);
lean_closure_set(v___f_3140_, 2, v_____do__lift_3138_);
lean_closure_set(v___f_3140_, 3, v_inst_3132_);
v___x_3141_ = lean_box(v_pu_3130_);
v___x_3142_ = lean_box(v_t_3134_);
v___f_3143_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3143_, 0, v___x_3141_);
lean_closure_set(v___f_3143_, 1, v_value_3133_);
lean_closure_set(v___f_3143_, 2, v___x_3142_);
lean_closure_set(v___f_3143_, 3, v_toPure_3135_);
lean_inc(v_toBind_3136_);
v___x_3144_ = lean_apply_4(v_toBind_3136_, lean_box(0), lean_box(0), v_inst_3137_, v___f_3143_);
v___x_3145_ = lean_apply_4(v_toBind_3136_, lean_box(0), lean_box(0), v___x_3144_, v___f_3140_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed(lean_object* v_pu_3146_, lean_object* v_decl_3147_, lean_object* v_inst_3148_, lean_object* v_value_3149_, lean_object* v_t_3150_, lean_object* v_toPure_3151_, lean_object* v_toBind_3152_, lean_object* v_inst_3153_, lean_object* v_____do__lift_3154_){
_start:
{
uint8_t v_pu_boxed_3155_; uint8_t v_t_boxed_3156_; lean_object* v_res_3157_; 
v_pu_boxed_3155_ = lean_unbox(v_pu_3146_);
v_t_boxed_3156_ = lean_unbox(v_t_3150_);
v_res_3157_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(v_pu_boxed_3155_, v_decl_3147_, v_inst_3148_, v_value_3149_, v_t_boxed_3156_, v_toPure_3151_, v_toBind_3152_, v_inst_3153_, v_____do__lift_3154_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg(uint8_t v_pu_3158_, uint8_t v_t_3159_, lean_object* v_inst_3160_, lean_object* v_inst_3161_, lean_object* v_inst_3162_, lean_object* v_decl_3163_){
_start:
{
lean_object* v_toApplicative_3164_; lean_object* v_toBind_3165_; lean_object* v_type_3166_; lean_object* v_value_3167_; lean_object* v_toPure_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___f_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___f_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v_toApplicative_3164_ = lean_ctor_get(v_inst_3161_, 0);
lean_inc_ref(v_toApplicative_3164_);
v_toBind_3165_ = lean_ctor_get(v_inst_3161_, 1);
lean_inc(v_toBind_3165_);
lean_dec_ref(v_inst_3161_);
v_type_3166_ = lean_ctor_get(v_decl_3163_, 2);
lean_inc_ref(v_type_3166_);
v_value_3167_ = lean_ctor_get(v_decl_3163_, 3);
lean_inc(v_value_3167_);
v_toPure_3168_ = lean_ctor_get(v_toApplicative_3164_, 1);
lean_inc(v_toPure_3168_);
lean_dec_ref(v_toApplicative_3164_);
v___x_3169_ = lean_box(v_pu_3158_);
v___x_3170_ = lean_box(v_t_3159_);
lean_inc(v_inst_3162_);
lean_inc(v_toBind_3165_);
lean_inc(v_toPure_3168_);
v___f_3171_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_3171_, 0, v___x_3169_);
lean_closure_set(v___f_3171_, 1, v_decl_3163_);
lean_closure_set(v___f_3171_, 2, v_inst_3160_);
lean_closure_set(v___f_3171_, 3, v_value_3167_);
lean_closure_set(v___f_3171_, 4, v___x_3170_);
lean_closure_set(v___f_3171_, 5, v_toPure_3168_);
lean_closure_set(v___f_3171_, 6, v_toBind_3165_);
lean_closure_set(v___f_3171_, 7, v_inst_3162_);
v___x_3172_ = lean_box(v_pu_3158_);
v___x_3173_ = lean_box(v_t_3159_);
v___f_3174_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3174_, 0, v___x_3172_);
lean_closure_set(v___f_3174_, 1, v___x_3173_);
lean_closure_set(v___f_3174_, 2, v_type_3166_);
lean_closure_set(v___f_3174_, 3, v_toPure_3168_);
lean_inc(v_toBind_3165_);
v___x_3175_ = lean_apply_4(v_toBind_3165_, lean_box(0), lean_box(0), v_inst_3162_, v___f_3174_);
v___x_3176_ = lean_apply_4(v_toBind_3165_, lean_box(0), lean_box(0), v___x_3175_, v___f_3171_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___boxed(lean_object* v_pu_3177_, lean_object* v_t_3178_, lean_object* v_inst_3179_, lean_object* v_inst_3180_, lean_object* v_inst_3181_, lean_object* v_decl_3182_){
_start:
{
uint8_t v_pu_boxed_3183_; uint8_t v_t_boxed_3184_; lean_object* v_res_3185_; 
v_pu_boxed_3183_ = lean_unbox(v_pu_3177_);
v_t_boxed_3184_ = lean_unbox(v_t_3178_);
v_res_3185_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_boxed_3183_, v_t_boxed_3184_, v_inst_3179_, v_inst_3180_, v_inst_3181_, v_decl_3182_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl(lean_object* v_m_3186_, uint8_t v_pu_3187_, uint8_t v_t_3188_, lean_object* v_inst_3189_, lean_object* v_inst_3190_, lean_object* v_inst_3191_, lean_object* v_decl_3192_){
_start:
{
lean_object* v___x_3193_; 
v___x_3193_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_3187_, v_t_3188_, v_inst_3189_, v_inst_3190_, v_inst_3191_, v_decl_3192_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___boxed(lean_object* v_m_3194_, lean_object* v_pu_3195_, lean_object* v_t_3196_, lean_object* v_inst_3197_, lean_object* v_inst_3198_, lean_object* v_inst_3199_, lean_object* v_decl_3200_){
_start:
{
uint8_t v_pu_boxed_3201_; uint8_t v_t_boxed_3202_; lean_object* v_res_3203_; 
v_pu_boxed_3201_ = lean_unbox(v_pu_3195_);
v_t_boxed_3202_ = lean_unbox(v_t_3196_);
v_res_3203_ = l_Lean_Compiler_LCNF_normLetDecl(v_m_3194_, v_pu_boxed_3201_, v_t_boxed_3202_, v_inst_3197_, v_inst_3198_, v_inst_3199_, v_decl_3200_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(uint8_t v_pu_3204_, uint8_t v_t_3205_){
_start:
{
lean_object* v___x_3206_; lean_object* v_toApplicative_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3265_; 
v___x_3206_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_3207_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3265_ == 0)
{
lean_object* v_unused_3266_; 
v_unused_3266_ = lean_ctor_get(v___x_3206_, 1);
lean_dec(v_unused_3266_);
v___x_3209_ = v___x_3206_;
v_isShared_3210_ = v_isSharedCheck_3265_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_toApplicative_3207_);
lean_dec(v___x_3206_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3265_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v_toFunctor_3211_; lean_object* v_toSeq_3212_; lean_object* v_toSeqLeft_3213_; lean_object* v_toSeqRight_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3263_; 
v_toFunctor_3211_ = lean_ctor_get(v_toApplicative_3207_, 0);
v_toSeq_3212_ = lean_ctor_get(v_toApplicative_3207_, 2);
v_toSeqLeft_3213_ = lean_ctor_get(v_toApplicative_3207_, 3);
v_toSeqRight_3214_ = lean_ctor_get(v_toApplicative_3207_, 4);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_toApplicative_3207_);
if (v_isSharedCheck_3263_ == 0)
{
lean_object* v_unused_3264_; 
v_unused_3264_ = lean_ctor_get(v_toApplicative_3207_, 1);
lean_dec(v_unused_3264_);
v___x_3216_ = v_toApplicative_3207_;
v_isShared_3217_ = v_isSharedCheck_3263_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_toSeqRight_3214_);
lean_inc(v_toSeqLeft_3213_);
lean_inc(v_toSeq_3212_);
lean_inc(v_toFunctor_3211_);
lean_dec(v_toApplicative_3207_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3263_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___f_3218_; lean_object* v___f_3219_; lean_object* v___f_3220_; lean_object* v___f_3221_; lean_object* v___x_3222_; lean_object* v___f_3223_; lean_object* v___f_3224_; lean_object* v___f_3225_; lean_object* v___x_3227_; 
v___f_3218_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_3219_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref(v_toFunctor_3211_);
v___f_3220_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3220_, 0, v_toFunctor_3211_);
v___f_3221_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3221_, 0, v_toFunctor_3211_);
v___x_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___f_3220_);
lean_ctor_set(v___x_3222_, 1, v___f_3221_);
v___f_3223_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3223_, 0, v_toSeqRight_3214_);
v___f_3224_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3224_, 0, v_toSeqLeft_3213_);
v___f_3225_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3225_, 0, v_toSeq_3212_);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 4, v___f_3223_);
lean_ctor_set(v___x_3216_, 3, v___f_3224_);
lean_ctor_set(v___x_3216_, 2, v___f_3225_);
lean_ctor_set(v___x_3216_, 1, v___f_3218_);
lean_ctor_set(v___x_3216_, 0, v___x_3222_);
v___x_3227_ = v___x_3216_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3222_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v___f_3218_);
lean_ctor_set(v_reuseFailAlloc_3262_, 2, v___f_3225_);
lean_ctor_set(v_reuseFailAlloc_3262_, 3, v___f_3224_);
lean_ctor_set(v_reuseFailAlloc_3262_, 4, v___f_3223_);
v___x_3227_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
lean_object* v___x_3229_; 
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 1, v___f_3219_);
lean_ctor_set(v___x_3209_, 0, v___x_3227_);
v___x_3229_ = v___x_3209_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3227_);
lean_ctor_set(v_reuseFailAlloc_3261_, 1, v___f_3219_);
v___x_3229_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
lean_object* v___x_3230_; lean_object* v_toApplicative_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3259_; 
v___x_3230_ = l_ReaderT_instMonad___redArg(v___x_3229_);
v_toApplicative_3231_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3259_ == 0)
{
lean_object* v_unused_3260_; 
v_unused_3260_ = lean_ctor_get(v___x_3230_, 1);
lean_dec(v_unused_3260_);
v___x_3233_ = v___x_3230_;
v_isShared_3234_ = v_isSharedCheck_3259_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_toApplicative_3231_);
lean_dec(v___x_3230_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3259_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v_toFunctor_3235_; lean_object* v_toSeq_3236_; lean_object* v_toSeqLeft_3237_; lean_object* v_toSeqRight_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3257_; 
v_toFunctor_3235_ = lean_ctor_get(v_toApplicative_3231_, 0);
v_toSeq_3236_ = lean_ctor_get(v_toApplicative_3231_, 2);
v_toSeqLeft_3237_ = lean_ctor_get(v_toApplicative_3231_, 3);
v_toSeqRight_3238_ = lean_ctor_get(v_toApplicative_3231_, 4);
v_isSharedCheck_3257_ = !lean_is_exclusive(v_toApplicative_3231_);
if (v_isSharedCheck_3257_ == 0)
{
lean_object* v_unused_3258_; 
v_unused_3258_ = lean_ctor_get(v_toApplicative_3231_, 1);
lean_dec(v_unused_3258_);
v___x_3240_ = v_toApplicative_3231_;
v_isShared_3241_ = v_isSharedCheck_3257_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_toSeqRight_3238_);
lean_inc(v_toSeqLeft_3237_);
lean_inc(v_toSeq_3236_);
lean_inc(v_toFunctor_3235_);
lean_dec(v_toApplicative_3231_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3257_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___f_3242_; lean_object* v___f_3243_; lean_object* v___f_3244_; lean_object* v___f_3245_; lean_object* v___x_3246_; lean_object* v___f_3247_; lean_object* v___f_3248_; lean_object* v___f_3249_; lean_object* v___x_3251_; 
v___f_3242_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_3243_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_3235_);
v___f_3244_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3244_, 0, v_toFunctor_3235_);
v___f_3245_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3245_, 0, v_toFunctor_3235_);
v___x_3246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___f_3244_);
lean_ctor_set(v___x_3246_, 1, v___f_3245_);
v___f_3247_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3247_, 0, v_toSeqRight_3238_);
v___f_3248_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3248_, 0, v_toSeqLeft_3237_);
v___f_3249_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3249_, 0, v_toSeq_3236_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 4, v___f_3247_);
lean_ctor_set(v___x_3240_, 3, v___f_3248_);
lean_ctor_set(v___x_3240_, 2, v___f_3249_);
lean_ctor_set(v___x_3240_, 1, v___f_3242_);
lean_ctor_set(v___x_3240_, 0, v___x_3246_);
v___x_3251_ = v___x_3240_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3246_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v___f_3242_);
lean_ctor_set(v_reuseFailAlloc_3256_, 2, v___f_3249_);
lean_ctor_set(v_reuseFailAlloc_3256_, 3, v___f_3248_);
lean_ctor_set(v_reuseFailAlloc_3256_, 4, v___f_3247_);
v___x_3251_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
lean_object* v___x_3253_; 
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 1, v___f_3243_);
lean_ctor_set(v___x_3233_, 0, v___x_3251_);
v___x_3253_ = v___x_3233_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3251_);
lean_ctor_set(v_reuseFailAlloc_3255_, 1, v___f_3243_);
v___x_3253_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
lean_object* v___x_3254_; 
v___x_3254_ = lean_alloc_closure((void*)(l_ReaderT_read), 4, 3);
lean_closure_set(v___x_3254_, 0, lean_box(0));
lean_closure_set(v___x_3254_, 1, lean_box(0));
lean_closure_set(v___x_3254_, 2, v___x_3253_);
return v___x_3254_;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___boxed(lean_object* v_pu_3267_, lean_object* v_t_3268_){
_start:
{
uint8_t v_pu_boxed_3269_; uint8_t v_t_boxed_3270_; lean_object* v_res_3271_; 
v_pu_boxed_3269_ = lean_unbox(v_pu_3267_);
v_t_boxed_3270_ = lean_unbox(v_t_3268_);
v_res_3271_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(v_pu_boxed_3269_, v_t_boxed_3270_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg(uint8_t v_pu_3272_, lean_object* v_inst_3273_, lean_object* v_result_3274_, lean_object* v_x_3275_){
_start:
{
if (lean_obj_tag(v_result_3274_) == 0)
{
lean_object* v_fvarId_3276_; lean_object* v___x_3277_; 
lean_dec(v_inst_3273_);
v_fvarId_3276_ = lean_ctor_get(v_result_3274_, 0);
lean_inc(v_fvarId_3276_);
lean_dec_ref(v_result_3274_);
v___x_3277_ = lean_apply_1(v_x_3275_, v_fvarId_3276_);
return v___x_3277_;
}
else
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
lean_dec(v_x_3275_);
v___x_3278_ = lean_box(v_pu_3272_);
v___x_3279_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3279_, 0, v___x_3278_);
v___x_3280_ = lean_apply_2(v_inst_3273_, lean_box(0), v___x_3279_);
return v___x_3280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg___boxed(lean_object* v_pu_3281_, lean_object* v_inst_3282_, lean_object* v_result_3283_, lean_object* v_x_3284_){
_start:
{
uint8_t v_pu_boxed_3285_; lean_object* v_res_3286_; 
v_pu_boxed_3285_ = lean_unbox(v_pu_3281_);
v_res_3286_ = l_Lean_Compiler_LCNF_withNormFVarResult___redArg(v_pu_boxed_3285_, v_inst_3282_, v_result_3283_, v_x_3284_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult(lean_object* v_m_3287_, uint8_t v_pu_3288_, lean_object* v_inst_3289_, lean_object* v_inst_3290_, lean_object* v_result_3291_, lean_object* v_x_3292_){
_start:
{
if (lean_obj_tag(v_result_3291_) == 0)
{
lean_object* v_fvarId_3293_; lean_object* v___x_3294_; 
lean_dec(v_inst_3289_);
v_fvarId_3293_ = lean_ctor_get(v_result_3291_, 0);
lean_inc(v_fvarId_3293_);
lean_dec_ref(v_result_3291_);
v___x_3294_ = lean_apply_1(v_x_3292_, v_fvarId_3293_);
return v___x_3294_;
}
else
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
lean_dec(v_x_3292_);
v___x_3295_ = lean_box(v_pu_3288_);
v___x_3296_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3296_, 0, v___x_3295_);
v___x_3297_ = lean_apply_2(v_inst_3289_, lean_box(0), v___x_3296_);
return v___x_3297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___boxed(lean_object* v_m_3298_, lean_object* v_pu_3299_, lean_object* v_inst_3300_, lean_object* v_inst_3301_, lean_object* v_result_3302_, lean_object* v_x_3303_){
_start:
{
uint8_t v_pu_boxed_3304_; lean_object* v_res_3305_; 
v_pu_boxed_3304_ = lean_unbox(v_pu_3299_);
v_res_3305_ = l_Lean_Compiler_LCNF_withNormFVarResult(v_m_3298_, v_pu_boxed_3304_, v_inst_3300_, v_inst_3301_, v_result_3302_, v_x_3303_);
lean_dec_ref(v_inst_3301_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(uint8_t v_pu_3306_, uint8_t v_t_3307_, lean_object* v_args_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3311_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_3306_, v___y_3309_, v_args_3308_, v_t_3307_);
v___x_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg___boxed(lean_object* v_pu_3313_, lean_object* v_t_3314_, lean_object* v_args_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
uint8_t v_pu_boxed_3318_; uint8_t v_t_boxed_3319_; lean_object* v_res_3320_; 
v_pu_boxed_3318_ = lean_unbox(v_pu_3313_);
v_t_boxed_3319_ = lean_unbox(v_t_3314_);
v_res_3320_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_boxed_3318_, v_t_boxed_3319_, v_args_3315_, v___y_3316_);
lean_dec_ref(v___y_3316_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(uint8_t v_pu_3321_, uint8_t v_t_3322_, lean_object* v_i_3323_, lean_object* v_as_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
lean_object* v___x_3328_; uint8_t v___x_3329_; 
v___x_3328_ = lean_array_get_size(v_as_3324_);
v___x_3329_ = lean_nat_dec_lt(v_i_3323_, v___x_3328_);
if (v___x_3329_ == 0)
{
lean_object* v___x_3330_; 
lean_dec(v_i_3323_);
v___x_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3330_, 0, v_as_3324_);
return v___x_3330_;
}
else
{
lean_object* v_a_3331_; lean_object* v_type_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v_a_3331_ = lean_array_fget_borrowed(v_as_3324_, v_i_3323_);
v_type_3332_ = lean_ctor_get(v_a_3331_, 2);
lean_inc_ref(v_type_3332_);
v___x_3333_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3321_, v___y_3325_, v_t_3322_, v_type_3332_);
lean_inc(v_a_3331_);
v___x_3334_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_3321_, v_a_3331_, v___x_3333_, v___y_3326_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; size_t v___x_3336_; size_t v___x_3337_; uint8_t v___x_3338_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref(v___x_3334_);
v___x_3336_ = lean_ptr_addr(v_a_3331_);
v___x_3337_ = lean_ptr_addr(v_a_3335_);
v___x_3338_ = lean_usize_dec_eq(v___x_3336_, v___x_3337_);
if (v___x_3338_ == 0)
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3339_ = lean_unsigned_to_nat(1u);
v___x_3340_ = lean_nat_add(v_i_3323_, v___x_3339_);
v___x_3341_ = lean_array_fset(v_as_3324_, v_i_3323_, v_a_3335_);
lean_dec(v_i_3323_);
v_i_3323_ = v___x_3340_;
v_as_3324_ = v___x_3341_;
goto _start;
}
else
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
lean_dec(v_a_3335_);
v___x_3343_ = lean_unsigned_to_nat(1u);
v___x_3344_ = lean_nat_add(v_i_3323_, v___x_3343_);
lean_dec(v_i_3323_);
v_i_3323_ = v___x_3344_;
goto _start;
}
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
lean_dec_ref(v_as_3324_);
lean_dec(v_i_3323_);
v_a_3346_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3334_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3334_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg___boxed(lean_object* v_pu_3354_, lean_object* v_t_3355_, lean_object* v_i_3356_, lean_object* v_as_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
uint8_t v_pu_boxed_3361_; uint8_t v_t_boxed_3362_; lean_object* v_res_3363_; 
v_pu_boxed_3361_ = lean_unbox(v_pu_3354_);
v_t_boxed_3362_ = lean_unbox(v_t_3355_);
v_res_3363_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_boxed_3361_, v_t_boxed_3362_, v_i_3356_, v_as_3357_, v___y_3358_, v___y_3359_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(uint8_t v_pu_3364_, uint8_t v_t_3365_, lean_object* v_ps_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3373_ = lean_unsigned_to_nat(0u);
v___x_3374_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_3364_, v_t_3365_, v___x_3373_, v_ps_3366_, v___y_3367_, v___y_3369_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg___boxed(lean_object* v_pu_3375_, lean_object* v_t_3376_, lean_object* v_ps_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
uint8_t v_pu_boxed_3384_; uint8_t v_t_boxed_3385_; lean_object* v_res_3386_; 
v_pu_boxed_3384_ = lean_unbox(v_pu_3375_);
v_t_boxed_3385_ = lean_unbox(v_t_3376_);
v_res_3386_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_boxed_3384_, v_t_boxed_3385_, v_ps_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec_ref(v___y_3378_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(uint8_t v_pu_3387_, uint8_t v_t_3388_, lean_object* v_decl_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v_type_3393_; lean_object* v_value_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v_type_3393_ = lean_ctor_get(v_decl_3389_, 2);
v_value_3394_ = lean_ctor_get(v_decl_3389_, 3);
lean_inc_ref(v_type_3393_);
v___x_3395_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3387_, v___y_3390_, v_t_3388_, v_type_3393_);
lean_inc(v_value_3394_);
v___x_3396_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3387_, v___y_3390_, v_value_3394_, v_t_3388_);
v___x_3397_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_3387_, v_decl_3389_, v___x_3395_, v___x_3396_, v___y_3391_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg___boxed(lean_object* v_pu_3398_, lean_object* v_t_3399_, lean_object* v_decl_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
uint8_t v_pu_boxed_3404_; uint8_t v_t_boxed_3405_; lean_object* v_res_3406_; 
v_pu_boxed_3404_ = lean_unbox(v_pu_3398_);
v_t_boxed_3405_ = lean_unbox(v_t_3399_);
v_res_3406_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_boxed_3404_, v_t_boxed_3405_, v_decl_3400_, v___y_3401_, v___y_3402_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(uint8_t v_pu_3407_, uint8_t v_t_3408_, lean_object* v_i_3409_, lean_object* v_as_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v___x_3417_; uint8_t v___x_3418_; 
v___x_3417_ = lean_array_get_size(v_as_3410_);
v___x_3418_ = lean_nat_dec_lt(v_i_3409_, v___x_3417_);
if (v___x_3418_ == 0)
{
lean_object* v___x_3419_; 
lean_dec(v_i_3409_);
v___x_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3419_, 0, v_as_3410_);
return v___x_3419_;
}
else
{
lean_object* v_a_3420_; lean_object* v_a_3422_; 
v_a_3420_ = lean_array_fget_borrowed(v_as_3410_, v_i_3409_);
switch(lean_obj_tag(v_a_3420_))
{
case 0:
{
lean_object* v_params_3433_; lean_object* v_code_3434_; lean_object* v___x_3435_; 
v_params_3433_ = lean_ctor_get(v_a_3420_, 1);
v_code_3434_ = lean_ctor_get(v_a_3420_, 2);
lean_inc_ref(v_params_3433_);
v___x_3435_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_3407_, v_t_3408_, v_params_3433_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3436_; lean_object* v___x_3437_; 
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_a_3436_);
lean_dec_ref(v___x_3435_);
lean_inc_ref(v_code_3434_);
v___x_3437_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3407_, v_t_3408_, v_code_3434_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3439_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref(v___x_3437_);
lean_inc_ref(v_a_3420_);
v___x_3439_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_3407_, v_a_3420_, v_a_3436_, v_a_3438_);
v_a_3422_ = v___x_3439_;
goto v___jp_3421_;
}
else
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec(v_a_3436_);
lean_dec_ref(v_as_3410_);
lean_dec(v_i_3409_);
v_a_3440_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3437_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3437_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_dec_ref(v_as_3410_);
lean_dec(v_i_3409_);
v_a_3448_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3435_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3435_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
case 1:
{
lean_object* v_code_3456_; lean_object* v___x_3457_; 
v_code_3456_ = lean_ctor_get(v_a_3420_, 1);
lean_inc_ref(v_code_3456_);
v___x_3457_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3407_, v_t_3408_, v_code_3456_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3459_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref(v___x_3457_);
lean_inc_ref(v_a_3420_);
v___x_3459_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3420_, v_a_3458_);
v_a_3422_ = v___x_3459_;
goto v___jp_3421_;
}
else
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
lean_dec_ref(v_as_3410_);
lean_dec(v_i_3409_);
v_a_3460_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3457_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3457_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
default: 
{
lean_object* v_code_3468_; lean_object* v___x_3469_; 
v_code_3468_ = lean_ctor_get(v_a_3420_, 0);
lean_inc_ref(v_code_3468_);
v___x_3469_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3407_, v_t_3408_, v_code_3468_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; lean_object* v___x_3471_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3470_);
lean_dec_ref(v___x_3469_);
lean_inc_ref(v_a_3420_);
v___x_3471_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3420_, v_a_3470_);
v_a_3422_ = v___x_3471_;
goto v___jp_3421_;
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_dec_ref(v_as_3410_);
lean_dec(v_i_3409_);
v_a_3472_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3469_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3469_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
}
v___jp_3421_:
{
size_t v___x_3423_; size_t v___x_3424_; uint8_t v___x_3425_; 
v___x_3423_ = lean_ptr_addr(v_a_3420_);
v___x_3424_ = lean_ptr_addr(v_a_3422_);
v___x_3425_ = lean_usize_dec_eq(v___x_3423_, v___x_3424_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3426_ = lean_unsigned_to_nat(1u);
v___x_3427_ = lean_nat_add(v_i_3409_, v___x_3426_);
v___x_3428_ = lean_array_fset(v_as_3410_, v_i_3409_, v_a_3422_);
lean_dec(v_i_3409_);
v_i_3409_ = v___x_3427_;
v_as_3410_ = v___x_3428_;
goto _start;
}
else
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
lean_dec_ref(v_a_3422_);
v___x_3430_ = lean_unsigned_to_nat(1u);
v___x_3431_ = lean_nat_add(v_i_3409_, v___x_3430_);
lean_dec(v_i_3409_);
v_i_3409_ = v___x_3431_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp(uint8_t v_pu_3480_, uint8_t v_t_3481_, lean_object* v_code_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_){
_start:
{
switch(lean_obj_tag(v_code_3482_))
{
case 0:
{
lean_object* v_decl_3489_; lean_object* v_k_3490_; lean_object* v___x_3491_; 
v_decl_3489_ = lean_ctor_get(v_code_3482_, 0);
v_k_3490_ = lean_ctor_get(v_code_3482_, 1);
lean_inc_ref(v_decl_3489_);
v___x_3491_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_3480_, v_t_3481_, v_decl_3489_, v_a_3483_, v_a_3485_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3493_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref(v___x_3491_);
lean_inc_ref(v_k_3490_);
v___x_3493_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3480_, v_t_3481_, v_k_3490_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3521_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3496_ = v___x_3493_;
v_isShared_3497_ = v_isSharedCheck_3521_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3493_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3521_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
uint8_t v___y_3499_; size_t v___x_3515_; size_t v___x_3516_; uint8_t v___x_3517_; 
v___x_3515_ = lean_ptr_addr(v_k_3490_);
v___x_3516_ = lean_ptr_addr(v_a_3494_);
v___x_3517_ = lean_usize_dec_eq(v___x_3515_, v___x_3516_);
if (v___x_3517_ == 0)
{
v___y_3499_ = v___x_3517_;
goto v___jp_3498_;
}
else
{
size_t v___x_3518_; size_t v___x_3519_; uint8_t v___x_3520_; 
v___x_3518_ = lean_ptr_addr(v_decl_3489_);
v___x_3519_ = lean_ptr_addr(v_a_3492_);
v___x_3520_ = lean_usize_dec_eq(v___x_3518_, v___x_3519_);
v___y_3499_ = v___x_3520_;
goto v___jp_3498_;
}
v___jp_3498_:
{
if (v___y_3499_ == 0)
{
lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3509_; 
v_isSharedCheck_3509_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_3509_ == 0)
{
lean_object* v_unused_3510_; lean_object* v_unused_3511_; 
v_unused_3510_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_3510_);
v_unused_3511_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_3511_);
v___x_3501_ = v_code_3482_;
v_isShared_3502_ = v_isSharedCheck_3509_;
goto v_resetjp_3500_;
}
else
{
lean_dec(v_code_3482_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3509_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 1, v_a_3494_);
lean_ctor_set(v___x_3501_, 0, v_a_3492_);
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3492_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v_a_3494_);
v___x_3504_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3506_; 
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 0, v___x_3504_);
v___x_3506_ = v___x_3496_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3504_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
else
{
lean_object* v___x_3513_; 
lean_dec(v_a_3494_);
lean_dec(v_a_3492_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 0, v_code_3482_);
v___x_3513_ = v___x_3496_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_code_3482_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
}
else
{
lean_dec(v_a_3492_);
lean_dec_ref(v_code_3482_);
return v___x_3493_;
}
}
else
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3529_; 
lean_dec_ref(v_code_3482_);
v_a_3522_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3524_ = v___x_3491_;
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3491_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
case 1:
{
lean_object* v_decl_3530_; lean_object* v_k_3531_; lean_object* v___x_3532_; 
v_decl_3530_ = lean_ctor_get(v_code_3482_, 0);
v_k_3531_ = lean_ctor_get(v_code_3482_, 1);
lean_inc_ref(v_decl_3530_);
v___x_3532_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3480_, v_t_3481_, v_decl_3530_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v___x_3534_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3533_);
lean_dec_ref(v___x_3532_);
lean_inc_ref(v_k_3531_);
v___x_3534_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3480_, v_t_3481_, v_k_3531_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3562_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3537_ = v___x_3534_;
v_isShared_3538_ = v_isSharedCheck_3562_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3534_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3562_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
uint8_t v___y_3540_; size_t v___x_3556_; size_t v___x_3557_; uint8_t v___x_3558_; 
v___x_3556_ = lean_ptr_addr(v_k_3531_);
v___x_3557_ = lean_ptr_addr(v_a_3535_);
v___x_3558_ = lean_usize_dec_eq(v___x_3556_, v___x_3557_);
if (v___x_3558_ == 0)
{
v___y_3540_ = v___x_3558_;
goto v___jp_3539_;
}
else
{
size_t v___x_3559_; size_t v___x_3560_; uint8_t v___x_3561_; 
v___x_3559_ = lean_ptr_addr(v_decl_3530_);
v___x_3560_ = lean_ptr_addr(v_a_3533_);
v___x_3561_ = lean_usize_dec_eq(v___x_3559_, v___x_3560_);
v___y_3540_ = v___x_3561_;
goto v___jp_3539_;
}
v___jp_3539_:
{
if (v___y_3540_ == 0)
{
lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3550_; 
v_isSharedCheck_3550_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_3550_ == 0)
{
lean_object* v_unused_3551_; lean_object* v_unused_3552_; 
v_unused_3551_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_3551_);
v_unused_3552_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_3552_);
v___x_3542_ = v_code_3482_;
v_isShared_3543_ = v_isSharedCheck_3550_;
goto v_resetjp_3541_;
}
else
{
lean_dec(v_code_3482_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3550_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 1, v_a_3535_);
lean_ctor_set(v___x_3542_, 0, v_a_3533_);
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3533_);
lean_ctor_set(v_reuseFailAlloc_3549_, 1, v_a_3535_);
v___x_3545_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
lean_object* v___x_3547_; 
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v___x_3545_);
v___x_3547_ = v___x_3537_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3545_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
}
else
{
lean_object* v___x_3554_; 
lean_dec(v_a_3535_);
lean_dec(v_a_3533_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v_code_3482_);
v___x_3554_ = v___x_3537_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_code_3482_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
}
else
{
lean_dec(v_a_3533_);
lean_dec_ref(v_code_3482_);
return v___x_3534_;
}
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_dec_ref(v_code_3482_);
v_a_3563_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3532_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3532_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
case 2:
{
lean_object* v_decl_3571_; lean_object* v_k_3572_; lean_object* v___x_3573_; 
v_decl_3571_ = lean_ctor_get(v_code_3482_, 0);
v_k_3572_ = lean_ctor_get(v_code_3482_, 1);
lean_inc_ref(v_decl_3571_);
v___x_3573_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3480_, v_t_3481_, v_decl_3571_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; lean_object* v___x_3575_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
lean_inc(v_a_3574_);
lean_dec_ref(v___x_3573_);
lean_inc_ref(v_k_3572_);
v___x_3575_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3480_, v_t_3481_, v_k_3572_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3603_; 
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3578_ = v___x_3575_;
v_isShared_3579_ = v_isSharedCheck_3603_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3575_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3603_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
uint8_t v___y_3581_; size_t v___x_3597_; size_t v___x_3598_; uint8_t v___x_3599_; 
v___x_3597_ = lean_ptr_addr(v_k_3572_);
v___x_3598_ = lean_ptr_addr(v_a_3576_);
v___x_3599_ = lean_usize_dec_eq(v___x_3597_, v___x_3598_);
if (v___x_3599_ == 0)
{
v___y_3581_ = v___x_3599_;
goto v___jp_3580_;
}
else
{
size_t v___x_3600_; size_t v___x_3601_; uint8_t v___x_3602_; 
v___x_3600_ = lean_ptr_addr(v_decl_3571_);
v___x_3601_ = lean_ptr_addr(v_a_3574_);
v___x_3602_ = lean_usize_dec_eq(v___x_3600_, v___x_3601_);
v___y_3581_ = v___x_3602_;
goto v___jp_3580_;
}
v___jp_3580_:
{
if (v___y_3581_ == 0)
{
lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3591_; 
v_isSharedCheck_3591_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_3591_ == 0)
{
lean_object* v_unused_3592_; lean_object* v_unused_3593_; 
v_unused_3592_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_3592_);
v_unused_3593_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_3593_);
v___x_3583_ = v_code_3482_;
v_isShared_3584_ = v_isSharedCheck_3591_;
goto v_resetjp_3582_;
}
else
{
lean_dec(v_code_3482_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3591_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 1, v_a_3576_);
lean_ctor_set(v___x_3583_, 0, v_a_3574_);
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3574_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_a_3576_);
v___x_3586_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
lean_object* v___x_3588_; 
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 0, v___x_3586_);
v___x_3588_ = v___x_3578_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3586_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
else
{
lean_object* v___x_3595_; 
lean_dec(v_a_3576_);
lean_dec(v_a_3574_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 0, v_code_3482_);
v___x_3595_ = v___x_3578_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_code_3482_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
}
else
{
lean_dec(v_a_3574_);
lean_dec_ref(v_code_3482_);
return v___x_3575_;
}
}
else
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
lean_dec_ref(v_code_3482_);
v_a_3604_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3606_ = v___x_3573_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3573_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_a_3604_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3612_; lean_object* v_args_3613_; lean_object* v___x_3614_; 
v_fvarId_3612_ = lean_ctor_get(v_code_3482_, 0);
v_args_3613_ = lean_ctor_get(v_code_3482_, 1);
lean_inc(v_fvarId_3612_);
v___x_3614_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3483_, v_fvarId_3612_, v_t_3481_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v_fvarId_3615_; lean_object* v___x_3616_; 
v_fvarId_3615_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_fvarId_3615_);
lean_dec_ref(v___x_3614_);
lean_inc_ref(v_args_3613_);
v___x_3616_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_3480_, v_t_3481_, v_args_3613_, v_a_3483_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3642_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3619_ = v___x_3616_;
v_isShared_3620_ = v_isSharedCheck_3642_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3616_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3642_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
uint8_t v___y_3622_; uint8_t v___x_3638_; 
v___x_3638_ = l_Lean_instBEqFVarId_beq(v_fvarId_3612_, v_fvarId_3615_);
if (v___x_3638_ == 0)
{
v___y_3622_ = v___x_3638_;
goto v___jp_3621_;
}
else
{
size_t v___x_3639_; size_t v___x_3640_; uint8_t v___x_3641_; 
v___x_3639_ = lean_ptr_addr(v_args_3613_);
v___x_3640_ = lean_ptr_addr(v_a_3617_);
v___x_3641_ = lean_usize_dec_eq(v___x_3639_, v___x_3640_);
v___y_3622_ = v___x_3641_;
goto v___jp_3621_;
}
v___jp_3621_:
{
if (v___y_3622_ == 0)
{
lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3632_; 
v_isSharedCheck_3632_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_3632_ == 0)
{
lean_object* v_unused_3633_; lean_object* v_unused_3634_; 
v_unused_3633_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_3633_);
v_unused_3634_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_3634_);
v___x_3624_ = v_code_3482_;
v_isShared_3625_ = v_isSharedCheck_3632_;
goto v_resetjp_3623_;
}
else
{
lean_dec(v_code_3482_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3632_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 1, v_a_3617_);
lean_ctor_set(v___x_3624_, 0, v_fvarId_3615_);
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_fvarId_3615_);
lean_ctor_set(v_reuseFailAlloc_3631_, 1, v_a_3617_);
v___x_3627_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
lean_object* v___x_3629_; 
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 0, v___x_3627_);
v___x_3629_ = v___x_3619_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3627_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
else
{
lean_object* v___x_3636_; 
lean_dec(v_a_3617_);
lean_dec(v_fvarId_3615_);
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 0, v_code_3482_);
v___x_3636_ = v___x_3619_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_code_3482_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
}
else
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3650_; 
lean_dec(v_fvarId_3615_);
lean_dec_ref(v_code_3482_);
v_a_3643_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3645_ = v___x_3616_;
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3616_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3648_; 
if (v_isShared_3646_ == 0)
{
v___x_3648_ = v___x_3645_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_a_3643_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
}
else
{
lean_object* v___x_3651_; 
lean_dec_ref(v_code_3482_);
v___x_3651_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3480_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
return v___x_3651_;
}
}
case 4:
{
lean_object* v_cases_3652_; lean_object* v_typeName_3653_; lean_object* v_resultType_3654_; lean_object* v_discr_3655_; lean_object* v_alts_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3703_; 
v_cases_3652_ = lean_ctor_get(v_code_3482_, 0);
lean_inc_ref(v_cases_3652_);
v_typeName_3653_ = lean_ctor_get(v_cases_3652_, 0);
v_resultType_3654_ = lean_ctor_get(v_cases_3652_, 1);
v_discr_3655_ = lean_ctor_get(v_cases_3652_, 2);
v_alts_3656_ = lean_ctor_get(v_cases_3652_, 3);
v_isSharedCheck_3703_ = !lean_is_exclusive(v_cases_3652_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3658_ = v_cases_3652_;
v_isShared_3659_ = v_isSharedCheck_3703_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_alts_3656_);
lean_inc(v_discr_3655_);
lean_inc(v_resultType_3654_);
lean_inc(v_typeName_3653_);
lean_dec(v_cases_3652_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3703_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
lean_inc_ref(v_resultType_3654_);
v___x_3660_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3480_, v_a_3483_, v_t_3481_, v_resultType_3654_);
lean_inc(v_discr_3655_);
v___x_3661_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3483_, v_discr_3655_, v_t_3481_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_fvarId_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3701_; 
v_fvarId_3662_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3664_ = v___x_3661_;
v_isShared_3665_ = v_isSharedCheck_3701_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_fvarId_3662_);
lean_dec(v___x_3661_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3701_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3656_);
v___x_3667_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_3480_, v_t_3481_, v___x_3666_, v_alts_3656_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3692_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3670_ = v___x_3667_;
v_isShared_3671_ = v_isSharedCheck_3692_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3667_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3692_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
uint8_t v___y_3683_; size_t v___x_3686_; size_t v___x_3687_; uint8_t v___x_3688_; 
v___x_3686_ = lean_ptr_addr(v_alts_3656_);
lean_dec_ref(v_alts_3656_);
v___x_3687_ = lean_ptr_addr(v_a_3668_);
v___x_3688_ = lean_usize_dec_eq(v___x_3686_, v___x_3687_);
if (v___x_3688_ == 0)
{
lean_dec_ref(v_resultType_3654_);
v___y_3683_ = v___x_3688_;
goto v___jp_3682_;
}
else
{
size_t v___x_3689_; size_t v___x_3690_; uint8_t v___x_3691_; 
v___x_3689_ = lean_ptr_addr(v_resultType_3654_);
lean_dec_ref(v_resultType_3654_);
v___x_3690_ = lean_ptr_addr(v___x_3660_);
v___x_3691_ = lean_usize_dec_eq(v___x_3689_, v___x_3690_);
v___y_3683_ = v___x_3691_;
goto v___jp_3682_;
}
v___jp_3672_:
{
lean_object* v___x_3674_; 
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 3, v_a_3668_);
lean_ctor_set(v___x_3658_, 2, v_fvarId_3662_);
lean_ctor_set(v___x_3658_, 1, v___x_3660_);
v___x_3674_ = v___x_3658_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_typeName_3653_);
lean_ctor_set(v_reuseFailAlloc_3681_, 1, v___x_3660_);
lean_ctor_set(v_reuseFailAlloc_3681_, 2, v_fvarId_3662_);
lean_ctor_set(v_reuseFailAlloc_3681_, 3, v_a_3668_);
v___x_3674_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
lean_object* v___x_3676_; 
if (v_isShared_3665_ == 0)
{
lean_ctor_set_tag(v___x_3664_, 4);
lean_ctor_set(v___x_3664_, 0, v___x_3674_);
v___x_3676_ = v___x_3664_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3674_);
v___x_3676_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3678_; 
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v___x_3676_);
v___x_3678_ = v___x_3670_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3676_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
v___jp_3682_:
{
if (v___y_3683_ == 0)
{
lean_dec(v_discr_3655_);
lean_dec_ref(v_code_3482_);
goto v___jp_3672_;
}
else
{
uint8_t v___x_3684_; 
v___x_3684_ = l_Lean_instBEqFVarId_beq(v_discr_3655_, v_fvarId_3662_);
lean_dec(v_discr_3655_);
if (v___x_3684_ == 0)
{
lean_dec_ref(v_code_3482_);
goto v___jp_3672_;
}
else
{
lean_object* v___x_3685_; 
lean_del_object(v___x_3670_);
lean_dec(v_a_3668_);
lean_del_object(v___x_3664_);
lean_dec(v_fvarId_3662_);
lean_dec_ref(v___x_3660_);
lean_del_object(v___x_3658_);
lean_dec(v_typeName_3653_);
v___x_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3685_, 0, v_code_3482_);
return v___x_3685_;
}
}
}
}
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3700_; 
lean_del_object(v___x_3664_);
lean_dec(v_fvarId_3662_);
lean_dec_ref(v___x_3660_);
lean_del_object(v___x_3658_);
lean_dec_ref(v_alts_3656_);
lean_dec(v_discr_3655_);
lean_dec_ref(v_resultType_3654_);
lean_dec(v_typeName_3653_);
lean_dec_ref(v_code_3482_);
v_a_3693_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3695_ = v___x_3667_;
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3667_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3698_; 
if (v_isShared_3696_ == 0)
{
v___x_3698_ = v___x_3695_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
}
else
{
lean_object* v___x_3702_; 
lean_dec_ref(v___x_3660_);
lean_del_object(v___x_3658_);
lean_dec_ref(v_alts_3656_);
lean_dec(v_discr_3655_);
lean_dec_ref(v_resultType_3654_);
lean_dec(v_typeName_3653_);
lean_dec_ref(v_code_3482_);
v___x_3702_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3480_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
return v___x_3702_;
}
}
}
case 5:
{
lean_object* v_fvarId_3704_; lean_object* v___x_3705_; 
v_fvarId_3704_ = lean_ctor_get(v_code_3482_, 0);
lean_inc(v_fvarId_3704_);
v___x_3705_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3483_, v_fvarId_3704_, v_t_3481_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_fvarId_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3725_; 
v_fvarId_3706_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3708_ = v___x_3705_;
v_isShared_3709_ = v_isSharedCheck_3725_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_fvarId_3706_);
lean_dec(v___x_3705_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3725_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
uint8_t v___x_3710_; 
v___x_3710_ = l_Lean_instBEqFVarId_beq(v_fvarId_3704_, v_fvarId_3706_);
if (v___x_3710_ == 0)
{
lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3720_; 
v_isSharedCheck_3720_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_3720_ == 0)
{
lean_object* v_unused_3721_; 
v_unused_3721_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_3721_);
v___x_3712_ = v_code_3482_;
v_isShared_3713_ = v_isSharedCheck_3720_;
goto v_resetjp_3711_;
}
else
{
lean_dec(v_code_3482_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3720_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3715_; 
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 0, v_fvarId_3706_);
v___x_3715_ = v___x_3712_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_fvarId_3706_);
v___x_3715_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
lean_object* v___x_3717_; 
if (v_isShared_3709_ == 0)
{
lean_ctor_set(v___x_3708_, 0, v___x_3715_);
v___x_3717_ = v___x_3708_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3715_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
else
{
lean_object* v___x_3723_; 
lean_dec(v_fvarId_3706_);
if (v_isShared_3709_ == 0)
{
lean_ctor_set(v___x_3708_, 0, v_code_3482_);
v___x_3723_ = v___x_3708_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_code_3482_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
}
else
{
lean_object* v___x_3726_; 
lean_dec_ref(v_code_3482_);
v___x_3726_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3480_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
return v___x_3726_;
}
}
case 6:
{
lean_object* v_type_3727_; lean_object* v___x_3728_; size_t v___x_3729_; size_t v___x_3730_; uint8_t v___x_3731_; 
v_type_3727_ = lean_ctor_get(v_code_3482_, 0);
lean_inc_ref(v_type_3727_);
v___x_3728_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3480_, v_a_3483_, v_t_3481_, v_type_3727_);
v___x_3729_ = lean_ptr_addr(v_type_3727_);
v___x_3730_ = lean_ptr_addr(v___x_3728_);
v___x_3731_ = lean_usize_dec_eq(v___x_3729_, v___x_3730_);
if (v___x_3731_ == 0)
{
lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3739_; 
v_isSharedCheck_3739_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_3739_ == 0)
{
lean_object* v_unused_3740_; 
v_unused_3740_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_3740_);
v___x_3733_ = v_code_3482_;
v_isShared_3734_ = v_isSharedCheck_3739_;
goto v_resetjp_3732_;
}
else
{
lean_dec(v_code_3482_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3739_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 0, v___x_3728_);
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3728_);
v___x_3736_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
lean_object* v___x_3737_; 
v___x_3737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
return v___x_3737_;
}
}
}
else
{
lean_object* v___x_3741_; 
lean_dec_ref(v___x_3728_);
v___x_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3741_, 0, v_code_3482_);
return v___x_3741_;
}
}
case 7:
{
lean_object* v_fvarId_3742_; lean_object* v_i_3743_; lean_object* v_y_3744_; lean_object* v_k_3745_; lean_object* v___x_3746_; 
v_fvarId_3742_ = lean_ctor_get(v_code_3482_, 0);
v_i_3743_ = lean_ctor_get(v_code_3482_, 1);
v_y_3744_ = lean_ctor_get(v_code_3482_, 2);
v_k_3745_ = lean_ctor_get(v_code_3482_, 3);
lean_inc(v_fvarId_3742_);
v___x_3746_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3483_, v_fvarId_3742_, v_t_3481_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v_fvarId_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v_fvarId_3747_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_fvarId_3747_);
lean_dec_ref(v___x_3746_);
lean_inc(v_y_3744_);
v___x_3748_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_3480_, v_a_3483_, v_y_3744_, v_t_3481_);
lean_inc_ref(v_k_3745_);
v___x_3749_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3480_, v_t_3481_, v_k_3745_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3811_; 
v_a_3750_ = lean_ctor_get(v___x_3749_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3752_ = v___x_3749_;
v_isShared_3753_ = v_isSharedCheck_3811_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3749_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3811_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
uint8_t v___y_3755_; size_t v___x_3807_; size_t v___x_3808_; uint8_t v___x_3809_; 
v___x_3807_ = lean_ptr_addr(v_fvarId_3742_);
v___x_3808_ = lean_ptr_addr(v_fvarId_3747_);
v___x_3809_ = lean_usize_dec_eq(v___x_3807_, v___x_3808_);
if (v___x_3809_ == 0)
{
v___y_3755_ = v___x_3809_;
goto v___jp_3754_;
}
else
{
uint8_t v___x_3810_; 
v___x_3810_ = lean_nat_dec_eq(v_i_3743_, v_i_3743_);
v___y_3755_ = v___x_3810_;
goto v___jp_3754_;
}
v___jp_3754_:
{
if (v___y_3755_ == 0)
{
lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3765_; 
lean_inc(v_i_3743_);
v_isSharedCheck_3765_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_3765_ == 0)
{
lean_object* v_unused_3766_; lean_object* v_unused_3767_; lean_object* v_unused_3768_; lean_object* v_unused_3769_; 
v_unused_3766_ = lean_ctor_get(v_code_3482_, 3);
lean_dec(v_unused_3766_);
v_unused_3767_ = lean_ctor_get(v_code_3482_, 2);
lean_dec(v_unused_3767_);
v_unused_3768_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_3768_);
v_unused_3769_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_3769_);
v___x_3757_ = v_code_3482_;
v_isShared_3758_ = v_isSharedCheck_3765_;
goto v_resetjp_3756_;
}
else
{
lean_dec(v_code_3482_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3765_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
lean_ctor_set(v___x_3757_, 3, v_a_3750_);
lean_ctor_set(v___x_3757_, 2, v___x_3748_);
lean_ctor_set(v___x_3757_, 0, v_fvarId_3747_);
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_fvarId_3747_);
lean_ctor_set(v_reuseFailAlloc_3764_, 1, v_i_3743_);
lean_ctor_set(v_reuseFailAlloc_3764_, 2, v___x_3748_);
lean_ctor_set(v_reuseFailAlloc_3764_, 3, v_a_3750_);
v___x_3760_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
lean_object* v___x_3762_; 
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 0, v___x_3760_);
v___x_3762_ = v___x_3752_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3760_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
else
{
size_t v___x_3770_; size_t v___x_3771_; uint8_t v___x_3772_; 
v___x_3770_ = lean_ptr_addr(v_y_3744_);
v___x_3771_ = lean_ptr_addr(v___x_3748_);
v___x_3772_ = lean_usize_dec_eq(v___x_3770_, v___x_3771_);
if (v___x_3772_ == 0)
{
lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3782_; 
lean_inc(v_i_3743_);
v_isSharedCheck_3782_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_3782_ == 0)
{
lean_object* v_unused_3783_; lean_object* v_unused_3784_; lean_object* v_unused_3785_; lean_object* v_unused_3786_; 
v_unused_3783_ = lean_ctor_get(v_code_3482_, 3);
lean_dec(v_unused_3783_);
v_unused_3784_ = lean_ctor_get(v_code_3482_, 2);
lean_dec(v_unused_3784_);
v_unused_3785_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_3785_);
v_unused_3786_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_3786_);
v___x_3774_ = v_code_3482_;
v_isShared_3775_ = v_isSharedCheck_3782_;
goto v_resetjp_3773_;
}
else
{
lean_dec(v_code_3482_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3782_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 3, v_a_3750_);
lean_ctor_set(v___x_3774_, 2, v___x_3748_);
lean_ctor_set(v___x_3774_, 0, v_fvarId_3747_);
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_fvarId_3747_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_i_3743_);
lean_ctor_set(v_reuseFailAlloc_3781_, 2, v___x_3748_);
lean_ctor_set(v_reuseFailAlloc_3781_, 3, v_a_3750_);
v___x_3777_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
lean_object* v___x_3779_; 
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 0, v___x_3777_);
v___x_3779_ = v___x_3752_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3777_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
else
{
size_t v___x_3787_; size_t v___x_3788_; uint8_t v___x_3789_; 
v___x_3787_ = lean_ptr_addr(v_k_3745_);
v___x_3788_ = lean_ptr_addr(v_a_3750_);
v___x_3789_ = lean_usize_dec_eq(v___x_3787_, v___x_3788_);
if (v___x_3789_ == 0)
{
lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3799_; 
lean_inc(v_i_3743_);
v_isSharedCheck_3799_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_3799_ == 0)
{
lean_object* v_unused_3800_; lean_object* v_unused_3801_; lean_object* v_unused_3802_; lean_object* v_unused_3803_; 
v_unused_3800_ = lean_ctor_get(v_code_3482_, 3);
lean_dec(v_unused_3800_);
v_unused_3801_ = lean_ctor_get(v_code_3482_, 2);
lean_dec(v_unused_3801_);
v_unused_3802_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_3802_);
v_unused_3803_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_3803_);
v___x_3791_ = v_code_3482_;
v_isShared_3792_ = v_isSharedCheck_3799_;
goto v_resetjp_3790_;
}
else
{
lean_dec(v_code_3482_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3799_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 3, v_a_3750_);
lean_ctor_set(v___x_3791_, 2, v___x_3748_);
lean_ctor_set(v___x_3791_, 0, v_fvarId_3747_);
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_fvarId_3747_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_i_3743_);
lean_ctor_set(v_reuseFailAlloc_3798_, 2, v___x_3748_);
lean_ctor_set(v_reuseFailAlloc_3798_, 3, v_a_3750_);
v___x_3794_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
lean_object* v___x_3796_; 
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 0, v___x_3794_);
v___x_3796_ = v___x_3752_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3794_);
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
else
{
lean_object* v___x_3805_; 
lean_dec(v_a_3750_);
lean_dec(v___x_3748_);
lean_dec(v_fvarId_3747_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 0, v_code_3482_);
v___x_3805_ = v___x_3752_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_code_3482_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3748_);
lean_dec(v_fvarId_3747_);
lean_dec_ref(v_code_3482_);
return v___x_3749_;
}
}
else
{
lean_object* v___x_3812_; 
lean_dec_ref(v_code_3482_);
v___x_3812_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3480_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
return v___x_3812_;
}
}
case 8:
{
lean_object* v_fvarId_3813_; lean_object* v_i_3814_; lean_object* v_y_3815_; lean_object* v_k_3816_; lean_object* v___x_3817_; 
v_fvarId_3813_ = lean_ctor_get(v_code_3482_, 0);
v_i_3814_ = lean_ctor_get(v_code_3482_, 1);
v_y_3815_ = lean_ctor_get(v_code_3482_, 2);
v_k_3816_ = lean_ctor_get(v_code_3482_, 3);
lean_inc(v_fvarId_3813_);
v___x_3817_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3483_, v_fvarId_3813_, v_t_3481_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_fvarId_3818_; lean_object* v___x_3819_; 
v_fvarId_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_fvarId_3818_);
lean_dec_ref(v___x_3817_);
lean_inc(v_y_3815_);
v___x_3819_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3483_, v_y_3815_, v_t_3481_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_fvarId_3820_; lean_object* v___x_3821_; 
v_fvarId_3820_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_fvarId_3820_);
lean_dec_ref(v___x_3819_);
lean_inc_ref(v_k_3816_);
v___x_3821_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3480_, v_t_3481_, v_k_3816_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3883_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3824_ = v___x_3821_;
v_isShared_3825_ = v_isSharedCheck_3883_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3821_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3883_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
uint8_t v___y_3827_; size_t v___x_3879_; size_t v___x_3880_; uint8_t v___x_3881_; 
v___x_3879_ = lean_ptr_addr(v_fvarId_3813_);
v___x_3880_ = lean_ptr_addr(v_fvarId_3818_);
v___x_3881_ = lean_usize_dec_eq(v___x_3879_, v___x_3880_);
if (v___x_3881_ == 0)
{
v___y_3827_ = v___x_3881_;
goto v___jp_3826_;
}
else
{
uint8_t v___x_3882_; 
v___x_3882_ = lean_nat_dec_eq(v_i_3814_, v_i_3814_);
v___y_3827_ = v___x_3882_;
goto v___jp_3826_;
}
v___jp_3826_:
{
if (v___y_3827_ == 0)
{
lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3837_; 
lean_inc(v_i_3814_);
v_isSharedCheck_3837_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_3837_ == 0)
{
lean_object* v_unused_3838_; lean_object* v_unused_3839_; lean_object* v_unused_3840_; lean_object* v_unused_3841_; 
v_unused_3838_ = lean_ctor_get(v_code_3482_, 3);
lean_dec(v_unused_3838_);
v_unused_3839_ = lean_ctor_get(v_code_3482_, 2);
lean_dec(v_unused_3839_);
v_unused_3840_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_3840_);
v_unused_3841_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_3841_);
v___x_3829_ = v_code_3482_;
v_isShared_3830_ = v_isSharedCheck_3837_;
goto v_resetjp_3828_;
}
else
{
lean_dec(v_code_3482_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3837_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 3, v_a_3822_);
lean_ctor_set(v___x_3829_, 2, v_fvarId_3820_);
lean_ctor_set(v___x_3829_, 0, v_fvarId_3818_);
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_fvarId_3818_);
lean_ctor_set(v_reuseFailAlloc_3836_, 1, v_i_3814_);
lean_ctor_set(v_reuseFailAlloc_3836_, 2, v_fvarId_3820_);
lean_ctor_set(v_reuseFailAlloc_3836_, 3, v_a_3822_);
v___x_3832_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
lean_object* v___x_3834_; 
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v___x_3832_);
v___x_3834_ = v___x_3824_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3832_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
else
{
size_t v___x_3842_; size_t v___x_3843_; uint8_t v___x_3844_; 
v___x_3842_ = lean_ptr_addr(v_y_3815_);
v___x_3843_ = lean_ptr_addr(v_fvarId_3820_);
v___x_3844_ = lean_usize_dec_eq(v___x_3842_, v___x_3843_);
if (v___x_3844_ == 0)
{
lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3854_; 
lean_inc(v_i_3814_);
v_isSharedCheck_3854_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_3854_ == 0)
{
lean_object* v_unused_3855_; lean_object* v_unused_3856_; lean_object* v_unused_3857_; lean_object* v_unused_3858_; 
v_unused_3855_ = lean_ctor_get(v_code_3482_, 3);
lean_dec(v_unused_3855_);
v_unused_3856_ = lean_ctor_get(v_code_3482_, 2);
lean_dec(v_unused_3856_);
v_unused_3857_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_3857_);
v_unused_3858_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_3858_);
v___x_3846_ = v_code_3482_;
v_isShared_3847_ = v_isSharedCheck_3854_;
goto v_resetjp_3845_;
}
else
{
lean_dec(v_code_3482_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3854_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
lean_ctor_set(v___x_3846_, 3, v_a_3822_);
lean_ctor_set(v___x_3846_, 2, v_fvarId_3820_);
lean_ctor_set(v___x_3846_, 0, v_fvarId_3818_);
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_fvarId_3818_);
lean_ctor_set(v_reuseFailAlloc_3853_, 1, v_i_3814_);
lean_ctor_set(v_reuseFailAlloc_3853_, 2, v_fvarId_3820_);
lean_ctor_set(v_reuseFailAlloc_3853_, 3, v_a_3822_);
v___x_3849_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
lean_object* v___x_3851_; 
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v___x_3849_);
v___x_3851_ = v___x_3824_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v___x_3849_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
else
{
size_t v___x_3859_; size_t v___x_3860_; uint8_t v___x_3861_; 
v___x_3859_ = lean_ptr_addr(v_k_3816_);
v___x_3860_ = lean_ptr_addr(v_a_3822_);
v___x_3861_ = lean_usize_dec_eq(v___x_3859_, v___x_3860_);
if (v___x_3861_ == 0)
{
lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3871_; 
lean_inc(v_i_3814_);
v_isSharedCheck_3871_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_3871_ == 0)
{
lean_object* v_unused_3872_; lean_object* v_unused_3873_; lean_object* v_unused_3874_; lean_object* v_unused_3875_; 
v_unused_3872_ = lean_ctor_get(v_code_3482_, 3);
lean_dec(v_unused_3872_);
v_unused_3873_ = lean_ctor_get(v_code_3482_, 2);
lean_dec(v_unused_3873_);
v_unused_3874_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_3874_);
v_unused_3875_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_3875_);
v___x_3863_ = v_code_3482_;
v_isShared_3864_ = v_isSharedCheck_3871_;
goto v_resetjp_3862_;
}
else
{
lean_dec(v_code_3482_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3871_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 3, v_a_3822_);
lean_ctor_set(v___x_3863_, 2, v_fvarId_3820_);
lean_ctor_set(v___x_3863_, 0, v_fvarId_3818_);
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_fvarId_3818_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v_i_3814_);
lean_ctor_set(v_reuseFailAlloc_3870_, 2, v_fvarId_3820_);
lean_ctor_set(v_reuseFailAlloc_3870_, 3, v_a_3822_);
v___x_3866_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
lean_object* v___x_3868_; 
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v___x_3866_);
v___x_3868_ = v___x_3824_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v___x_3866_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
else
{
lean_object* v___x_3877_; 
lean_dec(v_a_3822_);
lean_dec(v_fvarId_3820_);
lean_dec(v_fvarId_3818_);
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v_code_3482_);
v___x_3877_ = v___x_3824_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_code_3482_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_3820_);
lean_dec(v_fvarId_3818_);
lean_dec_ref(v_code_3482_);
return v___x_3821_;
}
}
else
{
lean_object* v___x_3884_; 
lean_dec(v_fvarId_3818_);
lean_dec_ref(v_code_3482_);
v___x_3884_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3480_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
return v___x_3884_;
}
}
else
{
lean_object* v___x_3885_; 
lean_dec_ref(v_code_3482_);
v___x_3885_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3480_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
return v___x_3885_;
}
}
case 9:
{
lean_object* v_fvarId_3886_; lean_object* v_i_3887_; lean_object* v_offset_3888_; lean_object* v_y_3889_; lean_object* v_ty_3890_; lean_object* v_k_3891_; lean_object* v___x_3892_; 
v_fvarId_3886_ = lean_ctor_get(v_code_3482_, 0);
v_i_3887_ = lean_ctor_get(v_code_3482_, 1);
v_offset_3888_ = lean_ctor_get(v_code_3482_, 2);
v_y_3889_ = lean_ctor_get(v_code_3482_, 3);
v_ty_3890_ = lean_ctor_get(v_code_3482_, 4);
v_k_3891_ = lean_ctor_get(v_code_3482_, 5);
lean_inc(v_fvarId_3886_);
v___x_3892_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3483_, v_fvarId_3886_, v_t_3481_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_fvarId_3893_; lean_object* v___x_3894_; 
v_fvarId_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_fvarId_3893_);
lean_dec_ref(v___x_3892_);
lean_inc(v_y_3889_);
v___x_3894_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3483_, v_y_3889_, v_t_3481_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_fvarId_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v_fvarId_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_fvarId_3895_);
lean_dec_ref(v___x_3894_);
lean_inc_ref(v_ty_3890_);
v___x_3896_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3480_, v_a_3483_, v_t_3481_, v_ty_3890_);
lean_inc_ref(v_k_3891_);
v___x_3897_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3480_, v_t_3481_, v_k_3891_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_4001_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3900_ = v___x_3897_;
v_isShared_3901_ = v_isSharedCheck_4001_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3897_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_4001_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
uint8_t v___y_3903_; size_t v___x_3997_; size_t v___x_3998_; uint8_t v___x_3999_; 
v___x_3997_ = lean_ptr_addr(v_fvarId_3886_);
v___x_3998_ = lean_ptr_addr(v_fvarId_3893_);
v___x_3999_ = lean_usize_dec_eq(v___x_3997_, v___x_3998_);
if (v___x_3999_ == 0)
{
v___y_3903_ = v___x_3999_;
goto v___jp_3902_;
}
else
{
uint8_t v___x_4000_; 
v___x_4000_ = lean_nat_dec_eq(v_i_3887_, v_i_3887_);
v___y_3903_ = v___x_4000_;
goto v___jp_3902_;
}
v___jp_3902_:
{
if (v___y_3903_ == 0)
{
lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3913_; 
lean_inc(v_offset_3888_);
lean_inc(v_i_3887_);
v_isSharedCheck_3913_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_3913_ == 0)
{
lean_object* v_unused_3914_; lean_object* v_unused_3915_; lean_object* v_unused_3916_; lean_object* v_unused_3917_; lean_object* v_unused_3918_; lean_object* v_unused_3919_; 
v_unused_3914_ = lean_ctor_get(v_code_3482_, 5);
lean_dec(v_unused_3914_);
v_unused_3915_ = lean_ctor_get(v_code_3482_, 4);
lean_dec(v_unused_3915_);
v_unused_3916_ = lean_ctor_get(v_code_3482_, 3);
lean_dec(v_unused_3916_);
v_unused_3917_ = lean_ctor_get(v_code_3482_, 2);
lean_dec(v_unused_3917_);
v_unused_3918_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_3918_);
v_unused_3919_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_3919_);
v___x_3905_ = v_code_3482_;
v_isShared_3906_ = v_isSharedCheck_3913_;
goto v_resetjp_3904_;
}
else
{
lean_dec(v_code_3482_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3913_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3908_; 
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 5, v_a_3898_);
lean_ctor_set(v___x_3905_, 4, v___x_3896_);
lean_ctor_set(v___x_3905_, 3, v_fvarId_3895_);
lean_ctor_set(v___x_3905_, 0, v_fvarId_3893_);
v___x_3908_ = v___x_3905_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_fvarId_3893_);
lean_ctor_set(v_reuseFailAlloc_3912_, 1, v_i_3887_);
lean_ctor_set(v_reuseFailAlloc_3912_, 2, v_offset_3888_);
lean_ctor_set(v_reuseFailAlloc_3912_, 3, v_fvarId_3895_);
lean_ctor_set(v_reuseFailAlloc_3912_, 4, v___x_3896_);
lean_ctor_set(v_reuseFailAlloc_3912_, 5, v_a_3898_);
v___x_3908_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
lean_object* v___x_3910_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v___x_3908_);
v___x_3910_ = v___x_3900_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3908_);
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
uint8_t v___x_3920_; 
v___x_3920_ = lean_nat_dec_eq(v_offset_3888_, v_offset_3888_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3930_; 
lean_inc(v_offset_3888_);
lean_inc(v_i_3887_);
v_isSharedCheck_3930_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_3930_ == 0)
{
lean_object* v_unused_3931_; lean_object* v_unused_3932_; lean_object* v_unused_3933_; lean_object* v_unused_3934_; lean_object* v_unused_3935_; lean_object* v_unused_3936_; 
v_unused_3931_ = lean_ctor_get(v_code_3482_, 5);
lean_dec(v_unused_3931_);
v_unused_3932_ = lean_ctor_get(v_code_3482_, 4);
lean_dec(v_unused_3932_);
v_unused_3933_ = lean_ctor_get(v_code_3482_, 3);
lean_dec(v_unused_3933_);
v_unused_3934_ = lean_ctor_get(v_code_3482_, 2);
lean_dec(v_unused_3934_);
v_unused_3935_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_3935_);
v_unused_3936_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_3936_);
v___x_3922_ = v_code_3482_;
v_isShared_3923_ = v_isSharedCheck_3930_;
goto v_resetjp_3921_;
}
else
{
lean_dec(v_code_3482_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3930_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
lean_ctor_set(v___x_3922_, 5, v_a_3898_);
lean_ctor_set(v___x_3922_, 4, v___x_3896_);
lean_ctor_set(v___x_3922_, 3, v_fvarId_3895_);
lean_ctor_set(v___x_3922_, 0, v_fvarId_3893_);
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_fvarId_3893_);
lean_ctor_set(v_reuseFailAlloc_3929_, 1, v_i_3887_);
lean_ctor_set(v_reuseFailAlloc_3929_, 2, v_offset_3888_);
lean_ctor_set(v_reuseFailAlloc_3929_, 3, v_fvarId_3895_);
lean_ctor_set(v_reuseFailAlloc_3929_, 4, v___x_3896_);
lean_ctor_set(v_reuseFailAlloc_3929_, 5, v_a_3898_);
v___x_3925_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
lean_object* v___x_3927_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v___x_3925_);
v___x_3927_ = v___x_3900_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3925_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
else
{
size_t v___x_3937_; size_t v___x_3938_; uint8_t v___x_3939_; 
v___x_3937_ = lean_ptr_addr(v_y_3889_);
v___x_3938_ = lean_ptr_addr(v_fvarId_3895_);
v___x_3939_ = lean_usize_dec_eq(v___x_3937_, v___x_3938_);
if (v___x_3939_ == 0)
{
lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3949_; 
lean_inc(v_offset_3888_);
lean_inc(v_i_3887_);
v_isSharedCheck_3949_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_3949_ == 0)
{
lean_object* v_unused_3950_; lean_object* v_unused_3951_; lean_object* v_unused_3952_; lean_object* v_unused_3953_; lean_object* v_unused_3954_; lean_object* v_unused_3955_; 
v_unused_3950_ = lean_ctor_get(v_code_3482_, 5);
lean_dec(v_unused_3950_);
v_unused_3951_ = lean_ctor_get(v_code_3482_, 4);
lean_dec(v_unused_3951_);
v_unused_3952_ = lean_ctor_get(v_code_3482_, 3);
lean_dec(v_unused_3952_);
v_unused_3953_ = lean_ctor_get(v_code_3482_, 2);
lean_dec(v_unused_3953_);
v_unused_3954_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_3954_);
v_unused_3955_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_3955_);
v___x_3941_ = v_code_3482_;
v_isShared_3942_ = v_isSharedCheck_3949_;
goto v_resetjp_3940_;
}
else
{
lean_dec(v_code_3482_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3949_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3944_; 
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 5, v_a_3898_);
lean_ctor_set(v___x_3941_, 4, v___x_3896_);
lean_ctor_set(v___x_3941_, 3, v_fvarId_3895_);
lean_ctor_set(v___x_3941_, 0, v_fvarId_3893_);
v___x_3944_ = v___x_3941_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_fvarId_3893_);
lean_ctor_set(v_reuseFailAlloc_3948_, 1, v_i_3887_);
lean_ctor_set(v_reuseFailAlloc_3948_, 2, v_offset_3888_);
lean_ctor_set(v_reuseFailAlloc_3948_, 3, v_fvarId_3895_);
lean_ctor_set(v_reuseFailAlloc_3948_, 4, v___x_3896_);
lean_ctor_set(v_reuseFailAlloc_3948_, 5, v_a_3898_);
v___x_3944_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
lean_object* v___x_3946_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v___x_3944_);
v___x_3946_ = v___x_3900_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3944_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
}
else
{
size_t v___x_3956_; size_t v___x_3957_; uint8_t v___x_3958_; 
v___x_3956_ = lean_ptr_addr(v_ty_3890_);
v___x_3957_ = lean_ptr_addr(v___x_3896_);
v___x_3958_ = lean_usize_dec_eq(v___x_3956_, v___x_3957_);
if (v___x_3958_ == 0)
{
lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3968_; 
lean_inc(v_offset_3888_);
lean_inc(v_i_3887_);
v_isSharedCheck_3968_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_3968_ == 0)
{
lean_object* v_unused_3969_; lean_object* v_unused_3970_; lean_object* v_unused_3971_; lean_object* v_unused_3972_; lean_object* v_unused_3973_; lean_object* v_unused_3974_; 
v_unused_3969_ = lean_ctor_get(v_code_3482_, 5);
lean_dec(v_unused_3969_);
v_unused_3970_ = lean_ctor_get(v_code_3482_, 4);
lean_dec(v_unused_3970_);
v_unused_3971_ = lean_ctor_get(v_code_3482_, 3);
lean_dec(v_unused_3971_);
v_unused_3972_ = lean_ctor_get(v_code_3482_, 2);
lean_dec(v_unused_3972_);
v_unused_3973_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_3973_);
v_unused_3974_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_3974_);
v___x_3960_ = v_code_3482_;
v_isShared_3961_ = v_isSharedCheck_3968_;
goto v_resetjp_3959_;
}
else
{
lean_dec(v_code_3482_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3968_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3963_; 
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 5, v_a_3898_);
lean_ctor_set(v___x_3960_, 4, v___x_3896_);
lean_ctor_set(v___x_3960_, 3, v_fvarId_3895_);
lean_ctor_set(v___x_3960_, 0, v_fvarId_3893_);
v___x_3963_ = v___x_3960_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_fvarId_3893_);
lean_ctor_set(v_reuseFailAlloc_3967_, 1, v_i_3887_);
lean_ctor_set(v_reuseFailAlloc_3967_, 2, v_offset_3888_);
lean_ctor_set(v_reuseFailAlloc_3967_, 3, v_fvarId_3895_);
lean_ctor_set(v_reuseFailAlloc_3967_, 4, v___x_3896_);
lean_ctor_set(v_reuseFailAlloc_3967_, 5, v_a_3898_);
v___x_3963_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
lean_object* v___x_3965_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v___x_3963_);
v___x_3965_ = v___x_3900_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v___x_3963_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
else
{
size_t v___x_3975_; size_t v___x_3976_; uint8_t v___x_3977_; 
v___x_3975_ = lean_ptr_addr(v_k_3891_);
v___x_3976_ = lean_ptr_addr(v_a_3898_);
v___x_3977_ = lean_usize_dec_eq(v___x_3975_, v___x_3976_);
if (v___x_3977_ == 0)
{
lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3987_; 
lean_inc(v_offset_3888_);
lean_inc(v_i_3887_);
v_isSharedCheck_3987_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_3987_ == 0)
{
lean_object* v_unused_3988_; lean_object* v_unused_3989_; lean_object* v_unused_3990_; lean_object* v_unused_3991_; lean_object* v_unused_3992_; lean_object* v_unused_3993_; 
v_unused_3988_ = lean_ctor_get(v_code_3482_, 5);
lean_dec(v_unused_3988_);
v_unused_3989_ = lean_ctor_get(v_code_3482_, 4);
lean_dec(v_unused_3989_);
v_unused_3990_ = lean_ctor_get(v_code_3482_, 3);
lean_dec(v_unused_3990_);
v_unused_3991_ = lean_ctor_get(v_code_3482_, 2);
lean_dec(v_unused_3991_);
v_unused_3992_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_3992_);
v_unused_3993_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_3993_);
v___x_3979_ = v_code_3482_;
v_isShared_3980_ = v_isSharedCheck_3987_;
goto v_resetjp_3978_;
}
else
{
lean_dec(v_code_3482_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3987_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 5, v_a_3898_);
lean_ctor_set(v___x_3979_, 4, v___x_3896_);
lean_ctor_set(v___x_3979_, 3, v_fvarId_3895_);
lean_ctor_set(v___x_3979_, 0, v_fvarId_3893_);
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_fvarId_3893_);
lean_ctor_set(v_reuseFailAlloc_3986_, 1, v_i_3887_);
lean_ctor_set(v_reuseFailAlloc_3986_, 2, v_offset_3888_);
lean_ctor_set(v_reuseFailAlloc_3986_, 3, v_fvarId_3895_);
lean_ctor_set(v_reuseFailAlloc_3986_, 4, v___x_3896_);
lean_ctor_set(v_reuseFailAlloc_3986_, 5, v_a_3898_);
v___x_3982_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
lean_object* v___x_3984_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v___x_3982_);
v___x_3984_ = v___x_3900_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v___x_3982_);
v___x_3984_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
return v___x_3984_;
}
}
}
}
else
{
lean_object* v___x_3995_; 
lean_dec(v_a_3898_);
lean_dec_ref(v___x_3896_);
lean_dec(v_fvarId_3895_);
lean_dec(v_fvarId_3893_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v_code_3482_);
v___x_3995_ = v___x_3900_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_code_3482_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
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
lean_dec_ref(v___x_3896_);
lean_dec(v_fvarId_3895_);
lean_dec(v_fvarId_3893_);
lean_dec_ref(v_code_3482_);
return v___x_3897_;
}
}
else
{
lean_object* v___x_4002_; 
lean_dec(v_fvarId_3893_);
lean_dec_ref(v_code_3482_);
v___x_4002_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3480_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
return v___x_4002_;
}
}
else
{
lean_object* v___x_4003_; 
lean_dec_ref(v_code_3482_);
v___x_4003_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3480_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
return v___x_4003_;
}
}
case 10:
{
lean_object* v_fvarId_4004_; lean_object* v_cidx_4005_; lean_object* v_k_4006_; lean_object* v___x_4007_; 
v_fvarId_4004_ = lean_ctor_get(v_code_3482_, 0);
v_cidx_4005_ = lean_ctor_get(v_code_3482_, 1);
v_k_4006_ = lean_ctor_get(v_code_3482_, 2);
lean_inc(v_fvarId_4004_);
v___x_4007_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3483_, v_fvarId_4004_, v_t_3481_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v_fvarId_4008_; lean_object* v___x_4009_; 
v_fvarId_4008_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_fvarId_4008_);
lean_dec_ref(v___x_4007_);
lean_inc_ref(v_k_4006_);
v___x_4009_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3480_, v_t_3481_, v_k_4006_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4052_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4012_ = v___x_4009_;
v_isShared_4013_ = v_isSharedCheck_4052_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_4009_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4052_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
uint8_t v___y_4015_; size_t v___x_4048_; size_t v___x_4049_; uint8_t v___x_4050_; 
v___x_4048_ = lean_ptr_addr(v_fvarId_4004_);
v___x_4049_ = lean_ptr_addr(v_fvarId_4008_);
v___x_4050_ = lean_usize_dec_eq(v___x_4048_, v___x_4049_);
if (v___x_4050_ == 0)
{
v___y_4015_ = v___x_4050_;
goto v___jp_4014_;
}
else
{
uint8_t v___x_4051_; 
v___x_4051_ = lean_nat_dec_eq(v_cidx_4005_, v_cidx_4005_);
v___y_4015_ = v___x_4051_;
goto v___jp_4014_;
}
v___jp_4014_:
{
if (v___y_4015_ == 0)
{
lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4025_; 
lean_inc(v_cidx_4005_);
v_isSharedCheck_4025_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_4025_ == 0)
{
lean_object* v_unused_4026_; lean_object* v_unused_4027_; lean_object* v_unused_4028_; 
v_unused_4026_ = lean_ctor_get(v_code_3482_, 2);
lean_dec(v_unused_4026_);
v_unused_4027_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_4027_);
v_unused_4028_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_4028_);
v___x_4017_ = v_code_3482_;
v_isShared_4018_ = v_isSharedCheck_4025_;
goto v_resetjp_4016_;
}
else
{
lean_dec(v_code_3482_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4025_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 2, v_a_4010_);
lean_ctor_set(v___x_4017_, 0, v_fvarId_4008_);
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_fvarId_4008_);
lean_ctor_set(v_reuseFailAlloc_4024_, 1, v_cidx_4005_);
lean_ctor_set(v_reuseFailAlloc_4024_, 2, v_a_4010_);
v___x_4020_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
lean_object* v___x_4022_; 
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 0, v___x_4020_);
v___x_4022_ = v___x_4012_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v___x_4020_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
else
{
size_t v___x_4029_; size_t v___x_4030_; uint8_t v___x_4031_; 
v___x_4029_ = lean_ptr_addr(v_k_4006_);
v___x_4030_ = lean_ptr_addr(v_a_4010_);
v___x_4031_ = lean_usize_dec_eq(v___x_4029_, v___x_4030_);
if (v___x_4031_ == 0)
{
lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4041_; 
lean_inc(v_cidx_4005_);
v_isSharedCheck_4041_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_4041_ == 0)
{
lean_object* v_unused_4042_; lean_object* v_unused_4043_; lean_object* v_unused_4044_; 
v_unused_4042_ = lean_ctor_get(v_code_3482_, 2);
lean_dec(v_unused_4042_);
v_unused_4043_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_4043_);
v_unused_4044_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_4044_);
v___x_4033_ = v_code_3482_;
v_isShared_4034_ = v_isSharedCheck_4041_;
goto v_resetjp_4032_;
}
else
{
lean_dec(v_code_3482_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4041_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4036_; 
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 2, v_a_4010_);
lean_ctor_set(v___x_4033_, 0, v_fvarId_4008_);
v___x_4036_ = v___x_4033_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_fvarId_4008_);
lean_ctor_set(v_reuseFailAlloc_4040_, 1, v_cidx_4005_);
lean_ctor_set(v_reuseFailAlloc_4040_, 2, v_a_4010_);
v___x_4036_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
lean_object* v___x_4038_; 
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 0, v___x_4036_);
v___x_4038_ = v___x_4012_;
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
lean_object* v___x_4046_; 
lean_dec(v_a_4010_);
lean_dec(v_fvarId_4008_);
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 0, v_code_3482_);
v___x_4046_ = v___x_4012_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_code_3482_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4008_);
lean_dec_ref(v_code_3482_);
return v___x_4009_;
}
}
else
{
lean_object* v___x_4053_; 
lean_dec_ref(v_code_3482_);
v___x_4053_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3480_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
return v___x_4053_;
}
}
case 11:
{
lean_object* v_fvarId_4054_; lean_object* v_n_4055_; uint8_t v_check_4056_; uint8_t v_persistent_4057_; lean_object* v_k_4058_; lean_object* v___x_4059_; 
v_fvarId_4054_ = lean_ctor_get(v_code_3482_, 0);
v_n_4055_ = lean_ctor_get(v_code_3482_, 1);
v_check_4056_ = lean_ctor_get_uint8(v_code_3482_, sizeof(void*)*3);
v_persistent_4057_ = lean_ctor_get_uint8(v_code_3482_, sizeof(void*)*3 + 1);
v_k_4058_ = lean_ctor_get(v_code_3482_, 2);
lean_inc(v_fvarId_4054_);
v___x_4059_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3483_, v_fvarId_4054_, v_t_3481_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v_fvarId_4060_; lean_object* v___x_4061_; 
v_fvarId_4060_ = lean_ctor_get(v___x_4059_, 0);
lean_inc(v_fvarId_4060_);
lean_dec_ref(v___x_4059_);
lean_inc_ref(v_k_4058_);
v___x_4061_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3480_, v_t_3481_, v_k_4058_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4104_; 
v_a_4062_ = lean_ctor_get(v___x_4061_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4064_ = v___x_4061_;
v_isShared_4065_ = v_isSharedCheck_4104_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_4061_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4104_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
uint8_t v___y_4067_; size_t v___x_4100_; size_t v___x_4101_; uint8_t v___x_4102_; 
v___x_4100_ = lean_ptr_addr(v_fvarId_4054_);
v___x_4101_ = lean_ptr_addr(v_fvarId_4060_);
v___x_4102_ = lean_usize_dec_eq(v___x_4100_, v___x_4101_);
if (v___x_4102_ == 0)
{
v___y_4067_ = v___x_4102_;
goto v___jp_4066_;
}
else
{
uint8_t v___x_4103_; 
v___x_4103_ = lean_nat_dec_eq(v_n_4055_, v_n_4055_);
v___y_4067_ = v___x_4103_;
goto v___jp_4066_;
}
v___jp_4066_:
{
if (v___y_4067_ == 0)
{
lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4077_; 
lean_inc(v_n_4055_);
v_isSharedCheck_4077_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_4077_ == 0)
{
lean_object* v_unused_4078_; lean_object* v_unused_4079_; lean_object* v_unused_4080_; 
v_unused_4078_ = lean_ctor_get(v_code_3482_, 2);
lean_dec(v_unused_4078_);
v_unused_4079_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_4079_);
v_unused_4080_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_4080_);
v___x_4069_ = v_code_3482_;
v_isShared_4070_ = v_isSharedCheck_4077_;
goto v_resetjp_4068_;
}
else
{
lean_dec(v_code_3482_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4077_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
lean_ctor_set(v___x_4069_, 2, v_a_4062_);
lean_ctor_set(v___x_4069_, 0, v_fvarId_4060_);
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_fvarId_4060_);
lean_ctor_set(v_reuseFailAlloc_4076_, 1, v_n_4055_);
lean_ctor_set(v_reuseFailAlloc_4076_, 2, v_a_4062_);
lean_ctor_set_uint8(v_reuseFailAlloc_4076_, sizeof(void*)*3, v_check_4056_);
lean_ctor_set_uint8(v_reuseFailAlloc_4076_, sizeof(void*)*3 + 1, v_persistent_4057_);
v___x_4072_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
lean_object* v___x_4074_; 
if (v_isShared_4065_ == 0)
{
lean_ctor_set(v___x_4064_, 0, v___x_4072_);
v___x_4074_ = v___x_4064_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v___x_4072_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
}
}
else
{
size_t v___x_4081_; size_t v___x_4082_; uint8_t v___x_4083_; 
v___x_4081_ = lean_ptr_addr(v_k_4058_);
v___x_4082_ = lean_ptr_addr(v_a_4062_);
v___x_4083_ = lean_usize_dec_eq(v___x_4081_, v___x_4082_);
if (v___x_4083_ == 0)
{
lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4093_; 
lean_inc(v_n_4055_);
v_isSharedCheck_4093_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_4093_ == 0)
{
lean_object* v_unused_4094_; lean_object* v_unused_4095_; lean_object* v_unused_4096_; 
v_unused_4094_ = lean_ctor_get(v_code_3482_, 2);
lean_dec(v_unused_4094_);
v_unused_4095_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_4095_);
v_unused_4096_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_4096_);
v___x_4085_ = v_code_3482_;
v_isShared_4086_ = v_isSharedCheck_4093_;
goto v_resetjp_4084_;
}
else
{
lean_dec(v_code_3482_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4093_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
lean_ctor_set(v___x_4085_, 2, v_a_4062_);
lean_ctor_set(v___x_4085_, 0, v_fvarId_4060_);
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_fvarId_4060_);
lean_ctor_set(v_reuseFailAlloc_4092_, 1, v_n_4055_);
lean_ctor_set(v_reuseFailAlloc_4092_, 2, v_a_4062_);
lean_ctor_set_uint8(v_reuseFailAlloc_4092_, sizeof(void*)*3, v_check_4056_);
lean_ctor_set_uint8(v_reuseFailAlloc_4092_, sizeof(void*)*3 + 1, v_persistent_4057_);
v___x_4088_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
lean_object* v___x_4090_; 
if (v_isShared_4065_ == 0)
{
lean_ctor_set(v___x_4064_, 0, v___x_4088_);
v___x_4090_ = v___x_4064_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4088_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
else
{
lean_object* v___x_4098_; 
lean_dec(v_a_4062_);
lean_dec(v_fvarId_4060_);
if (v_isShared_4065_ == 0)
{
lean_ctor_set(v___x_4064_, 0, v_code_3482_);
v___x_4098_ = v___x_4064_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_code_3482_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4060_);
lean_dec_ref(v_code_3482_);
return v___x_4061_;
}
}
else
{
lean_object* v___x_4105_; 
lean_dec_ref(v_code_3482_);
v___x_4105_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3480_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
return v___x_4105_;
}
}
case 12:
{
lean_object* v_fvarId_4106_; lean_object* v_n_4107_; uint8_t v_check_4108_; uint8_t v_persistent_4109_; lean_object* v_k_4110_; lean_object* v___x_4111_; 
v_fvarId_4106_ = lean_ctor_get(v_code_3482_, 0);
v_n_4107_ = lean_ctor_get(v_code_3482_, 1);
v_check_4108_ = lean_ctor_get_uint8(v_code_3482_, sizeof(void*)*3);
v_persistent_4109_ = lean_ctor_get_uint8(v_code_3482_, sizeof(void*)*3 + 1);
v_k_4110_ = lean_ctor_get(v_code_3482_, 2);
lean_inc(v_fvarId_4106_);
v___x_4111_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3483_, v_fvarId_4106_, v_t_3481_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_fvarId_4112_; lean_object* v___x_4113_; 
v_fvarId_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_fvarId_4112_);
lean_dec_ref(v___x_4111_);
lean_inc_ref(v_k_4110_);
v___x_4113_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3480_, v_t_3481_, v_k_4110_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4156_; 
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4116_ = v___x_4113_;
v_isShared_4117_ = v_isSharedCheck_4156_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4113_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4156_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
uint8_t v___y_4119_; size_t v___x_4152_; size_t v___x_4153_; uint8_t v___x_4154_; 
v___x_4152_ = lean_ptr_addr(v_fvarId_4106_);
v___x_4153_ = lean_ptr_addr(v_fvarId_4112_);
v___x_4154_ = lean_usize_dec_eq(v___x_4152_, v___x_4153_);
if (v___x_4154_ == 0)
{
v___y_4119_ = v___x_4154_;
goto v___jp_4118_;
}
else
{
uint8_t v___x_4155_; 
v___x_4155_ = lean_nat_dec_eq(v_n_4107_, v_n_4107_);
v___y_4119_ = v___x_4155_;
goto v___jp_4118_;
}
v___jp_4118_:
{
if (v___y_4119_ == 0)
{
lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4129_; 
lean_inc(v_n_4107_);
v_isSharedCheck_4129_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_4129_ == 0)
{
lean_object* v_unused_4130_; lean_object* v_unused_4131_; lean_object* v_unused_4132_; 
v_unused_4130_ = lean_ctor_get(v_code_3482_, 2);
lean_dec(v_unused_4130_);
v_unused_4131_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_4131_);
v_unused_4132_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_4132_);
v___x_4121_ = v_code_3482_;
v_isShared_4122_ = v_isSharedCheck_4129_;
goto v_resetjp_4120_;
}
else
{
lean_dec(v_code_3482_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4129_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
lean_ctor_set(v___x_4121_, 2, v_a_4114_);
lean_ctor_set(v___x_4121_, 0, v_fvarId_4112_);
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_fvarId_4112_);
lean_ctor_set(v_reuseFailAlloc_4128_, 1, v_n_4107_);
lean_ctor_set(v_reuseFailAlloc_4128_, 2, v_a_4114_);
lean_ctor_set_uint8(v_reuseFailAlloc_4128_, sizeof(void*)*3, v_check_4108_);
lean_ctor_set_uint8(v_reuseFailAlloc_4128_, sizeof(void*)*3 + 1, v_persistent_4109_);
v___x_4124_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
lean_object* v___x_4126_; 
if (v_isShared_4117_ == 0)
{
lean_ctor_set(v___x_4116_, 0, v___x_4124_);
v___x_4126_ = v___x_4116_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v___x_4124_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
return v___x_4126_;
}
}
}
}
else
{
size_t v___x_4133_; size_t v___x_4134_; uint8_t v___x_4135_; 
v___x_4133_ = lean_ptr_addr(v_k_4110_);
v___x_4134_ = lean_ptr_addr(v_a_4114_);
v___x_4135_ = lean_usize_dec_eq(v___x_4133_, v___x_4134_);
if (v___x_4135_ == 0)
{
lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4145_; 
lean_inc(v_n_4107_);
v_isSharedCheck_4145_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_4145_ == 0)
{
lean_object* v_unused_4146_; lean_object* v_unused_4147_; lean_object* v_unused_4148_; 
v_unused_4146_ = lean_ctor_get(v_code_3482_, 2);
lean_dec(v_unused_4146_);
v_unused_4147_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_4147_);
v_unused_4148_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_4148_);
v___x_4137_ = v_code_3482_;
v_isShared_4138_ = v_isSharedCheck_4145_;
goto v_resetjp_4136_;
}
else
{
lean_dec(v_code_3482_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4145_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
lean_ctor_set(v___x_4137_, 2, v_a_4114_);
lean_ctor_set(v___x_4137_, 0, v_fvarId_4112_);
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_fvarId_4112_);
lean_ctor_set(v_reuseFailAlloc_4144_, 1, v_n_4107_);
lean_ctor_set(v_reuseFailAlloc_4144_, 2, v_a_4114_);
lean_ctor_set_uint8(v_reuseFailAlloc_4144_, sizeof(void*)*3, v_check_4108_);
lean_ctor_set_uint8(v_reuseFailAlloc_4144_, sizeof(void*)*3 + 1, v_persistent_4109_);
v___x_4140_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
lean_object* v___x_4142_; 
if (v_isShared_4117_ == 0)
{
lean_ctor_set(v___x_4116_, 0, v___x_4140_);
v___x_4142_ = v___x_4116_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v___x_4140_);
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
else
{
lean_object* v___x_4150_; 
lean_dec(v_a_4114_);
lean_dec(v_fvarId_4112_);
if (v_isShared_4117_ == 0)
{
lean_ctor_set(v___x_4116_, 0, v_code_3482_);
v___x_4150_ = v___x_4116_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_code_3482_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4112_);
lean_dec_ref(v_code_3482_);
return v___x_4113_;
}
}
else
{
lean_object* v___x_4157_; 
lean_dec_ref(v_code_3482_);
v___x_4157_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3480_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
return v___x_4157_;
}
}
default: 
{
lean_object* v_fvarId_4158_; lean_object* v_k_4159_; lean_object* v___x_4160_; 
v_fvarId_4158_ = lean_ctor_get(v_code_3482_, 0);
v_k_4159_ = lean_ctor_get(v_code_3482_, 1);
lean_inc(v_fvarId_4158_);
v___x_4160_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3483_, v_fvarId_4158_, v_t_3481_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_fvarId_4161_; lean_object* v___x_4162_; 
v_fvarId_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_fvarId_4161_);
lean_dec_ref(v___x_4160_);
lean_inc_ref(v_k_4159_);
v___x_4162_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3480_, v_t_3481_, v_k_4159_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4190_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4165_ = v___x_4162_;
v_isShared_4166_ = v_isSharedCheck_4190_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4162_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4190_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
uint8_t v___y_4168_; size_t v___x_4184_; size_t v___x_4185_; uint8_t v___x_4186_; 
v___x_4184_ = lean_ptr_addr(v_fvarId_4158_);
v___x_4185_ = lean_ptr_addr(v_fvarId_4161_);
v___x_4186_ = lean_usize_dec_eq(v___x_4184_, v___x_4185_);
if (v___x_4186_ == 0)
{
v___y_4168_ = v___x_4186_;
goto v___jp_4167_;
}
else
{
size_t v___x_4187_; size_t v___x_4188_; uint8_t v___x_4189_; 
v___x_4187_ = lean_ptr_addr(v_k_4159_);
v___x_4188_ = lean_ptr_addr(v_a_4163_);
v___x_4189_ = lean_usize_dec_eq(v___x_4187_, v___x_4188_);
v___y_4168_ = v___x_4189_;
goto v___jp_4167_;
}
v___jp_4167_:
{
if (v___y_4168_ == 0)
{
lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4178_; 
v_isSharedCheck_4178_ = !lean_is_exclusive(v_code_3482_);
if (v_isSharedCheck_4178_ == 0)
{
lean_object* v_unused_4179_; lean_object* v_unused_4180_; 
v_unused_4179_ = lean_ctor_get(v_code_3482_, 1);
lean_dec(v_unused_4179_);
v_unused_4180_ = lean_ctor_get(v_code_3482_, 0);
lean_dec(v_unused_4180_);
v___x_4170_ = v_code_3482_;
v_isShared_4171_ = v_isSharedCheck_4178_;
goto v_resetjp_4169_;
}
else
{
lean_dec(v_code_3482_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4178_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
lean_ctor_set(v___x_4170_, 1, v_a_4163_);
lean_ctor_set(v___x_4170_, 0, v_fvarId_4161_);
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v_fvarId_4161_);
lean_ctor_set(v_reuseFailAlloc_4177_, 1, v_a_4163_);
v___x_4173_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
lean_object* v___x_4175_; 
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 0, v___x_4173_);
v___x_4175_ = v___x_4165_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4173_);
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
lean_object* v___x_4182_; 
lean_dec(v_a_4163_);
lean_dec(v_fvarId_4161_);
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 0, v_code_3482_);
v___x_4182_ = v___x_4165_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_code_3482_);
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
else
{
lean_dec(v_fvarId_4161_);
lean_dec_ref(v_code_3482_);
return v___x_4162_;
}
}
else
{
lean_object* v___x_4191_; 
lean_dec_ref(v_code_3482_);
v___x_4191_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3480_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
return v___x_4191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t v_pu_4192_, uint8_t v_t_4193_, lean_object* v_decl_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_){
_start:
{
lean_object* v_params_4201_; lean_object* v_type_4202_; lean_object* v_value_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v_params_4201_ = lean_ctor_get(v_decl_4194_, 2);
v_type_4202_ = lean_ctor_get(v_decl_4194_, 3);
v_value_4203_ = lean_ctor_get(v_decl_4194_, 4);
lean_inc_ref(v_type_4202_);
v___x_4204_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4192_, v_a_4195_, v_t_4193_, v_type_4202_);
lean_inc_ref(v_params_4201_);
v___x_4205_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4192_, v_t_4193_, v_params_4201_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; lean_object* v___x_4207_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref(v___x_4205_);
lean_inc_ref(v_value_4203_);
v___x_4207_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4192_, v_t_4193_, v_value_4203_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
if (lean_obj_tag(v___x_4207_) == 0)
{
lean_object* v_a_4208_; lean_object* v___x_4209_; 
v_a_4208_ = lean_ctor_get(v___x_4207_, 0);
lean_inc(v_a_4208_);
lean_dec_ref(v___x_4207_);
v___x_4209_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_4192_, v_decl_4194_, v___x_4204_, v_a_4206_, v_a_4208_, v_a_4197_);
return v___x_4209_;
}
else
{
lean_object* v_a_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4217_; 
lean_dec(v_a_4206_);
lean_dec_ref(v___x_4204_);
lean_dec_ref(v_decl_4194_);
v_a_4210_ = lean_ctor_get(v___x_4207_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4207_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4212_ = v___x_4207_;
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_a_4210_);
lean_dec(v___x_4207_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4215_; 
if (v_isShared_4213_ == 0)
{
v___x_4215_ = v___x_4212_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_a_4210_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
}
}
else
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4225_; 
lean_dec_ref(v___x_4204_);
lean_dec_ref(v_decl_4194_);
v_a_4218_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4225_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4220_ = v___x_4205_;
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___x_4205_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4223_; 
if (v_isShared_4221_ == 0)
{
v___x_4223_ = v___x_4220_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_a_4218_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp___boxed(lean_object* v_pu_4226_, lean_object* v_t_4227_, lean_object* v_decl_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_){
_start:
{
uint8_t v_pu_boxed_4235_; uint8_t v_t_boxed_4236_; lean_object* v_res_4237_; 
v_pu_boxed_4235_ = lean_unbox(v_pu_4226_);
v_t_boxed_4236_ = lean_unbox(v_t_4227_);
v_res_4237_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_boxed_4235_, v_t_boxed_4236_, v_decl_4228_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_);
lean_dec(v_a_4233_);
lean_dec_ref(v_a_4232_);
lean_dec(v_a_4231_);
lean_dec_ref(v_a_4230_);
lean_dec_ref(v_a_4229_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4___boxed(lean_object* v_pu_4238_, lean_object* v_t_4239_, lean_object* v_i_4240_, lean_object* v_as_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_){
_start:
{
uint8_t v_pu_boxed_4248_; uint8_t v_t_boxed_4249_; lean_object* v_res_4250_; 
v_pu_boxed_4248_ = lean_unbox(v_pu_4238_);
v_t_boxed_4249_ = lean_unbox(v_t_4239_);
v_res_4250_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_boxed_4248_, v_t_boxed_4249_, v_i_4240_, v_as_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_);
lean_dec(v___y_4246_);
lean_dec_ref(v___y_4245_);
lean_dec(v___y_4244_);
lean_dec_ref(v___y_4243_);
lean_dec_ref(v___y_4242_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp___boxed(lean_object* v_pu_4251_, lean_object* v_t_4252_, lean_object* v_code_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_){
_start:
{
uint8_t v_pu_boxed_4260_; uint8_t v_t_boxed_4261_; lean_object* v_res_4262_; 
v_pu_boxed_4260_ = lean_unbox(v_pu_4251_);
v_t_boxed_4261_ = lean_unbox(v_t_4252_);
v_res_4262_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_boxed_4260_, v_t_boxed_4261_, v_code_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_);
lean_dec(v_a_4258_);
lean_dec_ref(v_a_4257_);
lean_dec(v_a_4256_);
lean_dec_ref(v_a_4255_);
lean_dec_ref(v_a_4254_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(uint8_t v_pu_4263_, uint8_t v_t_4264_, uint8_t v_pu_4265_, uint8_t v_t_4266_, lean_object* v_decl_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_){
_start:
{
lean_object* v___x_4274_; 
v___x_4274_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_4265_, v_t_4266_, v_decl_4267_, v___y_4268_, v___y_4270_);
return v___x_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___boxed(lean_object* v_pu_4275_, lean_object* v_t_4276_, lean_object* v_pu_4277_, lean_object* v_t_4278_, lean_object* v_decl_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
uint8_t v_pu_boxed_4286_; uint8_t v_t_boxed_4287_; uint8_t v_pu_boxed_4288_; uint8_t v_t_boxed_4289_; lean_object* v_res_4290_; 
v_pu_boxed_4286_ = lean_unbox(v_pu_4275_);
v_t_boxed_4287_ = lean_unbox(v_t_4276_);
v_pu_boxed_4288_ = lean_unbox(v_pu_4277_);
v_t_boxed_4289_ = lean_unbox(v_t_4278_);
v_res_4290_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(v_pu_boxed_4286_, v_t_boxed_4287_, v_pu_boxed_4288_, v_t_boxed_4289_, v_decl_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec_ref(v___y_4280_);
return v_res_4290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(uint8_t v_pu_4291_, uint8_t v_t_4292_, uint8_t v_pu_4293_, uint8_t v_t_4294_, lean_object* v_args_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_){
_start:
{
lean_object* v___x_4302_; 
v___x_4302_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_4293_, v_t_4294_, v_args_4295_, v___y_4296_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___boxed(lean_object* v_pu_4303_, lean_object* v_t_4304_, lean_object* v_pu_4305_, lean_object* v_t_4306_, lean_object* v_args_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
uint8_t v_pu_boxed_4314_; uint8_t v_t_boxed_4315_; uint8_t v_pu_boxed_4316_; uint8_t v_t_boxed_4317_; lean_object* v_res_4318_; 
v_pu_boxed_4314_ = lean_unbox(v_pu_4303_);
v_t_boxed_4315_ = lean_unbox(v_t_4304_);
v_pu_boxed_4316_ = lean_unbox(v_pu_4305_);
v_t_boxed_4317_ = lean_unbox(v_t_4306_);
v_res_4318_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(v_pu_boxed_4314_, v_t_boxed_4315_, v_pu_boxed_4316_, v_t_boxed_4317_, v_args_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
lean_dec(v___y_4310_);
lean_dec_ref(v___y_4309_);
lean_dec_ref(v___y_4308_);
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(uint8_t v_pu_4319_, uint8_t v_t_4320_, uint8_t v_pu_4321_, uint8_t v_t_4322_, lean_object* v_ps_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
lean_object* v___x_4330_; 
v___x_4330_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4321_, v_t_4322_, v_ps_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___boxed(lean_object* v_pu_4331_, lean_object* v_t_4332_, lean_object* v_pu_4333_, lean_object* v_t_4334_, lean_object* v_ps_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
uint8_t v_pu_boxed_4342_; uint8_t v_t_boxed_4343_; uint8_t v_pu_boxed_4344_; uint8_t v_t_boxed_4345_; lean_object* v_res_4346_; 
v_pu_boxed_4342_ = lean_unbox(v_pu_4331_);
v_t_boxed_4343_ = lean_unbox(v_t_4332_);
v_pu_boxed_4344_ = lean_unbox(v_pu_4333_);
v_t_boxed_4345_ = lean_unbox(v_t_4334_);
v_res_4346_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(v_pu_boxed_4342_, v_t_boxed_4343_, v_pu_boxed_4344_, v_t_boxed_4345_, v_ps_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
lean_dec_ref(v___y_4336_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(uint8_t v_pu_4347_, uint8_t v_t_4348_, lean_object* v_i_4349_, lean_object* v_as_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
lean_object* v___x_4357_; 
v___x_4357_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_4347_, v_t_4348_, v_i_4349_, v_as_4350_, v___y_4351_, v___y_4353_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___boxed(lean_object* v_pu_4358_, lean_object* v_t_4359_, lean_object* v_i_4360_, lean_object* v_as_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
uint8_t v_pu_boxed_4368_; uint8_t v_t_boxed_4369_; lean_object* v_res_4370_; 
v_pu_boxed_4368_ = lean_unbox(v_pu_4358_);
v_t_boxed_4369_ = lean_unbox(v_t_4359_);
v_res_4370_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(v_pu_boxed_4368_, v_t_boxed_4369_, v_i_4360_, v_as_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec_ref(v___y_4362_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(uint8_t v_pu_4371_, uint8_t v_t_4372_, lean_object* v_decl_4373_, lean_object* v_inst_4374_, lean_object* v_____do__lift_4375_){
_start:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4376_ = lean_box(v_pu_4371_);
v___x_4377_ = lean_box(v_t_4372_);
v___x_4378_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDeclImp___boxed), 9, 4);
lean_closure_set(v___x_4378_, 0, v___x_4376_);
lean_closure_set(v___x_4378_, 1, v___x_4377_);
lean_closure_set(v___x_4378_, 2, v_decl_4373_);
lean_closure_set(v___x_4378_, 3, v_____do__lift_4375_);
v___x_4379_ = lean_apply_2(v_inst_4374_, lean_box(0), v___x_4378_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed(lean_object* v_pu_4380_, lean_object* v_t_4381_, lean_object* v_decl_4382_, lean_object* v_inst_4383_, lean_object* v_____do__lift_4384_){
_start:
{
uint8_t v_pu_boxed_4385_; uint8_t v_t_boxed_4386_; lean_object* v_res_4387_; 
v_pu_boxed_4385_ = lean_unbox(v_pu_4380_);
v_t_boxed_4386_ = lean_unbox(v_t_4381_);
v_res_4387_ = l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(v_pu_boxed_4385_, v_t_boxed_4386_, v_decl_4382_, v_inst_4383_, v_____do__lift_4384_);
return v_res_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg(uint8_t v_pu_4388_, uint8_t v_t_4389_, lean_object* v_inst_4390_, lean_object* v_inst_4391_, lean_object* v_inst_4392_, lean_object* v_decl_4393_){
_start:
{
lean_object* v_toBind_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___f_4397_; lean_object* v___x_4398_; 
v_toBind_4394_ = lean_ctor_get(v_inst_4391_, 1);
lean_inc(v_toBind_4394_);
lean_dec_ref(v_inst_4391_);
v___x_4395_ = lean_box(v_pu_4388_);
v___x_4396_ = lean_box(v_t_4389_);
v___f_4397_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4397_, 0, v___x_4395_);
lean_closure_set(v___f_4397_, 1, v___x_4396_);
lean_closure_set(v___f_4397_, 2, v_decl_4393_);
lean_closure_set(v___f_4397_, 3, v_inst_4390_);
v___x_4398_ = lean_apply_4(v_toBind_4394_, lean_box(0), lean_box(0), v_inst_4392_, v___f_4397_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___boxed(lean_object* v_pu_4399_, lean_object* v_t_4400_, lean_object* v_inst_4401_, lean_object* v_inst_4402_, lean_object* v_inst_4403_, lean_object* v_decl_4404_){
_start:
{
uint8_t v_pu_boxed_4405_; uint8_t v_t_boxed_4406_; lean_object* v_res_4407_; 
v_pu_boxed_4405_ = lean_unbox(v_pu_4399_);
v_t_boxed_4406_ = lean_unbox(v_t_4400_);
v_res_4407_ = l_Lean_Compiler_LCNF_normFunDecl___redArg(v_pu_boxed_4405_, v_t_boxed_4406_, v_inst_4401_, v_inst_4402_, v_inst_4403_, v_decl_4404_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl(lean_object* v_m_4408_, uint8_t v_pu_4409_, uint8_t v_t_4410_, lean_object* v_inst_4411_, lean_object* v_inst_4412_, lean_object* v_inst_4413_, lean_object* v_decl_4414_){
_start:
{
lean_object* v_toBind_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___f_4418_; lean_object* v___x_4419_; 
v_toBind_4415_ = lean_ctor_get(v_inst_4412_, 1);
lean_inc(v_toBind_4415_);
lean_dec_ref(v_inst_4412_);
v___x_4416_ = lean_box(v_pu_4409_);
v___x_4417_ = lean_box(v_t_4410_);
v___f_4418_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4418_, 0, v___x_4416_);
lean_closure_set(v___f_4418_, 1, v___x_4417_);
lean_closure_set(v___f_4418_, 2, v_decl_4414_);
lean_closure_set(v___f_4418_, 3, v_inst_4411_);
v___x_4419_ = lean_apply_4(v_toBind_4415_, lean_box(0), lean_box(0), v_inst_4413_, v___f_4418_);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___boxed(lean_object* v_m_4420_, lean_object* v_pu_4421_, lean_object* v_t_4422_, lean_object* v_inst_4423_, lean_object* v_inst_4424_, lean_object* v_inst_4425_, lean_object* v_decl_4426_){
_start:
{
uint8_t v_pu_boxed_4427_; uint8_t v_t_boxed_4428_; lean_object* v_res_4429_; 
v_pu_boxed_4427_ = lean_unbox(v_pu_4421_);
v_t_boxed_4428_ = lean_unbox(v_t_4422_);
v_res_4429_ = l_Lean_Compiler_LCNF_normFunDecl(v_m_4420_, v_pu_boxed_4427_, v_t_boxed_4428_, v_inst_4423_, v_inst_4424_, v_inst_4425_, v_decl_4426_);
return v_res_4429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0(uint8_t v_pu_4430_, uint8_t v_t_4431_, lean_object* v_code_4432_, lean_object* v_inst_4433_, lean_object* v_____do__lift_4434_){
_start:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4435_ = lean_box(v_pu_4430_);
v___x_4436_ = lean_box(v_t_4431_);
v___x_4437_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCodeImp___boxed), 9, 4);
lean_closure_set(v___x_4437_, 0, v___x_4435_);
lean_closure_set(v___x_4437_, 1, v___x_4436_);
lean_closure_set(v___x_4437_, 2, v_code_4432_);
lean_closure_set(v___x_4437_, 3, v_____do__lift_4434_);
v___x_4438_ = lean_apply_2(v_inst_4433_, lean_box(0), v___x_4437_);
return v___x_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed(lean_object* v_pu_4439_, lean_object* v_t_4440_, lean_object* v_code_4441_, lean_object* v_inst_4442_, lean_object* v_____do__lift_4443_){
_start:
{
uint8_t v_pu_boxed_4444_; uint8_t v_t_boxed_4445_; lean_object* v_res_4446_; 
v_pu_boxed_4444_ = lean_unbox(v_pu_4439_);
v_t_boxed_4445_ = lean_unbox(v_t_4440_);
v_res_4446_ = l_Lean_Compiler_LCNF_normCode___redArg___lam__0(v_pu_boxed_4444_, v_t_boxed_4445_, v_code_4441_, v_inst_4442_, v_____do__lift_4443_);
return v_res_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg(uint8_t v_pu_4447_, uint8_t v_t_4448_, lean_object* v_inst_4449_, lean_object* v_inst_4450_, lean_object* v_inst_4451_, lean_object* v_code_4452_){
_start:
{
lean_object* v_toBind_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___f_4456_; lean_object* v___x_4457_; 
v_toBind_4453_ = lean_ctor_get(v_inst_4450_, 1);
lean_inc(v_toBind_4453_);
lean_dec_ref(v_inst_4450_);
v___x_4454_ = lean_box(v_pu_4447_);
v___x_4455_ = lean_box(v_t_4448_);
v___f_4456_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4456_, 0, v___x_4454_);
lean_closure_set(v___f_4456_, 1, v___x_4455_);
lean_closure_set(v___f_4456_, 2, v_code_4452_);
lean_closure_set(v___f_4456_, 3, v_inst_4449_);
v___x_4457_ = lean_apply_4(v_toBind_4453_, lean_box(0), lean_box(0), v_inst_4451_, v___f_4456_);
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___boxed(lean_object* v_pu_4458_, lean_object* v_t_4459_, lean_object* v_inst_4460_, lean_object* v_inst_4461_, lean_object* v_inst_4462_, lean_object* v_code_4463_){
_start:
{
uint8_t v_pu_boxed_4464_; uint8_t v_t_boxed_4465_; lean_object* v_res_4466_; 
v_pu_boxed_4464_ = lean_unbox(v_pu_4458_);
v_t_boxed_4465_ = lean_unbox(v_t_4459_);
v_res_4466_ = l_Lean_Compiler_LCNF_normCode___redArg(v_pu_boxed_4464_, v_t_boxed_4465_, v_inst_4460_, v_inst_4461_, v_inst_4462_, v_code_4463_);
return v_res_4466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode(lean_object* v_m_4467_, uint8_t v_pu_4468_, uint8_t v_t_4469_, lean_object* v_inst_4470_, lean_object* v_inst_4471_, lean_object* v_inst_4472_, lean_object* v_code_4473_){
_start:
{
lean_object* v_toBind_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___f_4477_; lean_object* v___x_4478_; 
v_toBind_4474_ = lean_ctor_get(v_inst_4471_, 1);
lean_inc(v_toBind_4474_);
lean_dec_ref(v_inst_4471_);
v___x_4475_ = lean_box(v_pu_4468_);
v___x_4476_ = lean_box(v_t_4469_);
v___f_4477_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4477_, 0, v___x_4475_);
lean_closure_set(v___f_4477_, 1, v___x_4476_);
lean_closure_set(v___f_4477_, 2, v_code_4473_);
lean_closure_set(v___f_4477_, 3, v_inst_4470_);
v___x_4478_ = lean_apply_4(v_toBind_4474_, lean_box(0), lean_box(0), v_inst_4472_, v___f_4477_);
return v___x_4478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___boxed(lean_object* v_m_4479_, lean_object* v_pu_4480_, lean_object* v_t_4481_, lean_object* v_inst_4482_, lean_object* v_inst_4483_, lean_object* v_inst_4484_, lean_object* v_code_4485_){
_start:
{
uint8_t v_pu_boxed_4486_; uint8_t v_t_boxed_4487_; lean_object* v_res_4488_; 
v_pu_boxed_4486_ = lean_unbox(v_pu_4480_);
v_t_boxed_4487_ = lean_unbox(v_t_4481_);
v_res_4488_ = l_Lean_Compiler_LCNF_normCode(v_m_4479_, v_pu_boxed_4486_, v_t_boxed_4487_, v_inst_4482_, v_inst_4483_, v_inst_4484_, v_code_4485_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t v_pu_4489_, lean_object* v_e_4490_, lean_object* v_s_4491_, uint8_t v_translator_4492_){
_start:
{
lean_object* v___x_4494_; lean_object* v___x_4495_; 
v___x_4494_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4489_, v_s_4491_, v_translator_4492_, v_e_4490_);
v___x_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4494_);
return v___x_4495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg___boxed(lean_object* v_pu_4496_, lean_object* v_e_4497_, lean_object* v_s_4498_, lean_object* v_translator_4499_, lean_object* v_a_4500_){
_start:
{
uint8_t v_pu_boxed_4501_; uint8_t v_translator_boxed_4502_; lean_object* v_res_4503_; 
v_pu_boxed_4501_ = lean_unbox(v_pu_4496_);
v_translator_boxed_4502_ = lean_unbox(v_translator_4499_);
v_res_4503_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_boxed_4501_, v_e_4497_, v_s_4498_, v_translator_boxed_4502_);
lean_dec_ref(v_s_4498_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(uint8_t v_pu_4504_, lean_object* v_e_4505_, lean_object* v_s_4506_, uint8_t v_translator_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_){
_start:
{
lean_object* v___x_4513_; 
v___x_4513_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_4504_, v_e_4505_, v_s_4506_, v_translator_4507_);
return v___x_4513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___boxed(lean_object* v_pu_4514_, lean_object* v_e_4515_, lean_object* v_s_4516_, lean_object* v_translator_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_){
_start:
{
uint8_t v_pu_boxed_4523_; uint8_t v_translator_boxed_4524_; lean_object* v_res_4525_; 
v_pu_boxed_4523_ = lean_unbox(v_pu_4514_);
v_translator_boxed_4524_ = lean_unbox(v_translator_4517_);
v_res_4525_ = l_Lean_Compiler_LCNF_replaceExprFVars(v_pu_boxed_4523_, v_e_4515_, v_s_4516_, v_translator_boxed_4524_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_);
lean_dec(v_a_4521_);
lean_dec_ref(v_a_4520_);
lean_dec(v_a_4519_);
lean_dec_ref(v_a_4518_);
lean_dec_ref(v_s_4516_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t v_pu_4526_, lean_object* v_code_4527_, lean_object* v_s_4528_, uint8_t v_translator_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_){
_start:
{
lean_object* v___x_4535_; 
v___x_4535_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4526_, v_translator_4529_, v_code_4527_, v_s_4528_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_);
return v___x_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars___boxed(lean_object* v_pu_4536_, lean_object* v_code_4537_, lean_object* v_s_4538_, lean_object* v_translator_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_){
_start:
{
uint8_t v_pu_boxed_4545_; uint8_t v_translator_boxed_4546_; lean_object* v_res_4547_; 
v_pu_boxed_4545_ = lean_unbox(v_pu_4536_);
v_translator_boxed_4546_ = lean_unbox(v_translator_4539_);
v_res_4547_ = l_Lean_Compiler_LCNF_replaceFVars(v_pu_boxed_4545_, v_code_4537_, v_s_4538_, v_translator_boxed_4546_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
lean_dec(v_a_4543_);
lean_dec_ref(v_a_4542_);
lean_dec(v_a_4541_);
lean_dec_ref(v_a_4540_);
lean_dec_ref(v_s_4538_);
return v_res_4547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg(lean_object* v_a_4551_){
_start:
{
lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4553_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1));
v___x_4554_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4553_, v_a_4551_);
return v___x_4554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___boxed(lean_object* v_a_4555_, lean_object* v_a_4556_){
_start:
{
lean_object* v_res_4557_; 
v_res_4557_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4555_);
lean_dec(v_a_4555_);
return v_res_4557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName(lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_){
_start:
{
lean_object* v___x_4563_; 
v___x_4563_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4559_);
return v___x_4563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___boxed(lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_){
_start:
{
lean_object* v_res_4569_; 
v_res_4569_ = l_Lean_Compiler_LCNF_mkFreshJpName(v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
lean_dec(v_a_4565_);
lean_dec_ref(v_a_4564_);
return v_res_4569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t v_pu_4570_, lean_object* v_type_4571_, uint8_t v_borrow_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_){
_start:
{
lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v_a_4580_; lean_object* v___x_4581_; 
v___x_4578_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_4579_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4578_, v_a_4574_);
v_a_4580_ = lean_ctor_get(v___x_4579_, 0);
lean_inc(v_a_4580_);
lean_dec_ref(v___x_4579_);
v___x_4581_ = l_Lean_Compiler_LCNF_mkParam(v_pu_4570_, v_a_4580_, v_type_4571_, v_borrow_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_);
return v___x_4581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam___boxed(lean_object* v_pu_4582_, lean_object* v_type_4583_, lean_object* v_borrow_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_){
_start:
{
uint8_t v_pu_boxed_4590_; uint8_t v_borrow_boxed_4591_; lean_object* v_res_4592_; 
v_pu_boxed_4590_ = lean_unbox(v_pu_4582_);
v_borrow_boxed_4591_ = lean_unbox(v_borrow_4584_);
v_res_4592_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_boxed_4590_, v_type_4583_, v_borrow_boxed_4591_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_);
lean_dec(v_a_4588_);
lean_dec_ref(v_a_4587_);
lean_dec(v_a_4586_);
lean_dec_ref(v_a_4585_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object* v_a_4593_){
_start:
{
lean_object* v_config_4595_; lean_object* v___x_4596_; 
v_config_4595_ = lean_ctor_get(v_a_4593_, 0);
lean_inc_ref(v_config_4595_);
v___x_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4596_, 0, v_config_4595_);
return v___x_4596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg___boxed(lean_object* v_a_4597_, lean_object* v_a_4598_){
_start:
{
lean_object* v_res_4599_; 
v_res_4599_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4597_);
lean_dec_ref(v_a_4597_);
return v_res_4599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig(lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_){
_start:
{
lean_object* v___x_4605_; 
v___x_4605_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4600_);
return v___x_4605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___boxed(lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_){
_start:
{
lean_object* v_res_4611_; 
v_res_4611_ = l_Lean_Compiler_LCNF_getConfig(v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_);
lean_dec(v_a_4609_);
lean_dec_ref(v_a_4608_);
lean_dec(v_a_4607_);
lean_dec_ref(v_a_4606_);
return v_res_4611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object* v_x_4612_, lean_object* v_s_4613_, uint8_t v_phase_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_){
_start:
{
lean_object* v___x_4618_; lean_object* v_options_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4618_ = lean_st_mk_ref(v_s_4613_);
v_options_4619_ = lean_ctor_get(v_a_4615_, 2);
v___x_4620_ = l_Lean_Compiler_LCNF_toConfigOptions(v_options_4619_);
v___x_4621_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4621_, 0, v___x_4620_);
lean_ctor_set_uint8(v___x_4621_, sizeof(void*)*1, v_phase_4614_);
lean_inc(v___x_4618_);
v___x_4622_ = lean_apply_5(v_x_4612_, v___x_4621_, v___x_4618_, v_a_4615_, v_a_4616_, lean_box(0));
if (lean_obj_tag(v___x_4622_) == 0)
{
lean_object* v_a_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4631_; 
v_a_4623_ = lean_ctor_get(v___x_4622_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4622_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4625_ = v___x_4622_;
v_isShared_4626_ = v_isSharedCheck_4631_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_a_4623_);
lean_dec(v___x_4622_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4631_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4627_; lean_object* v___x_4629_; 
v___x_4627_ = lean_st_ref_get(v___x_4618_);
lean_dec(v___x_4618_);
lean_dec(v___x_4627_);
if (v_isShared_4626_ == 0)
{
v___x_4629_ = v___x_4625_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_a_4623_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
}
else
{
lean_dec(v___x_4618_);
return v___x_4622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg___boxed(lean_object* v_x_4632_, lean_object* v_s_4633_, lean_object* v_phase_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_){
_start:
{
uint8_t v_phase_boxed_4638_; lean_object* v_res_4639_; 
v_phase_boxed_4638_ = lean_unbox(v_phase_4634_);
v_res_4639_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4632_, v_s_4633_, v_phase_boxed_4638_, v_a_4635_, v_a_4636_);
return v_res_4639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run(lean_object* v_00_u03b1_4640_, lean_object* v_x_4641_, lean_object* v_s_4642_, uint8_t v_phase_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_){
_start:
{
lean_object* v___x_4647_; 
v___x_4647_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4641_, v_s_4642_, v_phase_4643_, v_a_4644_, v_a_4645_);
return v___x_4647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___boxed(lean_object* v_00_u03b1_4648_, lean_object* v_x_4649_, lean_object* v_s_4650_, lean_object* v_phase_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_){
_start:
{
uint8_t v_phase_boxed_4655_; lean_object* v_res_4656_; 
v_phase_boxed_4655_ = lean_unbox(v_phase_4651_);
v_res_4656_ = l_Lean_Compiler_LCNF_CompilerM_run(v_00_u03b1_4648_, v_x_4649_, v_s_4650_, v_phase_boxed_4655_, v_a_4652_, v_a_4653_);
return v_res_4656_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0(void){
_start:
{
lean_object* v___x_4657_; 
v___x_4657_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_){
_start:
{
lean_object* v___x_4662_; 
v___x_4662_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_){
_start:
{
lean_object* v_res_4667_; 
v_res_4667_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_);
lean_dec_ref(v_a_4666_);
lean_dec_ref(v_a_4665_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension(lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_){
_start:
{
lean_object* v___x_4672_; 
v___x_4672_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___boxed(lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_){
_start:
{
lean_object* v_res_4677_; 
v_res_4677_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension(v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_);
lean_dec_ref(v_a_4676_);
lean_dec_ref(v_a_4675_);
return v_res_4677_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; 
v___x_4681_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2));
v___x_4682_ = lean_unsigned_to_nat(14u);
v___x_4683_ = lean_unsigned_to_nat(177u);
v___x_4684_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1));
v___x_4685_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0));
v___x_4686_ = l_mkPanicMessageWithDecl(v___x_4685_, v___x_4684_, v___x_4683_, v___x_4682_, v___x_4681_);
return v___x_4686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(lean_object* v_inst_4687_, lean_object* v_inst_4688_, lean_object* v_snd_4689_, lean_object* v_inst_4690_, lean_object* v_s_4691_, lean_object* v_e_4692_){
_start:
{
lean_object* v_fst_4693_; lean_object* v_snd_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4709_; 
v_fst_4693_ = lean_ctor_get(v_s_4691_, 0);
v_snd_4694_ = lean_ctor_get(v_s_4691_, 1);
v_isSharedCheck_4709_ = !lean_is_exclusive(v_s_4691_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4696_ = v_s_4691_;
v_isShared_4697_ = v_isSharedCheck_4709_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_snd_4694_);
lean_inc(v_fst_4693_);
lean_dec(v_s_4691_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4709_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4698_; lean_object* v___y_4700_; lean_object* v___x_4705_; 
lean_inc(v_e_4692_);
v___x_4698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4698_, 0, v_e_4692_);
lean_ctor_set(v___x_4698_, 1, v_fst_4693_);
lean_inc(v_e_4692_);
lean_inc_ref(v_inst_4688_);
lean_inc_ref(v_inst_4687_);
v___x_4705_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4687_, v_inst_4688_, v_snd_4689_, v_e_4692_);
if (lean_obj_tag(v___x_4705_) == 0)
{
lean_object* v___x_4706_; lean_object* v___x_4707_; 
v___x_4706_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3);
v___x_4707_ = l_panic___redArg(v_inst_4690_, v___x_4706_);
v___y_4700_ = v___x_4707_;
goto v___jp_4699_;
}
else
{
lean_object* v_val_4708_; 
lean_dec(v_inst_4690_);
v_val_4708_ = lean_ctor_get(v___x_4705_, 0);
lean_inc(v_val_4708_);
lean_dec_ref(v___x_4705_);
v___y_4700_ = v_val_4708_;
goto v___jp_4699_;
}
v___jp_4699_:
{
lean_object* v___x_4701_; lean_object* v___x_4703_; 
v___x_4701_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4687_, v_inst_4688_, v_snd_4694_, v_e_4692_, v___y_4700_);
if (v_isShared_4697_ == 0)
{
lean_ctor_set(v___x_4696_, 1, v___x_4701_);
lean_ctor_set(v___x_4696_, 0, v___x_4698_);
v___x_4703_ = v___x_4696_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v___x_4698_);
lean_ctor_set(v_reuseFailAlloc_4704_, 1, v___x_4701_);
v___x_4703_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
return v___x_4703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(lean_object* v_inst_4712_, lean_object* v_inst_4713_, lean_object* v_inst_4714_, lean_object* v_oldState_4715_, lean_object* v_newState_4716_, lean_object* v_x_4717_, lean_object* v_s_4718_){
_start:
{
lean_object* v_fst_4719_; lean_object* v_snd_4720_; lean_object* v_fst_4721_; lean_object* v___f_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v_newEntries_4727_; lean_object* v___x_4728_; 
v_fst_4719_ = lean_ctor_get(v_newState_4716_, 0);
lean_inc(v_fst_4719_);
v_snd_4720_ = lean_ctor_get(v_newState_4716_, 1);
lean_inc(v_snd_4720_);
lean_dec_ref(v_newState_4716_);
v_fst_4721_ = lean_ctor_get(v_oldState_4715_, 0);
v___f_4722_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0), 6, 4);
lean_closure_set(v___f_4722_, 0, v_inst_4712_);
lean_closure_set(v___f_4722_, 1, v_inst_4713_);
lean_closure_set(v___f_4722_, 2, v_snd_4720_);
lean_closure_set(v___f_4722_, 3, v_inst_4714_);
v___x_4723_ = l_List_lengthTR___redArg(v_fst_4719_);
v___x_4724_ = l_List_lengthTR___redArg(v_fst_4721_);
v___x_4725_ = lean_nat_sub(v___x_4723_, v___x_4724_);
lean_dec(v___x_4724_);
lean_dec(v___x_4723_);
v___x_4726_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0));
lean_inc(v_fst_4719_);
v_newEntries_4727_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_fst_4719_, v_fst_4719_, v___x_4725_, v___x_4726_);
lean_dec(v_fst_4719_);
v___x_4728_ = l_List_foldl___redArg(v___f_4722_, v_s_4718_, v_newEntries_4727_);
return v___x_4728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(lean_object* v_inst_4729_, lean_object* v_inst_4730_, lean_object* v_inst_4731_, lean_object* v_oldState_4732_, lean_object* v_newState_4733_, lean_object* v_x_4734_, lean_object* v_s_4735_){
_start:
{
lean_object* v_res_4736_; 
v_res_4736_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(v_inst_4729_, v_inst_4730_, v_inst_4731_, v_oldState_4732_, v_newState_4733_, v_x_4734_, v_s_4735_);
lean_dec(v_x_4734_);
lean_dec_ref(v_oldState_4732_);
return v_res_4736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__2(lean_object* v___x_4737_){
_start:
{
lean_object* v___x_4739_; 
v___x_4739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4739_, 0, v___x_4737_);
return v___x_4739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__2___boxed(lean_object* v___x_4740_, lean_object* v___y_4741_){
_start:
{
lean_object* v_res_4742_; 
v_res_4742_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__2(v___x_4740_);
return v_res_4742_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0(void){
_start:
{
lean_object* v___x_4743_; 
v___x_4743_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4743_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1(void){
_start:
{
lean_object* v___x_4744_; lean_object* v___x_4745_; 
v___x_4744_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0);
v___x_4745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4745_, 0, v___x_4744_);
return v___x_4745_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2(void){
_start:
{
lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; 
v___x_4746_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1);
v___x_4747_ = lean_box(0);
v___x_4748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4748_, 0, v___x_4747_);
lean_ctor_set(v___x_4748_, 1, v___x_4746_);
return v___x_4748_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3(void){
_start:
{
lean_object* v___x_4749_; lean_object* v___f_4750_; 
v___x_4749_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2);
v___f_4750_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_4750_, 0, v___x_4749_);
return v___f_4750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object* v_inst_4751_, lean_object* v_inst_4752_, lean_object* v_inst_4753_){
_start:
{
lean_object* v___f_4755_; lean_object* v___f_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
v___f_4755_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4755_, 0, v_inst_4751_);
lean_closure_set(v___f_4755_, 1, v_inst_4752_);
lean_closure_set(v___f_4755_, 2, v_inst_4753_);
v___f_4756_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3);
v___x_4757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4757_, 0, v___f_4755_);
v___x_4758_ = lean_box(0);
v___x_4759_ = l_Lean_registerEnvExtension___redArg(v___f_4756_, v___x_4757_, v___x_4758_);
if (lean_obj_tag(v___x_4759_) == 0)
{
lean_object* v_a_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4767_; 
v_a_4760_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4762_ = v___x_4759_;
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_a_4760_);
lean_dec(v___x_4759_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
lean_object* v___x_4765_; 
if (v_isShared_4763_ == 0)
{
v___x_4765_ = v___x_4762_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_a_4760_);
v___x_4765_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
return v___x_4765_;
}
}
}
else
{
lean_object* v_a_4768_; lean_object* v___x_4770_; uint8_t v_isShared_4771_; uint8_t v_isSharedCheck_4775_; 
v_a_4768_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4775_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4775_ == 0)
{
v___x_4770_ = v___x_4759_;
v_isShared_4771_ = v_isSharedCheck_4775_;
goto v_resetjp_4769_;
}
else
{
lean_inc(v_a_4768_);
lean_dec(v___x_4759_);
v___x_4770_ = lean_box(0);
v_isShared_4771_ = v_isSharedCheck_4775_;
goto v_resetjp_4769_;
}
v_resetjp_4769_:
{
lean_object* v___x_4773_; 
if (v_isShared_4771_ == 0)
{
v___x_4773_ = v___x_4770_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v_a_4768_);
v___x_4773_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
return v___x_4773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object* v_inst_4776_, lean_object* v_inst_4777_, lean_object* v_inst_4778_, lean_object* v_a_4779_){
_start:
{
lean_object* v_res_4780_; 
v_res_4780_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4776_, v_inst_4777_, v_inst_4778_);
return v_res_4780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object* v_00_u03b1_4781_, lean_object* v_00_u03b2_4782_, lean_object* v_inst_4783_, lean_object* v_inst_4784_, lean_object* v_inst_4785_){
_start:
{
lean_object* v___x_4787_; 
v___x_4787_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4783_, v_inst_4784_, v_inst_4785_);
return v___x_4787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object* v_00_u03b1_4788_, lean_object* v_00_u03b2_4789_, lean_object* v_inst_4790_, lean_object* v_inst_4791_, lean_object* v_inst_4792_, lean_object* v_a_4793_){
_start:
{
lean_object* v_res_4794_; 
v_res_4794_ = l_Lean_Compiler_LCNF_CacheExtension_register(v_00_u03b1_4788_, v_00_u03b2_4789_, v_inst_4790_, v_inst_4791_, v_inst_4792_);
return v_res_4794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object* v_a_4795_, lean_object* v_inst_4796_, lean_object* v_inst_4797_, lean_object* v_b_4798_, lean_object* v_x_4799_){
_start:
{
lean_object* v_fst_4800_; lean_object* v_snd_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4810_; 
v_fst_4800_ = lean_ctor_get(v_x_4799_, 0);
v_snd_4801_ = lean_ctor_get(v_x_4799_, 1);
v_isSharedCheck_4810_ = !lean_is_exclusive(v_x_4799_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4803_ = v_x_4799_;
v_isShared_4804_ = v_isSharedCheck_4810_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_snd_4801_);
lean_inc(v_fst_4800_);
lean_dec(v_x_4799_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4810_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4808_; 
lean_inc(v_a_4795_);
v___x_4805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4805_, 0, v_a_4795_);
lean_ctor_set(v___x_4805_, 1, v_fst_4800_);
v___x_4806_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4796_, v_inst_4797_, v_snd_4801_, v_a_4795_, v_b_4798_);
if (v_isShared_4804_ == 0)
{
lean_ctor_set(v___x_4803_, 1, v___x_4806_);
lean_ctor_set(v___x_4803_, 0, v___x_4805_);
v___x_4808_ = v___x_4803_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v___x_4805_);
lean_ctor_set(v_reuseFailAlloc_4809_, 1, v___x_4806_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_4811_; 
v___x_4811_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4811_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; 
v___x_4812_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0);
v___x_4813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4813_, 0, v___x_4812_);
return v___x_4813_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2(void){
_start:
{
lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4814_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1);
v___x_4815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4815_, 0, v___x_4814_);
lean_ctor_set(v___x_4815_, 1, v___x_4814_);
return v___x_4815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object* v_inst_4816_, lean_object* v_inst_4817_, lean_object* v_ext_4818_, lean_object* v_a_4819_, lean_object* v_b_4820_, lean_object* v_a_4821_){
_start:
{
lean_object* v___x_4823_; lean_object* v_env_4824_; lean_object* v_nextMacroScope_4825_; lean_object* v_ngen_4826_; lean_object* v_auxDeclNGen_4827_; lean_object* v_traceState_4828_; lean_object* v_messages_4829_; lean_object* v_infoState_4830_; lean_object* v_snapshotTasks_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4846_; 
v___x_4823_ = lean_st_ref_take(v_a_4821_);
v_env_4824_ = lean_ctor_get(v___x_4823_, 0);
v_nextMacroScope_4825_ = lean_ctor_get(v___x_4823_, 1);
v_ngen_4826_ = lean_ctor_get(v___x_4823_, 2);
v_auxDeclNGen_4827_ = lean_ctor_get(v___x_4823_, 3);
v_traceState_4828_ = lean_ctor_get(v___x_4823_, 4);
v_messages_4829_ = lean_ctor_get(v___x_4823_, 6);
v_infoState_4830_ = lean_ctor_get(v___x_4823_, 7);
v_snapshotTasks_4831_ = lean_ctor_get(v___x_4823_, 8);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4823_);
if (v_isSharedCheck_4846_ == 0)
{
lean_object* v_unused_4847_; 
v_unused_4847_ = lean_ctor_get(v___x_4823_, 5);
lean_dec(v_unused_4847_);
v___x_4833_ = v___x_4823_;
v_isShared_4834_ = v_isSharedCheck_4846_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_snapshotTasks_4831_);
lean_inc(v_infoState_4830_);
lean_inc(v_messages_4829_);
lean_inc(v_traceState_4828_);
lean_inc(v_auxDeclNGen_4827_);
lean_inc(v_ngen_4826_);
lean_inc(v_nextMacroScope_4825_);
lean_inc(v_env_4824_);
lean_dec(v___x_4823_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4846_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v_asyncMode_4835_; lean_object* v___f_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4841_; 
v_asyncMode_4835_ = lean_ctor_get(v_ext_4818_, 2);
lean_inc(v_asyncMode_4835_);
v___f_4836_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4836_, 0, v_a_4819_);
lean_closure_set(v___f_4836_, 1, v_inst_4816_);
lean_closure_set(v___f_4836_, 2, v_inst_4817_);
lean_closure_set(v___f_4836_, 3, v_b_4820_);
v___x_4837_ = lean_box(0);
v___x_4838_ = l_Lean_EnvExtension_modifyState___redArg(v_ext_4818_, v_env_4824_, v___f_4836_, v_asyncMode_4835_, v___x_4837_);
lean_dec(v_asyncMode_4835_);
v___x_4839_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2);
if (v_isShared_4834_ == 0)
{
lean_ctor_set(v___x_4833_, 5, v___x_4839_);
lean_ctor_set(v___x_4833_, 0, v___x_4838_);
v___x_4841_ = v___x_4833_;
goto v_reusejp_4840_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v___x_4838_);
lean_ctor_set(v_reuseFailAlloc_4845_, 1, v_nextMacroScope_4825_);
lean_ctor_set(v_reuseFailAlloc_4845_, 2, v_ngen_4826_);
lean_ctor_set(v_reuseFailAlloc_4845_, 3, v_auxDeclNGen_4827_);
lean_ctor_set(v_reuseFailAlloc_4845_, 4, v_traceState_4828_);
lean_ctor_set(v_reuseFailAlloc_4845_, 5, v___x_4839_);
lean_ctor_set(v_reuseFailAlloc_4845_, 6, v_messages_4829_);
lean_ctor_set(v_reuseFailAlloc_4845_, 7, v_infoState_4830_);
lean_ctor_set(v_reuseFailAlloc_4845_, 8, v_snapshotTasks_4831_);
v___x_4841_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4840_;
}
v_reusejp_4840_:
{
lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4842_ = lean_st_ref_set(v_a_4821_, v___x_4841_);
v___x_4843_ = lean_box(0);
v___x_4844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4844_, 0, v___x_4843_);
return v___x_4844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object* v_inst_4848_, lean_object* v_inst_4849_, lean_object* v_ext_4850_, lean_object* v_a_4851_, lean_object* v_b_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_){
_start:
{
lean_object* v_res_4855_; 
v_res_4855_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4848_, v_inst_4849_, v_ext_4850_, v_a_4851_, v_b_4852_, v_a_4853_);
lean_dec(v_a_4853_);
return v_res_4855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object* v_00_u03b1_4856_, lean_object* v_00_u03b2_4857_, lean_object* v_inst_4858_, lean_object* v_inst_4859_, lean_object* v_inst_4860_, lean_object* v_ext_4861_, lean_object* v_a_4862_, lean_object* v_b_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_){
_start:
{
lean_object* v___x_4867_; 
v___x_4867_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4858_, v_inst_4859_, v_ext_4861_, v_a_4862_, v_b_4863_, v_a_4865_);
return v___x_4867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object* v_00_u03b1_4868_, lean_object* v_00_u03b2_4869_, lean_object* v_inst_4870_, lean_object* v_inst_4871_, lean_object* v_inst_4872_, lean_object* v_ext_4873_, lean_object* v_a_4874_, lean_object* v_b_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_){
_start:
{
lean_object* v_res_4879_; 
v_res_4879_ = l_Lean_Compiler_LCNF_CacheExtension_insert(v_00_u03b1_4868_, v_00_u03b2_4869_, v_inst_4870_, v_inst_4871_, v_inst_4872_, v_ext_4873_, v_a_4874_, v_b_4875_, v_a_4876_, v_a_4877_);
lean_dec(v_a_4877_);
lean_dec_ref(v_a_4876_);
lean_dec(v_inst_4872_);
return v_res_4879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(lean_object* v_inst_4880_, lean_object* v_inst_4881_, lean_object* v_ext_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_){
_start:
{
lean_object* v___x_4886_; lean_object* v_env_4887_; lean_object* v_asyncMode_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v_snd_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; 
v___x_4886_ = lean_st_ref_get(v_a_4884_);
v_env_4887_ = lean_ctor_get(v___x_4886_, 0);
lean_inc_ref(v_env_4887_);
lean_dec(v___x_4886_);
v_asyncMode_4888_ = lean_ctor_get(v_ext_4882_, 2);
v___x_4889_ = lean_box(0);
v___x_4890_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v_inst_4880_, v_inst_4881_);
v___x_4891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4891_, 0, v___x_4889_);
lean_ctor_set(v___x_4891_, 1, v___x_4890_);
v___x_4892_ = lean_box(0);
v___x_4893_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4891_, v_ext_4882_, v_env_4887_, v_asyncMode_4888_, v___x_4892_);
v_snd_4894_ = lean_ctor_get(v___x_4893_, 1);
lean_inc(v_snd_4894_);
lean_dec(v___x_4893_);
v___x_4895_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4880_, v_inst_4881_, v_snd_4894_, v_a_4883_);
v___x_4896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4896_, 0, v___x_4895_);
return v___x_4896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(lean_object* v_inst_4897_, lean_object* v_inst_4898_, lean_object* v_ext_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_){
_start:
{
lean_object* v_res_4903_; 
v_res_4903_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4897_, v_inst_4898_, v_ext_4899_, v_a_4900_, v_a_4901_);
lean_dec(v_a_4901_);
lean_dec_ref(v_ext_4899_);
return v_res_4903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_object* v_00_u03b1_4904_, lean_object* v_00_u03b2_4905_, lean_object* v_inst_4906_, lean_object* v_inst_4907_, lean_object* v_inst_4908_, lean_object* v_ext_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_){
_start:
{
lean_object* v___x_4914_; 
v___x_4914_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4906_, v_inst_4907_, v_ext_4909_, v_a_4910_, v_a_4912_);
return v___x_4914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(lean_object* v_00_u03b1_4915_, lean_object* v_00_u03b2_4916_, lean_object* v_inst_4917_, lean_object* v_inst_4918_, lean_object* v_inst_4919_, lean_object* v_ext_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_){
_start:
{
lean_object* v_res_4925_; 
v_res_4925_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f(v_00_u03b1_4915_, v_00_u03b2_4916_, v_inst_4917_, v_inst_4918_, v_inst_4919_, v_ext_4920_, v_a_4921_, v_a_4922_, v_a_4923_);
lean_dec(v_a_4923_);
lean_dec_ref(v_a_4922_);
lean_dec_ref(v_ext_4920_);
lean_dec(v_inst_4919_);
return v_res_4925_;
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
