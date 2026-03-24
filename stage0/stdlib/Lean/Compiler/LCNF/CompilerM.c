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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg(uint8_t v_phase_221_, lean_object* v_x_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_config_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_config_228_ = lean_ctor_get(v_a_223_, 0);
lean_inc_ref(v_config_228_);
v___x_229_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_229_, 0, v_config_228_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*1, v_phase_221_);
lean_inc(v_a_226_);
lean_inc_ref(v_a_225_);
lean_inc(v_a_224_);
v___x_230_ = lean_apply_5(v_x_222_, v___x_229_, v_a_224_, v_a_225_, v_a_226_, lean_box(0));
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg___boxed(lean_object* v_phase_231_, lean_object* v_x_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
uint8_t v_phase_boxed_238_; lean_object* v_res_239_; 
v_phase_boxed_238_ = lean_unbox(v_phase_231_);
v_res_239_ = l_Lean_Compiler_LCNF_withPhase___redArg(v_phase_boxed_238_, v_x_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase(lean_object* v_00_u03b1_240_, uint8_t v_phase_241_, lean_object* v_x_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_config_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_config_248_ = lean_ctor_get(v_a_243_, 0);
lean_inc_ref(v_config_248_);
v___x_249_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_249_, 0, v_config_248_);
lean_ctor_set_uint8(v___x_249_, sizeof(void*)*1, v_phase_241_);
lean_inc(v_a_246_);
lean_inc_ref(v_a_245_);
lean_inc(v_a_244_);
v___x_250_ = lean_apply_5(v_x_242_, v___x_249_, v_a_244_, v_a_245_, v_a_246_, lean_box(0));
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___boxed(lean_object* v_00_u03b1_251_, lean_object* v_phase_252_, lean_object* v_x_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
uint8_t v_phase_boxed_259_; lean_object* v_res_260_; 
v_phase_boxed_259_ = lean_unbox(v_phase_252_);
v_res_260_ = l_Lean_Compiler_LCNF_withPhase(v_00_u03b1_251_, v_phase_boxed_259_, v_x_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object* v_a_261_){
_start:
{
uint8_t v_phase_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_phase_263_ = lean_ctor_get_uint8(v_a_261_, sizeof(void*)*1);
v___x_264_ = lean_box(v_phase_263_);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg___boxed(lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_266_);
lean_dec_ref(v_a_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase(lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_269_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___boxed(lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Compiler_LCNF_getPhase(v_a_275_, v_a_276_, v_a_277_, v_a_278_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object* v_a_281_){
_start:
{
lean_object* v___x_283_; lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_294_; 
v___x_283_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_281_);
v_a_284_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_294_ == 0)
{
v___x_286_ = v___x_283_;
v_isShared_287_ = v_isSharedCheck_294_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_294_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
uint8_t v___x_288_; uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_288_ = lean_unbox(v_a_284_);
lean_dec(v_a_284_);
v___x_289_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_288_);
v___x_290_ = lean_box(v___x_289_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_290_);
v___x_292_ = v___x_286_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg___boxed(lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_295_);
lean_dec_ref(v_a_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity(lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_298_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___boxed(lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Compiler_LCNF_getPurity(v_a_304_, v_a_305_, v_a_306_, v_a_307_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg(lean_object* v_a_310_){
_start:
{
lean_object* v___x_312_; lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_328_; 
v___x_312_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_310_);
v_a_313_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_328_ == 0)
{
v___x_315_ = v___x_312_;
v_isShared_316_ = v_isSharedCheck_328_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_328_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
uint8_t v___x_317_; 
v___x_317_ = lean_unbox(v_a_313_);
lean_dec(v_a_313_);
if (v___x_317_ == 0)
{
uint8_t v___x_318_; lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_318_ = 1;
v___x_319_ = lean_box(v___x_318_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_319_);
v___x_321_ = v___x_315_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
else
{
uint8_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_323_ = 0;
v___x_324_ = lean_box(v___x_323_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_324_);
v___x_326_ = v___x_315_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_324_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg___boxed(lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_329_);
lean_dec_ref(v_a_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase(lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_332_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___boxed(lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_Compiler_LCNF_inBasePhase(v_a_338_, v_a_339_, v_a_340_, v_a_341_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
return v_res_343_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0(void){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_344_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_347_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
lean_ctor_set(v___x_349_, 2, v___x_348_);
lean_ctor_set(v___x_349_, 3, v___x_347_);
lean_ctor_set(v___x_349_, 4, v___x_347_);
lean_ctor_set(v___x_349_, 5, v___x_347_);
lean_ctor_set(v___x_349_, 6, v___x_347_);
lean_ctor_set(v___x_349_, 7, v___x_347_);
lean_ctor_set(v___x_349_, 8, v___x_347_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(lean_object* v_msgData_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_st_ref_get(v___y_354_);
v___x_357_ = lean_st_ref_get(v___y_352_);
v___x_358_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_351_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_381_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_381_ == 0)
{
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_381_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_381_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v_env_363_; lean_object* v_lctx_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_379_; 
v_env_363_ = lean_ctor_get(v___x_356_, 0);
lean_inc_ref(v_env_363_);
lean_dec(v___x_356_);
v_lctx_364_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; 
v_unused_380_ = lean_ctor_get(v___x_357_, 1);
lean_dec(v_unused_380_);
v___x_366_ = v___x_357_;
v_isShared_367_ = v_isSharedCheck_379_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_lctx_364_);
lean_dec(v___x_357_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_379_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v_options_368_; uint8_t v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
v_options_368_ = lean_ctor_get(v___y_353_, 2);
v___x_369_ = lean_unbox(v_a_359_);
lean_dec(v_a_359_);
v___x_370_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_364_, v___x_369_);
lean_dec_ref(v_lctx_364_);
v___x_371_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_368_);
v___x_372_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_372_, 0, v_env_363_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
lean_ctor_set(v___x_372_, 2, v___x_370_);
lean_ctor_set(v___x_372_, 3, v_options_368_);
if (v_isShared_367_ == 0)
{
lean_ctor_set_tag(v___x_366_, 3);
lean_ctor_set(v___x_366_, 1, v_msgData_350_);
lean_ctor_set(v___x_366_, 0, v___x_372_);
v___x_374_ = v___x_366_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_msgData_350_);
v___x_374_ = v_reuseFailAlloc_378_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_376_; 
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_374_);
v___x_376_ = v___x_361_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec(v___x_357_);
lean_dec(v___x_356_);
lean_dec_ref(v_msgData_350_);
v_a_382_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_358_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_358_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed(lean_object* v_msgData_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(v_msgData_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(lean_object* v_msg_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_options_405_; lean_object* v_ref_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_options_405_ = lean_ctor_get(v___y_402_, 2);
v_ref_406_ = lean_ctor_get(v___y_402_, 5);
v___x_407_ = lean_st_ref_get(v___y_403_);
v___x_408_ = lean_st_ref_get(v___y_401_);
v___x_409_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_400_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_432_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_432_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_432_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_432_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v_env_414_; lean_object* v_lctx_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_430_; 
v_env_414_ = lean_ctor_get(v___x_407_, 0);
lean_inc_ref(v_env_414_);
lean_dec(v___x_407_);
v_lctx_415_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; 
v_unused_431_ = lean_ctor_get(v___x_408_, 1);
lean_dec(v_unused_431_);
v___x_417_ = v___x_408_;
v_isShared_418_ = v_isSharedCheck_430_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_lctx_415_);
lean_dec(v___x_408_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_430_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
uint8_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_419_ = lean_unbox(v_a_410_);
lean_dec(v_a_410_);
v___x_420_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_415_, v___x_419_);
lean_dec_ref(v_lctx_415_);
v___x_421_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_405_);
v___x_422_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_422_, 0, v_env_414_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
lean_ctor_set(v___x_422_, 2, v___x_420_);
lean_ctor_set(v___x_422_, 3, v_options_405_);
if (v_isShared_418_ == 0)
{
lean_ctor_set_tag(v___x_417_, 3);
lean_ctor_set(v___x_417_, 1, v_msg_399_);
lean_ctor_set(v___x_417_, 0, v___x_422_);
v___x_424_ = v___x_417_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_msg_399_);
v___x_424_ = v_reuseFailAlloc_429_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_425_; lean_object* v___x_427_; 
lean_inc(v_ref_406_);
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v_ref_406_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
if (v_isShared_413_ == 0)
{
lean_ctor_set_tag(v___x_412_, 1);
lean_ctor_set(v___x_412_, 0, v___x_425_);
v___x_427_ = v___x_412_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
lean_dec(v___x_408_);
lean_dec(v___x_407_);
lean_dec_ref(v_msg_399_);
v_a_433_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_409_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_409_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg___boxed(lean_object* v_msg_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(lean_object* v_00_u03b1_448_, lean_object* v_msg_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___boxed(lean_object* v_00_u03b1_456_, lean_object* v_msg_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(v_00_u03b1_456_, v_msg_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(lean_object* v_a_464_, lean_object* v_x_465_){
_start:
{
if (lean_obj_tag(v_x_465_) == 0)
{
lean_object* v___x_466_; 
v___x_466_ = lean_box(0);
return v___x_466_;
}
else
{
lean_object* v_key_467_; lean_object* v_value_468_; lean_object* v_tail_469_; uint8_t v___x_470_; 
v_key_467_ = lean_ctor_get(v_x_465_, 0);
v_value_468_ = lean_ctor_get(v_x_465_, 1);
v_tail_469_ = lean_ctor_get(v_x_465_, 2);
v___x_470_ = l_Lean_instBEqFVarId_beq(v_key_467_, v_a_464_);
if (v___x_470_ == 0)
{
v_x_465_ = v_tail_469_;
goto _start;
}
else
{
lean_object* v___x_472_; 
lean_inc(v_value_468_);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v_value_468_);
return v___x_472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg___boxed(lean_object* v_a_473_, lean_object* v_x_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_473_, v_x_474_);
lean_dec(v_x_474_);
lean_dec(v_a_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object* v_m_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_buckets_478_; lean_object* v___x_479_; uint64_t v___x_480_; uint64_t v___x_481_; uint64_t v___x_482_; uint64_t v_fold_483_; uint64_t v___x_484_; uint64_t v___x_485_; uint64_t v___x_486_; size_t v___x_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; size_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_buckets_478_ = lean_ctor_get(v_m_476_, 1);
v___x_479_ = lean_array_get_size(v_buckets_478_);
v___x_480_ = l_Lean_instHashableFVarId_hash(v_a_477_);
v___x_481_ = 32ULL;
v___x_482_ = lean_uint64_shift_right(v___x_480_, v___x_481_);
v_fold_483_ = lean_uint64_xor(v___x_480_, v___x_482_);
v___x_484_ = 16ULL;
v___x_485_ = lean_uint64_shift_right(v_fold_483_, v___x_484_);
v___x_486_ = lean_uint64_xor(v_fold_483_, v___x_485_);
v___x_487_ = lean_uint64_to_usize(v___x_486_);
v___x_488_ = lean_usize_of_nat(v___x_479_);
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_sub(v___x_488_, v___x_489_);
v___x_491_ = lean_usize_land(v___x_487_, v___x_490_);
v___x_492_ = lean_array_uget_borrowed(v_buckets_478_, v___x_491_);
v___x_493_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_477_, v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg___boxed(lean_object* v_m_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_494_, v_a_495_);
lean_dec(v_a_495_);
lean_dec_ref(v_m_494_);
return v_res_496_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getType___closed__1(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l_Lean_Compiler_LCNF_getType___closed__0));
v___x_499_ = l_Lean_stringToMessageData(v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType(lean_object* v_fvarId_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_st_ref_get(v_a_502_);
v___x_507_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_501_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_558_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_558_ == 0)
{
v___x_510_ = v___x_507_;
v_isShared_511_ = v_isSharedCheck_558_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_558_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___y_513_; lean_object* v_lctx_524_; lean_object* v___y_526_; lean_object* v___y_541_; uint8_t v___x_555_; 
v_lctx_524_ = lean_ctor_get(v___x_506_, 0);
lean_inc_ref(v_lctx_524_);
lean_dec(v___x_506_);
v___x_555_ = lean_unbox(v_a_508_);
if (v___x_555_ == 0)
{
lean_object* v_letDeclsPure_556_; 
v_letDeclsPure_556_ = lean_ctor_get(v_lctx_524_, 2);
lean_inc_ref(v_letDeclsPure_556_);
v___y_541_ = v_letDeclsPure_556_;
goto v___jp_540_;
}
else
{
lean_object* v_letDeclsImpure_557_; 
v_letDeclsImpure_557_ = lean_ctor_get(v_lctx_524_, 3);
lean_inc_ref(v_letDeclsImpure_557_);
v___y_541_ = v_letDeclsImpure_557_;
goto v___jp_540_;
}
v___jp_512_:
{
lean_object* v___x_514_; 
v___x_514_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_513_, v_fvarId_500_);
lean_dec_ref(v___y_513_);
if (lean_obj_tag(v___x_514_) == 1)
{
lean_object* v_val_515_; lean_object* v_type_516_; lean_object* v___x_518_; 
lean_dec(v_fvarId_500_);
v_val_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_val_515_);
lean_dec_ref(v___x_514_);
v_type_516_ = lean_ctor_get(v_val_515_, 3);
lean_inc_ref(v_type_516_);
lean_dec(v_val_515_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v_type_516_);
v___x_518_ = v___x_510_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_type_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec(v___x_514_);
lean_del_object(v___x_510_);
v___x_520_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_521_ = l_Lean_MessageData_ofName(v_fvarId_500_);
v___x_522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_522_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
return v___x_523_;
}
}
v___jp_525_:
{
lean_object* v___x_527_; 
v___x_527_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_526_, v_fvarId_500_);
lean_dec_ref(v___y_526_);
if (lean_obj_tag(v___x_527_) == 1)
{
lean_object* v_val_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_536_; 
lean_dec_ref(v_lctx_524_);
lean_del_object(v___x_510_);
lean_dec(v_a_508_);
lean_dec(v_fvarId_500_);
v_val_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_536_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_val_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v_type_532_; lean_object* v___x_534_; 
v_type_532_ = lean_ctor_get(v_val_528_, 2);
lean_inc_ref(v_type_532_);
lean_dec(v_val_528_);
if (v_isShared_531_ == 0)
{
lean_ctor_set_tag(v___x_530_, 0);
lean_ctor_set(v___x_530_, 0, v_type_532_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_type_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
else
{
uint8_t v___x_537_; 
lean_dec(v___x_527_);
v___x_537_ = lean_unbox(v_a_508_);
lean_dec(v_a_508_);
if (v___x_537_ == 0)
{
lean_object* v_funDeclsPure_538_; 
v_funDeclsPure_538_ = lean_ctor_get(v_lctx_524_, 4);
lean_inc_ref(v_funDeclsPure_538_);
lean_dec_ref(v_lctx_524_);
v___y_513_ = v_funDeclsPure_538_;
goto v___jp_512_;
}
else
{
lean_object* v_funDeclsImpure_539_; 
v_funDeclsImpure_539_ = lean_ctor_get(v_lctx_524_, 5);
lean_inc_ref(v_funDeclsImpure_539_);
lean_dec_ref(v_lctx_524_);
v___y_513_ = v_funDeclsImpure_539_;
goto v___jp_512_;
}
}
}
v___jp_540_:
{
lean_object* v___x_542_; 
v___x_542_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_541_, v_fvarId_500_);
lean_dec_ref(v___y_541_);
if (lean_obj_tag(v___x_542_) == 1)
{
lean_object* v_val_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_551_; 
lean_dec_ref(v_lctx_524_);
lean_del_object(v___x_510_);
lean_dec(v_a_508_);
lean_dec(v_fvarId_500_);
v_val_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_551_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_val_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v_type_547_; lean_object* v___x_549_; 
v_type_547_ = lean_ctor_get(v_val_543_, 2);
lean_inc_ref(v_type_547_);
lean_dec(v_val_543_);
if (v_isShared_546_ == 0)
{
lean_ctor_set_tag(v___x_545_, 0);
lean_ctor_set(v___x_545_, 0, v_type_547_);
v___x_549_ = v___x_545_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_type_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
else
{
uint8_t v___x_552_; 
lean_dec(v___x_542_);
v___x_552_ = lean_unbox(v_a_508_);
if (v___x_552_ == 0)
{
lean_object* v_paramsPure_553_; 
v_paramsPure_553_ = lean_ctor_get(v_lctx_524_, 0);
lean_inc_ref(v_paramsPure_553_);
v___y_526_ = v_paramsPure_553_;
goto v___jp_525_;
}
else
{
lean_object* v_paramsImpure_554_; 
v_paramsImpure_554_ = lean_ctor_get(v_lctx_524_, 1);
lean_inc_ref(v_paramsImpure_554_);
v___y_526_ = v_paramsImpure_554_;
goto v___jp_525_;
}
}
}
}
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
lean_dec(v___x_506_);
lean_dec(v_fvarId_500_);
v_a_559_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_507_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_507_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType___boxed(lean_object* v_fvarId_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_Compiler_LCNF_getType(v_fvarId_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(lean_object* v_00_u03b2_574_, lean_object* v_m_575_, lean_object* v_a_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_575_, v_a_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___boxed(lean_object* v_00_u03b2_578_, lean_object* v_m_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(v_00_u03b2_578_, v_m_579_, v_a_580_);
lean_dec(v_a_580_);
lean_dec_ref(v_m_579_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(lean_object* v_00_u03b2_582_, lean_object* v_a_583_, lean_object* v_x_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_583_, v_x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_586_, lean_object* v_a_587_, lean_object* v_x_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(v_00_u03b2_586_, v_a_587_, v_x_588_);
lean_dec(v_x_588_);
lean_dec(v_a_587_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object* v_fvarId_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_st_ref_get(v_a_592_);
v___x_597_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_591_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_648_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_648_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_648_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_648_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___y_603_; lean_object* v_lctx_614_; lean_object* v___y_616_; lean_object* v___y_631_; uint8_t v___x_645_; 
v_lctx_614_ = lean_ctor_get(v___x_596_, 0);
lean_inc_ref(v_lctx_614_);
lean_dec(v___x_596_);
v___x_645_ = lean_unbox(v_a_598_);
if (v___x_645_ == 0)
{
lean_object* v_letDeclsPure_646_; 
v_letDeclsPure_646_ = lean_ctor_get(v_lctx_614_, 2);
lean_inc_ref(v_letDeclsPure_646_);
v___y_631_ = v_letDeclsPure_646_;
goto v___jp_630_;
}
else
{
lean_object* v_letDeclsImpure_647_; 
v_letDeclsImpure_647_ = lean_ctor_get(v_lctx_614_, 3);
lean_inc_ref(v_letDeclsImpure_647_);
v___y_631_ = v_letDeclsImpure_647_;
goto v___jp_630_;
}
v___jp_602_:
{
lean_object* v___x_604_; 
v___x_604_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_603_, v_fvarId_590_);
lean_dec_ref(v___y_603_);
if (lean_obj_tag(v___x_604_) == 1)
{
lean_object* v_val_605_; lean_object* v_binderName_606_; lean_object* v___x_608_; 
lean_dec(v_fvarId_590_);
v_val_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_val_605_);
lean_dec_ref(v___x_604_);
v_binderName_606_ = lean_ctor_get(v_val_605_, 1);
lean_inc(v_binderName_606_);
lean_dec(v_val_605_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v_binderName_606_);
v___x_608_ = v___x_600_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_binderName_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec(v___x_604_);
lean_del_object(v___x_600_);
v___x_610_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_611_ = l_Lean_MessageData_ofName(v_fvarId_590_);
v___x_612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_612_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
return v___x_613_;
}
}
v___jp_615_:
{
lean_object* v___x_617_; 
v___x_617_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_616_, v_fvarId_590_);
lean_dec_ref(v___y_616_);
if (lean_obj_tag(v___x_617_) == 1)
{
lean_object* v_val_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_626_; 
lean_dec_ref(v_lctx_614_);
lean_del_object(v___x_600_);
lean_dec(v_a_598_);
lean_dec(v_fvarId_590_);
v_val_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_626_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_626_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_val_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_626_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v_binderName_622_; lean_object* v___x_624_; 
v_binderName_622_ = lean_ctor_get(v_val_618_, 1);
lean_inc(v_binderName_622_);
lean_dec(v_val_618_);
if (v_isShared_621_ == 0)
{
lean_ctor_set_tag(v___x_620_, 0);
lean_ctor_set(v___x_620_, 0, v_binderName_622_);
v___x_624_ = v___x_620_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_binderName_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
else
{
uint8_t v___x_627_; 
lean_dec(v___x_617_);
v___x_627_ = lean_unbox(v_a_598_);
lean_dec(v_a_598_);
if (v___x_627_ == 0)
{
lean_object* v_funDeclsPure_628_; 
v_funDeclsPure_628_ = lean_ctor_get(v_lctx_614_, 4);
lean_inc_ref(v_funDeclsPure_628_);
lean_dec_ref(v_lctx_614_);
v___y_603_ = v_funDeclsPure_628_;
goto v___jp_602_;
}
else
{
lean_object* v_funDeclsImpure_629_; 
v_funDeclsImpure_629_ = lean_ctor_get(v_lctx_614_, 5);
lean_inc_ref(v_funDeclsImpure_629_);
lean_dec_ref(v_lctx_614_);
v___y_603_ = v_funDeclsImpure_629_;
goto v___jp_602_;
}
}
}
v___jp_630_:
{
lean_object* v___x_632_; 
v___x_632_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_631_, v_fvarId_590_);
lean_dec_ref(v___y_631_);
if (lean_obj_tag(v___x_632_) == 1)
{
lean_object* v_val_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_641_; 
lean_dec_ref(v_lctx_614_);
lean_del_object(v___x_600_);
lean_dec(v_a_598_);
lean_dec(v_fvarId_590_);
v_val_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_641_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_641_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_val_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_641_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_binderName_637_; lean_object* v___x_639_; 
v_binderName_637_ = lean_ctor_get(v_val_633_, 1);
lean_inc(v_binderName_637_);
lean_dec(v_val_633_);
if (v_isShared_636_ == 0)
{
lean_ctor_set_tag(v___x_635_, 0);
lean_ctor_set(v___x_635_, 0, v_binderName_637_);
v___x_639_ = v___x_635_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_binderName_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
else
{
uint8_t v___x_642_; 
lean_dec(v___x_632_);
v___x_642_ = lean_unbox(v_a_598_);
if (v___x_642_ == 0)
{
lean_object* v_paramsPure_643_; 
v_paramsPure_643_ = lean_ctor_get(v_lctx_614_, 0);
lean_inc_ref(v_paramsPure_643_);
v___y_616_ = v_paramsPure_643_;
goto v___jp_615_;
}
else
{
lean_object* v_paramsImpure_644_; 
v_paramsImpure_644_ = lean_ctor_get(v_lctx_614_, 1);
lean_inc_ref(v_paramsImpure_644_);
v___y_616_ = v_paramsImpure_644_;
goto v___jp_615_;
}
}
}
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec(v___x_596_);
lean_dec(v_fvarId_590_);
v_a_649_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_597_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_597_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName___boxed(lean_object* v_fvarId_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t v_pu_664_, lean_object* v_fvarId_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___x_668_; lean_object* v___y_670_; 
v___x_668_ = lean_st_ref_get(v_a_666_);
if (v_pu_664_ == 0)
{
lean_object* v_lctx_673_; lean_object* v_paramsPure_674_; 
v_lctx_673_ = lean_ctor_get(v___x_668_, 0);
lean_inc_ref(v_lctx_673_);
lean_dec(v___x_668_);
v_paramsPure_674_ = lean_ctor_get(v_lctx_673_, 0);
lean_inc_ref(v_paramsPure_674_);
lean_dec_ref(v_lctx_673_);
v___y_670_ = v_paramsPure_674_;
goto v___jp_669_;
}
else
{
lean_object* v_lctx_675_; lean_object* v_paramsImpure_676_; 
v_lctx_675_ = lean_ctor_get(v___x_668_, 0);
lean_inc_ref(v_lctx_675_);
lean_dec(v___x_668_);
v_paramsImpure_676_ = lean_ctor_get(v_lctx_675_, 1);
lean_inc_ref(v_paramsImpure_676_);
lean_dec_ref(v_lctx_675_);
v___y_670_ = v_paramsImpure_676_;
goto v___jp_669_;
}
v___jp_669_:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_670_, v_fvarId_665_);
lean_dec_ref(v___y_670_);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg___boxed(lean_object* v_pu_677_, lean_object* v_fvarId_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
uint8_t v_pu_boxed_681_; lean_object* v_res_682_; 
v_pu_boxed_681_ = lean_unbox(v_pu_677_);
v_res_682_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_boxed_681_, v_fvarId_678_, v_a_679_);
lean_dec(v_a_679_);
lean_dec(v_fvarId_678_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f(uint8_t v_pu_683_, lean_object* v_fvarId_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_683_, v_fvarId_684_, v_a_686_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___boxed(lean_object* v_pu_691_, lean_object* v_fvarId_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
uint8_t v_pu_boxed_698_; lean_object* v_res_699_; 
v_pu_boxed_698_ = lean_unbox(v_pu_691_);
v_res_699_ = l_Lean_Compiler_LCNF_findParam_x3f(v_pu_boxed_698_, v_fvarId_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_fvarId_692_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t v_pu_700_, lean_object* v_fvarId_701_, lean_object* v_a_702_){
_start:
{
lean_object* v___x_704_; lean_object* v___y_706_; 
v___x_704_ = lean_st_ref_get(v_a_702_);
if (v_pu_700_ == 0)
{
lean_object* v_lctx_709_; lean_object* v_letDeclsPure_710_; 
v_lctx_709_ = lean_ctor_get(v___x_704_, 0);
lean_inc_ref(v_lctx_709_);
lean_dec(v___x_704_);
v_letDeclsPure_710_ = lean_ctor_get(v_lctx_709_, 2);
lean_inc_ref(v_letDeclsPure_710_);
lean_dec_ref(v_lctx_709_);
v___y_706_ = v_letDeclsPure_710_;
goto v___jp_705_;
}
else
{
lean_object* v_lctx_711_; lean_object* v_letDeclsImpure_712_; 
v_lctx_711_ = lean_ctor_get(v___x_704_, 0);
lean_inc_ref(v_lctx_711_);
lean_dec(v___x_704_);
v_letDeclsImpure_712_ = lean_ctor_get(v_lctx_711_, 3);
lean_inc_ref(v_letDeclsImpure_712_);
lean_dec_ref(v_lctx_711_);
v___y_706_ = v_letDeclsImpure_712_;
goto v___jp_705_;
}
v___jp_705_:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_706_, v_fvarId_701_);
lean_dec_ref(v___y_706_);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg___boxed(lean_object* v_pu_713_, lean_object* v_fvarId_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
uint8_t v_pu_boxed_717_; lean_object* v_res_718_; 
v_pu_boxed_717_ = lean_unbox(v_pu_713_);
v_res_718_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_boxed_717_, v_fvarId_714_, v_a_715_);
lean_dec(v_a_715_);
lean_dec(v_fvarId_714_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(uint8_t v_pu_719_, lean_object* v_fvarId_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_719_, v_fvarId_720_, v_a_722_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___boxed(lean_object* v_pu_727_, lean_object* v_fvarId_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
uint8_t v_pu_boxed_734_; lean_object* v_res_735_; 
v_pu_boxed_734_ = lean_unbox(v_pu_727_);
v_res_735_ = l_Lean_Compiler_LCNF_findLetDecl_x3f(v_pu_boxed_734_, v_fvarId_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_fvarId_728_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t v_pu_736_, lean_object* v_fvarId_737_, lean_object* v_a_738_){
_start:
{
lean_object* v___x_740_; lean_object* v___y_742_; 
v___x_740_ = lean_st_ref_get(v_a_738_);
if (v_pu_736_ == 0)
{
lean_object* v_lctx_745_; lean_object* v_funDeclsPure_746_; 
v_lctx_745_ = lean_ctor_get(v___x_740_, 0);
lean_inc_ref(v_lctx_745_);
lean_dec(v___x_740_);
v_funDeclsPure_746_ = lean_ctor_get(v_lctx_745_, 4);
lean_inc_ref(v_funDeclsPure_746_);
lean_dec_ref(v_lctx_745_);
v___y_742_ = v_funDeclsPure_746_;
goto v___jp_741_;
}
else
{
lean_object* v_lctx_747_; lean_object* v_funDeclsImpure_748_; 
v_lctx_747_ = lean_ctor_get(v___x_740_, 0);
lean_inc_ref(v_lctx_747_);
lean_dec(v___x_740_);
v_funDeclsImpure_748_ = lean_ctor_get(v_lctx_747_, 5);
lean_inc_ref(v_funDeclsImpure_748_);
lean_dec_ref(v_lctx_747_);
v___y_742_ = v_funDeclsImpure_748_;
goto v___jp_741_;
}
v___jp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_742_, v_fvarId_737_);
lean_dec_ref(v___y_742_);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg___boxed(lean_object* v_pu_749_, lean_object* v_fvarId_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
uint8_t v_pu_boxed_753_; lean_object* v_res_754_; 
v_pu_boxed_753_ = lean_unbox(v_pu_749_);
v_res_754_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_boxed_753_, v_fvarId_750_, v_a_751_);
lean_dec(v_a_751_);
lean_dec(v_fvarId_750_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(uint8_t v_pu_755_, lean_object* v_fvarId_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_755_, v_fvarId_756_, v_a_758_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___boxed(lean_object* v_pu_763_, lean_object* v_fvarId_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
uint8_t v_pu_boxed_770_; lean_object* v_res_771_; 
v_pu_boxed_770_ = lean_unbox(v_pu_763_);
v_res_771_ = l_Lean_Compiler_LCNF_findFunDecl_x3f(v_pu_boxed_770_, v_fvarId_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_fvarId_764_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t v_pu_772_, lean_object* v_fvarId_773_, lean_object* v_a_774_){
_start:
{
lean_object* v___x_776_; lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_797_; 
v___x_776_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_772_, v_fvarId_773_, v_a_774_);
v_a_777_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_797_ == 0)
{
v___x_779_ = v___x_776_;
v_isShared_780_ = v_isSharedCheck_797_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_776_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_797_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
if (lean_obj_tag(v_a_777_) == 1)
{
lean_object* v_val_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_792_; 
v_val_781_ = lean_ctor_get(v_a_777_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v_a_777_);
if (v_isSharedCheck_792_ == 0)
{
v___x_783_ = v_a_777_;
v_isShared_784_ = v_isSharedCheck_792_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_val_781_);
lean_dec(v_a_777_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_792_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v_value_785_; lean_object* v___x_787_; 
v_value_785_ = lean_ctor_get(v_val_781_, 3);
lean_inc(v_value_785_);
lean_dec(v_val_781_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v_value_785_);
v___x_787_ = v___x_783_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_value_785_);
v___x_787_ = v_reuseFailAlloc_791_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_789_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_787_);
v___x_789_ = v___x_779_;
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
else
{
lean_object* v___x_793_; lean_object* v___x_795_; 
lean_dec(v_a_777_);
v___x_793_ = lean_box(0);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_793_);
v___x_795_ = v___x_779_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg___boxed(lean_object* v_pu_798_, lean_object* v_fvarId_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
uint8_t v_pu_boxed_802_; lean_object* v_res_803_; 
v_pu_boxed_802_ = lean_unbox(v_pu_798_);
v_res_803_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_boxed_802_, v_fvarId_799_, v_a_800_);
lean_dec(v_a_800_);
lean_dec(v_fvarId_799_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f(uint8_t v_pu_804_, lean_object* v_fvarId_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_804_, v_fvarId_805_, v_a_807_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___boxed(lean_object* v_pu_812_, lean_object* v_fvarId_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
uint8_t v_pu_boxed_819_; lean_object* v_res_820_; 
v_pu_boxed_819_ = lean_unbox(v_pu_812_);
v_res_820_ = l_Lean_Compiler_LCNF_findLetValue_x3f(v_pu_boxed_819_, v_fvarId_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_fvarId_813_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg(lean_object* v_fvarId_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
uint8_t v___x_825_; lean_object* v___x_826_; 
v___x_825_ = 0;
v___x_826_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_825_, v_fvarId_821_, v_a_822_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_870_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_870_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_870_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_870_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
if (lean_obj_tag(v_a_827_) == 1)
{
lean_object* v_val_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_869_; 
v_val_837_ = lean_ctor_get(v_a_827_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v_a_827_);
if (v_isSharedCheck_869_ == 0)
{
v___x_839_ = v_a_827_;
v_isShared_840_ = v_isSharedCheck_869_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_val_837_);
lean_dec(v_a_827_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_869_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
if (lean_obj_tag(v_val_837_) == 3)
{
lean_object* v_declName_841_; lean_object* v___x_842_; lean_object* v_env_843_; uint8_t v___x_844_; lean_object* v___x_845_; 
lean_del_object(v___x_829_);
v_declName_841_ = lean_ctor_get(v_val_837_, 0);
lean_inc(v_declName_841_);
lean_dec_ref(v_val_837_);
v___x_842_ = lean_st_ref_get(v_a_823_);
v_env_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc_ref(v_env_843_);
lean_dec(v___x_842_);
v___x_844_ = 0;
v___x_845_ = l_Lean_Environment_find_x3f(v_env_843_, v_declName_841_, v___x_844_);
if (lean_obj_tag(v___x_845_) == 1)
{
lean_object* v_val_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_864_; 
lean_del_object(v___x_839_);
v_val_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_864_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_864_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_val_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_864_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
if (lean_obj_tag(v_val_846_) == 6)
{
lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_858_; 
lean_del_object(v___x_848_);
v_isSharedCheck_858_ = !lean_is_exclusive(v_val_846_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v_val_846_, 0);
lean_dec(v_unused_859_);
v___x_851_ = v_val_846_;
v_isShared_852_ = v_isSharedCheck_858_;
goto v_resetjp_850_;
}
else
{
lean_dec(v_val_846_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_858_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
uint8_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_853_ = 1;
v___x_854_ = lean_box(v___x_853_);
if (v_isShared_852_ == 0)
{
lean_ctor_set_tag(v___x_851_, 0);
lean_ctor_set(v___x_851_, 0, v___x_854_);
v___x_856_ = v___x_851_;
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
else
{
lean_object* v___x_860_; lean_object* v___x_862_; 
lean_dec(v_val_846_);
v___x_860_ = lean_box(v___x_844_);
if (v_isShared_849_ == 0)
{
lean_ctor_set_tag(v___x_848_, 0);
lean_ctor_set(v___x_848_, 0, v___x_860_);
v___x_862_ = v___x_848_;
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
}
}
else
{
lean_object* v___x_865_; lean_object* v___x_867_; 
lean_dec(v___x_845_);
v___x_865_ = lean_box(v___x_844_);
if (v_isShared_840_ == 0)
{
lean_ctor_set_tag(v___x_839_, 0);
lean_ctor_set(v___x_839_, 0, v___x_865_);
v___x_867_ = v___x_839_;
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
}
else
{
lean_del_object(v___x_839_);
lean_dec(v_val_837_);
goto v___jp_831_;
}
}
}
else
{
lean_dec(v_a_827_);
goto v___jp_831_;
}
v___jp_831_:
{
uint8_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_832_ = 0;
v___x_833_ = lean_box(v___x_832_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_833_);
v___x_835_ = v___x_829_;
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
}
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
v_a_871_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_826_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_826_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg___boxed(lean_object* v_fvarId_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_879_, v_a_880_, v_a_881_);
lean_dec(v_a_881_);
lean_dec(v_a_880_);
lean_dec(v_fvarId_879_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp(lean_object* v_fvarId_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_884_, v_a_886_, v_a_888_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___boxed(lean_object* v_fvarId_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_Compiler_LCNF_isConstructorApp(v_fvarId_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_fvarId_891_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(lean_object* v_arg_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
if (lean_obj_tag(v_arg_898_) == 1)
{
lean_object* v_fvarId_902_; lean_object* v___x_903_; 
v_fvarId_902_ = lean_ctor_get(v_arg_898_, 0);
v___x_903_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_902_, v_a_899_, v_a_900_);
return v___x_903_;
}
else
{
uint8_t v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = 0;
v___x_905_ = lean_box(v___x_904_);
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
return v___x_906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg___boxed(lean_object* v_arg_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_907_, v_a_908_, v_a_909_);
lean_dec(v_a_909_);
lean_dec(v_a_908_);
lean_dec(v_arg_907_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp(uint8_t v_pu_912_, lean_object* v_arg_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_913_, v_a_915_, v_a_917_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___boxed(lean_object* v_pu_920_, lean_object* v_arg_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
uint8_t v_pu_boxed_927_; lean_object* v_res_928_; 
v_pu_boxed_927_ = lean_unbox(v_pu_920_);
v_res_928_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp(v_pu_boxed_927_, v_arg_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_arg_921_);
return v_res_928_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getParam___closed__1(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParam___closed__0));
v___x_931_ = l_Lean_stringToMessageData(v___x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam(uint8_t v_pu_932_, lean_object* v_fvarId_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v___x_939_; lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_952_; 
v___x_939_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_932_, v_fvarId_933_, v_a_935_);
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_952_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_952_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_952_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
if (lean_obj_tag(v_a_940_) == 1)
{
lean_object* v_val_944_; lean_object* v___x_946_; 
lean_dec(v_fvarId_933_);
v_val_944_ = lean_ctor_get(v_a_940_, 0);
lean_inc(v_val_944_);
lean_dec_ref(v_a_940_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v_val_944_);
v___x_946_ = v___x_942_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_val_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
lean_del_object(v___x_942_);
lean_dec(v_a_940_);
v___x_948_ = lean_obj_once(&l_Lean_Compiler_LCNF_getParam___closed__1, &l_Lean_Compiler_LCNF_getParam___closed__1_once, _init_l_Lean_Compiler_LCNF_getParam___closed__1);
v___x_949_ = l_Lean_MessageData_ofName(v_fvarId_933_);
v___x_950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_948_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_950_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
return v___x_951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam___boxed(lean_object* v_pu_953_, lean_object* v_fvarId_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
uint8_t v_pu_boxed_960_; lean_object* v_res_961_; 
v_pu_boxed_960_ = lean_unbox(v_pu_953_);
v_res_961_ = l_Lean_Compiler_LCNF_getParam(v_pu_boxed_960_, v_fvarId_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
return v_res_961_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l_Lean_Compiler_LCNF_getLetDecl___closed__0));
v___x_964_ = l_Lean_stringToMessageData(v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl(uint8_t v_pu_965_, lean_object* v_fvarId_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v___x_972_; lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_985_; 
v___x_972_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_965_, v_fvarId_966_, v_a_968_);
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_985_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_985_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_985_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
if (lean_obj_tag(v_a_973_) == 1)
{
lean_object* v_val_977_; lean_object* v___x_979_; 
lean_dec(v_fvarId_966_);
v_val_977_ = lean_ctor_get(v_a_973_, 0);
lean_inc(v_val_977_);
lean_dec_ref(v_a_973_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v_val_977_);
v___x_979_ = v___x_975_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_val_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
else
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
lean_del_object(v___x_975_);
lean_dec(v_a_973_);
v___x_981_ = lean_obj_once(&l_Lean_Compiler_LCNF_getLetDecl___closed__1, &l_Lean_Compiler_LCNF_getLetDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1);
v___x_982_ = l_Lean_MessageData_ofName(v_fvarId_966_);
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_983_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl___boxed(lean_object* v_pu_986_, lean_object* v_fvarId_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
uint8_t v_pu_boxed_993_; lean_object* v_res_994_; 
v_pu_boxed_993_ = lean_unbox(v_pu_986_);
v_res_994_ = l_Lean_Compiler_LCNF_getLetDecl(v_pu_boxed_993_, v_fvarId_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
return v_res_994_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = ((lean_object*)(l_Lean_Compiler_LCNF_getFunDecl___closed__0));
v___x_997_ = l_Lean_stringToMessageData(v___x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t v_pu_998_, lean_object* v_fvarId_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v___x_1005_; lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1018_; 
v___x_1005_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_998_, v_fvarId_999_, v_a_1001_);
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1018_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1018_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
if (lean_obj_tag(v_a_1006_) == 1)
{
lean_object* v_val_1010_; lean_object* v___x_1012_; 
lean_dec(v_fvarId_999_);
v_val_1010_ = lean_ctor_get(v_a_1006_, 0);
lean_inc(v_val_1010_);
lean_dec_ref(v_a_1006_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v_val_1010_);
v___x_1012_ = v___x_1008_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_val_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_del_object(v___x_1008_);
lean_dec(v_a_1006_);
v___x_1014_ = lean_obj_once(&l_Lean_Compiler_LCNF_getFunDecl___closed__1, &l_Lean_Compiler_LCNF_getFunDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1);
v___x_1015_ = l_Lean_MessageData_ofName(v_fvarId_999_);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_1016_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
return v___x_1017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl___boxed(lean_object* v_pu_1019_, lean_object* v_fvarId_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
uint8_t v_pu_boxed_1026_; lean_object* v_res_1027_; 
v_pu_boxed_1026_ = lean_unbox(v_pu_1019_);
v_res_1027_ = l_Lean_Compiler_LCNF_getFunDecl(v_pu_boxed_1026_, v_fvarId_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg(lean_object* v_f_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v___x_1031_; lean_object* v_lctx_1032_; lean_object* v_nextIdx_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1044_; 
v___x_1031_ = lean_st_ref_take(v_a_1029_);
v_lctx_1032_ = lean_ctor_get(v___x_1031_, 0);
v_nextIdx_1033_ = lean_ctor_get(v___x_1031_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1035_ = v___x_1031_;
v_isShared_1036_ = v_isSharedCheck_1044_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_nextIdx_1033_);
lean_inc(v_lctx_1032_);
lean_dec(v___x_1031_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1044_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1037_ = lean_apply_1(v_f_1028_, v_lctx_1032_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1037_);
v___x_1039_ = v___x_1035_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_nextIdx_1033_);
v___x_1039_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1040_ = lean_st_ref_set(v_a_1029_, v___x_1039_);
v___x_1041_ = lean_box(0);
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
return v___x_1042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg___boxed(lean_object* v_f_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_Compiler_LCNF_modifyLCtx___redArg(v_f_1045_, v_a_1046_);
lean_dec(v_a_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx(lean_object* v_f_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v___x_1055_; lean_object* v_lctx_1056_; lean_object* v_nextIdx_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1068_; 
v___x_1055_ = lean_st_ref_take(v_a_1051_);
v_lctx_1056_ = lean_ctor_get(v___x_1055_, 0);
v_nextIdx_1057_ = lean_ctor_get(v___x_1055_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1059_ = v___x_1055_;
v_isShared_1060_ = v_isSharedCheck_1068_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_nextIdx_1057_);
lean_inc(v_lctx_1056_);
lean_dec(v___x_1055_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1068_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1061_ = lean_apply_1(v_f_1049_, v_lctx_1056_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v___x_1061_);
v___x_1063_ = v___x_1059_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_nextIdx_1057_);
v___x_1063_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1064_ = lean_st_ref_set(v_a_1051_, v___x_1063_);
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___boxed(lean_object* v_f_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_Compiler_LCNF_modifyLCtx(v_f_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t v_pu_1076_, lean_object* v_decl_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v___x_1080_; lean_object* v_lctx_1081_; lean_object* v_nextIdx_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1093_; 
v___x_1080_ = lean_st_ref_take(v_a_1078_);
v_lctx_1081_ = lean_ctor_get(v___x_1080_, 0);
v_nextIdx_1082_ = lean_ctor_get(v___x_1080_, 1);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1084_ = v___x_1080_;
v_isShared_1085_ = v_isSharedCheck_1093_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_nextIdx_1082_);
lean_inc(v_lctx_1081_);
lean_dec(v___x_1080_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1093_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1086_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_1076_, v_lctx_1081_, v_decl_1077_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1086_);
v___x_1088_ = v___x_1084_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_nextIdx_1082_);
v___x_1088_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = lean_st_ref_set(v_a_1078_, v___x_1088_);
v___x_1090_ = lean_box(0);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg___boxed(lean_object* v_pu_1094_, lean_object* v_decl_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
uint8_t v_pu_boxed_1098_; lean_object* v_res_1099_; 
v_pu_boxed_1098_ = lean_unbox(v_pu_1094_);
v_res_1099_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_boxed_1098_, v_decl_1095_, v_a_1096_);
lean_dec(v_a_1096_);
lean_dec_ref(v_decl_1095_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(uint8_t v_pu_1100_, lean_object* v_decl_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1100_, v_decl_1101_, v_a_1103_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___boxed(lean_object* v_pu_1108_, lean_object* v_decl_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
uint8_t v_pu_boxed_1115_; lean_object* v_res_1116_; 
v_pu_boxed_1115_ = lean_unbox(v_pu_1108_);
v_res_1116_ = l_Lean_Compiler_LCNF_eraseLetDecl(v_pu_boxed_1115_, v_decl_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec_ref(v_decl_1109_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t v_pu_1117_, lean_object* v_decl_1118_, uint8_t v_recursive_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v___x_1122_; lean_object* v_lctx_1123_; lean_object* v_nextIdx_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1135_; 
v___x_1122_ = lean_st_ref_take(v_a_1120_);
v_lctx_1123_ = lean_ctor_get(v___x_1122_, 0);
v_nextIdx_1124_ = lean_ctor_get(v___x_1122_, 1);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1126_ = v___x_1122_;
v_isShared_1127_ = v_isSharedCheck_1135_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_nextIdx_1124_);
lean_inc(v_lctx_1123_);
lean_dec(v___x_1122_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1135_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1128_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_1117_, v_lctx_1123_, v_decl_1118_, v_recursive_1119_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1128_);
v___x_1130_ = v___x_1126_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_nextIdx_1124_);
v___x_1130_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1131_ = lean_st_ref_set(v_a_1120_, v___x_1130_);
v___x_1132_ = lean_box(0);
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
return v___x_1133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg___boxed(lean_object* v_pu_1136_, lean_object* v_decl_1137_, lean_object* v_recursive_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
uint8_t v_pu_boxed_1141_; uint8_t v_recursive_boxed_1142_; lean_object* v_res_1143_; 
v_pu_boxed_1141_ = lean_unbox(v_pu_1136_);
v_recursive_boxed_1142_ = lean_unbox(v_recursive_1138_);
v_res_1143_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_boxed_1141_, v_decl_1137_, v_recursive_boxed_1142_, v_a_1139_);
lean_dec(v_a_1139_);
lean_dec_ref(v_decl_1137_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(uint8_t v_pu_1144_, lean_object* v_decl_1145_, uint8_t v_recursive_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1144_, v_decl_1145_, v_recursive_1146_, v_a_1148_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___boxed(lean_object* v_pu_1153_, lean_object* v_decl_1154_, lean_object* v_recursive_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
uint8_t v_pu_boxed_1161_; uint8_t v_recursive_boxed_1162_; lean_object* v_res_1163_; 
v_pu_boxed_1161_ = lean_unbox(v_pu_1153_);
v_recursive_boxed_1162_ = lean_unbox(v_recursive_1155_);
v_res_1163_ = l_Lean_Compiler_LCNF_eraseFunDecl(v_pu_boxed_1161_, v_decl_1154_, v_recursive_boxed_1162_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec_ref(v_decl_1154_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t v_pu_1164_, lean_object* v_code_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v___x_1168_; lean_object* v_lctx_1169_; lean_object* v_nextIdx_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1181_; 
v___x_1168_ = lean_st_ref_take(v_a_1166_);
v_lctx_1169_ = lean_ctor_get(v___x_1168_, 0);
v_nextIdx_1170_ = lean_ctor_get(v___x_1168_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1172_ = v___x_1168_;
v_isShared_1173_ = v_isSharedCheck_1181_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_nextIdx_1170_);
lean_inc(v_lctx_1169_);
lean_dec(v___x_1168_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1181_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_1174_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_1164_, v_code_1165_, v_lctx_1169_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v___x_1174_);
v___x_1176_ = v___x_1172_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_nextIdx_1170_);
v___x_1176_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1177_ = lean_st_ref_set(v_a_1166_, v___x_1176_);
v___x_1178_ = lean_box(0);
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
return v___x_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg___boxed(lean_object* v_pu_1182_, lean_object* v_code_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
uint8_t v_pu_boxed_1186_; lean_object* v_res_1187_; 
v_pu_boxed_1186_ = lean_unbox(v_pu_1182_);
v_res_1187_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_boxed_1186_, v_code_1183_, v_a_1184_);
lean_dec(v_a_1184_);
lean_dec_ref(v_code_1183_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode(uint8_t v_pu_1188_, lean_object* v_code_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_1188_, v_code_1189_, v_a_1191_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___boxed(lean_object* v_pu_1196_, lean_object* v_code_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
uint8_t v_pu_boxed_1203_; lean_object* v_res_1204_; 
v_pu_boxed_1203_ = lean_unbox(v_pu_1196_);
v_res_1204_ = l_Lean_Compiler_LCNF_eraseCode(v_pu_boxed_1203_, v_code_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec_ref(v_code_1197_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t v_pu_1205_, lean_object* v_param_1206_, lean_object* v_a_1207_){
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
v___x_1215_ = l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_1205_, v_lctx_1210_, v_param_1206_);
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
v___x_1218_ = lean_st_ref_set(v_a_1207_, v___x_1217_);
v___x_1219_ = lean_box(0);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg___boxed(lean_object* v_pu_1223_, lean_object* v_param_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
uint8_t v_pu_boxed_1227_; lean_object* v_res_1228_; 
v_pu_boxed_1227_ = lean_unbox(v_pu_1223_);
v_res_1228_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_boxed_1227_, v_param_1224_, v_a_1225_);
lean_dec(v_a_1225_);
lean_dec_ref(v_param_1224_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam(uint8_t v_pu_1229_, lean_object* v_param_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_1229_, v_param_1230_, v_a_1232_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___boxed(lean_object* v_pu_1237_, lean_object* v_param_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
uint8_t v_pu_boxed_1244_; lean_object* v_res_1245_; 
v_pu_boxed_1244_ = lean_unbox(v_pu_1237_);
v_res_1245_ = l_Lean_Compiler_LCNF_eraseParam(v_pu_boxed_1244_, v_param_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec_ref(v_param_1238_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t v_pu_1246_, lean_object* v_params_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v___x_1250_; lean_object* v_lctx_1251_; lean_object* v_nextIdx_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1263_; 
v___x_1250_ = lean_st_ref_take(v_a_1248_);
v_lctx_1251_ = lean_ctor_get(v___x_1250_, 0);
v_nextIdx_1252_ = lean_ctor_get(v___x_1250_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1254_ = v___x_1250_;
v_isShared_1255_ = v_isSharedCheck_1263_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_nextIdx_1252_);
lean_inc(v_lctx_1251_);
lean_dec(v___x_1250_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1263_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; lean_object* v___x_1258_; 
v___x_1256_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_1246_, v_lctx_1251_, v_params_1247_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 0, v___x_1256_);
v___x_1258_ = v___x_1254_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1256_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_nextIdx_1252_);
v___x_1258_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = lean_st_ref_set(v_a_1248_, v___x_1258_);
v___x_1260_ = lean_box(0);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
return v___x_1261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg___boxed(lean_object* v_pu_1264_, lean_object* v_params_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
uint8_t v_pu_boxed_1268_; lean_object* v_res_1269_; 
v_pu_boxed_1268_ = lean_unbox(v_pu_1264_);
v_res_1269_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_boxed_1268_, v_params_1265_, v_a_1266_);
lean_dec(v_a_1266_);
lean_dec_ref(v_params_1265_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams(uint8_t v_pu_1270_, lean_object* v_params_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1270_, v_params_1271_, v_a_1273_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___boxed(lean_object* v_pu_1278_, lean_object* v_params_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
uint8_t v_pu_boxed_1285_; lean_object* v_res_1286_; 
v_pu_boxed_1285_ = lean_unbox(v_pu_1278_);
v_res_1286_ = l_Lean_Compiler_LCNF_eraseParams(v_pu_boxed_1285_, v_params_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
lean_dec_ref(v_params_1279_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t v_pu_1287_, lean_object* v_decl_1288_, lean_object* v_a_1289_){
_start:
{
switch(lean_obj_tag(v_decl_1288_))
{
case 0:
{
lean_object* v_decl_1291_; lean_object* v___x_1292_; 
v_decl_1291_ = lean_ctor_get(v_decl_1288_, 0);
v___x_1292_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1287_, v_decl_1291_, v_a_1289_);
return v___x_1292_;
}
case 1:
{
lean_object* v_decl_1293_; uint8_t v___x_1294_; lean_object* v___x_1295_; 
v_decl_1293_ = lean_ctor_get(v_decl_1288_, 0);
v___x_1294_ = 1;
v___x_1295_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1287_, v_decl_1293_, v___x_1294_, v_a_1289_);
return v___x_1295_;
}
case 2:
{
lean_object* v_decl_1296_; uint8_t v___x_1297_; lean_object* v___x_1298_; 
v_decl_1296_ = lean_ctor_get(v_decl_1288_, 0);
v___x_1297_ = 1;
v___x_1298_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1287_, v_decl_1296_, v___x_1297_, v_a_1289_);
return v___x_1298_;
}
default: 
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = lean_box(0);
v___x_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
return v___x_1300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg___boxed(lean_object* v_pu_1301_, lean_object* v_decl_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
uint8_t v_pu_boxed_1305_; lean_object* v_res_1306_; 
v_pu_boxed_1305_ = lean_unbox(v_pu_1301_);
v_res_1306_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_boxed_1305_, v_decl_1302_, v_a_1303_);
lean_dec(v_a_1303_);
lean_dec_ref(v_decl_1302_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl(uint8_t v_pu_1307_, lean_object* v_decl_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1307_, v_decl_1308_, v_a_1310_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___boxed(lean_object* v_pu_1315_, lean_object* v_decl_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_){
_start:
{
uint8_t v_pu_boxed_1322_; lean_object* v_res_1323_; 
v_pu_boxed_1322_ = lean_unbox(v_pu_1315_);
v_res_1323_ = l_Lean_Compiler_LCNF_eraseCodeDecl(v_pu_boxed_1322_, v_decl_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec_ref(v_decl_1316_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(uint8_t v_pu_1324_, lean_object* v_as_1325_, size_t v_i_1326_, size_t v_stop_1327_, lean_object* v_b_1328_, lean_object* v___y_1329_){
_start:
{
uint8_t v___x_1331_; 
v___x_1331_ = lean_usize_dec_eq(v_i_1326_, v_stop_1327_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = lean_array_uget_borrowed(v_as_1325_, v_i_1326_);
v___x_1333_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1324_, v___x_1332_, v___y_1329_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; size_t v___x_1335_; size_t v___x_1336_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1334_);
lean_dec_ref(v___x_1333_);
v___x_1335_ = ((size_t)1ULL);
v___x_1336_ = lean_usize_add(v_i_1326_, v___x_1335_);
v_i_1326_ = v___x_1336_;
v_b_1328_ = v_a_1334_;
goto _start;
}
else
{
return v___x_1333_;
}
}
else
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v_b_1328_);
return v___x_1338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg___boxed(lean_object* v_pu_1339_, lean_object* v_as_1340_, lean_object* v_i_1341_, lean_object* v_stop_1342_, lean_object* v_b_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
uint8_t v_pu_boxed_1346_; size_t v_i_boxed_1347_; size_t v_stop_boxed_1348_; lean_object* v_res_1349_; 
v_pu_boxed_1346_ = lean_unbox(v_pu_1339_);
v_i_boxed_1347_ = lean_unbox_usize(v_i_1341_);
lean_dec(v_i_1341_);
v_stop_boxed_1348_ = lean_unbox_usize(v_stop_1342_);
lean_dec(v_stop_1342_);
v_res_1349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_boxed_1346_, v_as_1340_, v_i_boxed_1347_, v_stop_boxed_1348_, v_b_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v_as_1340_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls(uint8_t v_pu_1350_, lean_object* v_decls_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = lean_array_get_size(v_decls_1351_);
v___x_1359_ = lean_box(0);
v___x_1360_ = lean_nat_dec_lt(v___x_1357_, v___x_1358_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1359_);
return v___x_1361_;
}
else
{
uint8_t v___x_1362_; 
v___x_1362_ = lean_nat_dec_le(v___x_1358_, v___x_1358_);
if (v___x_1362_ == 0)
{
if (v___x_1360_ == 0)
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1359_);
return v___x_1363_;
}
else
{
size_t v___x_1364_; size_t v___x_1365_; lean_object* v___x_1366_; 
v___x_1364_ = ((size_t)0ULL);
v___x_1365_ = lean_usize_of_nat(v___x_1358_);
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1350_, v_decls_1351_, v___x_1364_, v___x_1365_, v___x_1359_, v_a_1353_);
return v___x_1366_;
}
}
else
{
size_t v___x_1367_; size_t v___x_1368_; lean_object* v___x_1369_; 
v___x_1367_ = ((size_t)0ULL);
v___x_1368_ = lean_usize_of_nat(v___x_1358_);
v___x_1369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1350_, v_decls_1351_, v___x_1367_, v___x_1368_, v___x_1359_, v_a_1353_);
return v___x_1369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls___boxed(lean_object* v_pu_1370_, lean_object* v_decls_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
uint8_t v_pu_boxed_1377_; lean_object* v_res_1378_; 
v_pu_boxed_1377_ = lean_unbox(v_pu_1370_);
v_res_1378_ = l_Lean_Compiler_LCNF_eraseCodeDecls(v_pu_boxed_1377_, v_decls_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
lean_dec_ref(v_decls_1371_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(uint8_t v_pu_1379_, lean_object* v_as_1380_, size_t v_i_1381_, size_t v_stop_1382_, lean_object* v_b_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1379_, v_as_1380_, v_i_1381_, v_stop_1382_, v_b_1383_, v___y_1385_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___boxed(lean_object* v_pu_1390_, lean_object* v_as_1391_, lean_object* v_i_1392_, lean_object* v_stop_1393_, lean_object* v_b_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
uint8_t v_pu_boxed_1400_; size_t v_i_boxed_1401_; size_t v_stop_boxed_1402_; lean_object* v_res_1403_; 
v_pu_boxed_1400_ = lean_unbox(v_pu_1390_);
v_i_boxed_1401_ = lean_unbox_usize(v_i_1392_);
lean_dec(v_i_1392_);
v_stop_boxed_1402_ = lean_unbox_usize(v_stop_1393_);
lean_dec(v_stop_1393_);
v_res_1403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(v_pu_boxed_1400_, v_as_1391_, v_i_boxed_1401_, v_stop_boxed_1402_, v_b_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec_ref(v_as_1391_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(lean_object* v_f_1404_, lean_object* v_v_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
if (lean_obj_tag(v_v_1405_) == 0)
{
lean_object* v_code_1411_; lean_object* v___x_1412_; 
v_code_1411_ = lean_ctor_get(v_v_1405_, 0);
lean_inc_ref(v_code_1411_);
lean_dec_ref(v_v_1405_);
lean_inc(v___y_1409_);
lean_inc_ref(v___y_1408_);
lean_inc(v___y_1407_);
lean_inc_ref(v___y_1406_);
v___x_1412_ = lean_apply_6(v_f_1404_, v_code_1411_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, lean_box(0));
return v___x_1412_;
}
else
{
lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v_f_1404_);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_v_1405_);
if (v_isSharedCheck_1420_ == 0)
{
lean_object* v_unused_1421_; 
v_unused_1421_ = lean_ctor_get(v_v_1405_, 0);
lean_dec(v_unused_1421_);
v___x_1414_ = v_v_1405_;
v_isShared_1415_ = v_isSharedCheck_1420_;
goto v_resetjp_1413_;
}
else
{
lean_dec(v_v_1405_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1420_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1416_ = lean_box(0);
if (v_isShared_1415_ == 0)
{
lean_ctor_set_tag(v___x_1414_, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1416_);
v___x_1418_ = v___x_1414_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg___boxed(lean_object* v_f_1422_, lean_object* v_v_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1422_, v_v_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(uint8_t v_pu_1430_, lean_object* v_f_1431_, lean_object* v_v_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1431_, v_v_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___boxed(lean_object* v_pu_1439_, lean_object* v_f_1440_, lean_object* v_v_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
uint8_t v_pu_boxed_1447_; lean_object* v_res_1448_; 
v_pu_boxed_1447_ = lean_unbox(v_pu_1439_);
v_res_1448_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(v_pu_boxed_1447_, v_f_1440_, v_v_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t v_pu_1449_, lean_object* v_decl_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_){
_start:
{
lean_object* v_toSignature_1456_; lean_object* v_value_1457_; lean_object* v_params_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v_toSignature_1456_ = lean_ctor_get(v_decl_1450_, 0);
lean_inc_ref(v_toSignature_1456_);
v_value_1457_ = lean_ctor_get(v_decl_1450_, 1);
lean_inc_ref(v_value_1457_);
lean_dec_ref(v_decl_1450_);
v_params_1458_ = lean_ctor_get(v_toSignature_1456_, 3);
lean_inc_ref(v_params_1458_);
lean_dec_ref(v_toSignature_1456_);
v___x_1459_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1449_, v_params_1458_, v_a_1452_);
lean_dec_ref(v_params_1458_);
lean_dec_ref(v___x_1459_);
v___x_1460_ = lean_box(v_pu_1449_);
v___x_1461_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_eraseCode___boxed), 7, 1);
lean_closure_set(v___x_1461_, 0, v___x_1460_);
v___x_1462_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v___x_1461_, v_value_1457_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl___boxed(lean_object* v_pu_1463_, lean_object* v_decl_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
uint8_t v_pu_boxed_1470_; lean_object* v_res_1471_; 
v_pu_boxed_1470_ = lean_unbox(v_pu_1463_);
v_res_1471_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_boxed_1470_, v_decl_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase(uint8_t v_pu_1472_, lean_object* v_decl_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_1472_, v_decl_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase___boxed(lean_object* v_pu_1480_, lean_object* v_decl_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
uint8_t v_pu_boxed_1487_; lean_object* v_res_1488_; 
v_pu_boxed_1487_ = lean_unbox(v_pu_1480_);
v_res_1488_ = l_Lean_Compiler_LCNF_Decl_erase(v_pu_boxed_1487_, v_decl_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
lean_dec(v_a_1485_);
lean_dec_ref(v_a_1484_);
lean_dec(v_a_1483_);
lean_dec_ref(v_a_1482_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(lean_object* v_msg_1489_){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = l_Lean_instInhabitedExpr;
v___x_1491_ = lean_panic_fn(v___x_1490_, v_msg_1489_);
return v___x_1491_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1495_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2));
v___x_1496_ = lean_unsigned_to_nat(20u);
v___x_1497_ = lean_unsigned_to_nat(215u);
v___x_1498_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1));
v___x_1499_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0));
v___x_1500_ = l_mkPanicMessageWithDecl(v___x_1499_, v___x_1498_, v___x_1497_, v___x_1496_, v___x_1495_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t v_pu_1501_, lean_object* v_s_1502_, uint8_t v_translator_1503_, lean_object* v_e_1504_){
_start:
{
uint8_t v___x_1505_; 
v___x_1505_ = l_Lean_Expr_hasFVar(v_e_1504_);
if (v___x_1505_ == 0)
{
return v_e_1504_;
}
else
{
switch(lean_obj_tag(v_e_1504_))
{
case 1:
{
lean_object* v_fvarId_1506_; lean_object* v___x_1507_; 
v_fvarId_1506_ = lean_ctor_get(v_e_1504_, 0);
v___x_1507_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1502_, v_fvarId_1506_);
if (lean_obj_tag(v___x_1507_) == 0)
{
return v_e_1504_;
}
else
{
lean_object* v_val_1508_; 
lean_dec_ref(v_e_1504_);
v_val_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_val_1508_);
lean_dec_ref(v___x_1507_);
switch(lean_obj_tag(v_val_1508_))
{
case 0:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_Compiler_LCNF_erasedExpr;
return v___x_1509_;
}
case 1:
{
if (v_translator_1503_ == 0)
{
lean_object* v_fvarId_1510_; lean_object* v___x_1511_; 
v_fvarId_1510_ = lean_ctor_get(v_val_1508_, 0);
lean_inc(v_fvarId_1510_);
lean_dec_ref(v_val_1508_);
v___x_1511_ = l_Lean_Expr_fvar___override(v_fvarId_1510_);
v_e_1504_ = v___x_1511_;
goto _start;
}
else
{
lean_object* v_fvarId_1513_; lean_object* v___x_1514_; 
v_fvarId_1513_ = lean_ctor_get(v_val_1508_, 0);
lean_inc(v_fvarId_1513_);
lean_dec_ref(v_val_1508_);
v___x_1514_ = l_Lean_Expr_fvar___override(v_fvarId_1513_);
return v___x_1514_;
}
}
default: 
{
if (v_translator_1503_ == 0)
{
lean_object* v_expr_1515_; 
v_expr_1515_ = lean_ctor_get(v_val_1508_, 0);
lean_inc_ref(v_expr_1515_);
lean_dec_ref(v_val_1508_);
v_e_1504_ = v_expr_1515_;
goto _start;
}
else
{
lean_object* v_expr_1517_; 
v_expr_1517_ = lean_ctor_get(v_val_1508_, 0);
lean_inc_ref(v_expr_1517_);
lean_dec_ref(v_val_1508_);
return v_expr_1517_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_1518_; lean_object* v_arg_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; uint8_t v___y_1523_; size_t v___x_1527_; size_t v___x_1528_; uint8_t v___x_1529_; 
v_fn_1518_ = lean_ctor_get(v_e_1504_, 0);
v_arg_1519_ = lean_ctor_get(v_e_1504_, 1);
lean_inc_ref(v_fn_1518_);
v___x_1520_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1501_, v_s_1502_, v_translator_1503_, v_fn_1518_);
lean_inc_ref(v_arg_1519_);
v___x_1521_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1501_, v_s_1502_, v_translator_1503_, v_arg_1519_);
v___x_1527_ = lean_ptr_addr(v_fn_1518_);
v___x_1528_ = lean_ptr_addr(v___x_1520_);
v___x_1529_ = lean_usize_dec_eq(v___x_1527_, v___x_1528_);
if (v___x_1529_ == 0)
{
v___y_1523_ = v___x_1529_;
goto v___jp_1522_;
}
else
{
size_t v___x_1530_; size_t v___x_1531_; uint8_t v___x_1532_; 
v___x_1530_ = lean_ptr_addr(v_arg_1519_);
v___x_1531_ = lean_ptr_addr(v___x_1521_);
v___x_1532_ = lean_usize_dec_eq(v___x_1530_, v___x_1531_);
v___y_1523_ = v___x_1532_;
goto v___jp_1522_;
}
v___jp_1522_:
{
if (v___y_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec_ref(v_e_1504_);
v___x_1524_ = l_Lean_Expr_app___override(v___x_1520_, v___x_1521_);
v___x_1525_ = l_Lean_Expr_headBeta(v___x_1524_);
return v___x_1525_;
}
else
{
lean_object* v___x_1526_; 
lean_dec_ref(v___x_1521_);
lean_dec_ref(v___x_1520_);
v___x_1526_ = l_Lean_Expr_headBeta(v_e_1504_);
return v___x_1526_;
}
}
}
case 6:
{
lean_object* v_binderName_1533_; lean_object* v_binderType_1534_; lean_object* v_body_1535_; uint8_t v_binderInfo_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___y_1540_; size_t v___x_1544_; size_t v___x_1545_; uint8_t v___x_1546_; 
v_binderName_1533_ = lean_ctor_get(v_e_1504_, 0);
v_binderType_1534_ = lean_ctor_get(v_e_1504_, 1);
v_body_1535_ = lean_ctor_get(v_e_1504_, 2);
v_binderInfo_1536_ = lean_ctor_get_uint8(v_e_1504_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1534_);
v___x_1537_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1501_, v_s_1502_, v_translator_1503_, v_binderType_1534_);
lean_inc_ref(v_body_1535_);
v___x_1538_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1501_, v_s_1502_, v_translator_1503_, v_body_1535_);
v___x_1544_ = lean_ptr_addr(v_binderType_1534_);
v___x_1545_ = lean_ptr_addr(v___x_1537_);
v___x_1546_ = lean_usize_dec_eq(v___x_1544_, v___x_1545_);
if (v___x_1546_ == 0)
{
v___y_1540_ = v___x_1546_;
goto v___jp_1539_;
}
else
{
size_t v___x_1547_; size_t v___x_1548_; uint8_t v___x_1549_; 
v___x_1547_ = lean_ptr_addr(v_body_1535_);
v___x_1548_ = lean_ptr_addr(v___x_1538_);
v___x_1549_ = lean_usize_dec_eq(v___x_1547_, v___x_1548_);
v___y_1540_ = v___x_1549_;
goto v___jp_1539_;
}
v___jp_1539_:
{
if (v___y_1540_ == 0)
{
lean_object* v___x_1541_; 
lean_inc(v_binderName_1533_);
lean_dec_ref(v_e_1504_);
v___x_1541_ = l_Lean_Expr_lam___override(v_binderName_1533_, v___x_1537_, v___x_1538_, v_binderInfo_1536_);
return v___x_1541_;
}
else
{
uint8_t v___x_1542_; 
v___x_1542_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1536_, v_binderInfo_1536_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; 
lean_inc(v_binderName_1533_);
lean_dec_ref(v_e_1504_);
v___x_1543_ = l_Lean_Expr_lam___override(v_binderName_1533_, v___x_1537_, v___x_1538_, v_binderInfo_1536_);
return v___x_1543_;
}
else
{
lean_dec_ref(v___x_1538_);
lean_dec_ref(v___x_1537_);
return v_e_1504_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1550_; lean_object* v_binderType_1551_; lean_object* v_body_1552_; uint8_t v_binderInfo_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___y_1557_; size_t v___x_1561_; size_t v___x_1562_; uint8_t v___x_1563_; 
v_binderName_1550_ = lean_ctor_get(v_e_1504_, 0);
v_binderType_1551_ = lean_ctor_get(v_e_1504_, 1);
v_body_1552_ = lean_ctor_get(v_e_1504_, 2);
v_binderInfo_1553_ = lean_ctor_get_uint8(v_e_1504_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1551_);
v___x_1554_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1501_, v_s_1502_, v_translator_1503_, v_binderType_1551_);
lean_inc_ref(v_body_1552_);
v___x_1555_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1501_, v_s_1502_, v_translator_1503_, v_body_1552_);
v___x_1561_ = lean_ptr_addr(v_binderType_1551_);
v___x_1562_ = lean_ptr_addr(v___x_1554_);
v___x_1563_ = lean_usize_dec_eq(v___x_1561_, v___x_1562_);
if (v___x_1563_ == 0)
{
v___y_1557_ = v___x_1563_;
goto v___jp_1556_;
}
else
{
size_t v___x_1564_; size_t v___x_1565_; uint8_t v___x_1566_; 
v___x_1564_ = lean_ptr_addr(v_body_1552_);
v___x_1565_ = lean_ptr_addr(v___x_1555_);
v___x_1566_ = lean_usize_dec_eq(v___x_1564_, v___x_1565_);
v___y_1557_ = v___x_1566_;
goto v___jp_1556_;
}
v___jp_1556_:
{
if (v___y_1557_ == 0)
{
lean_object* v___x_1558_; 
lean_inc(v_binderName_1550_);
lean_dec_ref(v_e_1504_);
v___x_1558_ = l_Lean_Expr_forallE___override(v_binderName_1550_, v___x_1554_, v___x_1555_, v_binderInfo_1553_);
return v___x_1558_;
}
else
{
uint8_t v___x_1559_; 
v___x_1559_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1553_, v_binderInfo_1553_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; 
lean_inc(v_binderName_1550_);
lean_dec_ref(v_e_1504_);
v___x_1560_ = l_Lean_Expr_forallE___override(v_binderName_1550_, v___x_1554_, v___x_1555_, v_binderInfo_1553_);
return v___x_1560_;
}
else
{
lean_dec_ref(v___x_1555_);
lean_dec_ref(v___x_1554_);
return v_e_1504_;
}
}
}
}
case 8:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_dec_ref(v_e_1504_);
v___x_1567_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3, &l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3);
v___x_1568_ = l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(v___x_1567_);
return v___x_1568_;
}
case 10:
{
lean_object* v_data_1569_; lean_object* v_expr_1570_; lean_object* v___x_1571_; size_t v___x_1572_; size_t v___x_1573_; uint8_t v___x_1574_; 
v_data_1569_ = lean_ctor_get(v_e_1504_, 0);
v_expr_1570_ = lean_ctor_get(v_e_1504_, 1);
lean_inc_ref(v_expr_1570_);
v___x_1571_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1501_, v_s_1502_, v_translator_1503_, v_expr_1570_);
v___x_1572_ = lean_ptr_addr(v_expr_1570_);
v___x_1573_ = lean_ptr_addr(v___x_1571_);
v___x_1574_ = lean_usize_dec_eq(v___x_1572_, v___x_1573_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; 
lean_inc(v_data_1569_);
lean_dec_ref(v_e_1504_);
v___x_1575_ = l_Lean_Expr_mdata___override(v_data_1569_, v___x_1571_);
return v___x_1575_;
}
else
{
lean_dec_ref(v___x_1571_);
return v_e_1504_;
}
}
case 11:
{
lean_object* v_typeName_1576_; lean_object* v_idx_1577_; lean_object* v_struct_1578_; lean_object* v___x_1579_; size_t v___x_1580_; size_t v___x_1581_; uint8_t v___x_1582_; 
v_typeName_1576_ = lean_ctor_get(v_e_1504_, 0);
v_idx_1577_ = lean_ctor_get(v_e_1504_, 1);
v_struct_1578_ = lean_ctor_get(v_e_1504_, 2);
lean_inc_ref(v_struct_1578_);
v___x_1579_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1501_, v_s_1502_, v_translator_1503_, v_struct_1578_);
v___x_1580_ = lean_ptr_addr(v_struct_1578_);
v___x_1581_ = lean_ptr_addr(v___x_1579_);
v___x_1582_ = lean_usize_dec_eq(v___x_1580_, v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
lean_inc(v_idx_1577_);
lean_inc(v_typeName_1576_);
lean_dec_ref(v_e_1504_);
v___x_1583_ = l_Lean_Expr_proj___override(v_typeName_1576_, v_idx_1577_, v___x_1579_);
return v___x_1583_;
}
else
{
lean_dec_ref(v___x_1579_);
return v_e_1504_;
}
}
default: 
{
return v_e_1504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(uint8_t v_pu_1584_, lean_object* v_s_1585_, uint8_t v_translator_1586_, lean_object* v_e_1587_){
_start:
{
if (lean_obj_tag(v_e_1587_) == 5)
{
lean_object* v_fn_1588_; lean_object* v_arg_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; uint8_t v___y_1593_; size_t v___x_1595_; size_t v___x_1596_; uint8_t v___x_1597_; 
v_fn_1588_ = lean_ctor_get(v_e_1587_, 0);
v_arg_1589_ = lean_ctor_get(v_e_1587_, 1);
lean_inc_ref(v_fn_1588_);
v___x_1590_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1584_, v_s_1585_, v_translator_1586_, v_fn_1588_);
lean_inc_ref(v_arg_1589_);
v___x_1591_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1584_, v_s_1585_, v_translator_1586_, v_arg_1589_);
v___x_1595_ = lean_ptr_addr(v_fn_1588_);
v___x_1596_ = lean_ptr_addr(v___x_1590_);
v___x_1597_ = lean_usize_dec_eq(v___x_1595_, v___x_1596_);
if (v___x_1597_ == 0)
{
v___y_1593_ = v___x_1597_;
goto v___jp_1592_;
}
else
{
size_t v___x_1598_; size_t v___x_1599_; uint8_t v___x_1600_; 
v___x_1598_ = lean_ptr_addr(v_arg_1589_);
v___x_1599_ = lean_ptr_addr(v___x_1591_);
v___x_1600_ = lean_usize_dec_eq(v___x_1598_, v___x_1599_);
v___y_1593_ = v___x_1600_;
goto v___jp_1592_;
}
v___jp_1592_:
{
if (v___y_1593_ == 0)
{
lean_object* v___x_1594_; 
lean_dec_ref(v_e_1587_);
v___x_1594_ = l_Lean_Expr_app___override(v___x_1590_, v___x_1591_);
return v___x_1594_;
}
else
{
lean_dec_ref(v___x_1591_);
lean_dec_ref(v___x_1590_);
return v_e_1587_;
}
}
}
else
{
lean_object* v___x_1601_; 
v___x_1601_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1584_, v_s_1585_, v_translator_1586_, v_e_1587_);
return v___x_1601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(lean_object* v_pu_1602_, lean_object* v_s_1603_, lean_object* v_translator_1604_, lean_object* v_e_1605_){
_start:
{
uint8_t v_pu_boxed_1606_; uint8_t v_translator_boxed_1607_; lean_object* v_res_1608_; 
v_pu_boxed_1606_ = lean_unbox(v_pu_1602_);
v_translator_boxed_1607_ = lean_unbox(v_translator_1604_);
v_res_1608_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_boxed_1606_, v_s_1603_, v_translator_boxed_1607_, v_e_1605_);
lean_dec_ref(v_s_1603_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(lean_object* v_pu_1609_, lean_object* v_s_1610_, lean_object* v_translator_1611_, lean_object* v_e_1612_){
_start:
{
uint8_t v_pu_boxed_1613_; uint8_t v_translator_boxed_1614_; lean_object* v_res_1615_; 
v_pu_boxed_1613_ = lean_unbox(v_pu_1609_);
v_translator_boxed_1614_ = lean_unbox(v_translator_1611_);
v_res_1615_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_boxed_1613_, v_s_1610_, v_translator_boxed_1614_, v_e_1612_);
lean_dec_ref(v_s_1610_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(uint8_t v_pu_1616_, lean_object* v_s_1617_, lean_object* v_e_1618_, uint8_t v_translator_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1616_, v_s_1617_, v_translator_1619_, v_e_1618_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(lean_object* v_pu_1621_, lean_object* v_s_1622_, lean_object* v_e_1623_, lean_object* v_translator_1624_){
_start:
{
uint8_t v_pu_boxed_1625_; uint8_t v_translator_boxed_1626_; lean_object* v_res_1627_; 
v_pu_boxed_1625_ = lean_unbox(v_pu_1621_);
v_translator_boxed_1626_ = lean_unbox(v_translator_1624_);
v_res_1627_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(v_pu_boxed_1625_, v_s_1622_, v_e_1623_, v_translator_boxed_1626_);
lean_dec_ref(v_s_1622_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(lean_object* v_x_1628_){
_start:
{
if (lean_obj_tag(v_x_1628_) == 0)
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_unsigned_to_nat(0u);
return v___x_1629_;
}
else
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_unsigned_to_nat(1u);
return v___x_1630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___boxed(lean_object* v_x_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(v_x_1631_);
lean_dec(v_x_1631_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(lean_object* v_t_1633_, lean_object* v_k_1634_){
_start:
{
if (lean_obj_tag(v_t_1633_) == 0)
{
lean_object* v_fvarId_1635_; lean_object* v___x_1636_; 
v_fvarId_1635_ = lean_ctor_get(v_t_1633_, 0);
lean_inc(v_fvarId_1635_);
lean_dec_ref(v_t_1633_);
v___x_1636_ = lean_apply_1(v_k_1634_, v_fvarId_1635_);
return v___x_1636_;
}
else
{
return v_k_1634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(lean_object* v_motive_1637_, lean_object* v_ctorIdx_1638_, lean_object* v_t_1639_, lean_object* v_h_1640_, lean_object* v_k_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1639_, v_k_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___boxed(lean_object* v_motive_1643_, lean_object* v_ctorIdx_1644_, lean_object* v_t_1645_, lean_object* v_h_1646_, lean_object* v_k_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(v_motive_1643_, v_ctorIdx_1644_, v_t_1645_, v_h_1646_, v_k_1647_);
lean_dec(v_ctorIdx_1644_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim___redArg(lean_object* v_t_1649_, lean_object* v_fvar_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1649_, v_fvar_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim(lean_object* v_motive_1652_, lean_object* v_t_1653_, lean_object* v_h_1654_, lean_object* v_fvar_1655_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1653_, v_fvar_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim___redArg(lean_object* v_t_1657_, lean_object* v_erased_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1657_, v_erased_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim(lean_object* v_motive_1660_, lean_object* v_t_1661_, lean_object* v_h_1662_, lean_object* v_erased_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1661_, v_erased_1663_);
return v___x_1664_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = l_Lean_instInhabitedFVarId_default;
v___x_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
return v___x_1666_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default(void){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0);
return v___x_1667_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedNormFVarResult(void){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default;
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object* v_s_1669_, lean_object* v_fvarId_1670_, uint8_t v_translator_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1669_, v_fvarId_1670_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1673_, 0, v_fvarId_1670_);
return v___x_1673_;
}
else
{
lean_object* v_val_1674_; 
lean_dec(v_fvarId_1670_);
v_val_1674_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_val_1674_);
lean_dec_ref(v___x_1672_);
if (lean_obj_tag(v_val_1674_) == 1)
{
if (v_translator_1671_ == 0)
{
lean_object* v_fvarId_1675_; 
v_fvarId_1675_ = lean_ctor_get(v_val_1674_, 0);
lean_inc(v_fvarId_1675_);
lean_dec_ref(v_val_1674_);
v_fvarId_1670_ = v_fvarId_1675_;
goto _start;
}
else
{
lean_object* v_fvarId_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
v_fvarId_1677_ = lean_ctor_get(v_val_1674_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_val_1674_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v_val_1674_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_fvarId_1677_);
lean_dec(v_val_1674_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
lean_ctor_set_tag(v___x_1679_, 0);
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_fvarId_1677_);
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
else
{
lean_object* v___x_1685_; 
lean_dec(v_val_1674_);
v___x_1685_ = lean_box(1);
return v___x_1685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg___boxed(lean_object* v_s_1686_, lean_object* v_fvarId_1687_, lean_object* v_translator_1688_){
_start:
{
uint8_t v_translator_boxed_1689_; lean_object* v_res_1690_; 
v_translator_boxed_1689_ = lean_unbox(v_translator_1688_);
v_res_1690_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1686_, v_fvarId_1687_, v_translator_boxed_1689_);
lean_dec_ref(v_s_1686_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp(uint8_t v_pu_1691_, lean_object* v_s_1692_, lean_object* v_fvarId_1693_, uint8_t v_translator_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1692_, v_fvarId_1693_, v_translator_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___boxed(lean_object* v_pu_1696_, lean_object* v_s_1697_, lean_object* v_fvarId_1698_, lean_object* v_translator_1699_){
_start:
{
uint8_t v_pu_boxed_1700_; uint8_t v_translator_boxed_1701_; lean_object* v_res_1702_; 
v_pu_boxed_1700_ = lean_unbox(v_pu_1696_);
v_translator_boxed_1701_ = lean_unbox(v_translator_1699_);
v_res_1702_ = l_Lean_Compiler_LCNF_normFVarImp(v_pu_boxed_1700_, v_s_1697_, v_fvarId_1698_, v_translator_boxed_1701_);
lean_dec_ref(v_s_1697_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t v_pu_1703_, lean_object* v_s_1704_, lean_object* v_arg_1705_, uint8_t v_translator_1706_){
_start:
{
switch(lean_obj_tag(v_arg_1705_))
{
case 0:
{
return v_arg_1705_;
}
case 1:
{
lean_object* v_fvarId_1707_; lean_object* v___x_1708_; 
v_fvarId_1707_ = lean_ctor_get(v_arg_1705_, 0);
v___x_1708_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1704_, v_fvarId_1707_);
if (lean_obj_tag(v___x_1708_) == 0)
{
return v_arg_1705_;
}
else
{
lean_object* v_val_1709_; 
lean_dec_ref(v_arg_1705_);
v_val_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_val_1709_);
lean_dec_ref(v___x_1708_);
switch(lean_obj_tag(v_val_1709_))
{
case 0:
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_box(0);
return v___x_1710_;
}
case 1:
{
lean_object* v_fvarId_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1719_; 
v_fvarId_1711_ = lean_ctor_get(v_val_1709_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_val_1709_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1713_ = v_val_1709_;
v_isShared_1714_ = v_isSharedCheck_1719_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_fvarId_1711_);
lean_dec(v_val_1709_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1719_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_fvarId_1711_);
v___x_1716_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
if (v_translator_1706_ == 0)
{
v_arg_1705_ = v___x_1716_;
goto _start;
}
else
{
return v___x_1716_;
}
}
}
}
default: 
{
lean_object* v_expr_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
v_expr_1720_ = lean_ctor_get(v_val_1709_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_val_1709_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v_val_1709_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_expr_1720_);
lean_dec(v_val_1709_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_expr_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
}
}
default: 
{
lean_object* v_expr_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v_expr_1728_ = lean_ctor_get(v_arg_1705_, 0);
lean_inc_ref(v_expr_1728_);
v___x_1729_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1703_, v_s_1704_, v_translator_1706_, v_expr_1728_);
v___x_1730_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1703_, v_arg_1705_, v___x_1729_);
return v___x_1730_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp___boxed(lean_object* v_pu_1731_, lean_object* v_s_1732_, lean_object* v_arg_1733_, lean_object* v_translator_1734_){
_start:
{
uint8_t v_pu_boxed_1735_; uint8_t v_translator_boxed_1736_; lean_object* v_res_1737_; 
v_pu_boxed_1735_ = lean_unbox(v_pu_1731_);
v_translator_boxed_1736_ = lean_unbox(v_translator_1734_);
v_res_1737_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_boxed_1735_, v_s_1732_, v_arg_1733_, v_translator_boxed_1736_);
lean_dec_ref(v_s_1732_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(uint8_t v_pu_1738_, lean_object* v_s_1739_, uint8_t v_translator_1740_, lean_object* v_i_1741_, lean_object* v_as_1742_){
_start:
{
lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1743_ = lean_array_get_size(v_as_1742_);
v___x_1744_ = lean_nat_dec_lt(v_i_1741_, v___x_1743_);
if (v___x_1744_ == 0)
{
lean_dec(v_i_1741_);
return v_as_1742_;
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1746_; size_t v___x_1747_; size_t v___x_1748_; uint8_t v___x_1749_; 
v_a_1745_ = lean_array_fget_borrowed(v_as_1742_, v_i_1741_);
lean_inc(v_a_1745_);
v___x_1746_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1738_, v_s_1739_, v_a_1745_, v_translator_1740_);
v___x_1747_ = lean_ptr_addr(v_a_1745_);
v___x_1748_ = lean_ptr_addr(v___x_1746_);
v___x_1749_ = lean_usize_dec_eq(v___x_1747_, v___x_1748_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1750_ = lean_unsigned_to_nat(1u);
v___x_1751_ = lean_nat_add(v_i_1741_, v___x_1750_);
v___x_1752_ = lean_array_fset(v_as_1742_, v_i_1741_, v___x_1746_);
lean_dec(v_i_1741_);
v_i_1741_ = v___x_1751_;
v_as_1742_ = v___x_1752_;
goto _start;
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_dec(v___x_1746_);
v___x_1754_ = lean_unsigned_to_nat(1u);
v___x_1755_ = lean_nat_add(v_i_1741_, v___x_1754_);
lean_dec(v_i_1741_);
v_i_1741_ = v___x_1755_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0___boxed(lean_object* v_pu_1757_, lean_object* v_s_1758_, lean_object* v_translator_1759_, lean_object* v_i_1760_, lean_object* v_as_1761_){
_start:
{
uint8_t v_pu_boxed_1762_; uint8_t v_translator_boxed_1763_; lean_object* v_res_1764_; 
v_pu_boxed_1762_ = lean_unbox(v_pu_1757_);
v_translator_boxed_1763_ = lean_unbox(v_translator_1759_);
v_res_1764_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_boxed_1762_, v_s_1758_, v_translator_boxed_1763_, v_i_1760_, v_as_1761_);
lean_dec_ref(v_s_1758_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t v_pu_1765_, lean_object* v_s_1766_, lean_object* v_args_1767_, uint8_t v_translator_1768_){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = lean_unsigned_to_nat(0u);
v___x_1770_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_1765_, v_s_1766_, v_translator_1768_, v___x_1769_, v_args_1767_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp___boxed(lean_object* v_pu_1771_, lean_object* v_s_1772_, lean_object* v_args_1773_, lean_object* v_translator_1774_){
_start:
{
uint8_t v_pu_boxed_1775_; uint8_t v_translator_boxed_1776_; lean_object* v_res_1777_; 
v_pu_boxed_1775_ = lean_unbox(v_pu_1771_);
v_translator_boxed_1776_ = lean_unbox(v_translator_1774_);
v_res_1777_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_boxed_1775_, v_s_1772_, v_args_1773_, v_translator_boxed_1776_);
lean_dec_ref(v_s_1772_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t v_pu_1778_, lean_object* v_s_1779_, lean_object* v_e_1780_, uint8_t v_translator_1781_){
_start:
{
lean_object* v_fvarId_1783_; lean_object* v_args_1789_; 
switch(lean_obj_tag(v_e_1780_))
{
case 2:
{
lean_object* v_struct_1792_; lean_object* v___x_1793_; 
v_struct_1792_ = lean_ctor_get(v_e_1780_, 2);
lean_inc(v_struct_1792_);
v___x_1793_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1779_, v_struct_1792_, v_translator_1781_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_fvarId_1794_; lean_object* v___x_1795_; 
v_fvarId_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_fvarId_1794_);
lean_dec_ref(v___x_1793_);
v___x_1795_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1778_, v_e_1780_, v_fvarId_1794_);
return v___x_1795_;
}
else
{
lean_object* v___x_1796_; 
lean_dec_ref(v_e_1780_);
v___x_1796_ = lean_box(1);
return v___x_1796_;
}
}
case 3:
{
lean_object* v_args_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v_args_1797_ = lean_ctor_get(v_e_1780_, 2);
lean_inc_ref(v_args_1797_);
v___x_1798_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1778_, v_s_1779_, v_args_1797_, v_translator_1781_);
v___x_1799_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1778_, v_e_1780_, v___x_1798_);
return v___x_1799_;
}
case 4:
{
lean_object* v_fvarId_1800_; lean_object* v_args_1801_; lean_object* v___x_1802_; 
v_fvarId_1800_ = lean_ctor_get(v_e_1780_, 0);
v_args_1801_ = lean_ctor_get(v_e_1780_, 1);
lean_inc(v_fvarId_1800_);
v___x_1802_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1779_, v_fvarId_1800_, v_translator_1781_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_fvarId_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v_fvarId_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_fvarId_1803_);
lean_dec_ref(v___x_1802_);
lean_inc_ref(v_args_1801_);
v___x_1804_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1778_, v_s_1779_, v_args_1801_, v_translator_1781_);
v___x_1805_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_1778_, v_e_1780_, v_fvarId_1803_, v___x_1804_);
lean_dec_ref(v_e_1780_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; 
lean_dec_ref(v_e_1780_);
v___x_1806_ = lean_box(1);
return v___x_1806_;
}
}
case 5:
{
lean_object* v_args_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v_args_1807_ = lean_ctor_get(v_e_1780_, 1);
lean_inc_ref(v_args_1807_);
v___x_1808_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1778_, v_s_1779_, v_args_1807_, v_translator_1781_);
v___x_1809_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1778_, v_e_1780_, v___x_1808_);
return v___x_1809_;
}
case 6:
{
lean_object* v_var_1810_; 
v_var_1810_ = lean_ctor_get(v_e_1780_, 1);
lean_inc(v_var_1810_);
v_fvarId_1783_ = v_var_1810_;
goto v___jp_1782_;
}
case 7:
{
lean_object* v_var_1811_; 
v_var_1811_ = lean_ctor_get(v_e_1780_, 1);
lean_inc(v_var_1811_);
v_fvarId_1783_ = v_var_1811_;
goto v___jp_1782_;
}
case 8:
{
lean_object* v_var_1812_; lean_object* v___x_1813_; 
v_var_1812_ = lean_ctor_get(v_e_1780_, 2);
lean_inc(v_var_1812_);
v___x_1813_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1779_, v_var_1812_, v_translator_1781_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_fvarId_1814_; lean_object* v___x_1815_; 
v_fvarId_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_fvarId_1814_);
lean_dec_ref(v___x_1813_);
v___x_1815_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1778_, v_e_1780_, v_fvarId_1814_);
return v___x_1815_;
}
else
{
lean_object* v___x_1816_; 
lean_dec_ref(v_e_1780_);
v___x_1816_ = lean_box(1);
return v___x_1816_;
}
}
case 9:
{
lean_object* v_args_1817_; 
v_args_1817_ = lean_ctor_get(v_e_1780_, 1);
lean_inc_ref(v_args_1817_);
v_args_1789_ = v_args_1817_;
goto v___jp_1788_;
}
case 10:
{
lean_object* v_args_1818_; 
v_args_1818_ = lean_ctor_get(v_e_1780_, 1);
lean_inc_ref(v_args_1818_);
v_args_1789_ = v_args_1818_;
goto v___jp_1788_;
}
case 11:
{
lean_object* v_n_1819_; lean_object* v_var_1820_; lean_object* v___x_1821_; 
v_n_1819_ = lean_ctor_get(v_e_1780_, 0);
lean_inc(v_n_1819_);
v_var_1820_ = lean_ctor_get(v_e_1780_, 1);
lean_inc(v_var_1820_);
v___x_1821_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1779_, v_var_1820_, v_translator_1781_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_fvarId_1822_; lean_object* v___x_1823_; 
v_fvarId_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_fvarId_1822_);
lean_dec_ref(v___x_1821_);
v___x_1823_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_1778_, v_e_1780_, v_n_1819_, v_fvarId_1822_);
lean_dec_ref(v_e_1780_);
return v___x_1823_;
}
else
{
lean_object* v___x_1824_; 
lean_dec(v_n_1819_);
lean_dec_ref(v_e_1780_);
v___x_1824_ = lean_box(1);
return v___x_1824_;
}
}
case 12:
{
lean_object* v_var_1825_; lean_object* v_i_1826_; uint8_t v_updateHeader_1827_; lean_object* v_args_1828_; lean_object* v___x_1829_; 
v_var_1825_ = lean_ctor_get(v_e_1780_, 0);
v_i_1826_ = lean_ctor_get(v_e_1780_, 1);
lean_inc_ref(v_i_1826_);
v_updateHeader_1827_ = lean_ctor_get_uint8(v_e_1780_, sizeof(void*)*3);
v_args_1828_ = lean_ctor_get(v_e_1780_, 2);
lean_inc(v_var_1825_);
v___x_1829_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1779_, v_var_1825_, v_translator_1781_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_fvarId_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v_fvarId_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_fvarId_1830_);
lean_dec_ref(v___x_1829_);
lean_inc_ref(v_args_1828_);
v___x_1831_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1778_, v_s_1779_, v_args_1828_, v_translator_1781_);
v___x_1832_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_1778_, v_e_1780_, v_fvarId_1830_, v_i_1826_, v_updateHeader_1827_, v___x_1831_);
return v___x_1832_;
}
else
{
lean_object* v___x_1833_; 
lean_dec_ref(v_i_1826_);
lean_dec_ref(v_e_1780_);
v___x_1833_ = lean_box(1);
return v___x_1833_;
}
}
case 13:
{
lean_object* v_ty_1834_; lean_object* v_fvarId_1835_; lean_object* v___x_1836_; 
v_ty_1834_ = lean_ctor_get(v_e_1780_, 0);
lean_inc_ref(v_ty_1834_);
v_fvarId_1835_ = lean_ctor_get(v_e_1780_, 1);
lean_inc(v_fvarId_1835_);
v___x_1836_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1779_, v_fvarId_1835_, v_translator_1781_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_fvarId_1837_; lean_object* v___x_1838_; 
v_fvarId_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_fvarId_1837_);
lean_dec_ref(v___x_1836_);
v___x_1838_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_1778_, v_e_1780_, v_ty_1834_, v_fvarId_1837_);
lean_dec_ref(v_e_1780_);
return v___x_1838_;
}
else
{
lean_object* v___x_1839_; 
lean_dec_ref(v_ty_1834_);
lean_dec_ref(v_e_1780_);
v___x_1839_ = lean_box(1);
return v___x_1839_;
}
}
case 14:
{
lean_object* v_fvarId_1840_; lean_object* v___x_1841_; 
v_fvarId_1840_ = lean_ctor_get(v_e_1780_, 0);
lean_inc(v_fvarId_1840_);
v___x_1841_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1779_, v_fvarId_1840_, v_translator_1781_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_fvarId_1842_; lean_object* v___x_1843_; 
v_fvarId_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_fvarId_1842_);
lean_dec_ref(v___x_1841_);
v___x_1843_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_1778_, v_e_1780_, v_fvarId_1842_);
return v___x_1843_;
}
else
{
lean_object* v___x_1844_; 
lean_dec_ref(v_e_1780_);
v___x_1844_ = lean_box(1);
return v___x_1844_;
}
}
case 15:
{
lean_object* v_fvarId_1845_; lean_object* v___x_1846_; 
v_fvarId_1845_ = lean_ctor_get(v_e_1780_, 0);
lean_inc(v_fvarId_1845_);
v___x_1846_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1779_, v_fvarId_1845_, v_translator_1781_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_fvarId_1847_; lean_object* v___x_1848_; 
v_fvarId_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_fvarId_1847_);
lean_dec_ref(v___x_1846_);
v___x_1848_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_1778_, v_e_1780_, v_fvarId_1847_);
return v___x_1848_;
}
else
{
lean_object* v___x_1849_; 
lean_dec_ref(v_e_1780_);
v___x_1849_ = lean_box(1);
return v___x_1849_;
}
}
default: 
{
return v_e_1780_;
}
}
v___jp_1782_:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1779_, v_fvarId_1783_, v_translator_1781_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_fvarId_1785_; lean_object* v___x_1786_; 
v_fvarId_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_fvarId_1785_);
lean_dec_ref(v___x_1784_);
v___x_1786_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1778_, v_e_1780_, v_fvarId_1785_);
return v___x_1786_;
}
else
{
lean_object* v___x_1787_; 
lean_dec(v_e_1780_);
v___x_1787_ = lean_box(1);
return v___x_1787_;
}
}
v___jp_1788_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1778_, v_s_1779_, v_args_1789_, v_translator_1781_);
v___x_1791_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1778_, v_e_1780_, v___x_1790_);
return v___x_1791_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp___boxed(lean_object* v_pu_1850_, lean_object* v_s_1851_, lean_object* v_e_1852_, lean_object* v_translator_1853_){
_start:
{
uint8_t v_pu_boxed_1854_; uint8_t v_translator_boxed_1855_; lean_object* v_res_1856_; 
v_pu_boxed_1854_ = lean_unbox(v_pu_1850_);
v_translator_boxed_1855_ = lean_unbox(v_translator_1853_);
v_res_1856_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_boxed_1854_, v_s_1851_, v_e_1852_, v_translator_boxed_1855_);
lean_dec_ref(v_s_1851_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___redArg(lean_object* v_inst_1857_, lean_object* v_inst_1858_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_apply_2(v_inst_1857_, lean_box(0), v_inst_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(uint8_t v_pu_1860_, uint8_t v_t_1861_, lean_object* v_m_1862_, lean_object* v_n_1863_, lean_object* v_inst_1864_, lean_object* v_inst_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = lean_apply_2(v_inst_1864_, lean_box(0), v_inst_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___boxed(lean_object* v_pu_1867_, lean_object* v_t_1868_, lean_object* v_m_1869_, lean_object* v_n_1870_, lean_object* v_inst_1871_, lean_object* v_inst_1872_){
_start:
{
uint8_t v_pu_boxed_1873_; uint8_t v_t_boxed_1874_; lean_object* v_res_1875_; 
v_pu_boxed_1873_ = lean_unbox(v_pu_1867_);
v_t_boxed_1874_ = lean_unbox(v_t_1868_);
v_res_1875_ = l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(v_pu_boxed_1873_, v_t_boxed_1874_, v_m_1869_, v_n_1870_, v_inst_1871_, v_inst_1872_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0(lean_object* v_inst_1876_, lean_object* v_inst_1877_, lean_object* v_f_1878_){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = lean_apply_1(v_inst_1876_, v_f_1878_);
v___x_1880_ = lean_apply_2(v_inst_1877_, lean_box(0), v___x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg(lean_object* v_inst_1881_, lean_object* v_inst_1882_){
_start:
{
lean_object* v___f_1883_; 
v___f_1883_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1883_, 0, v_inst_1882_);
lean_closure_set(v___f_1883_, 1, v_inst_1881_);
return v___f_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(uint8_t v_pu_1884_, lean_object* v_m_1885_, lean_object* v_n_1886_, lean_object* v_inst_1887_, lean_object* v_inst_1888_){
_start:
{
lean_object* v___f_1889_; 
v___f_1889_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1889_, 0, v_inst_1888_);
lean_closure_set(v___f_1889_, 1, v_inst_1887_);
return v___f_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___boxed(lean_object* v_pu_1890_, lean_object* v_m_1891_, lean_object* v_n_1892_, lean_object* v_inst_1893_, lean_object* v_inst_1894_){
_start:
{
uint8_t v_pu_boxed_1895_; lean_object* v_res_1896_; 
v_pu_boxed_1895_ = lean_unbox(v_pu_1890_);
v_res_1896_ = l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(v_pu_boxed_1895_, v_m_1891_, v_n_1892_, v_inst_1893_, v_inst_1894_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___lam__0(lean_object* v___x_1897_, lean_object* v___x_1898_, lean_object* v_fvarId_1899_, lean_object* v_arg_1900_, lean_object* v_s_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1897_, v___x_1898_, v_s_1901_, v_fvarId_1899_, v_arg_1900_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg(lean_object* v_inst_1905_, lean_object* v_fvarId_1906_, lean_object* v_arg_1907_){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___f_1910_; lean_object* v___x_1911_; 
v___x_1908_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1909_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1910_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1910_, 0, v___x_1908_);
lean_closure_set(v___f_1910_, 1, v___x_1909_);
lean_closure_set(v___f_1910_, 2, v_fvarId_1906_);
lean_closure_set(v___f_1910_, 3, v_arg_1907_);
v___x_1911_ = lean_apply_1(v_inst_1905_, v___f_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst(lean_object* v_m_1912_, uint8_t v_pu_1913_, lean_object* v_inst_1914_, lean_object* v_fvarId_1915_, lean_object* v_arg_1916_){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___f_1919_; lean_object* v___x_1920_; 
v___x_1917_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1918_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1919_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1919_, 0, v___x_1917_);
lean_closure_set(v___f_1919_, 1, v___x_1918_);
lean_closure_set(v___f_1919_, 2, v_fvarId_1915_);
lean_closure_set(v___f_1919_, 3, v_arg_1916_);
v___x_1920_ = lean_apply_1(v_inst_1914_, v___f_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___boxed(lean_object* v_m_1921_, lean_object* v_pu_1922_, lean_object* v_inst_1923_, lean_object* v_fvarId_1924_, lean_object* v_arg_1925_){
_start:
{
uint8_t v_pu_boxed_1926_; lean_object* v_res_1927_; 
v_pu_boxed_1926_ = lean_unbox(v_pu_1922_);
v_res_1927_ = l_Lean_Compiler_LCNF_addSubst(v_m_1921_, v_pu_boxed_1926_, v_inst_1923_, v_fvarId_1924_, v_arg_1925_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0(lean_object* v_fvarId_x27_1928_, lean_object* v___x_1929_, lean_object* v___x_1930_, lean_object* v_fvarId_1931_, lean_object* v_s_1932_){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1933_, 0, v_fvarId_x27_1928_);
v___x_1934_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1929_, v___x_1930_, v_s_1932_, v_fvarId_1931_, v___x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg(lean_object* v_inst_1935_, lean_object* v_fvarId_1936_, lean_object* v_fvarId_x27_1937_){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___f_1940_; lean_object* v___x_1941_; 
v___x_1938_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1939_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1940_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1940_, 0, v_fvarId_x27_1937_);
lean_closure_set(v___f_1940_, 1, v___x_1938_);
lean_closure_set(v___f_1940_, 2, v___x_1939_);
lean_closure_set(v___f_1940_, 3, v_fvarId_1936_);
v___x_1941_ = lean_apply_1(v_inst_1935_, v___f_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst(lean_object* v_m_1942_, uint8_t v_ph_1943_, lean_object* v_inst_1944_, lean_object* v_fvarId_1945_, lean_object* v_fvarId_x27_1946_){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___f_1949_; lean_object* v___x_1950_; 
v___x_1947_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1948_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1949_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1949_, 0, v_fvarId_x27_1946_);
lean_closure_set(v___f_1949_, 1, v___x_1947_);
lean_closure_set(v___f_1949_, 2, v___x_1948_);
lean_closure_set(v___f_1949_, 3, v_fvarId_1945_);
v___x_1950_ = lean_apply_1(v_inst_1944_, v___f_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___boxed(lean_object* v_m_1951_, lean_object* v_ph_1952_, lean_object* v_inst_1953_, lean_object* v_fvarId_1954_, lean_object* v_fvarId_x27_1955_){
_start:
{
uint8_t v_ph_boxed_1956_; lean_object* v_res_1957_; 
v_ph_boxed_1956_ = lean_unbox(v_ph_1952_);
v_res_1957_ = l_Lean_Compiler_LCNF_addFVarSubst(v_m_1951_, v_ph_boxed_1956_, v_inst_1953_, v_fvarId_1954_, v_fvarId_x27_1955_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(lean_object* v_fvarId_1958_, uint8_t v_t_1959_, lean_object* v_toPure_1960_, lean_object* v_____do__lift_1961_){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_____do__lift_1961_, v_fvarId_1958_, v_t_1959_);
v___x_1963_ = lean_apply_2(v_toPure_1960_, lean_box(0), v___x_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed(lean_object* v_fvarId_1964_, lean_object* v_t_1965_, lean_object* v_toPure_1966_, lean_object* v_____do__lift_1967_){
_start:
{
uint8_t v_t_boxed_1968_; lean_object* v_res_1969_; 
v_t_boxed_1968_ = lean_unbox(v_t_1965_);
v_res_1969_ = l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(v_fvarId_1964_, v_t_boxed_1968_, v_toPure_1966_, v_____do__lift_1967_);
lean_dec_ref(v_____do__lift_1967_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg(uint8_t v_t_1970_, lean_object* v_inst_1971_, lean_object* v_inst_1972_, lean_object* v_fvarId_1973_){
_start:
{
lean_object* v_toApplicative_1974_; lean_object* v_toBind_1975_; lean_object* v_toPure_1976_; lean_object* v___x_1977_; lean_object* v___f_1978_; lean_object* v___x_1979_; 
v_toApplicative_1974_ = lean_ctor_get(v_inst_1972_, 0);
lean_inc_ref(v_toApplicative_1974_);
v_toBind_1975_ = lean_ctor_get(v_inst_1972_, 1);
lean_inc(v_toBind_1975_);
lean_dec_ref(v_inst_1972_);
v_toPure_1976_ = lean_ctor_get(v_toApplicative_1974_, 1);
lean_inc(v_toPure_1976_);
lean_dec_ref(v_toApplicative_1974_);
v___x_1977_ = lean_box(v_t_1970_);
v___f_1978_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1978_, 0, v_fvarId_1973_);
lean_closure_set(v___f_1978_, 1, v___x_1977_);
lean_closure_set(v___f_1978_, 2, v_toPure_1976_);
v___x_1979_ = lean_apply_4(v_toBind_1975_, lean_box(0), lean_box(0), v_inst_1971_, v___f_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___boxed(lean_object* v_t_1980_, lean_object* v_inst_1981_, lean_object* v_inst_1982_, lean_object* v_fvarId_1983_){
_start:
{
uint8_t v_t_boxed_1984_; lean_object* v_res_1985_; 
v_t_boxed_1984_ = lean_unbox(v_t_1980_);
v_res_1985_ = l_Lean_Compiler_LCNF_normFVar___redArg(v_t_boxed_1984_, v_inst_1981_, v_inst_1982_, v_fvarId_1983_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar(lean_object* v_m_1986_, uint8_t v_pu_1987_, uint8_t v_t_1988_, lean_object* v_inst_1989_, lean_object* v_inst_1990_, lean_object* v_fvarId_1991_){
_start:
{
lean_object* v_toApplicative_1992_; lean_object* v_toBind_1993_; lean_object* v_toPure_1994_; lean_object* v___x_1995_; lean_object* v___f_1996_; lean_object* v___x_1997_; 
v_toApplicative_1992_ = lean_ctor_get(v_inst_1990_, 0);
lean_inc_ref(v_toApplicative_1992_);
v_toBind_1993_ = lean_ctor_get(v_inst_1990_, 1);
lean_inc(v_toBind_1993_);
lean_dec_ref(v_inst_1990_);
v_toPure_1994_ = lean_ctor_get(v_toApplicative_1992_, 1);
lean_inc(v_toPure_1994_);
lean_dec_ref(v_toApplicative_1992_);
v___x_1995_ = lean_box(v_t_1988_);
v___f_1996_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1996_, 0, v_fvarId_1991_);
lean_closure_set(v___f_1996_, 1, v___x_1995_);
lean_closure_set(v___f_1996_, 2, v_toPure_1994_);
v___x_1997_ = lean_apply_4(v_toBind_1993_, lean_box(0), lean_box(0), v_inst_1989_, v___f_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___boxed(lean_object* v_m_1998_, lean_object* v_pu_1999_, lean_object* v_t_2000_, lean_object* v_inst_2001_, lean_object* v_inst_2002_, lean_object* v_fvarId_2003_){
_start:
{
uint8_t v_pu_boxed_2004_; uint8_t v_t_boxed_2005_; lean_object* v_res_2006_; 
v_pu_boxed_2004_ = lean_unbox(v_pu_1999_);
v_t_boxed_2005_ = lean_unbox(v_t_2000_);
v_res_2006_ = l_Lean_Compiler_LCNF_normFVar(v_m_1998_, v_pu_boxed_2004_, v_t_boxed_2005_, v_inst_2001_, v_inst_2002_, v_fvarId_2003_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(uint8_t v_pu_2007_, uint8_t v_t_2008_, lean_object* v_e_2009_, lean_object* v_toPure_2010_, lean_object* v_____do__lift_2011_){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2007_, v_____do__lift_2011_, v_t_2008_, v_e_2009_);
v___x_2013_ = lean_apply_2(v_toPure_2010_, lean_box(0), v___x_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed(lean_object* v_pu_2014_, lean_object* v_t_2015_, lean_object* v_e_2016_, lean_object* v_toPure_2017_, lean_object* v_____do__lift_2018_){
_start:
{
uint8_t v_pu_boxed_2019_; uint8_t v_t_boxed_2020_; lean_object* v_res_2021_; 
v_pu_boxed_2019_ = lean_unbox(v_pu_2014_);
v_t_boxed_2020_ = lean_unbox(v_t_2015_);
v_res_2021_ = l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(v_pu_boxed_2019_, v_t_boxed_2020_, v_e_2016_, v_toPure_2017_, v_____do__lift_2018_);
lean_dec_ref(v_____do__lift_2018_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg(uint8_t v_pu_2022_, uint8_t v_t_2023_, lean_object* v_inst_2024_, lean_object* v_inst_2025_, lean_object* v_e_2026_){
_start:
{
lean_object* v_toApplicative_2027_; lean_object* v_toBind_2028_; lean_object* v_toPure_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___f_2032_; lean_object* v___x_2033_; 
v_toApplicative_2027_ = lean_ctor_get(v_inst_2025_, 0);
lean_inc_ref(v_toApplicative_2027_);
v_toBind_2028_ = lean_ctor_get(v_inst_2025_, 1);
lean_inc(v_toBind_2028_);
lean_dec_ref(v_inst_2025_);
v_toPure_2029_ = lean_ctor_get(v_toApplicative_2027_, 1);
lean_inc(v_toPure_2029_);
lean_dec_ref(v_toApplicative_2027_);
v___x_2030_ = lean_box(v_pu_2022_);
v___x_2031_ = lean_box(v_t_2023_);
v___f_2032_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2032_, 0, v___x_2030_);
lean_closure_set(v___f_2032_, 1, v___x_2031_);
lean_closure_set(v___f_2032_, 2, v_e_2026_);
lean_closure_set(v___f_2032_, 3, v_toPure_2029_);
v___x_2033_ = lean_apply_4(v_toBind_2028_, lean_box(0), lean_box(0), v_inst_2024_, v___f_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___boxed(lean_object* v_pu_2034_, lean_object* v_t_2035_, lean_object* v_inst_2036_, lean_object* v_inst_2037_, lean_object* v_e_2038_){
_start:
{
uint8_t v_pu_boxed_2039_; uint8_t v_t_boxed_2040_; lean_object* v_res_2041_; 
v_pu_boxed_2039_ = lean_unbox(v_pu_2034_);
v_t_boxed_2040_ = lean_unbox(v_t_2035_);
v_res_2041_ = l_Lean_Compiler_LCNF_normExpr___redArg(v_pu_boxed_2039_, v_t_boxed_2040_, v_inst_2036_, v_inst_2037_, v_e_2038_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr(lean_object* v_m_2042_, uint8_t v_pu_2043_, uint8_t v_t_2044_, lean_object* v_inst_2045_, lean_object* v_inst_2046_, lean_object* v_e_2047_){
_start:
{
lean_object* v_toApplicative_2048_; lean_object* v_toBind_2049_; lean_object* v_toPure_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___f_2053_; lean_object* v___x_2054_; 
v_toApplicative_2048_ = lean_ctor_get(v_inst_2046_, 0);
lean_inc_ref(v_toApplicative_2048_);
v_toBind_2049_ = lean_ctor_get(v_inst_2046_, 1);
lean_inc(v_toBind_2049_);
lean_dec_ref(v_inst_2046_);
v_toPure_2050_ = lean_ctor_get(v_toApplicative_2048_, 1);
lean_inc(v_toPure_2050_);
lean_dec_ref(v_toApplicative_2048_);
v___x_2051_ = lean_box(v_pu_2043_);
v___x_2052_ = lean_box(v_t_2044_);
v___f_2053_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2053_, 0, v___x_2051_);
lean_closure_set(v___f_2053_, 1, v___x_2052_);
lean_closure_set(v___f_2053_, 2, v_e_2047_);
lean_closure_set(v___f_2053_, 3, v_toPure_2050_);
v___x_2054_ = lean_apply_4(v_toBind_2049_, lean_box(0), lean_box(0), v_inst_2045_, v___f_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___boxed(lean_object* v_m_2055_, lean_object* v_pu_2056_, lean_object* v_t_2057_, lean_object* v_inst_2058_, lean_object* v_inst_2059_, lean_object* v_e_2060_){
_start:
{
uint8_t v_pu_boxed_2061_; uint8_t v_t_boxed_2062_; lean_object* v_res_2063_; 
v_pu_boxed_2061_ = lean_unbox(v_pu_2056_);
v_t_boxed_2062_ = lean_unbox(v_t_2057_);
v_res_2063_ = l_Lean_Compiler_LCNF_normExpr(v_m_2055_, v_pu_boxed_2061_, v_t_boxed_2062_, v_inst_2058_, v_inst_2059_, v_e_2060_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0(uint8_t v_pu_2064_, lean_object* v_arg_2065_, uint8_t v_t_2066_, lean_object* v_toPure_2067_, lean_object* v_____do__lift_2068_){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2064_, v_____do__lift_2068_, v_arg_2065_, v_t_2066_);
v___x_2070_ = lean_apply_2(v_toPure_2067_, lean_box(0), v___x_2069_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed(lean_object* v_pu_2071_, lean_object* v_arg_2072_, lean_object* v_t_2073_, lean_object* v_toPure_2074_, lean_object* v_____do__lift_2075_){
_start:
{
uint8_t v_pu_boxed_2076_; uint8_t v_t_boxed_2077_; lean_object* v_res_2078_; 
v_pu_boxed_2076_ = lean_unbox(v_pu_2071_);
v_t_boxed_2077_ = lean_unbox(v_t_2073_);
v_res_2078_ = l_Lean_Compiler_LCNF_normArg___redArg___lam__0(v_pu_boxed_2076_, v_arg_2072_, v_t_boxed_2077_, v_toPure_2074_, v_____do__lift_2075_);
lean_dec_ref(v_____do__lift_2075_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg(uint8_t v_pu_2079_, uint8_t v_t_2080_, lean_object* v_inst_2081_, lean_object* v_inst_2082_, lean_object* v_arg_2083_){
_start:
{
lean_object* v_toApplicative_2084_; lean_object* v_toBind_2085_; lean_object* v_toPure_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___f_2089_; lean_object* v___x_2090_; 
v_toApplicative_2084_ = lean_ctor_get(v_inst_2082_, 0);
lean_inc_ref(v_toApplicative_2084_);
v_toBind_2085_ = lean_ctor_get(v_inst_2082_, 1);
lean_inc(v_toBind_2085_);
lean_dec_ref(v_inst_2082_);
v_toPure_2086_ = lean_ctor_get(v_toApplicative_2084_, 1);
lean_inc(v_toPure_2086_);
lean_dec_ref(v_toApplicative_2084_);
v___x_2087_ = lean_box(v_pu_2079_);
v___x_2088_ = lean_box(v_t_2080_);
v___f_2089_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2089_, 0, v___x_2087_);
lean_closure_set(v___f_2089_, 1, v_arg_2083_);
lean_closure_set(v___f_2089_, 2, v___x_2088_);
lean_closure_set(v___f_2089_, 3, v_toPure_2086_);
v___x_2090_ = lean_apply_4(v_toBind_2085_, lean_box(0), lean_box(0), v_inst_2081_, v___f_2089_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___boxed(lean_object* v_pu_2091_, lean_object* v_t_2092_, lean_object* v_inst_2093_, lean_object* v_inst_2094_, lean_object* v_arg_2095_){
_start:
{
uint8_t v_pu_boxed_2096_; uint8_t v_t_boxed_2097_; lean_object* v_res_2098_; 
v_pu_boxed_2096_ = lean_unbox(v_pu_2091_);
v_t_boxed_2097_ = lean_unbox(v_t_2092_);
v_res_2098_ = l_Lean_Compiler_LCNF_normArg___redArg(v_pu_boxed_2096_, v_t_boxed_2097_, v_inst_2093_, v_inst_2094_, v_arg_2095_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg(lean_object* v_m_2099_, uint8_t v_pu_2100_, uint8_t v_t_2101_, lean_object* v_inst_2102_, lean_object* v_inst_2103_, lean_object* v_arg_2104_){
_start:
{
lean_object* v_toApplicative_2105_; lean_object* v_toBind_2106_; lean_object* v_toPure_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___f_2110_; lean_object* v___x_2111_; 
v_toApplicative_2105_ = lean_ctor_get(v_inst_2103_, 0);
lean_inc_ref(v_toApplicative_2105_);
v_toBind_2106_ = lean_ctor_get(v_inst_2103_, 1);
lean_inc(v_toBind_2106_);
lean_dec_ref(v_inst_2103_);
v_toPure_2107_ = lean_ctor_get(v_toApplicative_2105_, 1);
lean_inc(v_toPure_2107_);
lean_dec_ref(v_toApplicative_2105_);
v___x_2108_ = lean_box(v_pu_2100_);
v___x_2109_ = lean_box(v_t_2101_);
v___f_2110_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2110_, 0, v___x_2108_);
lean_closure_set(v___f_2110_, 1, v_arg_2104_);
lean_closure_set(v___f_2110_, 2, v___x_2109_);
lean_closure_set(v___f_2110_, 3, v_toPure_2107_);
v___x_2111_ = lean_apply_4(v_toBind_2106_, lean_box(0), lean_box(0), v_inst_2102_, v___f_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___boxed(lean_object* v_m_2112_, lean_object* v_pu_2113_, lean_object* v_t_2114_, lean_object* v_inst_2115_, lean_object* v_inst_2116_, lean_object* v_arg_2117_){
_start:
{
uint8_t v_pu_boxed_2118_; uint8_t v_t_boxed_2119_; lean_object* v_res_2120_; 
v_pu_boxed_2118_ = lean_unbox(v_pu_2113_);
v_t_boxed_2119_ = lean_unbox(v_t_2114_);
v_res_2120_ = l_Lean_Compiler_LCNF_normArg(v_m_2112_, v_pu_boxed_2118_, v_t_boxed_2119_, v_inst_2115_, v_inst_2116_, v_arg_2117_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(uint8_t v_pu_2121_, lean_object* v_e_2122_, uint8_t v_t_2123_, lean_object* v_toPure_2124_, lean_object* v_____do__lift_2125_){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_2121_, v_____do__lift_2125_, v_e_2122_, v_t_2123_);
v___x_2127_ = lean_apply_2(v_toPure_2124_, lean_box(0), v___x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed(lean_object* v_pu_2128_, lean_object* v_e_2129_, lean_object* v_t_2130_, lean_object* v_toPure_2131_, lean_object* v_____do__lift_2132_){
_start:
{
uint8_t v_pu_boxed_2133_; uint8_t v_t_boxed_2134_; lean_object* v_res_2135_; 
v_pu_boxed_2133_ = lean_unbox(v_pu_2128_);
v_t_boxed_2134_ = lean_unbox(v_t_2130_);
v_res_2135_ = l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(v_pu_boxed_2133_, v_e_2129_, v_t_boxed_2134_, v_toPure_2131_, v_____do__lift_2132_);
lean_dec_ref(v_____do__lift_2132_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg(uint8_t v_pu_2136_, uint8_t v_t_2137_, lean_object* v_inst_2138_, lean_object* v_inst_2139_, lean_object* v_e_2140_){
_start:
{
lean_object* v_toApplicative_2141_; lean_object* v_toBind_2142_; lean_object* v_toPure_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___f_2146_; lean_object* v___x_2147_; 
v_toApplicative_2141_ = lean_ctor_get(v_inst_2139_, 0);
lean_inc_ref(v_toApplicative_2141_);
v_toBind_2142_ = lean_ctor_get(v_inst_2139_, 1);
lean_inc(v_toBind_2142_);
lean_dec_ref(v_inst_2139_);
v_toPure_2143_ = lean_ctor_get(v_toApplicative_2141_, 1);
lean_inc(v_toPure_2143_);
lean_dec_ref(v_toApplicative_2141_);
v___x_2144_ = lean_box(v_pu_2136_);
v___x_2145_ = lean_box(v_t_2137_);
v___f_2146_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2146_, 0, v___x_2144_);
lean_closure_set(v___f_2146_, 1, v_e_2140_);
lean_closure_set(v___f_2146_, 2, v___x_2145_);
lean_closure_set(v___f_2146_, 3, v_toPure_2143_);
v___x_2147_ = lean_apply_4(v_toBind_2142_, lean_box(0), lean_box(0), v_inst_2138_, v___f_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___boxed(lean_object* v_pu_2148_, lean_object* v_t_2149_, lean_object* v_inst_2150_, lean_object* v_inst_2151_, lean_object* v_e_2152_){
_start:
{
uint8_t v_pu_boxed_2153_; uint8_t v_t_boxed_2154_; lean_object* v_res_2155_; 
v_pu_boxed_2153_ = lean_unbox(v_pu_2148_);
v_t_boxed_2154_ = lean_unbox(v_t_2149_);
v_res_2155_ = l_Lean_Compiler_LCNF_normLetValue___redArg(v_pu_boxed_2153_, v_t_boxed_2154_, v_inst_2150_, v_inst_2151_, v_e_2152_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue(lean_object* v_m_2156_, uint8_t v_pu_2157_, uint8_t v_t_2158_, lean_object* v_inst_2159_, lean_object* v_inst_2160_, lean_object* v_e_2161_){
_start:
{
lean_object* v_toApplicative_2162_; lean_object* v_toBind_2163_; lean_object* v_toPure_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___f_2167_; lean_object* v___x_2168_; 
v_toApplicative_2162_ = lean_ctor_get(v_inst_2160_, 0);
lean_inc_ref(v_toApplicative_2162_);
v_toBind_2163_ = lean_ctor_get(v_inst_2160_, 1);
lean_inc(v_toBind_2163_);
lean_dec_ref(v_inst_2160_);
v_toPure_2164_ = lean_ctor_get(v_toApplicative_2162_, 1);
lean_inc(v_toPure_2164_);
lean_dec_ref(v_toApplicative_2162_);
v___x_2165_ = lean_box(v_pu_2157_);
v___x_2166_ = lean_box(v_t_2158_);
v___f_2167_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2167_, 0, v___x_2165_);
lean_closure_set(v___f_2167_, 1, v_e_2161_);
lean_closure_set(v___f_2167_, 2, v___x_2166_);
lean_closure_set(v___f_2167_, 3, v_toPure_2164_);
v___x_2168_ = lean_apply_4(v_toBind_2163_, lean_box(0), lean_box(0), v_inst_2159_, v___f_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___boxed(lean_object* v_m_2169_, lean_object* v_pu_2170_, lean_object* v_t_2171_, lean_object* v_inst_2172_, lean_object* v_inst_2173_, lean_object* v_e_2174_){
_start:
{
uint8_t v_pu_boxed_2175_; uint8_t v_t_boxed_2176_; lean_object* v_res_2177_; 
v_pu_boxed_2175_ = lean_unbox(v_pu_2170_);
v_t_boxed_2176_ = lean_unbox(v_t_2171_);
v_res_2177_ = l_Lean_Compiler_LCNF_normLetValue(v_m_2169_, v_pu_boxed_2175_, v_t_boxed_2176_, v_inst_2172_, v_inst_2173_, v_e_2174_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore(uint8_t v_pu_2178_, lean_object* v_s_2179_, lean_object* v_e_2180_, uint8_t v_translator_2181_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2178_, v_s_2179_, v_translator_2181_, v_e_2180_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore___boxed(lean_object* v_pu_2183_, lean_object* v_s_2184_, lean_object* v_e_2185_, lean_object* v_translator_2186_){
_start:
{
uint8_t v_pu_boxed_2187_; uint8_t v_translator_boxed_2188_; lean_object* v_res_2189_; 
v_pu_boxed_2187_ = lean_unbox(v_pu_2183_);
v_translator_boxed_2188_ = lean_unbox(v_translator_2186_);
v_res_2189_ = l_Lean_Compiler_LCNF_normExprCore(v_pu_boxed_2187_, v_s_2184_, v_e_2185_, v_translator_boxed_2188_);
lean_dec_ref(v_s_2184_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(uint8_t v_pu_2190_, lean_object* v_args_2191_, uint8_t v_t_2192_, lean_object* v_toPure_2193_, lean_object* v_____do__lift_2194_){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_2190_, v_____do__lift_2194_, v_args_2191_, v_t_2192_);
v___x_2196_ = lean_apply_2(v_toPure_2193_, lean_box(0), v___x_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed(lean_object* v_pu_2197_, lean_object* v_args_2198_, lean_object* v_t_2199_, lean_object* v_toPure_2200_, lean_object* v_____do__lift_2201_){
_start:
{
uint8_t v_pu_boxed_2202_; uint8_t v_t_boxed_2203_; lean_object* v_res_2204_; 
v_pu_boxed_2202_ = lean_unbox(v_pu_2197_);
v_t_boxed_2203_ = lean_unbox(v_t_2199_);
v_res_2204_ = l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(v_pu_boxed_2202_, v_args_2198_, v_t_boxed_2203_, v_toPure_2200_, v_____do__lift_2201_);
lean_dec_ref(v_____do__lift_2201_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg(uint8_t v_pu_2205_, uint8_t v_t_2206_, lean_object* v_inst_2207_, lean_object* v_inst_2208_, lean_object* v_args_2209_){
_start:
{
lean_object* v_toApplicative_2210_; lean_object* v_toBind_2211_; lean_object* v_toPure_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___f_2215_; lean_object* v___x_2216_; 
v_toApplicative_2210_ = lean_ctor_get(v_inst_2208_, 0);
lean_inc_ref(v_toApplicative_2210_);
v_toBind_2211_ = lean_ctor_get(v_inst_2208_, 1);
lean_inc(v_toBind_2211_);
lean_dec_ref(v_inst_2208_);
v_toPure_2212_ = lean_ctor_get(v_toApplicative_2210_, 1);
lean_inc(v_toPure_2212_);
lean_dec_ref(v_toApplicative_2210_);
v___x_2213_ = lean_box(v_pu_2205_);
v___x_2214_ = lean_box(v_t_2206_);
v___f_2215_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2215_, 0, v___x_2213_);
lean_closure_set(v___f_2215_, 1, v_args_2209_);
lean_closure_set(v___f_2215_, 2, v___x_2214_);
lean_closure_set(v___f_2215_, 3, v_toPure_2212_);
v___x_2216_ = lean_apply_4(v_toBind_2211_, lean_box(0), lean_box(0), v_inst_2207_, v___f_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___boxed(lean_object* v_pu_2217_, lean_object* v_t_2218_, lean_object* v_inst_2219_, lean_object* v_inst_2220_, lean_object* v_args_2221_){
_start:
{
uint8_t v_pu_boxed_2222_; uint8_t v_t_boxed_2223_; lean_object* v_res_2224_; 
v_pu_boxed_2222_ = lean_unbox(v_pu_2217_);
v_t_boxed_2223_ = lean_unbox(v_t_2218_);
v_res_2224_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_boxed_2222_, v_t_boxed_2223_, v_inst_2219_, v_inst_2220_, v_args_2221_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs(lean_object* v_m_2225_, uint8_t v_pu_2226_, uint8_t v_t_2227_, lean_object* v_inst_2228_, lean_object* v_inst_2229_, lean_object* v_args_2230_){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_2226_, v_t_2227_, v_inst_2228_, v_inst_2229_, v_args_2230_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___boxed(lean_object* v_m_2232_, lean_object* v_pu_2233_, lean_object* v_t_2234_, lean_object* v_inst_2235_, lean_object* v_inst_2236_, lean_object* v_args_2237_){
_start:
{
uint8_t v_pu_boxed_2238_; uint8_t v_t_boxed_2239_; lean_object* v_res_2240_; 
v_pu_boxed_2238_ = lean_unbox(v_pu_2233_);
v_t_boxed_2239_ = lean_unbox(v_t_2234_);
v_res_2240_ = l_Lean_Compiler_LCNF_normArgs(v_m_2232_, v_pu_boxed_2238_, v_t_boxed_2239_, v_inst_2235_, v_inst_2236_, v_args_2237_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object* v_binderName_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v_lctx_2246_; lean_object* v_nextIdx_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2260_; 
v___x_2244_ = lean_st_ref_get(v_a_2242_);
v___x_2245_ = lean_st_ref_take(v_a_2242_);
v_lctx_2246_ = lean_ctor_get(v___x_2245_, 0);
v_nextIdx_2247_ = lean_ctor_get(v___x_2245_, 1);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2249_ = v___x_2245_;
v_isShared_2250_ = v_isSharedCheck_2260_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_nextIdx_2247_);
lean_inc(v_lctx_2246_);
lean_dec(v___x_2245_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2260_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2254_; 
v___x_2251_ = lean_unsigned_to_nat(1u);
v___x_2252_ = lean_nat_add(v_nextIdx_2247_, v___x_2251_);
lean_dec(v_nextIdx_2247_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 1, v___x_2252_);
v___x_2254_ = v___x_2249_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_lctx_2246_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v___x_2252_);
v___x_2254_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
lean_object* v___x_2255_; lean_object* v_nextIdx_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2255_ = lean_st_ref_set(v_a_2242_, v___x_2254_);
v_nextIdx_2256_ = lean_ctor_get(v___x_2244_, 1);
lean_inc(v_nextIdx_2256_);
lean_dec(v___x_2244_);
v___x_2257_ = l_Lean_Name_num___override(v_binderName_2241_, v_nextIdx_2256_);
v___x_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
return v___x_2258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg___boxed(lean_object* v_binderName_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2261_, v_a_2262_);
lean_dec(v_a_2262_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object* v_binderName_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2265_, v_a_2267_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___boxed(lean_object* v_binderName_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_Compiler_LCNF_mkFreshBinderName(v_binderName_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
lean_dec(v_a_2276_);
lean_dec_ref(v_a_2275_);
lean_dec(v_a_2274_);
lean_dec_ref(v_a_2273_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(lean_object* v_binderName_2279_, lean_object* v_baseName_2280_, lean_object* v_a_2281_){
_start:
{
uint8_t v___x_2283_; 
v___x_2283_ = l_Lean_Name_isAnonymous(v_binderName_2279_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; 
lean_dec(v_baseName_2280_);
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v_binderName_2279_);
return v___x_2284_;
}
else
{
lean_object* v___x_2285_; 
lean_dec(v_binderName_2279_);
v___x_2285_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_baseName_2280_, v_a_2281_);
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg___boxed(lean_object* v_binderName_2286_, lean_object* v_baseName_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2286_, v_baseName_2287_, v_a_2288_);
lean_dec(v_a_2288_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous(lean_object* v_binderName_2291_, lean_object* v_baseName_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2291_, v_baseName_2292_, v_a_2294_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___boxed(lean_object* v_binderName_2299_, lean_object* v_baseName_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_Compiler_LCNF_ensureNotAnonymous(v_binderName_2299_, v_baseName_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
lean_dec(v_a_2304_);
lean_dec_ref(v_a_2303_);
lean_dec(v_a_2302_);
lean_dec_ref(v_a_2301_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(lean_object* v___y_2307_){
_start:
{
lean_object* v___x_2309_; lean_object* v_ngen_2310_; lean_object* v_namePrefix_2311_; lean_object* v_idx_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2341_; 
v___x_2309_ = lean_st_ref_get(v___y_2307_);
v_ngen_2310_ = lean_ctor_get(v___x_2309_, 2);
lean_inc_ref(v_ngen_2310_);
lean_dec(v___x_2309_);
v_namePrefix_2311_ = lean_ctor_get(v_ngen_2310_, 0);
v_idx_2312_ = lean_ctor_get(v_ngen_2310_, 1);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_ngen_2310_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2314_ = v_ngen_2310_;
v_isShared_2315_ = v_isSharedCheck_2341_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_idx_2312_);
lean_inc(v_namePrefix_2311_);
lean_dec(v_ngen_2310_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2341_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; lean_object* v_env_2317_; lean_object* v_nextMacroScope_2318_; lean_object* v_auxDeclNGen_2319_; lean_object* v_traceState_2320_; lean_object* v_cache_2321_; lean_object* v_messages_2322_; lean_object* v_infoState_2323_; lean_object* v_snapshotTasks_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2339_; 
v___x_2316_ = lean_st_ref_take(v___y_2307_);
v_env_2317_ = lean_ctor_get(v___x_2316_, 0);
v_nextMacroScope_2318_ = lean_ctor_get(v___x_2316_, 1);
v_auxDeclNGen_2319_ = lean_ctor_get(v___x_2316_, 3);
v_traceState_2320_ = lean_ctor_get(v___x_2316_, 4);
v_cache_2321_ = lean_ctor_get(v___x_2316_, 5);
v_messages_2322_ = lean_ctor_get(v___x_2316_, 6);
v_infoState_2323_ = lean_ctor_get(v___x_2316_, 7);
v_snapshotTasks_2324_ = lean_ctor_get(v___x_2316_, 8);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2339_ == 0)
{
lean_object* v_unused_2340_; 
v_unused_2340_ = lean_ctor_get(v___x_2316_, 2);
lean_dec(v_unused_2340_);
v___x_2326_ = v___x_2316_;
v_isShared_2327_ = v_isSharedCheck_2339_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_snapshotTasks_2324_);
lean_inc(v_infoState_2323_);
lean_inc(v_messages_2322_);
lean_inc(v_cache_2321_);
lean_inc(v_traceState_2320_);
lean_inc(v_auxDeclNGen_2319_);
lean_inc(v_nextMacroScope_2318_);
lean_inc(v_env_2317_);
lean_dec(v___x_2316_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2339_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v_r_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2332_; 
lean_inc(v_idx_2312_);
lean_inc(v_namePrefix_2311_);
v_r_2328_ = l_Lean_Name_num___override(v_namePrefix_2311_, v_idx_2312_);
v___x_2329_ = lean_unsigned_to_nat(1u);
v___x_2330_ = lean_nat_add(v_idx_2312_, v___x_2329_);
lean_dec(v_idx_2312_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 1, v___x_2330_);
v___x_2332_ = v___x_2314_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_namePrefix_2311_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2334_; 
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 2, v___x_2332_);
v___x_2334_ = v___x_2326_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_env_2317_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v_nextMacroScope_2318_);
lean_ctor_set(v_reuseFailAlloc_2337_, 2, v___x_2332_);
lean_ctor_set(v_reuseFailAlloc_2337_, 3, v_auxDeclNGen_2319_);
lean_ctor_set(v_reuseFailAlloc_2337_, 4, v_traceState_2320_);
lean_ctor_set(v_reuseFailAlloc_2337_, 5, v_cache_2321_);
lean_ctor_set(v_reuseFailAlloc_2337_, 6, v_messages_2322_);
lean_ctor_set(v_reuseFailAlloc_2337_, 7, v_infoState_2323_);
lean_ctor_set(v_reuseFailAlloc_2337_, 8, v_snapshotTasks_2324_);
v___x_2334_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = lean_st_ref_set(v___y_2307_, v___x_2334_);
v___x_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2336_, 0, v_r_2328_);
return v___x_2336_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg___boxed(lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2342_);
lean_dec(v___y_2342_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v___x_2350_; lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
v___x_2350_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2348_);
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0___boxed(lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t v_pu_2368_, lean_object* v_binderName_2369_, lean_object* v_type_2370_, uint8_t v_borrow_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2401_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2378_);
lean_dec_ref(v___x_2377_);
v___x_2379_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_2380_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2369_, v___x_2379_, v_a_2373_);
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2383_ = v___x_2380_;
v_isShared_2384_ = v_isSharedCheck_2401_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2380_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2401_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2385_; lean_object* v_lctx_2386_; lean_object* v_nextIdx_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2400_; 
v___x_2385_ = lean_st_ref_take(v_a_2373_);
v_lctx_2386_ = lean_ctor_get(v___x_2385_, 0);
v_nextIdx_2387_ = lean_ctor_get(v___x_2385_, 1);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2389_ = v___x_2385_;
v_isShared_2390_ = v_isSharedCheck_2400_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_nextIdx_2387_);
lean_inc(v_lctx_2386_);
lean_dec(v___x_2385_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2400_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2394_; 
v___x_2391_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2391_, 0, v_a_2378_);
lean_ctor_set(v___x_2391_, 1, v_a_2381_);
lean_ctor_set(v___x_2391_, 2, v_type_2370_);
lean_ctor_set_uint8(v___x_2391_, sizeof(void*)*3, v_borrow_2371_);
lean_inc_ref(v___x_2391_);
v___x_2392_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2368_, v_lctx_2386_, v___x_2391_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2392_);
v___x_2394_ = v___x_2389_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2399_, 1, v_nextIdx_2387_);
v___x_2394_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
lean_object* v___x_2395_; lean_object* v___x_2397_; 
v___x_2395_ = lean_st_ref_set(v_a_2373_, v___x_2394_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v___x_2391_);
v___x_2397_ = v___x_2383_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2391_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_dec_ref(v_type_2370_);
lean_dec(v_binderName_2369_);
v_a_2402_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2377_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2377_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam___boxed(lean_object* v_pu_2410_, lean_object* v_binderName_2411_, lean_object* v_type_2412_, lean_object* v_borrow_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
uint8_t v_pu_boxed_2419_; uint8_t v_borrow_boxed_2420_; lean_object* v_res_2421_; 
v_pu_boxed_2419_ = lean_unbox(v_pu_2410_);
v_borrow_boxed_2420_ = lean_unbox(v_borrow_2413_);
v_res_2421_ = l_Lean_Compiler_LCNF_mkParam(v_pu_boxed_2419_, v_binderName_2411_, v_type_2412_, v_borrow_boxed_2420_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2425_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___boxed(lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t v_pu_2437_, lean_object* v_binderName_2438_, lean_object* v_type_2439_, lean_object* v_value_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2470_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_a_2447_);
lean_dec_ref(v___x_2446_);
v___x_2448_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2449_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2438_, v___x_2448_, v_a_2442_);
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2452_ = v___x_2449_;
v_isShared_2453_ = v_isSharedCheck_2470_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2449_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2470_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2454_; lean_object* v_lctx_2455_; lean_object* v_nextIdx_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2469_; 
v___x_2454_ = lean_st_ref_take(v_a_2442_);
v_lctx_2455_ = lean_ctor_get(v___x_2454_, 0);
v_nextIdx_2456_ = lean_ctor_get(v___x_2454_, 1);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2458_ = v___x_2454_;
v_isShared_2459_ = v_isSharedCheck_2469_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_nextIdx_2456_);
lean_inc(v_lctx_2455_);
lean_dec(v___x_2454_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2469_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2463_; 
v___x_2460_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2460_, 0, v_a_2447_);
lean_ctor_set(v___x_2460_, 1, v_a_2450_);
lean_ctor_set(v___x_2460_, 2, v_type_2439_);
lean_ctor_set(v___x_2460_, 3, v_value_2440_);
lean_inc_ref(v___x_2460_);
v___x_2461_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2437_, v_lctx_2455_, v___x_2460_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v___x_2461_);
v___x_2463_ = v___x_2458_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_nextIdx_2456_);
v___x_2463_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2464_ = lean_st_ref_set(v_a_2442_, v___x_2463_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v___x_2460_);
v___x_2466_ = v___x_2452_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2460_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
lean_dec(v_value_2440_);
lean_dec_ref(v_type_2439_);
lean_dec(v_binderName_2438_);
v_a_2471_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2446_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2446_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl___boxed(lean_object* v_pu_2479_, lean_object* v_binderName_2480_, lean_object* v_type_2481_, lean_object* v_value_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_){
_start:
{
uint8_t v_pu_boxed_2488_; lean_object* v_res_2489_; 
v_pu_boxed_2488_ = lean_unbox(v_pu_2479_);
v_res_2489_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_boxed_2488_, v_binderName_2480_, v_type_2481_, v_value_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_);
lean_dec(v_a_2486_);
lean_dec_ref(v_a_2485_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t v_pu_2493_, lean_object* v_binderName_2494_, lean_object* v_type_2495_, lean_object* v_params_2496_, lean_object* v_value_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2527_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref(v___x_2503_);
v___x_2505_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFunDecl___closed__1));
v___x_2506_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2494_, v___x_2505_, v_a_2499_);
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2509_ = v___x_2506_;
v_isShared_2510_ = v_isSharedCheck_2527_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2506_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2527_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2511_; lean_object* v_lctx_2512_; lean_object* v_nextIdx_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2526_; 
v___x_2511_ = lean_st_ref_take(v_a_2499_);
v_lctx_2512_ = lean_ctor_get(v___x_2511_, 0);
v_nextIdx_2513_ = lean_ctor_get(v___x_2511_, 1);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2515_ = v___x_2511_;
v_isShared_2516_ = v_isSharedCheck_2526_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_nextIdx_2513_);
lean_inc(v_lctx_2512_);
lean_dec(v___x_2511_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2526_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2520_; 
v___x_2517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2517_, 0, v_a_2504_);
lean_ctor_set(v___x_2517_, 1, v_a_2507_);
lean_ctor_set(v___x_2517_, 2, v_params_2496_);
lean_ctor_set(v___x_2517_, 3, v_type_2495_);
lean_ctor_set(v___x_2517_, 4, v_value_2497_);
lean_inc_ref(v___x_2517_);
v___x_2518_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2493_, v_lctx_2512_, v___x_2517_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v___x_2518_);
v___x_2520_ = v___x_2515_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_nextIdx_2513_);
v___x_2520_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2521_ = lean_st_ref_set(v_a_2499_, v___x_2520_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 0, v___x_2517_);
v___x_2523_ = v___x_2509_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2517_);
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
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec_ref(v_value_2497_);
lean_dec_ref(v_params_2496_);
lean_dec_ref(v_type_2495_);
lean_dec(v_binderName_2494_);
v_a_2528_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2503_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2503_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl___boxed(lean_object* v_pu_2536_, lean_object* v_binderName_2537_, lean_object* v_type_2538_, lean_object* v_params_2539_, lean_object* v_value_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_){
_start:
{
uint8_t v_pu_boxed_2546_; lean_object* v_res_2547_; 
v_pu_boxed_2546_ = lean_unbox(v_pu_2536_);
v_res_2547_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_boxed_2546_, v_binderName_2537_, v_type_2538_, v_params_2539_, v_value_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(uint8_t v_pu_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v_a_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2554_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2555_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2554_, v_a_2550_);
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref(v___x_2555_);
v___x_2557_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2558_ = lean_box(1);
v___x_2559_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2548_, v_a_2556_, v___x_2557_, v___x_2558_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased___boxed(lean_object* v_pu_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_){
_start:
{
uint8_t v_pu_boxed_2566_; lean_object* v_res_2567_; 
v_pu_boxed_2566_ = lean_unbox(v_pu_2560_);
v_res_2567_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_boxed_2566_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_);
lean_dec(v_a_2564_);
lean_dec_ref(v_a_2563_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t v_pu_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2585_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2577_ = v___x_2574_;
v_isShared_2578_ = v_isSharedCheck_2585_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2585_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v_fvarId_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2583_; 
v_fvarId_2579_ = lean_ctor_get(v_a_2575_, 0);
lean_inc(v_fvarId_2579_);
v___x_2580_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2580_, 0, v_fvarId_2579_);
v___x_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2581_, 0, v_a_2575_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2581_);
v___x_2583_ = v___x_2577_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
v_a_2586_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2574_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2574_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased___boxed(lean_object* v_pu_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_){
_start:
{
uint8_t v_pu_boxed_2600_; lean_object* v_res_2601_; 
v_pu_boxed_2600_ = lean_unbox(v_pu_2594_);
v_res_2601_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_boxed_2600_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_a_2596_);
lean_dec_ref(v_a_2595_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t v_pu_2602_, lean_object* v_p_2603_, lean_object* v_type_2604_, lean_object* v_a_2605_){
_start:
{
lean_object* v_fvarId_2607_; lean_object* v_binderName_2608_; lean_object* v_type_2609_; uint8_t v_borrow_2610_; size_t v___x_2611_; size_t v___x_2612_; uint8_t v___x_2613_; 
v_fvarId_2607_ = lean_ctor_get(v_p_2603_, 0);
v_binderName_2608_ = lean_ctor_get(v_p_2603_, 1);
v_type_2609_ = lean_ctor_get(v_p_2603_, 2);
v_borrow_2610_ = lean_ctor_get_uint8(v_p_2603_, sizeof(void*)*3);
v___x_2611_ = lean_ptr_addr(v_type_2604_);
v___x_2612_ = lean_ptr_addr(v_type_2609_);
v___x_2613_ = lean_usize_dec_eq(v___x_2611_, v___x_2612_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2633_; 
lean_inc(v_binderName_2608_);
lean_inc(v_fvarId_2607_);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_p_2603_);
if (v_isSharedCheck_2633_ == 0)
{
lean_object* v_unused_2634_; lean_object* v_unused_2635_; lean_object* v_unused_2636_; 
v_unused_2634_ = lean_ctor_get(v_p_2603_, 2);
lean_dec(v_unused_2634_);
v_unused_2635_ = lean_ctor_get(v_p_2603_, 1);
lean_dec(v_unused_2635_);
v_unused_2636_ = lean_ctor_get(v_p_2603_, 0);
lean_dec(v_unused_2636_);
v___x_2615_ = v_p_2603_;
v_isShared_2616_ = v_isSharedCheck_2633_;
goto v_resetjp_2614_;
}
else
{
lean_dec(v_p_2603_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2633_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2617_; lean_object* v_lctx_2618_; lean_object* v_nextIdx_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2632_; 
v___x_2617_ = lean_st_ref_take(v_a_2605_);
v_lctx_2618_ = lean_ctor_get(v___x_2617_, 0);
v_nextIdx_2619_ = lean_ctor_get(v___x_2617_, 1);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2621_ = v___x_2617_;
v_isShared_2622_ = v_isSharedCheck_2632_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_nextIdx_2619_);
lean_inc(v_lctx_2618_);
lean_dec(v___x_2617_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2632_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v_p_2624_; 
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 2, v_type_2604_);
v_p_2624_ = v___x_2615_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_fvarId_2607_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v_binderName_2608_);
lean_ctor_set(v_reuseFailAlloc_2631_, 2, v_type_2604_);
lean_ctor_set_uint8(v_reuseFailAlloc_2631_, sizeof(void*)*3, v_borrow_2610_);
v_p_2624_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
lean_object* v___x_2625_; lean_object* v___x_2627_; 
lean_inc_ref(v_p_2624_);
v___x_2625_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2602_, v_lctx_2618_, v_p_2624_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2625_);
v___x_2627_ = v___x_2621_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2625_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_nextIdx_2619_);
v___x_2627_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2628_ = lean_st_ref_set(v_a_2605_, v___x_2627_);
v___x_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2629_, 0, v_p_2624_);
return v___x_2629_;
}
}
}
}
}
else
{
lean_object* v___x_2637_; 
lean_dec_ref(v_type_2604_);
v___x_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2637_, 0, v_p_2603_);
return v___x_2637_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg___boxed(lean_object* v_pu_2638_, lean_object* v_p_2639_, lean_object* v_type_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
uint8_t v_pu_boxed_2643_; lean_object* v_res_2644_; 
v_pu_boxed_2643_ = lean_unbox(v_pu_2638_);
v_res_2644_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_boxed_2643_, v_p_2639_, v_type_2640_, v_a_2641_);
lean_dec(v_a_2641_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(uint8_t v_pu_2645_, lean_object* v_p_2646_, lean_object* v_type_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_){
_start:
{
lean_object* v___x_2653_; 
v___x_2653_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_2645_, v_p_2646_, v_type_2647_, v_a_2649_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(lean_object* v_pu_2654_, lean_object* v_p_2655_, lean_object* v_type_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
uint8_t v_pu_boxed_2662_; lean_object* v_res_2663_; 
v_pu_boxed_2662_ = lean_unbox(v_pu_2654_);
v_res_2663_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(v_pu_boxed_2662_, v_p_2655_, v_type_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t v_pu_2664_, lean_object* v_p_2665_, uint8_t v_borrow_2666_, lean_object* v_a_2667_){
_start:
{
lean_object* v_fvarId_2669_; lean_object* v_binderName_2670_; lean_object* v_type_2671_; uint8_t v_borrow_2672_; 
v_fvarId_2669_ = lean_ctor_get(v_p_2665_, 0);
v_binderName_2670_ = lean_ctor_get(v_p_2665_, 1);
v_type_2671_ = lean_ctor_get(v_p_2665_, 2);
v_borrow_2672_ = lean_ctor_get_uint8(v_p_2665_, sizeof(void*)*3);
if (v_borrow_2666_ == 0)
{
if (v_borrow_2672_ == 0)
{
lean_object* v___x_2688_; 
v___x_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2688_, 0, v_p_2665_);
return v___x_2688_;
}
else
{
lean_inc_ref(v_type_2671_);
lean_inc(v_binderName_2670_);
lean_inc(v_fvarId_2669_);
lean_dec_ref(v_p_2665_);
goto v___jp_2673_;
}
}
else
{
if (v_borrow_2672_ == 0)
{
lean_inc_ref(v_type_2671_);
lean_inc(v_binderName_2670_);
lean_inc(v_fvarId_2669_);
lean_dec_ref(v_p_2665_);
goto v___jp_2673_;
}
else
{
lean_object* v___x_2689_; 
v___x_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2689_, 0, v_p_2665_);
return v___x_2689_;
}
}
v___jp_2673_:
{
lean_object* v___x_2674_; lean_object* v_lctx_2675_; lean_object* v_nextIdx_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2687_; 
v___x_2674_ = lean_st_ref_take(v_a_2667_);
v_lctx_2675_ = lean_ctor_get(v___x_2674_, 0);
v_nextIdx_2676_ = lean_ctor_get(v___x_2674_, 1);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2678_ = v___x_2674_;
v_isShared_2679_ = v_isSharedCheck_2687_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_nextIdx_2676_);
lean_inc(v_lctx_2675_);
lean_dec(v___x_2674_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2687_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v_p_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; 
v_p_2680_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_p_2680_, 0, v_fvarId_2669_);
lean_ctor_set(v_p_2680_, 1, v_binderName_2670_);
lean_ctor_set(v_p_2680_, 2, v_type_2671_);
lean_ctor_set_uint8(v_p_2680_, sizeof(void*)*3, v_borrow_2666_);
lean_inc_ref(v_p_2680_);
v___x_2681_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2664_, v_lctx_2675_, v_p_2680_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2681_);
v___x_2683_ = v___x_2678_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v_nextIdx_2676_);
v___x_2683_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2684_ = lean_st_ref_set(v_a_2667_, v___x_2683_);
v___x_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2685_, 0, v_p_2680_);
return v___x_2685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg___boxed(lean_object* v_pu_2690_, lean_object* v_p_2691_, lean_object* v_borrow_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_){
_start:
{
uint8_t v_pu_boxed_2695_; uint8_t v_borrow_boxed_2696_; lean_object* v_res_2697_; 
v_pu_boxed_2695_ = lean_unbox(v_pu_2690_);
v_borrow_boxed_2696_ = lean_unbox(v_borrow_2692_);
v_res_2697_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_boxed_2695_, v_p_2691_, v_borrow_boxed_2696_, v_a_2693_);
lean_dec(v_a_2693_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(uint8_t v_pu_2698_, lean_object* v_p_2699_, uint8_t v_borrow_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v___x_2706_; 
v___x_2706_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_2698_, v_p_2699_, v_borrow_2700_, v_a_2702_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___boxed(lean_object* v_pu_2707_, lean_object* v_p_2708_, lean_object* v_borrow_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
uint8_t v_pu_boxed_2715_; uint8_t v_borrow_boxed_2716_; lean_object* v_res_2717_; 
v_pu_boxed_2715_ = lean_unbox(v_pu_2707_);
v_borrow_boxed_2716_ = lean_unbox(v_borrow_2709_);
v_res_2717_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(v_pu_boxed_2715_, v_p_2708_, v_borrow_boxed_2716_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t v_pu_2718_, lean_object* v_decl_2719_, lean_object* v_type_2720_, lean_object* v_value_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v_fvarId_2724_; lean_object* v_binderName_2725_; lean_object* v_type_2726_; lean_object* v_value_2727_; uint8_t v___y_2729_; size_t v___x_2755_; size_t v___x_2756_; uint8_t v___x_2757_; 
v_fvarId_2724_ = lean_ctor_get(v_decl_2719_, 0);
v_binderName_2725_ = lean_ctor_get(v_decl_2719_, 1);
v_type_2726_ = lean_ctor_get(v_decl_2719_, 2);
v_value_2727_ = lean_ctor_get(v_decl_2719_, 3);
v___x_2755_ = lean_ptr_addr(v_type_2720_);
v___x_2756_ = lean_ptr_addr(v_type_2726_);
v___x_2757_ = lean_usize_dec_eq(v___x_2755_, v___x_2756_);
if (v___x_2757_ == 0)
{
v___y_2729_ = v___x_2757_;
goto v___jp_2728_;
}
else
{
size_t v___x_2758_; size_t v___x_2759_; uint8_t v___x_2760_; 
v___x_2758_ = lean_ptr_addr(v_value_2721_);
v___x_2759_ = lean_ptr_addr(v_value_2727_);
v___x_2760_ = lean_usize_dec_eq(v___x_2758_, v___x_2759_);
v___y_2729_ = v___x_2760_;
goto v___jp_2728_;
}
v___jp_2728_:
{
if (v___y_2729_ == 0)
{
lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2749_; 
lean_inc(v_binderName_2725_);
lean_inc(v_fvarId_2724_);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_decl_2719_);
if (v_isSharedCheck_2749_ == 0)
{
lean_object* v_unused_2750_; lean_object* v_unused_2751_; lean_object* v_unused_2752_; lean_object* v_unused_2753_; 
v_unused_2750_ = lean_ctor_get(v_decl_2719_, 3);
lean_dec(v_unused_2750_);
v_unused_2751_ = lean_ctor_get(v_decl_2719_, 2);
lean_dec(v_unused_2751_);
v_unused_2752_ = lean_ctor_get(v_decl_2719_, 1);
lean_dec(v_unused_2752_);
v_unused_2753_ = lean_ctor_get(v_decl_2719_, 0);
lean_dec(v_unused_2753_);
v___x_2731_ = v_decl_2719_;
v_isShared_2732_ = v_isSharedCheck_2749_;
goto v_resetjp_2730_;
}
else
{
lean_dec(v_decl_2719_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2749_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2733_; lean_object* v_lctx_2734_; lean_object* v_nextIdx_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2748_; 
v___x_2733_ = lean_st_ref_take(v_a_2722_);
v_lctx_2734_ = lean_ctor_get(v___x_2733_, 0);
v_nextIdx_2735_ = lean_ctor_get(v___x_2733_, 1);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2737_ = v___x_2733_;
v_isShared_2738_ = v_isSharedCheck_2748_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_nextIdx_2735_);
lean_inc(v_lctx_2734_);
lean_dec(v___x_2733_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2748_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v_decl_2740_; 
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 3, v_value_2721_);
lean_ctor_set(v___x_2731_, 2, v_type_2720_);
v_decl_2740_ = v___x_2731_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_fvarId_2724_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v_binderName_2725_);
lean_ctor_set(v_reuseFailAlloc_2747_, 2, v_type_2720_);
lean_ctor_set(v_reuseFailAlloc_2747_, 3, v_value_2721_);
v_decl_2740_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
lean_object* v___x_2741_; lean_object* v___x_2743_; 
lean_inc_ref(v_decl_2740_);
v___x_2741_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2718_, v_lctx_2734_, v_decl_2740_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2741_);
v___x_2743_ = v___x_2737_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2741_);
lean_ctor_set(v_reuseFailAlloc_2746_, 1, v_nextIdx_2735_);
v___x_2743_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2744_ = lean_st_ref_set(v_a_2722_, v___x_2743_);
v___x_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2745_, 0, v_decl_2740_);
return v___x_2745_;
}
}
}
}
}
else
{
lean_object* v___x_2754_; 
lean_dec(v_value_2721_);
lean_dec_ref(v_type_2720_);
v___x_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2754_, 0, v_decl_2719_);
return v___x_2754_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg___boxed(lean_object* v_pu_2761_, lean_object* v_decl_2762_, lean_object* v_type_2763_, lean_object* v_value_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_){
_start:
{
uint8_t v_pu_boxed_2767_; lean_object* v_res_2768_; 
v_pu_boxed_2767_ = lean_unbox(v_pu_2761_);
v_res_2768_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_boxed_2767_, v_decl_2762_, v_type_2763_, v_value_2764_, v_a_2765_);
lean_dec(v_a_2765_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(uint8_t v_pu_2769_, lean_object* v_decl_2770_, lean_object* v_type_2771_, lean_object* v_value_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2769_, v_decl_2770_, v_type_2771_, v_value_2772_, v_a_2774_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(lean_object* v_pu_2779_, lean_object* v_decl_2780_, lean_object* v_type_2781_, lean_object* v_value_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_){
_start:
{
uint8_t v_pu_boxed_2788_; lean_object* v_res_2789_; 
v_pu_boxed_2788_ = lean_unbox(v_pu_2779_);
v_res_2789_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(v_pu_boxed_2788_, v_decl_2780_, v_type_2781_, v_value_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
lean_dec(v_a_2786_);
lean_dec_ref(v_a_2785_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t v_pu_2790_, lean_object* v_decl_2791_, lean_object* v_value_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v_type_2795_; lean_object* v___x_2796_; 
v_type_2795_ = lean_ctor_get(v_decl_2791_, 2);
lean_inc_ref(v_type_2795_);
v___x_2796_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2790_, v_decl_2791_, v_type_2795_, v_value_2792_, v_a_2793_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg___boxed(lean_object* v_pu_2797_, lean_object* v_decl_2798_, lean_object* v_value_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
uint8_t v_pu_boxed_2802_; lean_object* v_res_2803_; 
v_pu_boxed_2802_ = lean_unbox(v_pu_2797_);
v_res_2803_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_boxed_2802_, v_decl_2798_, v_value_2799_, v_a_2800_);
lean_dec(v_a_2800_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(uint8_t v_pu_2804_, lean_object* v_decl_2805_, lean_object* v_value_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_2804_, v_decl_2805_, v_value_2806_, v_a_2808_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___boxed(lean_object* v_pu_2813_, lean_object* v_decl_2814_, lean_object* v_value_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_){
_start:
{
uint8_t v_pu_boxed_2821_; lean_object* v_res_2822_; 
v_pu_boxed_2821_ = lean_unbox(v_pu_2813_);
v_res_2822_ = l_Lean_Compiler_LCNF_LetDecl_updateValue(v_pu_boxed_2821_, v_decl_2814_, v_value_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_);
lean_dec(v_a_2819_);
lean_dec_ref(v_a_2818_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t v_pu_2823_, lean_object* v_decl_2824_, lean_object* v_type_2825_, lean_object* v_params_2826_, lean_object* v_value_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v_fvarId_2830_; lean_object* v_binderName_2831_; lean_object* v_params_2832_; lean_object* v_type_2833_; lean_object* v_value_2834_; uint8_t v___y_2851_; size_t v___x_2856_; size_t v___x_2857_; uint8_t v___x_2858_; 
v_fvarId_2830_ = lean_ctor_get(v_decl_2824_, 0);
v_binderName_2831_ = lean_ctor_get(v_decl_2824_, 1);
v_params_2832_ = lean_ctor_get(v_decl_2824_, 2);
v_type_2833_ = lean_ctor_get(v_decl_2824_, 3);
v_value_2834_ = lean_ctor_get(v_decl_2824_, 4);
v___x_2856_ = lean_ptr_addr(v_type_2825_);
v___x_2857_ = lean_ptr_addr(v_type_2833_);
v___x_2858_ = lean_usize_dec_eq(v___x_2856_, v___x_2857_);
if (v___x_2858_ == 0)
{
v___y_2851_ = v___x_2858_;
goto v___jp_2850_;
}
else
{
size_t v___x_2859_; size_t v___x_2860_; uint8_t v___x_2861_; 
v___x_2859_ = lean_ptr_addr(v_params_2826_);
v___x_2860_ = lean_ptr_addr(v_params_2832_);
v___x_2861_ = lean_usize_dec_eq(v___x_2859_, v___x_2860_);
v___y_2851_ = v___x_2861_;
goto v___jp_2850_;
}
v___jp_2835_:
{
lean_object* v___x_2836_; lean_object* v_lctx_2837_; lean_object* v_nextIdx_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2849_; 
v___x_2836_ = lean_st_ref_take(v_a_2828_);
v_lctx_2837_ = lean_ctor_get(v___x_2836_, 0);
v_nextIdx_2838_ = lean_ctor_get(v___x_2836_, 1);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2840_ = v___x_2836_;
v_isShared_2841_ = v_isSharedCheck_2849_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_nextIdx_2838_);
lean_inc(v_lctx_2837_);
lean_dec(v___x_2836_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2849_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v_decl_2842_; lean_object* v___x_2843_; lean_object* v___x_2845_; 
v_decl_2842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_decl_2842_, 0, v_fvarId_2830_);
lean_ctor_set(v_decl_2842_, 1, v_binderName_2831_);
lean_ctor_set(v_decl_2842_, 2, v_params_2826_);
lean_ctor_set(v_decl_2842_, 3, v_type_2825_);
lean_ctor_set(v_decl_2842_, 4, v_value_2827_);
lean_inc_ref(v_decl_2842_);
v___x_2843_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2823_, v_lctx_2837_, v_decl_2842_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2843_);
v___x_2845_ = v___x_2840_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2843_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_nextIdx_2838_);
v___x_2845_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2846_ = lean_st_ref_set(v_a_2828_, v___x_2845_);
v___x_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2847_, 0, v_decl_2842_);
return v___x_2847_;
}
}
}
v___jp_2850_:
{
if (v___y_2851_ == 0)
{
lean_inc(v_binderName_2831_);
lean_inc(v_fvarId_2830_);
lean_dec_ref(v_decl_2824_);
goto v___jp_2835_;
}
else
{
size_t v___x_2852_; size_t v___x_2853_; uint8_t v___x_2854_; 
v___x_2852_ = lean_ptr_addr(v_value_2827_);
v___x_2853_ = lean_ptr_addr(v_value_2834_);
v___x_2854_ = lean_usize_dec_eq(v___x_2852_, v___x_2853_);
if (v___x_2854_ == 0)
{
lean_inc(v_binderName_2831_);
lean_inc(v_fvarId_2830_);
lean_dec_ref(v_decl_2824_);
goto v___jp_2835_;
}
else
{
lean_object* v___x_2855_; 
lean_dec_ref(v_value_2827_);
lean_dec_ref(v_params_2826_);
lean_dec_ref(v_type_2825_);
v___x_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2855_, 0, v_decl_2824_);
return v___x_2855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg___boxed(lean_object* v_pu_2862_, lean_object* v_decl_2863_, lean_object* v_type_2864_, lean_object* v_params_2865_, lean_object* v_value_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_){
_start:
{
uint8_t v_pu_boxed_2869_; lean_object* v_res_2870_; 
v_pu_boxed_2869_ = lean_unbox(v_pu_2862_);
v_res_2870_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_boxed_2869_, v_decl_2863_, v_type_2864_, v_params_2865_, v_value_2866_, v_a_2867_);
lean_dec(v_a_2867_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(uint8_t v_pu_2871_, lean_object* v_decl_2872_, lean_object* v_type_2873_, lean_object* v_params_2874_, lean_object* v_value_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2871_, v_decl_2872_, v_type_2873_, v_params_2874_, v_value_2875_, v_a_2877_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(lean_object* v_pu_2882_, lean_object* v_decl_2883_, lean_object* v_type_2884_, lean_object* v_params_2885_, lean_object* v_value_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_){
_start:
{
uint8_t v_pu_boxed_2892_; lean_object* v_res_2893_; 
v_pu_boxed_2892_ = lean_unbox(v_pu_2882_);
v_res_2893_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(v_pu_boxed_2892_, v_decl_2883_, v_type_2884_, v_params_2885_, v_value_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_);
lean_dec(v_a_2890_);
lean_dec_ref(v_a_2889_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(uint8_t v_pu_2894_, lean_object* v_decl_2895_, lean_object* v_type_2896_, lean_object* v_value_2897_, lean_object* v_a_2898_){
_start:
{
lean_object* v_params_2900_; lean_object* v___x_2901_; 
v_params_2900_ = lean_ctor_get(v_decl_2895_, 2);
lean_inc_ref(v_params_2900_);
v___x_2901_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2894_, v_decl_2895_, v_type_2896_, v_params_2900_, v_value_2897_, v_a_2898_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg___boxed(lean_object* v_pu_2902_, lean_object* v_decl_2903_, lean_object* v_type_2904_, lean_object* v_value_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
uint8_t v_pu_boxed_2908_; lean_object* v_res_2909_; 
v_pu_boxed_2908_ = lean_unbox(v_pu_2902_);
v_res_2909_ = l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(v_pu_boxed_2908_, v_decl_2903_, v_type_2904_, v_value_2905_, v_a_2906_);
lean_dec(v_a_2906_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27(uint8_t v_pu_2910_, lean_object* v_decl_2911_, lean_object* v_type_2912_, lean_object* v_value_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v_params_2919_; lean_object* v___x_2920_; 
v_params_2919_ = lean_ctor_get(v_decl_2911_, 2);
lean_inc_ref(v_params_2919_);
v___x_2920_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2910_, v_decl_2911_, v_type_2912_, v_params_2919_, v_value_2913_, v_a_2915_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___boxed(lean_object* v_pu_2921_, lean_object* v_decl_2922_, lean_object* v_type_2923_, lean_object* v_value_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_){
_start:
{
uint8_t v_pu_boxed_2930_; lean_object* v_res_2931_; 
v_pu_boxed_2930_ = lean_unbox(v_pu_2921_);
v_res_2931_ = l_Lean_Compiler_LCNF_FunDecl_update_x27(v_pu_boxed_2930_, v_decl_2922_, v_type_2923_, v_value_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
lean_dec(v_a_2928_);
lean_dec_ref(v_a_2927_);
lean_dec(v_a_2926_);
lean_dec_ref(v_a_2925_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(uint8_t v_pu_2932_, lean_object* v_decl_2933_, lean_object* v_value_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_params_2937_; lean_object* v_type_2938_; lean_object* v___x_2939_; 
v_params_2937_ = lean_ctor_get(v_decl_2933_, 2);
lean_inc_ref(v_params_2937_);
v_type_2938_ = lean_ctor_get(v_decl_2933_, 3);
lean_inc_ref(v_type_2938_);
v___x_2939_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2932_, v_decl_2933_, v_type_2938_, v_params_2937_, v_value_2934_, v_a_2935_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg___boxed(lean_object* v_pu_2940_, lean_object* v_decl_2941_, lean_object* v_value_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
uint8_t v_pu_boxed_2945_; lean_object* v_res_2946_; 
v_pu_boxed_2945_ = lean_unbox(v_pu_2940_);
v_res_2946_ = l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(v_pu_boxed_2945_, v_decl_2941_, v_value_2942_, v_a_2943_);
lean_dec(v_a_2943_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue(uint8_t v_pu_2947_, lean_object* v_decl_2948_, lean_object* v_value_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v_params_2955_; lean_object* v_type_2956_; lean_object* v___x_2957_; 
v_params_2955_ = lean_ctor_get(v_decl_2948_, 2);
lean_inc_ref(v_params_2955_);
v_type_2956_ = lean_ctor_get(v_decl_2948_, 3);
lean_inc_ref(v_type_2956_);
v___x_2957_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2947_, v_decl_2948_, v_type_2956_, v_params_2955_, v_value_2949_, v_a_2951_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___boxed(lean_object* v_pu_2958_, lean_object* v_decl_2959_, lean_object* v_value_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
uint8_t v_pu_boxed_2966_; lean_object* v_res_2967_; 
v_pu_boxed_2966_ = lean_unbox(v_pu_2958_);
v_res_2967_ = l_Lean_Compiler_LCNF_FunDecl_updateValue(v_pu_boxed_2966_, v_decl_2959_, v_value_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_);
lean_dec(v_a_2964_);
lean_dec_ref(v_a_2963_);
lean_dec(v_a_2962_);
lean_dec_ref(v_a_2961_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0(uint8_t v_pu_2968_, lean_object* v_p_2969_, lean_object* v_inst_2970_, lean_object* v_____do__lift_2971_){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2972_ = lean_box(v_pu_2968_);
v___x_2973_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_2973_, 0, v___x_2972_);
lean_closure_set(v___x_2973_, 1, v_p_2969_);
lean_closure_set(v___x_2973_, 2, v_____do__lift_2971_);
v___x_2974_ = lean_apply_2(v_inst_2970_, lean_box(0), v___x_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed(lean_object* v_pu_2975_, lean_object* v_p_2976_, lean_object* v_inst_2977_, lean_object* v_____do__lift_2978_){
_start:
{
uint8_t v_pu_boxed_2979_; lean_object* v_res_2980_; 
v_pu_boxed_2979_ = lean_unbox(v_pu_2975_);
v_res_2980_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__0(v_pu_boxed_2979_, v_p_2976_, v_inst_2977_, v_____do__lift_2978_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1(uint8_t v_pu_2981_, uint8_t v_t_2982_, lean_object* v_type_2983_, lean_object* v_toPure_2984_, lean_object* v_____do__lift_2985_){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2981_, v_____do__lift_2985_, v_t_2982_, v_type_2983_);
v___x_2987_ = lean_apply_2(v_toPure_2984_, lean_box(0), v___x_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed(lean_object* v_pu_2988_, lean_object* v_t_2989_, lean_object* v_type_2990_, lean_object* v_toPure_2991_, lean_object* v_____do__lift_2992_){
_start:
{
uint8_t v_pu_boxed_2993_; uint8_t v_t_boxed_2994_; lean_object* v_res_2995_; 
v_pu_boxed_2993_ = lean_unbox(v_pu_2988_);
v_t_boxed_2994_ = lean_unbox(v_t_2989_);
v_res_2995_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__1(v_pu_boxed_2993_, v_t_boxed_2994_, v_type_2990_, v_toPure_2991_, v_____do__lift_2992_);
lean_dec_ref(v_____do__lift_2992_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg(uint8_t v_pu_2996_, uint8_t v_t_2997_, lean_object* v_inst_2998_, lean_object* v_inst_2999_, lean_object* v_inst_3000_, lean_object* v_p_3001_){
_start:
{
lean_object* v_toApplicative_3002_; lean_object* v_toBind_3003_; lean_object* v_type_3004_; lean_object* v_toPure_3005_; lean_object* v___x_3006_; lean_object* v___f_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___f_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v_toApplicative_3002_ = lean_ctor_get(v_inst_2999_, 0);
lean_inc_ref(v_toApplicative_3002_);
v_toBind_3003_ = lean_ctor_get(v_inst_2999_, 1);
lean_inc(v_toBind_3003_);
lean_dec_ref(v_inst_2999_);
v_type_3004_ = lean_ctor_get(v_p_3001_, 2);
lean_inc_ref(v_type_3004_);
v_toPure_3005_ = lean_ctor_get(v_toApplicative_3002_, 1);
lean_inc(v_toPure_3005_);
lean_dec_ref(v_toApplicative_3002_);
v___x_3006_ = lean_box(v_pu_2996_);
v___f_3007_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3007_, 0, v___x_3006_);
lean_closure_set(v___f_3007_, 1, v_p_3001_);
lean_closure_set(v___f_3007_, 2, v_inst_2998_);
v___x_3008_ = lean_box(v_pu_2996_);
v___x_3009_ = lean_box(v_t_2997_);
v___f_3010_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3010_, 0, v___x_3008_);
lean_closure_set(v___f_3010_, 1, v___x_3009_);
lean_closure_set(v___f_3010_, 2, v_type_3004_);
lean_closure_set(v___f_3010_, 3, v_toPure_3005_);
lean_inc(v_toBind_3003_);
v___x_3011_ = lean_apply_4(v_toBind_3003_, lean_box(0), lean_box(0), v_inst_3000_, v___f_3010_);
v___x_3012_ = lean_apply_4(v_toBind_3003_, lean_box(0), lean_box(0), v___x_3011_, v___f_3007_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___boxed(lean_object* v_pu_3013_, lean_object* v_t_3014_, lean_object* v_inst_3015_, lean_object* v_inst_3016_, lean_object* v_inst_3017_, lean_object* v_p_3018_){
_start:
{
uint8_t v_pu_boxed_3019_; uint8_t v_t_boxed_3020_; lean_object* v_res_3021_; 
v_pu_boxed_3019_ = lean_unbox(v_pu_3013_);
v_t_boxed_3020_ = lean_unbox(v_t_3014_);
v_res_3021_ = l_Lean_Compiler_LCNF_normParam___redArg(v_pu_boxed_3019_, v_t_boxed_3020_, v_inst_3015_, v_inst_3016_, v_inst_3017_, v_p_3018_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam(lean_object* v_m_3022_, uint8_t v_pu_3023_, uint8_t v_t_3024_, lean_object* v_inst_3025_, lean_object* v_inst_3026_, lean_object* v_inst_3027_, lean_object* v_p_3028_){
_start:
{
lean_object* v_toApplicative_3029_; lean_object* v_toBind_3030_; lean_object* v_type_3031_; lean_object* v_toPure_3032_; lean_object* v___x_3033_; lean_object* v___f_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___f_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v_toApplicative_3029_ = lean_ctor_get(v_inst_3026_, 0);
lean_inc_ref(v_toApplicative_3029_);
v_toBind_3030_ = lean_ctor_get(v_inst_3026_, 1);
lean_inc(v_toBind_3030_);
lean_dec_ref(v_inst_3026_);
v_type_3031_ = lean_ctor_get(v_p_3028_, 2);
lean_inc_ref(v_type_3031_);
v_toPure_3032_ = lean_ctor_get(v_toApplicative_3029_, 1);
lean_inc(v_toPure_3032_);
lean_dec_ref(v_toApplicative_3029_);
v___x_3033_ = lean_box(v_pu_3023_);
v___f_3034_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3034_, 0, v___x_3033_);
lean_closure_set(v___f_3034_, 1, v_p_3028_);
lean_closure_set(v___f_3034_, 2, v_inst_3025_);
v___x_3035_ = lean_box(v_pu_3023_);
v___x_3036_ = lean_box(v_t_3024_);
v___f_3037_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3037_, 0, v___x_3035_);
lean_closure_set(v___f_3037_, 1, v___x_3036_);
lean_closure_set(v___f_3037_, 2, v_type_3031_);
lean_closure_set(v___f_3037_, 3, v_toPure_3032_);
lean_inc(v_toBind_3030_);
v___x_3038_ = lean_apply_4(v_toBind_3030_, lean_box(0), lean_box(0), v_inst_3027_, v___f_3037_);
v___x_3039_ = lean_apply_4(v_toBind_3030_, lean_box(0), lean_box(0), v___x_3038_, v___f_3034_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___boxed(lean_object* v_m_3040_, lean_object* v_pu_3041_, lean_object* v_t_3042_, lean_object* v_inst_3043_, lean_object* v_inst_3044_, lean_object* v_inst_3045_, lean_object* v_p_3046_){
_start:
{
uint8_t v_pu_boxed_3047_; uint8_t v_t_boxed_3048_; lean_object* v_res_3049_; 
v_pu_boxed_3047_ = lean_unbox(v_pu_3041_);
v_t_boxed_3048_ = lean_unbox(v_t_3042_);
v_res_3049_ = l_Lean_Compiler_LCNF_normParam(v_m_3040_, v_pu_boxed_3047_, v_t_boxed_3048_, v_inst_3043_, v_inst_3044_, v_inst_3045_, v_p_3046_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg(uint8_t v_pu_3050_, uint8_t v_t_3051_, lean_object* v_inst_3052_, lean_object* v_inst_3053_, lean_object* v_inst_3054_, lean_object* v_ps_3055_){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3056_ = lean_box(v_pu_3050_);
v___x_3057_ = lean_box(v_t_3051_);
lean_inc_ref(v_inst_3053_);
v___x_3058_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___boxed), 7, 6);
lean_closure_set(v___x_3058_, 0, lean_box(0));
lean_closure_set(v___x_3058_, 1, v___x_3056_);
lean_closure_set(v___x_3058_, 2, v___x_3057_);
lean_closure_set(v___x_3058_, 3, v_inst_3052_);
lean_closure_set(v___x_3058_, 4, v_inst_3053_);
lean_closure_set(v___x_3058_, 5, v_inst_3054_);
v___x_3059_ = lean_unsigned_to_nat(0u);
v___x_3060_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_3053_, v___x_3058_, v___x_3059_, v_ps_3055_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg___boxed(lean_object* v_pu_3061_, lean_object* v_t_3062_, lean_object* v_inst_3063_, lean_object* v_inst_3064_, lean_object* v_inst_3065_, lean_object* v_ps_3066_){
_start:
{
uint8_t v_pu_boxed_3067_; uint8_t v_t_boxed_3068_; lean_object* v_res_3069_; 
v_pu_boxed_3067_ = lean_unbox(v_pu_3061_);
v_t_boxed_3068_ = lean_unbox(v_t_3062_);
v_res_3069_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_boxed_3067_, v_t_boxed_3068_, v_inst_3063_, v_inst_3064_, v_inst_3065_, v_ps_3066_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams(lean_object* v_m_3070_, uint8_t v_pu_3071_, uint8_t v_t_3072_, lean_object* v_inst_3073_, lean_object* v_inst_3074_, lean_object* v_inst_3075_, lean_object* v_ps_3076_){
_start:
{
lean_object* v___x_3077_; 
v___x_3077_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_3071_, v_t_3072_, v_inst_3073_, v_inst_3074_, v_inst_3075_, v_ps_3076_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___boxed(lean_object* v_m_3078_, lean_object* v_pu_3079_, lean_object* v_t_3080_, lean_object* v_inst_3081_, lean_object* v_inst_3082_, lean_object* v_inst_3083_, lean_object* v_ps_3084_){
_start:
{
uint8_t v_pu_boxed_3085_; uint8_t v_t_boxed_3086_; lean_object* v_res_3087_; 
v_pu_boxed_3085_ = lean_unbox(v_pu_3079_);
v_t_boxed_3086_ = lean_unbox(v_t_3080_);
v_res_3087_ = l_Lean_Compiler_LCNF_normParams(v_m_3078_, v_pu_boxed_3085_, v_t_boxed_3086_, v_inst_3081_, v_inst_3082_, v_inst_3083_, v_ps_3084_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(uint8_t v_pu_3088_, lean_object* v_decl_3089_, lean_object* v_____do__lift_3090_, lean_object* v_inst_3091_, lean_object* v_____do__lift_3092_){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3093_ = lean_box(v_pu_3088_);
v___x_3094_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_3094_, 0, v___x_3093_);
lean_closure_set(v___x_3094_, 1, v_decl_3089_);
lean_closure_set(v___x_3094_, 2, v_____do__lift_3090_);
lean_closure_set(v___x_3094_, 3, v_____do__lift_3092_);
v___x_3095_ = lean_apply_2(v_inst_3091_, lean_box(0), v___x_3094_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed(lean_object* v_pu_3096_, lean_object* v_decl_3097_, lean_object* v_____do__lift_3098_, lean_object* v_inst_3099_, lean_object* v_____do__lift_3100_){
_start:
{
uint8_t v_pu_boxed_3101_; lean_object* v_res_3102_; 
v_pu_boxed_3101_ = lean_unbox(v_pu_3096_);
v_res_3102_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(v_pu_boxed_3101_, v_decl_3097_, v_____do__lift_3098_, v_inst_3099_, v_____do__lift_3100_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(uint8_t v_pu_3103_, lean_object* v_value_3104_, uint8_t v_t_3105_, lean_object* v_toPure_3106_, lean_object* v_____do__lift_3107_){
_start:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3108_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3103_, v_____do__lift_3107_, v_value_3104_, v_t_3105_);
v___x_3109_ = lean_apply_2(v_toPure_3106_, lean_box(0), v___x_3108_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed(lean_object* v_pu_3110_, lean_object* v_value_3111_, lean_object* v_t_3112_, lean_object* v_toPure_3113_, lean_object* v_____do__lift_3114_){
_start:
{
uint8_t v_pu_boxed_3115_; uint8_t v_t_boxed_3116_; lean_object* v_res_3117_; 
v_pu_boxed_3115_ = lean_unbox(v_pu_3110_);
v_t_boxed_3116_ = lean_unbox(v_t_3112_);
v_res_3117_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(v_pu_boxed_3115_, v_value_3111_, v_t_boxed_3116_, v_toPure_3113_, v_____do__lift_3114_);
lean_dec_ref(v_____do__lift_3114_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(uint8_t v_pu_3118_, lean_object* v_decl_3119_, lean_object* v_inst_3120_, lean_object* v_value_3121_, uint8_t v_t_3122_, lean_object* v_toPure_3123_, lean_object* v_toBind_3124_, lean_object* v_inst_3125_, lean_object* v_____do__lift_3126_){
_start:
{
lean_object* v___x_3127_; lean_object* v___f_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___f_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3127_ = lean_box(v_pu_3118_);
v___f_3128_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3128_, 0, v___x_3127_);
lean_closure_set(v___f_3128_, 1, v_decl_3119_);
lean_closure_set(v___f_3128_, 2, v_____do__lift_3126_);
lean_closure_set(v___f_3128_, 3, v_inst_3120_);
v___x_3129_ = lean_box(v_pu_3118_);
v___x_3130_ = lean_box(v_t_3122_);
v___f_3131_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3131_, 0, v___x_3129_);
lean_closure_set(v___f_3131_, 1, v_value_3121_);
lean_closure_set(v___f_3131_, 2, v___x_3130_);
lean_closure_set(v___f_3131_, 3, v_toPure_3123_);
lean_inc(v_toBind_3124_);
v___x_3132_ = lean_apply_4(v_toBind_3124_, lean_box(0), lean_box(0), v_inst_3125_, v___f_3131_);
v___x_3133_ = lean_apply_4(v_toBind_3124_, lean_box(0), lean_box(0), v___x_3132_, v___f_3128_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed(lean_object* v_pu_3134_, lean_object* v_decl_3135_, lean_object* v_inst_3136_, lean_object* v_value_3137_, lean_object* v_t_3138_, lean_object* v_toPure_3139_, lean_object* v_toBind_3140_, lean_object* v_inst_3141_, lean_object* v_____do__lift_3142_){
_start:
{
uint8_t v_pu_boxed_3143_; uint8_t v_t_boxed_3144_; lean_object* v_res_3145_; 
v_pu_boxed_3143_ = lean_unbox(v_pu_3134_);
v_t_boxed_3144_ = lean_unbox(v_t_3138_);
v_res_3145_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(v_pu_boxed_3143_, v_decl_3135_, v_inst_3136_, v_value_3137_, v_t_boxed_3144_, v_toPure_3139_, v_toBind_3140_, v_inst_3141_, v_____do__lift_3142_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg(uint8_t v_pu_3146_, uint8_t v_t_3147_, lean_object* v_inst_3148_, lean_object* v_inst_3149_, lean_object* v_inst_3150_, lean_object* v_decl_3151_){
_start:
{
lean_object* v_toApplicative_3152_; lean_object* v_toBind_3153_; lean_object* v_type_3154_; lean_object* v_value_3155_; lean_object* v_toPure_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___f_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___f_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v_toApplicative_3152_ = lean_ctor_get(v_inst_3149_, 0);
lean_inc_ref(v_toApplicative_3152_);
v_toBind_3153_ = lean_ctor_get(v_inst_3149_, 1);
lean_inc(v_toBind_3153_);
lean_dec_ref(v_inst_3149_);
v_type_3154_ = lean_ctor_get(v_decl_3151_, 2);
lean_inc_ref(v_type_3154_);
v_value_3155_ = lean_ctor_get(v_decl_3151_, 3);
lean_inc(v_value_3155_);
v_toPure_3156_ = lean_ctor_get(v_toApplicative_3152_, 1);
lean_inc(v_toPure_3156_);
lean_dec_ref(v_toApplicative_3152_);
v___x_3157_ = lean_box(v_pu_3146_);
v___x_3158_ = lean_box(v_t_3147_);
lean_inc(v_inst_3150_);
lean_inc(v_toBind_3153_);
lean_inc(v_toPure_3156_);
v___f_3159_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_3159_, 0, v___x_3157_);
lean_closure_set(v___f_3159_, 1, v_decl_3151_);
lean_closure_set(v___f_3159_, 2, v_inst_3148_);
lean_closure_set(v___f_3159_, 3, v_value_3155_);
lean_closure_set(v___f_3159_, 4, v___x_3158_);
lean_closure_set(v___f_3159_, 5, v_toPure_3156_);
lean_closure_set(v___f_3159_, 6, v_toBind_3153_);
lean_closure_set(v___f_3159_, 7, v_inst_3150_);
v___x_3160_ = lean_box(v_pu_3146_);
v___x_3161_ = lean_box(v_t_3147_);
v___f_3162_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3162_, 0, v___x_3160_);
lean_closure_set(v___f_3162_, 1, v___x_3161_);
lean_closure_set(v___f_3162_, 2, v_type_3154_);
lean_closure_set(v___f_3162_, 3, v_toPure_3156_);
lean_inc(v_toBind_3153_);
v___x_3163_ = lean_apply_4(v_toBind_3153_, lean_box(0), lean_box(0), v_inst_3150_, v___f_3162_);
v___x_3164_ = lean_apply_4(v_toBind_3153_, lean_box(0), lean_box(0), v___x_3163_, v___f_3159_);
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___boxed(lean_object* v_pu_3165_, lean_object* v_t_3166_, lean_object* v_inst_3167_, lean_object* v_inst_3168_, lean_object* v_inst_3169_, lean_object* v_decl_3170_){
_start:
{
uint8_t v_pu_boxed_3171_; uint8_t v_t_boxed_3172_; lean_object* v_res_3173_; 
v_pu_boxed_3171_ = lean_unbox(v_pu_3165_);
v_t_boxed_3172_ = lean_unbox(v_t_3166_);
v_res_3173_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_boxed_3171_, v_t_boxed_3172_, v_inst_3167_, v_inst_3168_, v_inst_3169_, v_decl_3170_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl(lean_object* v_m_3174_, uint8_t v_pu_3175_, uint8_t v_t_3176_, lean_object* v_inst_3177_, lean_object* v_inst_3178_, lean_object* v_inst_3179_, lean_object* v_decl_3180_){
_start:
{
lean_object* v___x_3181_; 
v___x_3181_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_3175_, v_t_3176_, v_inst_3177_, v_inst_3178_, v_inst_3179_, v_decl_3180_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___boxed(lean_object* v_m_3182_, lean_object* v_pu_3183_, lean_object* v_t_3184_, lean_object* v_inst_3185_, lean_object* v_inst_3186_, lean_object* v_inst_3187_, lean_object* v_decl_3188_){
_start:
{
uint8_t v_pu_boxed_3189_; uint8_t v_t_boxed_3190_; lean_object* v_res_3191_; 
v_pu_boxed_3189_ = lean_unbox(v_pu_3183_);
v_t_boxed_3190_ = lean_unbox(v_t_3184_);
v_res_3191_ = l_Lean_Compiler_LCNF_normLetDecl(v_m_3182_, v_pu_boxed_3189_, v_t_boxed_3190_, v_inst_3185_, v_inst_3186_, v_inst_3187_, v_decl_3188_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(uint8_t v_pu_3192_, uint8_t v_t_3193_){
_start:
{
lean_object* v___x_3194_; lean_object* v_toApplicative_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3253_; 
v___x_3194_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3253_ == 0)
{
lean_object* v_unused_3254_; 
v_unused_3254_ = lean_ctor_get(v___x_3194_, 1);
lean_dec(v_unused_3254_);
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3253_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_toApplicative_3195_);
lean_dec(v___x_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3253_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v_toFunctor_3199_; lean_object* v_toSeq_3200_; lean_object* v_toSeqLeft_3201_; lean_object* v_toSeqRight_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3251_; 
v_toFunctor_3199_ = lean_ctor_get(v_toApplicative_3195_, 0);
v_toSeq_3200_ = lean_ctor_get(v_toApplicative_3195_, 2);
v_toSeqLeft_3201_ = lean_ctor_get(v_toApplicative_3195_, 3);
v_toSeqRight_3202_ = lean_ctor_get(v_toApplicative_3195_, 4);
v_isSharedCheck_3251_ = !lean_is_exclusive(v_toApplicative_3195_);
if (v_isSharedCheck_3251_ == 0)
{
lean_object* v_unused_3252_; 
v_unused_3252_ = lean_ctor_get(v_toApplicative_3195_, 1);
lean_dec(v_unused_3252_);
v___x_3204_ = v_toApplicative_3195_;
v_isShared_3205_ = v_isSharedCheck_3251_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_toSeqRight_3202_);
lean_inc(v_toSeqLeft_3201_);
lean_inc(v_toSeq_3200_);
lean_inc(v_toFunctor_3199_);
lean_dec(v_toApplicative_3195_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3251_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___f_3206_; lean_object* v___f_3207_; lean_object* v___f_3208_; lean_object* v___f_3209_; lean_object* v___x_3210_; lean_object* v___f_3211_; lean_object* v___f_3212_; lean_object* v___f_3213_; lean_object* v___x_3215_; 
v___f_3206_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_3207_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref(v_toFunctor_3199_);
v___f_3208_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3208_, 0, v_toFunctor_3199_);
v___f_3209_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3209_, 0, v_toFunctor_3199_);
v___x_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___f_3208_);
lean_ctor_set(v___x_3210_, 1, v___f_3209_);
v___f_3211_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3211_, 0, v_toSeqRight_3202_);
v___f_3212_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3212_, 0, v_toSeqLeft_3201_);
v___f_3213_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3213_, 0, v_toSeq_3200_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 4, v___f_3211_);
lean_ctor_set(v___x_3204_, 3, v___f_3212_);
lean_ctor_set(v___x_3204_, 2, v___f_3213_);
lean_ctor_set(v___x_3204_, 1, v___f_3206_);
lean_ctor_set(v___x_3204_, 0, v___x_3210_);
v___x_3215_ = v___x_3204_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v___x_3210_);
lean_ctor_set(v_reuseFailAlloc_3250_, 1, v___f_3206_);
lean_ctor_set(v_reuseFailAlloc_3250_, 2, v___f_3213_);
lean_ctor_set(v_reuseFailAlloc_3250_, 3, v___f_3212_);
lean_ctor_set(v_reuseFailAlloc_3250_, 4, v___f_3211_);
v___x_3215_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
lean_object* v___x_3217_; 
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 1, v___f_3207_);
lean_ctor_set(v___x_3197_, 0, v___x_3215_);
v___x_3217_ = v___x_3197_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3215_);
lean_ctor_set(v_reuseFailAlloc_3249_, 1, v___f_3207_);
v___x_3217_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
lean_object* v___x_3218_; lean_object* v_toApplicative_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3247_; 
v___x_3218_ = l_StateRefT_x27_instMonad___redArg(v___x_3217_);
v_toApplicative_3219_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3247_ == 0)
{
lean_object* v_unused_3248_; 
v_unused_3248_ = lean_ctor_get(v___x_3218_, 1);
lean_dec(v_unused_3248_);
v___x_3221_ = v___x_3218_;
v_isShared_3222_ = v_isSharedCheck_3247_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_toApplicative_3219_);
lean_dec(v___x_3218_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3247_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v_toFunctor_3223_; lean_object* v_toSeq_3224_; lean_object* v_toSeqLeft_3225_; lean_object* v_toSeqRight_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3245_; 
v_toFunctor_3223_ = lean_ctor_get(v_toApplicative_3219_, 0);
v_toSeq_3224_ = lean_ctor_get(v_toApplicative_3219_, 2);
v_toSeqLeft_3225_ = lean_ctor_get(v_toApplicative_3219_, 3);
v_toSeqRight_3226_ = lean_ctor_get(v_toApplicative_3219_, 4);
v_isSharedCheck_3245_ = !lean_is_exclusive(v_toApplicative_3219_);
if (v_isSharedCheck_3245_ == 0)
{
lean_object* v_unused_3246_; 
v_unused_3246_ = lean_ctor_get(v_toApplicative_3219_, 1);
lean_dec(v_unused_3246_);
v___x_3228_ = v_toApplicative_3219_;
v_isShared_3229_ = v_isSharedCheck_3245_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_toSeqRight_3226_);
lean_inc(v_toSeqLeft_3225_);
lean_inc(v_toSeq_3224_);
lean_inc(v_toFunctor_3223_);
lean_dec(v_toApplicative_3219_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3245_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___f_3230_; lean_object* v___f_3231_; lean_object* v___f_3232_; lean_object* v___f_3233_; lean_object* v___x_3234_; lean_object* v___f_3235_; lean_object* v___f_3236_; lean_object* v___f_3237_; lean_object* v___x_3239_; 
v___f_3230_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_3231_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_3223_);
v___f_3232_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3232_, 0, v_toFunctor_3223_);
v___f_3233_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3233_, 0, v_toFunctor_3223_);
v___x_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___f_3232_);
lean_ctor_set(v___x_3234_, 1, v___f_3233_);
v___f_3235_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3235_, 0, v_toSeqRight_3226_);
v___f_3236_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3236_, 0, v_toSeqLeft_3225_);
v___f_3237_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3237_, 0, v_toSeq_3224_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 4, v___f_3235_);
lean_ctor_set(v___x_3228_, 3, v___f_3236_);
lean_ctor_set(v___x_3228_, 2, v___f_3237_);
lean_ctor_set(v___x_3228_, 1, v___f_3230_);
lean_ctor_set(v___x_3228_, 0, v___x_3234_);
v___x_3239_ = v___x_3228_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v___f_3230_);
lean_ctor_set(v_reuseFailAlloc_3244_, 2, v___f_3237_);
lean_ctor_set(v_reuseFailAlloc_3244_, 3, v___f_3236_);
lean_ctor_set(v_reuseFailAlloc_3244_, 4, v___f_3235_);
v___x_3239_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
lean_object* v___x_3241_; 
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 1, v___f_3231_);
lean_ctor_set(v___x_3221_, 0, v___x_3239_);
v___x_3241_ = v___x_3221_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3239_);
lean_ctor_set(v_reuseFailAlloc_3243_, 1, v___f_3231_);
v___x_3241_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
lean_object* v___x_3242_; 
v___x_3242_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_3242_, 0, lean_box(0));
lean_closure_set(v___x_3242_, 1, lean_box(0));
lean_closure_set(v___x_3242_, 2, v___x_3241_);
return v___x_3242_;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___boxed(lean_object* v_pu_3255_, lean_object* v_t_3256_){
_start:
{
uint8_t v_pu_boxed_3257_; uint8_t v_t_boxed_3258_; lean_object* v_res_3259_; 
v_pu_boxed_3257_ = lean_unbox(v_pu_3255_);
v_t_boxed_3258_ = lean_unbox(v_t_3256_);
v_res_3259_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(v_pu_boxed_3257_, v_t_boxed_3258_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg(uint8_t v_pu_3260_, lean_object* v_inst_3261_, lean_object* v_result_3262_, lean_object* v_x_3263_){
_start:
{
if (lean_obj_tag(v_result_3262_) == 0)
{
lean_object* v_fvarId_3264_; lean_object* v___x_3265_; 
lean_dec(v_inst_3261_);
v_fvarId_3264_ = lean_ctor_get(v_result_3262_, 0);
lean_inc(v_fvarId_3264_);
lean_dec_ref(v_result_3262_);
v___x_3265_ = lean_apply_1(v_x_3263_, v_fvarId_3264_);
return v___x_3265_;
}
else
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
lean_dec(v_x_3263_);
v___x_3266_ = lean_box(v_pu_3260_);
v___x_3267_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3267_, 0, v___x_3266_);
v___x_3268_ = lean_apply_2(v_inst_3261_, lean_box(0), v___x_3267_);
return v___x_3268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg___boxed(lean_object* v_pu_3269_, lean_object* v_inst_3270_, lean_object* v_result_3271_, lean_object* v_x_3272_){
_start:
{
uint8_t v_pu_boxed_3273_; lean_object* v_res_3274_; 
v_pu_boxed_3273_ = lean_unbox(v_pu_3269_);
v_res_3274_ = l_Lean_Compiler_LCNF_withNormFVarResult___redArg(v_pu_boxed_3273_, v_inst_3270_, v_result_3271_, v_x_3272_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult(lean_object* v_m_3275_, uint8_t v_pu_3276_, lean_object* v_inst_3277_, lean_object* v_inst_3278_, lean_object* v_result_3279_, lean_object* v_x_3280_){
_start:
{
if (lean_obj_tag(v_result_3279_) == 0)
{
lean_object* v_fvarId_3281_; lean_object* v___x_3282_; 
lean_dec(v_inst_3277_);
v_fvarId_3281_ = lean_ctor_get(v_result_3279_, 0);
lean_inc(v_fvarId_3281_);
lean_dec_ref(v_result_3279_);
v___x_3282_ = lean_apply_1(v_x_3280_, v_fvarId_3281_);
return v___x_3282_;
}
else
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
lean_dec(v_x_3280_);
v___x_3283_ = lean_box(v_pu_3276_);
v___x_3284_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3284_, 0, v___x_3283_);
v___x_3285_ = lean_apply_2(v_inst_3277_, lean_box(0), v___x_3284_);
return v___x_3285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___boxed(lean_object* v_m_3286_, lean_object* v_pu_3287_, lean_object* v_inst_3288_, lean_object* v_inst_3289_, lean_object* v_result_3290_, lean_object* v_x_3291_){
_start:
{
uint8_t v_pu_boxed_3292_; lean_object* v_res_3293_; 
v_pu_boxed_3292_ = lean_unbox(v_pu_3287_);
v_res_3293_ = l_Lean_Compiler_LCNF_withNormFVarResult(v_m_3286_, v_pu_boxed_3292_, v_inst_3288_, v_inst_3289_, v_result_3290_, v_x_3291_);
lean_dec_ref(v_inst_3289_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(uint8_t v_pu_3294_, uint8_t v_t_3295_, lean_object* v_args_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_3294_, v___y_3297_, v_args_3296_, v_t_3295_);
v___x_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg___boxed(lean_object* v_pu_3301_, lean_object* v_t_3302_, lean_object* v_args_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
uint8_t v_pu_boxed_3306_; uint8_t v_t_boxed_3307_; lean_object* v_res_3308_; 
v_pu_boxed_3306_ = lean_unbox(v_pu_3301_);
v_t_boxed_3307_ = lean_unbox(v_t_3302_);
v_res_3308_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_boxed_3306_, v_t_boxed_3307_, v_args_3303_, v___y_3304_);
lean_dec_ref(v___y_3304_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(uint8_t v_pu_3309_, uint8_t v_t_3310_, lean_object* v_i_3311_, lean_object* v_as_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v___x_3316_; uint8_t v___x_3317_; 
v___x_3316_ = lean_array_get_size(v_as_3312_);
v___x_3317_ = lean_nat_dec_lt(v_i_3311_, v___x_3316_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; 
lean_dec(v_i_3311_);
v___x_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3318_, 0, v_as_3312_);
return v___x_3318_;
}
else
{
lean_object* v_a_3319_; lean_object* v_type_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v_a_3319_ = lean_array_fget_borrowed(v_as_3312_, v_i_3311_);
v_type_3320_ = lean_ctor_get(v_a_3319_, 2);
lean_inc_ref(v_type_3320_);
v___x_3321_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3309_, v___y_3313_, v_t_3310_, v_type_3320_);
lean_inc(v_a_3319_);
v___x_3322_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_3309_, v_a_3319_, v___x_3321_, v___y_3314_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; size_t v___x_3324_; size_t v___x_3325_; uint8_t v___x_3326_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3323_);
lean_dec_ref(v___x_3322_);
v___x_3324_ = lean_ptr_addr(v_a_3319_);
v___x_3325_ = lean_ptr_addr(v_a_3323_);
v___x_3326_ = lean_usize_dec_eq(v___x_3324_, v___x_3325_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3327_ = lean_unsigned_to_nat(1u);
v___x_3328_ = lean_nat_add(v_i_3311_, v___x_3327_);
v___x_3329_ = lean_array_fset(v_as_3312_, v_i_3311_, v_a_3323_);
lean_dec(v_i_3311_);
v_i_3311_ = v___x_3328_;
v_as_3312_ = v___x_3329_;
goto _start;
}
else
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
lean_dec(v_a_3323_);
v___x_3331_ = lean_unsigned_to_nat(1u);
v___x_3332_ = lean_nat_add(v_i_3311_, v___x_3331_);
lean_dec(v_i_3311_);
v_i_3311_ = v___x_3332_;
goto _start;
}
}
else
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
lean_dec_ref(v_as_3312_);
lean_dec(v_i_3311_);
v_a_3334_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___x_3322_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3322_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg___boxed(lean_object* v_pu_3342_, lean_object* v_t_3343_, lean_object* v_i_3344_, lean_object* v_as_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
uint8_t v_pu_boxed_3349_; uint8_t v_t_boxed_3350_; lean_object* v_res_3351_; 
v_pu_boxed_3349_ = lean_unbox(v_pu_3342_);
v_t_boxed_3350_ = lean_unbox(v_t_3343_);
v_res_3351_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_boxed_3349_, v_t_boxed_3350_, v_i_3344_, v_as_3345_, v___y_3346_, v___y_3347_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(uint8_t v_pu_3352_, uint8_t v_t_3353_, lean_object* v_ps_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3361_ = lean_unsigned_to_nat(0u);
v___x_3362_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_3352_, v_t_3353_, v___x_3361_, v_ps_3354_, v___y_3355_, v___y_3357_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg___boxed(lean_object* v_pu_3363_, lean_object* v_t_3364_, lean_object* v_ps_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
uint8_t v_pu_boxed_3372_; uint8_t v_t_boxed_3373_; lean_object* v_res_3374_; 
v_pu_boxed_3372_ = lean_unbox(v_pu_3363_);
v_t_boxed_3373_ = lean_unbox(v_t_3364_);
v_res_3374_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_boxed_3372_, v_t_boxed_3373_, v_ps_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec_ref(v___y_3366_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(uint8_t v_pu_3375_, uint8_t v_t_3376_, lean_object* v_decl_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v_type_3381_; lean_object* v_value_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v_type_3381_ = lean_ctor_get(v_decl_3377_, 2);
v_value_3382_ = lean_ctor_get(v_decl_3377_, 3);
lean_inc_ref(v_type_3381_);
v___x_3383_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3375_, v___y_3378_, v_t_3376_, v_type_3381_);
lean_inc(v_value_3382_);
v___x_3384_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3375_, v___y_3378_, v_value_3382_, v_t_3376_);
v___x_3385_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_3375_, v_decl_3377_, v___x_3383_, v___x_3384_, v___y_3379_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg___boxed(lean_object* v_pu_3386_, lean_object* v_t_3387_, lean_object* v_decl_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
uint8_t v_pu_boxed_3392_; uint8_t v_t_boxed_3393_; lean_object* v_res_3394_; 
v_pu_boxed_3392_ = lean_unbox(v_pu_3386_);
v_t_boxed_3393_ = lean_unbox(v_t_3387_);
v_res_3394_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_boxed_3392_, v_t_boxed_3393_, v_decl_3388_, v___y_3389_, v___y_3390_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(uint8_t v_pu_3395_, uint8_t v_t_3396_, lean_object* v_i_3397_, lean_object* v_as_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v___x_3405_; uint8_t v___x_3406_; 
v___x_3405_ = lean_array_get_size(v_as_3398_);
v___x_3406_ = lean_nat_dec_lt(v_i_3397_, v___x_3405_);
if (v___x_3406_ == 0)
{
lean_object* v___x_3407_; 
lean_dec(v_i_3397_);
v___x_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3407_, 0, v_as_3398_);
return v___x_3407_;
}
else
{
lean_object* v_a_3408_; lean_object* v_a_3410_; 
v_a_3408_ = lean_array_fget_borrowed(v_as_3398_, v_i_3397_);
switch(lean_obj_tag(v_a_3408_))
{
case 0:
{
lean_object* v_params_3421_; lean_object* v_code_3422_; lean_object* v___x_3423_; 
v_params_3421_ = lean_ctor_get(v_a_3408_, 1);
v_code_3422_ = lean_ctor_get(v_a_3408_, 2);
lean_inc_ref(v_params_3421_);
v___x_3423_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_3395_, v_t_3396_, v_params_3421_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; lean_object* v___x_3425_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
lean_dec_ref(v___x_3423_);
lean_inc_ref(v_code_3422_);
v___x_3425_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3395_, v_t_3396_, v_code_3422_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; lean_object* v___x_3427_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref(v___x_3425_);
lean_inc_ref(v_a_3408_);
v___x_3427_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_3395_, v_a_3408_, v_a_3424_, v_a_3426_);
v_a_3410_ = v___x_3427_;
goto v___jp_3409_;
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_dec(v_a_3424_);
lean_dec_ref(v_as_3398_);
lean_dec(v_i_3397_);
v_a_3428_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3425_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3425_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec_ref(v_as_3398_);
lean_dec(v_i_3397_);
v_a_3436_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3423_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3423_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
case 1:
{
lean_object* v_code_3444_; lean_object* v___x_3445_; 
v_code_3444_ = lean_ctor_get(v_a_3408_, 1);
lean_inc_ref(v_code_3444_);
v___x_3445_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3395_, v_t_3396_, v_code_3444_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v___x_3447_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3446_);
lean_dec_ref(v___x_3445_);
lean_inc_ref(v_a_3408_);
v___x_3447_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3408_, v_a_3446_);
v_a_3410_ = v___x_3447_;
goto v___jp_3409_;
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_dec_ref(v_as_3398_);
lean_dec(v_i_3397_);
v_a_3448_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3445_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3445_);
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
default: 
{
lean_object* v_code_3456_; lean_object* v___x_3457_; 
v_code_3456_ = lean_ctor_get(v_a_3408_, 0);
lean_inc_ref(v_code_3456_);
v___x_3457_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3395_, v_t_3396_, v_code_3456_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3459_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref(v___x_3457_);
lean_inc_ref(v_a_3408_);
v___x_3459_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3408_, v_a_3458_);
v_a_3410_ = v___x_3459_;
goto v___jp_3409_;
}
else
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
lean_dec_ref(v_as_3398_);
lean_dec(v_i_3397_);
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
}
v___jp_3409_:
{
size_t v___x_3411_; size_t v___x_3412_; uint8_t v___x_3413_; 
v___x_3411_ = lean_ptr_addr(v_a_3408_);
v___x_3412_ = lean_ptr_addr(v_a_3410_);
v___x_3413_ = lean_usize_dec_eq(v___x_3411_, v___x_3412_);
if (v___x_3413_ == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3414_ = lean_unsigned_to_nat(1u);
v___x_3415_ = lean_nat_add(v_i_3397_, v___x_3414_);
v___x_3416_ = lean_array_fset(v_as_3398_, v_i_3397_, v_a_3410_);
lean_dec(v_i_3397_);
v_i_3397_ = v___x_3415_;
v_as_3398_ = v___x_3416_;
goto _start;
}
else
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
lean_dec_ref(v_a_3410_);
v___x_3418_ = lean_unsigned_to_nat(1u);
v___x_3419_ = lean_nat_add(v_i_3397_, v___x_3418_);
lean_dec(v_i_3397_);
v_i_3397_ = v___x_3419_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp(uint8_t v_pu_3468_, uint8_t v_t_3469_, lean_object* v_code_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_){
_start:
{
switch(lean_obj_tag(v_code_3470_))
{
case 0:
{
lean_object* v_decl_3477_; lean_object* v_k_3478_; lean_object* v___x_3479_; 
v_decl_3477_ = lean_ctor_get(v_code_3470_, 0);
v_k_3478_ = lean_ctor_get(v_code_3470_, 1);
lean_inc_ref(v_decl_3477_);
v___x_3479_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_3468_, v_t_3469_, v_decl_3477_, v_a_3471_, v_a_3473_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___x_3481_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
lean_dec_ref(v___x_3479_);
lean_inc_ref(v_k_3478_);
v___x_3481_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3468_, v_t_3469_, v_k_3478_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3509_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3484_ = v___x_3481_;
v_isShared_3485_ = v_isSharedCheck_3509_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3481_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3509_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
uint8_t v___y_3487_; size_t v___x_3503_; size_t v___x_3504_; uint8_t v___x_3505_; 
v___x_3503_ = lean_ptr_addr(v_k_3478_);
v___x_3504_ = lean_ptr_addr(v_a_3482_);
v___x_3505_ = lean_usize_dec_eq(v___x_3503_, v___x_3504_);
if (v___x_3505_ == 0)
{
v___y_3487_ = v___x_3505_;
goto v___jp_3486_;
}
else
{
size_t v___x_3506_; size_t v___x_3507_; uint8_t v___x_3508_; 
v___x_3506_ = lean_ptr_addr(v_decl_3477_);
v___x_3507_ = lean_ptr_addr(v_a_3480_);
v___x_3508_ = lean_usize_dec_eq(v___x_3506_, v___x_3507_);
v___y_3487_ = v___x_3508_;
goto v___jp_3486_;
}
v___jp_3486_:
{
if (v___y_3487_ == 0)
{
lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3497_; 
v_isSharedCheck_3497_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_3497_ == 0)
{
lean_object* v_unused_3498_; lean_object* v_unused_3499_; 
v_unused_3498_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_3498_);
v_unused_3499_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_3499_);
v___x_3489_ = v_code_3470_;
v_isShared_3490_ = v_isSharedCheck_3497_;
goto v_resetjp_3488_;
}
else
{
lean_dec(v_code_3470_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3497_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 1, v_a_3482_);
lean_ctor_set(v___x_3489_, 0, v_a_3480_);
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3480_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v_a_3482_);
v___x_3492_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___x_3494_; 
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 0, v___x_3492_);
v___x_3494_ = v___x_3484_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3492_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
else
{
lean_object* v___x_3501_; 
lean_dec(v_a_3482_);
lean_dec(v_a_3480_);
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 0, v_code_3470_);
v___x_3501_ = v___x_3484_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_code_3470_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
}
else
{
lean_dec(v_a_3480_);
lean_dec_ref(v_code_3470_);
return v___x_3481_;
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_dec_ref(v_code_3470_);
v_a_3510_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3479_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3479_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
case 1:
{
lean_object* v_decl_3518_; lean_object* v_k_3519_; lean_object* v___x_3520_; 
v_decl_3518_ = lean_ctor_get(v_code_3470_, 0);
v_k_3519_ = lean_ctor_get(v_code_3470_, 1);
lean_inc_ref(v_decl_3518_);
v___x_3520_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3468_, v_t_3469_, v_decl_3518_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3522_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref(v___x_3520_);
lean_inc_ref(v_k_3519_);
v___x_3522_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3468_, v_t_3469_, v_k_3519_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3550_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3525_ = v___x_3522_;
v_isShared_3526_ = v_isSharedCheck_3550_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3522_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3550_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
uint8_t v___y_3528_; size_t v___x_3544_; size_t v___x_3545_; uint8_t v___x_3546_; 
v___x_3544_ = lean_ptr_addr(v_k_3519_);
v___x_3545_ = lean_ptr_addr(v_a_3523_);
v___x_3546_ = lean_usize_dec_eq(v___x_3544_, v___x_3545_);
if (v___x_3546_ == 0)
{
v___y_3528_ = v___x_3546_;
goto v___jp_3527_;
}
else
{
size_t v___x_3547_; size_t v___x_3548_; uint8_t v___x_3549_; 
v___x_3547_ = lean_ptr_addr(v_decl_3518_);
v___x_3548_ = lean_ptr_addr(v_a_3521_);
v___x_3549_ = lean_usize_dec_eq(v___x_3547_, v___x_3548_);
v___y_3528_ = v___x_3549_;
goto v___jp_3527_;
}
v___jp_3527_:
{
if (v___y_3528_ == 0)
{
lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3538_; 
v_isSharedCheck_3538_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_3538_ == 0)
{
lean_object* v_unused_3539_; lean_object* v_unused_3540_; 
v_unused_3539_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_3539_);
v_unused_3540_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_3540_);
v___x_3530_ = v_code_3470_;
v_isShared_3531_ = v_isSharedCheck_3538_;
goto v_resetjp_3529_;
}
else
{
lean_dec(v_code_3470_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3538_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 1, v_a_3523_);
lean_ctor_set(v___x_3530_, 0, v_a_3521_);
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3521_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_a_3523_);
v___x_3533_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
lean_object* v___x_3535_; 
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v___x_3533_);
v___x_3535_ = v___x_3525_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3533_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
else
{
lean_object* v___x_3542_; 
lean_dec(v_a_3523_);
lean_dec(v_a_3521_);
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v_code_3470_);
v___x_3542_ = v___x_3525_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_code_3470_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
}
else
{
lean_dec(v_a_3521_);
lean_dec_ref(v_code_3470_);
return v___x_3522_;
}
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_dec_ref(v_code_3470_);
v_a_3551_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3520_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3520_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
case 2:
{
lean_object* v_decl_3559_; lean_object* v_k_3560_; lean_object* v___x_3561_; 
v_decl_3559_ = lean_ctor_get(v_code_3470_, 0);
v_k_3560_ = lean_ctor_get(v_code_3470_, 1);
lean_inc_ref(v_decl_3559_);
v___x_3561_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3468_, v_t_3469_, v_decl_3559_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_a_3562_; lean_object* v___x_3563_; 
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
lean_inc(v_a_3562_);
lean_dec_ref(v___x_3561_);
lean_inc_ref(v_k_3560_);
v___x_3563_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3468_, v_t_3469_, v_k_3560_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3591_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3566_ = v___x_3563_;
v_isShared_3567_ = v_isSharedCheck_3591_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3563_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3591_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
uint8_t v___y_3569_; size_t v___x_3585_; size_t v___x_3586_; uint8_t v___x_3587_; 
v___x_3585_ = lean_ptr_addr(v_k_3560_);
v___x_3586_ = lean_ptr_addr(v_a_3564_);
v___x_3587_ = lean_usize_dec_eq(v___x_3585_, v___x_3586_);
if (v___x_3587_ == 0)
{
v___y_3569_ = v___x_3587_;
goto v___jp_3568_;
}
else
{
size_t v___x_3588_; size_t v___x_3589_; uint8_t v___x_3590_; 
v___x_3588_ = lean_ptr_addr(v_decl_3559_);
v___x_3589_ = lean_ptr_addr(v_a_3562_);
v___x_3590_ = lean_usize_dec_eq(v___x_3588_, v___x_3589_);
v___y_3569_ = v___x_3590_;
goto v___jp_3568_;
}
v___jp_3568_:
{
if (v___y_3569_ == 0)
{
lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3579_; 
v_isSharedCheck_3579_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_3579_ == 0)
{
lean_object* v_unused_3580_; lean_object* v_unused_3581_; 
v_unused_3580_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_3580_);
v_unused_3581_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_3581_);
v___x_3571_ = v_code_3470_;
v_isShared_3572_ = v_isSharedCheck_3579_;
goto v_resetjp_3570_;
}
else
{
lean_dec(v_code_3470_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3579_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
lean_ctor_set(v___x_3571_, 1, v_a_3564_);
lean_ctor_set(v___x_3571_, 0, v_a_3562_);
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3562_);
lean_ctor_set(v_reuseFailAlloc_3578_, 1, v_a_3564_);
v___x_3574_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
lean_object* v___x_3576_; 
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 0, v___x_3574_);
v___x_3576_ = v___x_3566_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3574_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
else
{
lean_object* v___x_3583_; 
lean_dec(v_a_3564_);
lean_dec(v_a_3562_);
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 0, v_code_3470_);
v___x_3583_ = v___x_3566_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_code_3470_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
}
else
{
lean_dec(v_a_3562_);
lean_dec_ref(v_code_3470_);
return v___x_3563_;
}
}
else
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
lean_dec_ref(v_code_3470_);
v_a_3592_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3561_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3561_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3600_; lean_object* v_args_3601_; lean_object* v___x_3602_; 
v_fvarId_3600_ = lean_ctor_get(v_code_3470_, 0);
v_args_3601_ = lean_ctor_get(v_code_3470_, 1);
lean_inc(v_fvarId_3600_);
v___x_3602_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3471_, v_fvarId_3600_, v_t_3469_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_fvarId_3603_; lean_object* v___x_3604_; 
v_fvarId_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_fvarId_3603_);
lean_dec_ref(v___x_3602_);
lean_inc_ref(v_args_3601_);
v___x_3604_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_3468_, v_t_3469_, v_args_3601_, v_a_3471_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3630_; 
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3607_ = v___x_3604_;
v_isShared_3608_ = v_isSharedCheck_3630_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3604_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3630_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
uint8_t v___y_3610_; uint8_t v___x_3626_; 
v___x_3626_ = l_Lean_instBEqFVarId_beq(v_fvarId_3600_, v_fvarId_3603_);
if (v___x_3626_ == 0)
{
v___y_3610_ = v___x_3626_;
goto v___jp_3609_;
}
else
{
size_t v___x_3627_; size_t v___x_3628_; uint8_t v___x_3629_; 
v___x_3627_ = lean_ptr_addr(v_args_3601_);
v___x_3628_ = lean_ptr_addr(v_a_3605_);
v___x_3629_ = lean_usize_dec_eq(v___x_3627_, v___x_3628_);
v___y_3610_ = v___x_3629_;
goto v___jp_3609_;
}
v___jp_3609_:
{
if (v___y_3610_ == 0)
{
lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3620_; 
v_isSharedCheck_3620_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_3620_ == 0)
{
lean_object* v_unused_3621_; lean_object* v_unused_3622_; 
v_unused_3621_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_3621_);
v_unused_3622_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_3622_);
v___x_3612_ = v_code_3470_;
v_isShared_3613_ = v_isSharedCheck_3620_;
goto v_resetjp_3611_;
}
else
{
lean_dec(v_code_3470_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3620_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 1, v_a_3605_);
lean_ctor_set(v___x_3612_, 0, v_fvarId_3603_);
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_fvarId_3603_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_a_3605_);
v___x_3615_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
lean_object* v___x_3617_; 
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 0, v___x_3615_);
v___x_3617_ = v___x_3607_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3615_);
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
lean_object* v___x_3624_; 
lean_dec(v_a_3605_);
lean_dec(v_fvarId_3603_);
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 0, v_code_3470_);
v___x_3624_ = v___x_3607_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_code_3470_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
}
else
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
lean_dec(v_fvarId_3603_);
lean_dec_ref(v_code_3470_);
v_a_3631_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3604_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3604_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
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
else
{
lean_object* v___x_3639_; 
lean_dec_ref(v_code_3470_);
v___x_3639_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3468_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
return v___x_3639_;
}
}
case 4:
{
lean_object* v_cases_3640_; lean_object* v_typeName_3641_; lean_object* v_resultType_3642_; lean_object* v_discr_3643_; lean_object* v_alts_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3691_; 
v_cases_3640_ = lean_ctor_get(v_code_3470_, 0);
lean_inc_ref(v_cases_3640_);
v_typeName_3641_ = lean_ctor_get(v_cases_3640_, 0);
v_resultType_3642_ = lean_ctor_get(v_cases_3640_, 1);
v_discr_3643_ = lean_ctor_get(v_cases_3640_, 2);
v_alts_3644_ = lean_ctor_get(v_cases_3640_, 3);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_cases_3640_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3646_ = v_cases_3640_;
v_isShared_3647_ = v_isSharedCheck_3691_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_alts_3644_);
lean_inc(v_discr_3643_);
lean_inc(v_resultType_3642_);
lean_inc(v_typeName_3641_);
lean_dec(v_cases_3640_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3691_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
lean_inc_ref(v_resultType_3642_);
v___x_3648_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3468_, v_a_3471_, v_t_3469_, v_resultType_3642_);
lean_inc(v_discr_3643_);
v___x_3649_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3471_, v_discr_3643_, v_t_3469_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_fvarId_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3689_; 
v_fvarId_3650_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3652_ = v___x_3649_;
v_isShared_3653_ = v_isSharedCheck_3689_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_fvarId_3650_);
lean_dec(v___x_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3689_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3644_);
v___x_3655_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_3468_, v_t_3469_, v___x_3654_, v_alts_3644_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3680_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3658_ = v___x_3655_;
v_isShared_3659_ = v_isSharedCheck_3680_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3655_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3680_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
uint8_t v___y_3671_; size_t v___x_3674_; size_t v___x_3675_; uint8_t v___x_3676_; 
v___x_3674_ = lean_ptr_addr(v_alts_3644_);
lean_dec_ref(v_alts_3644_);
v___x_3675_ = lean_ptr_addr(v_a_3656_);
v___x_3676_ = lean_usize_dec_eq(v___x_3674_, v___x_3675_);
if (v___x_3676_ == 0)
{
lean_dec_ref(v_resultType_3642_);
v___y_3671_ = v___x_3676_;
goto v___jp_3670_;
}
else
{
size_t v___x_3677_; size_t v___x_3678_; uint8_t v___x_3679_; 
v___x_3677_ = lean_ptr_addr(v_resultType_3642_);
lean_dec_ref(v_resultType_3642_);
v___x_3678_ = lean_ptr_addr(v___x_3648_);
v___x_3679_ = lean_usize_dec_eq(v___x_3677_, v___x_3678_);
v___y_3671_ = v___x_3679_;
goto v___jp_3670_;
}
v___jp_3660_:
{
lean_object* v___x_3662_; 
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 3, v_a_3656_);
lean_ctor_set(v___x_3646_, 2, v_fvarId_3650_);
lean_ctor_set(v___x_3646_, 1, v___x_3648_);
v___x_3662_ = v___x_3646_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_typeName_3641_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v___x_3648_);
lean_ctor_set(v_reuseFailAlloc_3669_, 2, v_fvarId_3650_);
lean_ctor_set(v_reuseFailAlloc_3669_, 3, v_a_3656_);
v___x_3662_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3664_; 
if (v_isShared_3653_ == 0)
{
lean_ctor_set_tag(v___x_3652_, 4);
lean_ctor_set(v___x_3652_, 0, v___x_3662_);
v___x_3664_ = v___x_3652_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3662_);
v___x_3664_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3666_; 
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 0, v___x_3664_);
v___x_3666_ = v___x_3658_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
v___jp_3670_:
{
if (v___y_3671_ == 0)
{
lean_dec(v_discr_3643_);
lean_dec_ref(v_code_3470_);
goto v___jp_3660_;
}
else
{
uint8_t v___x_3672_; 
v___x_3672_ = l_Lean_instBEqFVarId_beq(v_discr_3643_, v_fvarId_3650_);
lean_dec(v_discr_3643_);
if (v___x_3672_ == 0)
{
lean_dec_ref(v_code_3470_);
goto v___jp_3660_;
}
else
{
lean_object* v___x_3673_; 
lean_del_object(v___x_3658_);
lean_dec(v_a_3656_);
lean_del_object(v___x_3652_);
lean_dec(v_fvarId_3650_);
lean_dec_ref(v___x_3648_);
lean_del_object(v___x_3646_);
lean_dec(v_typeName_3641_);
v___x_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3673_, 0, v_code_3470_);
return v___x_3673_;
}
}
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_del_object(v___x_3652_);
lean_dec(v_fvarId_3650_);
lean_dec_ref(v___x_3648_);
lean_del_object(v___x_3646_);
lean_dec_ref(v_alts_3644_);
lean_dec(v_discr_3643_);
lean_dec_ref(v_resultType_3642_);
lean_dec(v_typeName_3641_);
lean_dec_ref(v_code_3470_);
v_a_3681_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3655_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3655_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
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
}
else
{
lean_object* v___x_3690_; 
lean_dec_ref(v___x_3648_);
lean_del_object(v___x_3646_);
lean_dec_ref(v_alts_3644_);
lean_dec(v_discr_3643_);
lean_dec_ref(v_resultType_3642_);
lean_dec(v_typeName_3641_);
lean_dec_ref(v_code_3470_);
v___x_3690_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3468_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
return v___x_3690_;
}
}
}
case 5:
{
lean_object* v_fvarId_3692_; lean_object* v___x_3693_; 
v_fvarId_3692_ = lean_ctor_get(v_code_3470_, 0);
lean_inc(v_fvarId_3692_);
v___x_3693_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3471_, v_fvarId_3692_, v_t_3469_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_fvarId_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3713_; 
v_fvarId_3694_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3696_ = v___x_3693_;
v_isShared_3697_ = v_isSharedCheck_3713_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_fvarId_3694_);
lean_dec(v___x_3693_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3713_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
uint8_t v___x_3698_; 
v___x_3698_ = l_Lean_instBEqFVarId_beq(v_fvarId_3692_, v_fvarId_3694_);
if (v___x_3698_ == 0)
{
lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3708_; 
v_isSharedCheck_3708_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_3708_ == 0)
{
lean_object* v_unused_3709_; 
v_unused_3709_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_3709_);
v___x_3700_ = v_code_3470_;
v_isShared_3701_ = v_isSharedCheck_3708_;
goto v_resetjp_3699_;
}
else
{
lean_dec(v_code_3470_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3708_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
lean_ctor_set(v___x_3700_, 0, v_fvarId_3694_);
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_fvarId_3694_);
v___x_3703_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
lean_object* v___x_3705_; 
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 0, v___x_3703_);
v___x_3705_ = v___x_3696_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v___x_3703_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
else
{
lean_object* v___x_3711_; 
lean_dec(v_fvarId_3694_);
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 0, v_code_3470_);
v___x_3711_ = v___x_3696_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_code_3470_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
}
else
{
lean_object* v___x_3714_; 
lean_dec_ref(v_code_3470_);
v___x_3714_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3468_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
return v___x_3714_;
}
}
case 6:
{
lean_object* v_type_3715_; lean_object* v___x_3716_; size_t v___x_3717_; size_t v___x_3718_; uint8_t v___x_3719_; 
v_type_3715_ = lean_ctor_get(v_code_3470_, 0);
lean_inc_ref(v_type_3715_);
v___x_3716_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3468_, v_a_3471_, v_t_3469_, v_type_3715_);
v___x_3717_ = lean_ptr_addr(v_type_3715_);
v___x_3718_ = lean_ptr_addr(v___x_3716_);
v___x_3719_ = lean_usize_dec_eq(v___x_3717_, v___x_3718_);
if (v___x_3719_ == 0)
{
lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3727_; 
v_isSharedCheck_3727_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_3727_ == 0)
{
lean_object* v_unused_3728_; 
v_unused_3728_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_3728_);
v___x_3721_ = v_code_3470_;
v_isShared_3722_ = v_isSharedCheck_3727_;
goto v_resetjp_3720_;
}
else
{
lean_dec(v_code_3470_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3727_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3724_; 
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v___x_3716_);
v___x_3724_ = v___x_3721_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3716_);
v___x_3724_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
lean_object* v___x_3725_; 
v___x_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3724_);
return v___x_3725_;
}
}
}
else
{
lean_object* v___x_3729_; 
lean_dec_ref(v___x_3716_);
v___x_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3729_, 0, v_code_3470_);
return v___x_3729_;
}
}
case 7:
{
lean_object* v_fvarId_3730_; lean_object* v_i_3731_; lean_object* v_y_3732_; lean_object* v_k_3733_; lean_object* v___x_3734_; 
v_fvarId_3730_ = lean_ctor_get(v_code_3470_, 0);
v_i_3731_ = lean_ctor_get(v_code_3470_, 1);
v_y_3732_ = lean_ctor_get(v_code_3470_, 2);
v_k_3733_ = lean_ctor_get(v_code_3470_, 3);
lean_inc(v_fvarId_3730_);
v___x_3734_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3471_, v_fvarId_3730_, v_t_3469_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_fvarId_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v_fvarId_3735_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_fvarId_3735_);
lean_dec_ref(v___x_3734_);
lean_inc(v_y_3732_);
v___x_3736_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_3468_, v_a_3471_, v_y_3732_, v_t_3469_);
lean_inc_ref(v_k_3733_);
v___x_3737_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3468_, v_t_3469_, v_k_3733_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3799_; 
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3740_ = v___x_3737_;
v_isShared_3741_ = v_isSharedCheck_3799_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3737_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3799_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
uint8_t v___y_3743_; size_t v___x_3795_; size_t v___x_3796_; uint8_t v___x_3797_; 
v___x_3795_ = lean_ptr_addr(v_fvarId_3730_);
v___x_3796_ = lean_ptr_addr(v_fvarId_3735_);
v___x_3797_ = lean_usize_dec_eq(v___x_3795_, v___x_3796_);
if (v___x_3797_ == 0)
{
v___y_3743_ = v___x_3797_;
goto v___jp_3742_;
}
else
{
uint8_t v___x_3798_; 
v___x_3798_ = lean_nat_dec_eq(v_i_3731_, v_i_3731_);
v___y_3743_ = v___x_3798_;
goto v___jp_3742_;
}
v___jp_3742_:
{
if (v___y_3743_ == 0)
{
lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3753_; 
lean_inc(v_i_3731_);
v_isSharedCheck_3753_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_3753_ == 0)
{
lean_object* v_unused_3754_; lean_object* v_unused_3755_; lean_object* v_unused_3756_; lean_object* v_unused_3757_; 
v_unused_3754_ = lean_ctor_get(v_code_3470_, 3);
lean_dec(v_unused_3754_);
v_unused_3755_ = lean_ctor_get(v_code_3470_, 2);
lean_dec(v_unused_3755_);
v_unused_3756_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_3756_);
v_unused_3757_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_3757_);
v___x_3745_ = v_code_3470_;
v_isShared_3746_ = v_isSharedCheck_3753_;
goto v_resetjp_3744_;
}
else
{
lean_dec(v_code_3470_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3753_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 3, v_a_3738_);
lean_ctor_set(v___x_3745_, 2, v___x_3736_);
lean_ctor_set(v___x_3745_, 0, v_fvarId_3735_);
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_fvarId_3735_);
lean_ctor_set(v_reuseFailAlloc_3752_, 1, v_i_3731_);
lean_ctor_set(v_reuseFailAlloc_3752_, 2, v___x_3736_);
lean_ctor_set(v_reuseFailAlloc_3752_, 3, v_a_3738_);
v___x_3748_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
lean_object* v___x_3750_; 
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 0, v___x_3748_);
v___x_3750_ = v___x_3740_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v___x_3748_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
else
{
size_t v___x_3758_; size_t v___x_3759_; uint8_t v___x_3760_; 
v___x_3758_ = lean_ptr_addr(v_y_3732_);
v___x_3759_ = lean_ptr_addr(v___x_3736_);
v___x_3760_ = lean_usize_dec_eq(v___x_3758_, v___x_3759_);
if (v___x_3760_ == 0)
{
lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3770_; 
lean_inc(v_i_3731_);
v_isSharedCheck_3770_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_3770_ == 0)
{
lean_object* v_unused_3771_; lean_object* v_unused_3772_; lean_object* v_unused_3773_; lean_object* v_unused_3774_; 
v_unused_3771_ = lean_ctor_get(v_code_3470_, 3);
lean_dec(v_unused_3771_);
v_unused_3772_ = lean_ctor_get(v_code_3470_, 2);
lean_dec(v_unused_3772_);
v_unused_3773_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_3773_);
v_unused_3774_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_3774_);
v___x_3762_ = v_code_3470_;
v_isShared_3763_ = v_isSharedCheck_3770_;
goto v_resetjp_3761_;
}
else
{
lean_dec(v_code_3470_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3770_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
lean_ctor_set(v___x_3762_, 3, v_a_3738_);
lean_ctor_set(v___x_3762_, 2, v___x_3736_);
lean_ctor_set(v___x_3762_, 0, v_fvarId_3735_);
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_fvarId_3735_);
lean_ctor_set(v_reuseFailAlloc_3769_, 1, v_i_3731_);
lean_ctor_set(v_reuseFailAlloc_3769_, 2, v___x_3736_);
lean_ctor_set(v_reuseFailAlloc_3769_, 3, v_a_3738_);
v___x_3765_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
lean_object* v___x_3767_; 
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 0, v___x_3765_);
v___x_3767_ = v___x_3740_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v___x_3765_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
else
{
size_t v___x_3775_; size_t v___x_3776_; uint8_t v___x_3777_; 
v___x_3775_ = lean_ptr_addr(v_k_3733_);
v___x_3776_ = lean_ptr_addr(v_a_3738_);
v___x_3777_ = lean_usize_dec_eq(v___x_3775_, v___x_3776_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3787_; 
lean_inc(v_i_3731_);
v_isSharedCheck_3787_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_3787_ == 0)
{
lean_object* v_unused_3788_; lean_object* v_unused_3789_; lean_object* v_unused_3790_; lean_object* v_unused_3791_; 
v_unused_3788_ = lean_ctor_get(v_code_3470_, 3);
lean_dec(v_unused_3788_);
v_unused_3789_ = lean_ctor_get(v_code_3470_, 2);
lean_dec(v_unused_3789_);
v_unused_3790_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_3790_);
v_unused_3791_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_3791_);
v___x_3779_ = v_code_3470_;
v_isShared_3780_ = v_isSharedCheck_3787_;
goto v_resetjp_3778_;
}
else
{
lean_dec(v_code_3470_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3787_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 3, v_a_3738_);
lean_ctor_set(v___x_3779_, 2, v___x_3736_);
lean_ctor_set(v___x_3779_, 0, v_fvarId_3735_);
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_fvarId_3735_);
lean_ctor_set(v_reuseFailAlloc_3786_, 1, v_i_3731_);
lean_ctor_set(v_reuseFailAlloc_3786_, 2, v___x_3736_);
lean_ctor_set(v_reuseFailAlloc_3786_, 3, v_a_3738_);
v___x_3782_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
lean_object* v___x_3784_; 
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 0, v___x_3782_);
v___x_3784_ = v___x_3740_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3782_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
else
{
lean_object* v___x_3793_; 
lean_dec(v_a_3738_);
lean_dec(v___x_3736_);
lean_dec(v_fvarId_3735_);
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 0, v_code_3470_);
v___x_3793_ = v___x_3740_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_code_3470_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3736_);
lean_dec(v_fvarId_3735_);
lean_dec_ref(v_code_3470_);
return v___x_3737_;
}
}
else
{
lean_object* v___x_3800_; 
lean_dec_ref(v_code_3470_);
v___x_3800_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3468_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
return v___x_3800_;
}
}
case 8:
{
lean_object* v_fvarId_3801_; lean_object* v_i_3802_; lean_object* v_y_3803_; lean_object* v_k_3804_; lean_object* v___x_3805_; 
v_fvarId_3801_ = lean_ctor_get(v_code_3470_, 0);
v_i_3802_ = lean_ctor_get(v_code_3470_, 1);
v_y_3803_ = lean_ctor_get(v_code_3470_, 2);
v_k_3804_ = lean_ctor_get(v_code_3470_, 3);
lean_inc(v_fvarId_3801_);
v___x_3805_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3471_, v_fvarId_3801_, v_t_3469_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v_fvarId_3806_; lean_object* v___x_3807_; 
v_fvarId_3806_ = lean_ctor_get(v___x_3805_, 0);
lean_inc(v_fvarId_3806_);
lean_dec_ref(v___x_3805_);
lean_inc(v_y_3803_);
v___x_3807_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3471_, v_y_3803_, v_t_3469_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_fvarId_3808_; lean_object* v___x_3809_; 
v_fvarId_3808_ = lean_ctor_get(v___x_3807_, 0);
lean_inc(v_fvarId_3808_);
lean_dec_ref(v___x_3807_);
lean_inc_ref(v_k_3804_);
v___x_3809_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3468_, v_t_3469_, v_k_3804_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3871_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3812_ = v___x_3809_;
v_isShared_3813_ = v_isSharedCheck_3871_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3809_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3871_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
uint8_t v___y_3815_; size_t v___x_3867_; size_t v___x_3868_; uint8_t v___x_3869_; 
v___x_3867_ = lean_ptr_addr(v_fvarId_3801_);
v___x_3868_ = lean_ptr_addr(v_fvarId_3806_);
v___x_3869_ = lean_usize_dec_eq(v___x_3867_, v___x_3868_);
if (v___x_3869_ == 0)
{
v___y_3815_ = v___x_3869_;
goto v___jp_3814_;
}
else
{
uint8_t v___x_3870_; 
v___x_3870_ = lean_nat_dec_eq(v_i_3802_, v_i_3802_);
v___y_3815_ = v___x_3870_;
goto v___jp_3814_;
}
v___jp_3814_:
{
if (v___y_3815_ == 0)
{
lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3825_; 
lean_inc(v_i_3802_);
v_isSharedCheck_3825_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_3825_ == 0)
{
lean_object* v_unused_3826_; lean_object* v_unused_3827_; lean_object* v_unused_3828_; lean_object* v_unused_3829_; 
v_unused_3826_ = lean_ctor_get(v_code_3470_, 3);
lean_dec(v_unused_3826_);
v_unused_3827_ = lean_ctor_get(v_code_3470_, 2);
lean_dec(v_unused_3827_);
v_unused_3828_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_3828_);
v_unused_3829_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_3829_);
v___x_3817_ = v_code_3470_;
v_isShared_3818_ = v_isSharedCheck_3825_;
goto v_resetjp_3816_;
}
else
{
lean_dec(v_code_3470_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3825_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3820_; 
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 3, v_a_3810_);
lean_ctor_set(v___x_3817_, 2, v_fvarId_3808_);
lean_ctor_set(v___x_3817_, 0, v_fvarId_3806_);
v___x_3820_ = v___x_3817_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_fvarId_3806_);
lean_ctor_set(v_reuseFailAlloc_3824_, 1, v_i_3802_);
lean_ctor_set(v_reuseFailAlloc_3824_, 2, v_fvarId_3808_);
lean_ctor_set(v_reuseFailAlloc_3824_, 3, v_a_3810_);
v___x_3820_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
lean_object* v___x_3822_; 
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 0, v___x_3820_);
v___x_3822_ = v___x_3812_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v___x_3820_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
else
{
size_t v___x_3830_; size_t v___x_3831_; uint8_t v___x_3832_; 
v___x_3830_ = lean_ptr_addr(v_y_3803_);
v___x_3831_ = lean_ptr_addr(v_fvarId_3808_);
v___x_3832_ = lean_usize_dec_eq(v___x_3830_, v___x_3831_);
if (v___x_3832_ == 0)
{
lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3842_; 
lean_inc(v_i_3802_);
v_isSharedCheck_3842_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_3842_ == 0)
{
lean_object* v_unused_3843_; lean_object* v_unused_3844_; lean_object* v_unused_3845_; lean_object* v_unused_3846_; 
v_unused_3843_ = lean_ctor_get(v_code_3470_, 3);
lean_dec(v_unused_3843_);
v_unused_3844_ = lean_ctor_get(v_code_3470_, 2);
lean_dec(v_unused_3844_);
v_unused_3845_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_3845_);
v_unused_3846_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_3846_);
v___x_3834_ = v_code_3470_;
v_isShared_3835_ = v_isSharedCheck_3842_;
goto v_resetjp_3833_;
}
else
{
lean_dec(v_code_3470_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3842_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 3, v_a_3810_);
lean_ctor_set(v___x_3834_, 2, v_fvarId_3808_);
lean_ctor_set(v___x_3834_, 0, v_fvarId_3806_);
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_fvarId_3806_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v_i_3802_);
lean_ctor_set(v_reuseFailAlloc_3841_, 2, v_fvarId_3808_);
lean_ctor_set(v_reuseFailAlloc_3841_, 3, v_a_3810_);
v___x_3837_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
lean_object* v___x_3839_; 
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 0, v___x_3837_);
v___x_3839_ = v___x_3812_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3837_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
else
{
size_t v___x_3847_; size_t v___x_3848_; uint8_t v___x_3849_; 
v___x_3847_ = lean_ptr_addr(v_k_3804_);
v___x_3848_ = lean_ptr_addr(v_a_3810_);
v___x_3849_ = lean_usize_dec_eq(v___x_3847_, v___x_3848_);
if (v___x_3849_ == 0)
{
lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3859_; 
lean_inc(v_i_3802_);
v_isSharedCheck_3859_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_3859_ == 0)
{
lean_object* v_unused_3860_; lean_object* v_unused_3861_; lean_object* v_unused_3862_; lean_object* v_unused_3863_; 
v_unused_3860_ = lean_ctor_get(v_code_3470_, 3);
lean_dec(v_unused_3860_);
v_unused_3861_ = lean_ctor_get(v_code_3470_, 2);
lean_dec(v_unused_3861_);
v_unused_3862_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_3862_);
v_unused_3863_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_3863_);
v___x_3851_ = v_code_3470_;
v_isShared_3852_ = v_isSharedCheck_3859_;
goto v_resetjp_3850_;
}
else
{
lean_dec(v_code_3470_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3859_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 3, v_a_3810_);
lean_ctor_set(v___x_3851_, 2, v_fvarId_3808_);
lean_ctor_set(v___x_3851_, 0, v_fvarId_3806_);
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_fvarId_3806_);
lean_ctor_set(v_reuseFailAlloc_3858_, 1, v_i_3802_);
lean_ctor_set(v_reuseFailAlloc_3858_, 2, v_fvarId_3808_);
lean_ctor_set(v_reuseFailAlloc_3858_, 3, v_a_3810_);
v___x_3854_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
lean_object* v___x_3856_; 
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 0, v___x_3854_);
v___x_3856_ = v___x_3812_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3854_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
else
{
lean_object* v___x_3865_; 
lean_dec(v_a_3810_);
lean_dec(v_fvarId_3808_);
lean_dec(v_fvarId_3806_);
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 0, v_code_3470_);
v___x_3865_ = v___x_3812_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_code_3470_);
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
}
}
}
else
{
lean_dec(v_fvarId_3808_);
lean_dec(v_fvarId_3806_);
lean_dec_ref(v_code_3470_);
return v___x_3809_;
}
}
else
{
lean_object* v___x_3872_; 
lean_dec(v_fvarId_3806_);
lean_dec_ref(v_code_3470_);
v___x_3872_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3468_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
return v___x_3872_;
}
}
else
{
lean_object* v___x_3873_; 
lean_dec_ref(v_code_3470_);
v___x_3873_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3468_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
return v___x_3873_;
}
}
case 9:
{
lean_object* v_fvarId_3874_; lean_object* v_i_3875_; lean_object* v_offset_3876_; lean_object* v_y_3877_; lean_object* v_ty_3878_; lean_object* v_k_3879_; lean_object* v___x_3880_; 
v_fvarId_3874_ = lean_ctor_get(v_code_3470_, 0);
v_i_3875_ = lean_ctor_get(v_code_3470_, 1);
v_offset_3876_ = lean_ctor_get(v_code_3470_, 2);
v_y_3877_ = lean_ctor_get(v_code_3470_, 3);
v_ty_3878_ = lean_ctor_get(v_code_3470_, 4);
v_k_3879_ = lean_ctor_get(v_code_3470_, 5);
lean_inc(v_fvarId_3874_);
v___x_3880_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3471_, v_fvarId_3874_, v_t_3469_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v_fvarId_3881_; lean_object* v___x_3882_; 
v_fvarId_3881_ = lean_ctor_get(v___x_3880_, 0);
lean_inc(v_fvarId_3881_);
lean_dec_ref(v___x_3880_);
lean_inc(v_y_3877_);
v___x_3882_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3471_, v_y_3877_, v_t_3469_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_fvarId_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v_fvarId_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_fvarId_3883_);
lean_dec_ref(v___x_3882_);
lean_inc_ref(v_ty_3878_);
v___x_3884_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3468_, v_a_3471_, v_t_3469_, v_ty_3878_);
lean_inc_ref(v_k_3879_);
v___x_3885_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3468_, v_t_3469_, v_k_3879_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3989_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3888_ = v___x_3885_;
v_isShared_3889_ = v_isSharedCheck_3989_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3885_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3989_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
uint8_t v___y_3891_; size_t v___x_3985_; size_t v___x_3986_; uint8_t v___x_3987_; 
v___x_3985_ = lean_ptr_addr(v_fvarId_3874_);
v___x_3986_ = lean_ptr_addr(v_fvarId_3881_);
v___x_3987_ = lean_usize_dec_eq(v___x_3985_, v___x_3986_);
if (v___x_3987_ == 0)
{
v___y_3891_ = v___x_3987_;
goto v___jp_3890_;
}
else
{
uint8_t v___x_3988_; 
v___x_3988_ = lean_nat_dec_eq(v_i_3875_, v_i_3875_);
v___y_3891_ = v___x_3988_;
goto v___jp_3890_;
}
v___jp_3890_:
{
if (v___y_3891_ == 0)
{
lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3901_; 
lean_inc(v_offset_3876_);
lean_inc(v_i_3875_);
v_isSharedCheck_3901_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_3901_ == 0)
{
lean_object* v_unused_3902_; lean_object* v_unused_3903_; lean_object* v_unused_3904_; lean_object* v_unused_3905_; lean_object* v_unused_3906_; lean_object* v_unused_3907_; 
v_unused_3902_ = lean_ctor_get(v_code_3470_, 5);
lean_dec(v_unused_3902_);
v_unused_3903_ = lean_ctor_get(v_code_3470_, 4);
lean_dec(v_unused_3903_);
v_unused_3904_ = lean_ctor_get(v_code_3470_, 3);
lean_dec(v_unused_3904_);
v_unused_3905_ = lean_ctor_get(v_code_3470_, 2);
lean_dec(v_unused_3905_);
v_unused_3906_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_3906_);
v_unused_3907_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_3907_);
v___x_3893_ = v_code_3470_;
v_isShared_3894_ = v_isSharedCheck_3901_;
goto v_resetjp_3892_;
}
else
{
lean_dec(v_code_3470_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3901_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 5, v_a_3886_);
lean_ctor_set(v___x_3893_, 4, v___x_3884_);
lean_ctor_set(v___x_3893_, 3, v_fvarId_3883_);
lean_ctor_set(v___x_3893_, 0, v_fvarId_3881_);
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_fvarId_3881_);
lean_ctor_set(v_reuseFailAlloc_3900_, 1, v_i_3875_);
lean_ctor_set(v_reuseFailAlloc_3900_, 2, v_offset_3876_);
lean_ctor_set(v_reuseFailAlloc_3900_, 3, v_fvarId_3883_);
lean_ctor_set(v_reuseFailAlloc_3900_, 4, v___x_3884_);
lean_ctor_set(v_reuseFailAlloc_3900_, 5, v_a_3886_);
v___x_3896_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
lean_object* v___x_3898_; 
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3896_);
v___x_3898_ = v___x_3888_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3896_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
else
{
uint8_t v___x_3908_; 
v___x_3908_ = lean_nat_dec_eq(v_offset_3876_, v_offset_3876_);
if (v___x_3908_ == 0)
{
lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3918_; 
lean_inc(v_offset_3876_);
lean_inc(v_i_3875_);
v_isSharedCheck_3918_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_3918_ == 0)
{
lean_object* v_unused_3919_; lean_object* v_unused_3920_; lean_object* v_unused_3921_; lean_object* v_unused_3922_; lean_object* v_unused_3923_; lean_object* v_unused_3924_; 
v_unused_3919_ = lean_ctor_get(v_code_3470_, 5);
lean_dec(v_unused_3919_);
v_unused_3920_ = lean_ctor_get(v_code_3470_, 4);
lean_dec(v_unused_3920_);
v_unused_3921_ = lean_ctor_get(v_code_3470_, 3);
lean_dec(v_unused_3921_);
v_unused_3922_ = lean_ctor_get(v_code_3470_, 2);
lean_dec(v_unused_3922_);
v_unused_3923_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_3923_);
v_unused_3924_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_3924_);
v___x_3910_ = v_code_3470_;
v_isShared_3911_ = v_isSharedCheck_3918_;
goto v_resetjp_3909_;
}
else
{
lean_dec(v_code_3470_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3918_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 5, v_a_3886_);
lean_ctor_set(v___x_3910_, 4, v___x_3884_);
lean_ctor_set(v___x_3910_, 3, v_fvarId_3883_);
lean_ctor_set(v___x_3910_, 0, v_fvarId_3881_);
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_fvarId_3881_);
lean_ctor_set(v_reuseFailAlloc_3917_, 1, v_i_3875_);
lean_ctor_set(v_reuseFailAlloc_3917_, 2, v_offset_3876_);
lean_ctor_set(v_reuseFailAlloc_3917_, 3, v_fvarId_3883_);
lean_ctor_set(v_reuseFailAlloc_3917_, 4, v___x_3884_);
lean_ctor_set(v_reuseFailAlloc_3917_, 5, v_a_3886_);
v___x_3913_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
lean_object* v___x_3915_; 
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3913_);
v___x_3915_ = v___x_3888_;
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
v___x_3925_ = lean_ptr_addr(v_y_3877_);
v___x_3926_ = lean_ptr_addr(v_fvarId_3883_);
v___x_3927_ = lean_usize_dec_eq(v___x_3925_, v___x_3926_);
if (v___x_3927_ == 0)
{
lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3937_; 
lean_inc(v_offset_3876_);
lean_inc(v_i_3875_);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_3937_ == 0)
{
lean_object* v_unused_3938_; lean_object* v_unused_3939_; lean_object* v_unused_3940_; lean_object* v_unused_3941_; lean_object* v_unused_3942_; lean_object* v_unused_3943_; 
v_unused_3938_ = lean_ctor_get(v_code_3470_, 5);
lean_dec(v_unused_3938_);
v_unused_3939_ = lean_ctor_get(v_code_3470_, 4);
lean_dec(v_unused_3939_);
v_unused_3940_ = lean_ctor_get(v_code_3470_, 3);
lean_dec(v_unused_3940_);
v_unused_3941_ = lean_ctor_get(v_code_3470_, 2);
lean_dec(v_unused_3941_);
v_unused_3942_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_3942_);
v_unused_3943_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_3943_);
v___x_3929_ = v_code_3470_;
v_isShared_3930_ = v_isSharedCheck_3937_;
goto v_resetjp_3928_;
}
else
{
lean_dec(v_code_3470_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3937_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
lean_ctor_set(v___x_3929_, 5, v_a_3886_);
lean_ctor_set(v___x_3929_, 4, v___x_3884_);
lean_ctor_set(v___x_3929_, 3, v_fvarId_3883_);
lean_ctor_set(v___x_3929_, 0, v_fvarId_3881_);
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_fvarId_3881_);
lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_i_3875_);
lean_ctor_set(v_reuseFailAlloc_3936_, 2, v_offset_3876_);
lean_ctor_set(v_reuseFailAlloc_3936_, 3, v_fvarId_3883_);
lean_ctor_set(v_reuseFailAlloc_3936_, 4, v___x_3884_);
lean_ctor_set(v_reuseFailAlloc_3936_, 5, v_a_3886_);
v___x_3932_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
lean_object* v___x_3934_; 
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3932_);
v___x_3934_ = v___x_3888_;
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
v___x_3944_ = lean_ptr_addr(v_ty_3878_);
v___x_3945_ = lean_ptr_addr(v___x_3884_);
v___x_3946_ = lean_usize_dec_eq(v___x_3944_, v___x_3945_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3956_; 
lean_inc(v_offset_3876_);
lean_inc(v_i_3875_);
v_isSharedCheck_3956_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_3956_ == 0)
{
lean_object* v_unused_3957_; lean_object* v_unused_3958_; lean_object* v_unused_3959_; lean_object* v_unused_3960_; lean_object* v_unused_3961_; lean_object* v_unused_3962_; 
v_unused_3957_ = lean_ctor_get(v_code_3470_, 5);
lean_dec(v_unused_3957_);
v_unused_3958_ = lean_ctor_get(v_code_3470_, 4);
lean_dec(v_unused_3958_);
v_unused_3959_ = lean_ctor_get(v_code_3470_, 3);
lean_dec(v_unused_3959_);
v_unused_3960_ = lean_ctor_get(v_code_3470_, 2);
lean_dec(v_unused_3960_);
v_unused_3961_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_3961_);
v_unused_3962_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_3962_);
v___x_3948_ = v_code_3470_;
v_isShared_3949_ = v_isSharedCheck_3956_;
goto v_resetjp_3947_;
}
else
{
lean_dec(v_code_3470_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3956_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 5, v_a_3886_);
lean_ctor_set(v___x_3948_, 4, v___x_3884_);
lean_ctor_set(v___x_3948_, 3, v_fvarId_3883_);
lean_ctor_set(v___x_3948_, 0, v_fvarId_3881_);
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_fvarId_3881_);
lean_ctor_set(v_reuseFailAlloc_3955_, 1, v_i_3875_);
lean_ctor_set(v_reuseFailAlloc_3955_, 2, v_offset_3876_);
lean_ctor_set(v_reuseFailAlloc_3955_, 3, v_fvarId_3883_);
lean_ctor_set(v_reuseFailAlloc_3955_, 4, v___x_3884_);
lean_ctor_set(v_reuseFailAlloc_3955_, 5, v_a_3886_);
v___x_3951_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
lean_object* v___x_3953_; 
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3951_);
v___x_3953_ = v___x_3888_;
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
size_t v___x_3963_; size_t v___x_3964_; uint8_t v___x_3965_; 
v___x_3963_ = lean_ptr_addr(v_k_3879_);
v___x_3964_ = lean_ptr_addr(v_a_3886_);
v___x_3965_ = lean_usize_dec_eq(v___x_3963_, v___x_3964_);
if (v___x_3965_ == 0)
{
lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3975_; 
lean_inc(v_offset_3876_);
lean_inc(v_i_3875_);
v_isSharedCheck_3975_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_3975_ == 0)
{
lean_object* v_unused_3976_; lean_object* v_unused_3977_; lean_object* v_unused_3978_; lean_object* v_unused_3979_; lean_object* v_unused_3980_; lean_object* v_unused_3981_; 
v_unused_3976_ = lean_ctor_get(v_code_3470_, 5);
lean_dec(v_unused_3976_);
v_unused_3977_ = lean_ctor_get(v_code_3470_, 4);
lean_dec(v_unused_3977_);
v_unused_3978_ = lean_ctor_get(v_code_3470_, 3);
lean_dec(v_unused_3978_);
v_unused_3979_ = lean_ctor_get(v_code_3470_, 2);
lean_dec(v_unused_3979_);
v_unused_3980_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_3980_);
v_unused_3981_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_3981_);
v___x_3967_ = v_code_3470_;
v_isShared_3968_ = v_isSharedCheck_3975_;
goto v_resetjp_3966_;
}
else
{
lean_dec(v_code_3470_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3975_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
lean_ctor_set(v___x_3967_, 5, v_a_3886_);
lean_ctor_set(v___x_3967_, 4, v___x_3884_);
lean_ctor_set(v___x_3967_, 3, v_fvarId_3883_);
lean_ctor_set(v___x_3967_, 0, v_fvarId_3881_);
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_fvarId_3881_);
lean_ctor_set(v_reuseFailAlloc_3974_, 1, v_i_3875_);
lean_ctor_set(v_reuseFailAlloc_3974_, 2, v_offset_3876_);
lean_ctor_set(v_reuseFailAlloc_3974_, 3, v_fvarId_3883_);
lean_ctor_set(v_reuseFailAlloc_3974_, 4, v___x_3884_);
lean_ctor_set(v_reuseFailAlloc_3974_, 5, v_a_3886_);
v___x_3970_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
lean_object* v___x_3972_; 
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3970_);
v___x_3972_ = v___x_3888_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v___x_3970_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
}
}
else
{
lean_object* v___x_3983_; 
lean_dec(v_a_3886_);
lean_dec_ref(v___x_3884_);
lean_dec(v_fvarId_3883_);
lean_dec(v_fvarId_3881_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v_code_3470_);
v___x_3983_ = v___x_3888_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_code_3470_);
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
}
}
}
}
}
else
{
lean_dec_ref(v___x_3884_);
lean_dec(v_fvarId_3883_);
lean_dec(v_fvarId_3881_);
lean_dec_ref(v_code_3470_);
return v___x_3885_;
}
}
else
{
lean_object* v___x_3990_; 
lean_dec(v_fvarId_3881_);
lean_dec_ref(v_code_3470_);
v___x_3990_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3468_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
return v___x_3990_;
}
}
else
{
lean_object* v___x_3991_; 
lean_dec_ref(v_code_3470_);
v___x_3991_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3468_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
return v___x_3991_;
}
}
case 10:
{
lean_object* v_fvarId_3992_; lean_object* v_cidx_3993_; lean_object* v_k_3994_; lean_object* v___x_3995_; 
v_fvarId_3992_ = lean_ctor_get(v_code_3470_, 0);
v_cidx_3993_ = lean_ctor_get(v_code_3470_, 1);
v_k_3994_ = lean_ctor_get(v_code_3470_, 2);
lean_inc(v_fvarId_3992_);
v___x_3995_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3471_, v_fvarId_3992_, v_t_3469_);
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v_fvarId_3996_; lean_object* v___x_3997_; 
v_fvarId_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc(v_fvarId_3996_);
lean_dec_ref(v___x_3995_);
lean_inc_ref(v_k_3994_);
v___x_3997_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3468_, v_t_3469_, v_k_3994_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4040_; 
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4000_ = v___x_3997_;
v_isShared_4001_ = v_isSharedCheck_4040_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3997_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4040_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
uint8_t v___y_4003_; size_t v___x_4036_; size_t v___x_4037_; uint8_t v___x_4038_; 
v___x_4036_ = lean_ptr_addr(v_fvarId_3992_);
v___x_4037_ = lean_ptr_addr(v_fvarId_3996_);
v___x_4038_ = lean_usize_dec_eq(v___x_4036_, v___x_4037_);
if (v___x_4038_ == 0)
{
v___y_4003_ = v___x_4038_;
goto v___jp_4002_;
}
else
{
uint8_t v___x_4039_; 
v___x_4039_ = lean_nat_dec_eq(v_cidx_3993_, v_cidx_3993_);
v___y_4003_ = v___x_4039_;
goto v___jp_4002_;
}
v___jp_4002_:
{
if (v___y_4003_ == 0)
{
lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4013_; 
lean_inc(v_cidx_3993_);
v_isSharedCheck_4013_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_4013_ == 0)
{
lean_object* v_unused_4014_; lean_object* v_unused_4015_; lean_object* v_unused_4016_; 
v_unused_4014_ = lean_ctor_get(v_code_3470_, 2);
lean_dec(v_unused_4014_);
v_unused_4015_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_4015_);
v_unused_4016_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_4016_);
v___x_4005_ = v_code_3470_;
v_isShared_4006_ = v_isSharedCheck_4013_;
goto v_resetjp_4004_;
}
else
{
lean_dec(v_code_3470_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4013_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
lean_ctor_set(v___x_4005_, 2, v_a_3998_);
lean_ctor_set(v___x_4005_, 0, v_fvarId_3996_);
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_fvarId_3996_);
lean_ctor_set(v_reuseFailAlloc_4012_, 1, v_cidx_3993_);
lean_ctor_set(v_reuseFailAlloc_4012_, 2, v_a_3998_);
v___x_4008_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
lean_object* v___x_4010_; 
if (v_isShared_4001_ == 0)
{
lean_ctor_set(v___x_4000_, 0, v___x_4008_);
v___x_4010_ = v___x_4000_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4008_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
else
{
size_t v___x_4017_; size_t v___x_4018_; uint8_t v___x_4019_; 
v___x_4017_ = lean_ptr_addr(v_k_3994_);
v___x_4018_ = lean_ptr_addr(v_a_3998_);
v___x_4019_ = lean_usize_dec_eq(v___x_4017_, v___x_4018_);
if (v___x_4019_ == 0)
{
lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4029_; 
lean_inc(v_cidx_3993_);
v_isSharedCheck_4029_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_4029_ == 0)
{
lean_object* v_unused_4030_; lean_object* v_unused_4031_; lean_object* v_unused_4032_; 
v_unused_4030_ = lean_ctor_get(v_code_3470_, 2);
lean_dec(v_unused_4030_);
v_unused_4031_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_4031_);
v_unused_4032_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_4032_);
v___x_4021_ = v_code_3470_;
v_isShared_4022_ = v_isSharedCheck_4029_;
goto v_resetjp_4020_;
}
else
{
lean_dec(v_code_3470_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4029_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4024_; 
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 2, v_a_3998_);
lean_ctor_set(v___x_4021_, 0, v_fvarId_3996_);
v___x_4024_ = v___x_4021_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_fvarId_3996_);
lean_ctor_set(v_reuseFailAlloc_4028_, 1, v_cidx_3993_);
lean_ctor_set(v_reuseFailAlloc_4028_, 2, v_a_3998_);
v___x_4024_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
lean_object* v___x_4026_; 
if (v_isShared_4001_ == 0)
{
lean_ctor_set(v___x_4000_, 0, v___x_4024_);
v___x_4026_ = v___x_4000_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4024_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
}
else
{
lean_object* v___x_4034_; 
lean_dec(v_a_3998_);
lean_dec(v_fvarId_3996_);
if (v_isShared_4001_ == 0)
{
lean_ctor_set(v___x_4000_, 0, v_code_3470_);
v___x_4034_ = v___x_4000_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_code_3470_);
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
}
}
else
{
lean_dec(v_fvarId_3996_);
lean_dec_ref(v_code_3470_);
return v___x_3997_;
}
}
else
{
lean_object* v___x_4041_; 
lean_dec_ref(v_code_3470_);
v___x_4041_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3468_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
return v___x_4041_;
}
}
case 11:
{
lean_object* v_fvarId_4042_; lean_object* v_n_4043_; uint8_t v_check_4044_; uint8_t v_persistent_4045_; lean_object* v_k_4046_; lean_object* v___x_4047_; 
v_fvarId_4042_ = lean_ctor_get(v_code_3470_, 0);
v_n_4043_ = lean_ctor_get(v_code_3470_, 1);
v_check_4044_ = lean_ctor_get_uint8(v_code_3470_, sizeof(void*)*3);
v_persistent_4045_ = lean_ctor_get_uint8(v_code_3470_, sizeof(void*)*3 + 1);
v_k_4046_ = lean_ctor_get(v_code_3470_, 2);
lean_inc(v_fvarId_4042_);
v___x_4047_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3471_, v_fvarId_4042_, v_t_3469_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_fvarId_4048_; lean_object* v___x_4049_; 
v_fvarId_4048_ = lean_ctor_get(v___x_4047_, 0);
lean_inc(v_fvarId_4048_);
lean_dec_ref(v___x_4047_);
lean_inc_ref(v_k_4046_);
v___x_4049_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3468_, v_t_3469_, v_k_4046_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4092_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4052_ = v___x_4049_;
v_isShared_4053_ = v_isSharedCheck_4092_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4049_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4092_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
uint8_t v___y_4055_; size_t v___x_4088_; size_t v___x_4089_; uint8_t v___x_4090_; 
v___x_4088_ = lean_ptr_addr(v_fvarId_4042_);
v___x_4089_ = lean_ptr_addr(v_fvarId_4048_);
v___x_4090_ = lean_usize_dec_eq(v___x_4088_, v___x_4089_);
if (v___x_4090_ == 0)
{
v___y_4055_ = v___x_4090_;
goto v___jp_4054_;
}
else
{
uint8_t v___x_4091_; 
v___x_4091_ = lean_nat_dec_eq(v_n_4043_, v_n_4043_);
v___y_4055_ = v___x_4091_;
goto v___jp_4054_;
}
v___jp_4054_:
{
if (v___y_4055_ == 0)
{
lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4065_; 
lean_inc(v_n_4043_);
v_isSharedCheck_4065_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_4065_ == 0)
{
lean_object* v_unused_4066_; lean_object* v_unused_4067_; lean_object* v_unused_4068_; 
v_unused_4066_ = lean_ctor_get(v_code_3470_, 2);
lean_dec(v_unused_4066_);
v_unused_4067_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_4067_);
v_unused_4068_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_4068_);
v___x_4057_ = v_code_3470_;
v_isShared_4058_ = v_isSharedCheck_4065_;
goto v_resetjp_4056_;
}
else
{
lean_dec(v_code_3470_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4065_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
lean_ctor_set(v___x_4057_, 2, v_a_4050_);
lean_ctor_set(v___x_4057_, 0, v_fvarId_4048_);
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_fvarId_4048_);
lean_ctor_set(v_reuseFailAlloc_4064_, 1, v_n_4043_);
lean_ctor_set(v_reuseFailAlloc_4064_, 2, v_a_4050_);
lean_ctor_set_uint8(v_reuseFailAlloc_4064_, sizeof(void*)*3, v_check_4044_);
lean_ctor_set_uint8(v_reuseFailAlloc_4064_, sizeof(void*)*3 + 1, v_persistent_4045_);
v___x_4060_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
lean_object* v___x_4062_; 
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 0, v___x_4060_);
v___x_4062_ = v___x_4052_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4060_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
}
else
{
size_t v___x_4069_; size_t v___x_4070_; uint8_t v___x_4071_; 
v___x_4069_ = lean_ptr_addr(v_k_4046_);
v___x_4070_ = lean_ptr_addr(v_a_4050_);
v___x_4071_ = lean_usize_dec_eq(v___x_4069_, v___x_4070_);
if (v___x_4071_ == 0)
{
lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4081_; 
lean_inc(v_n_4043_);
v_isSharedCheck_4081_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_4081_ == 0)
{
lean_object* v_unused_4082_; lean_object* v_unused_4083_; lean_object* v_unused_4084_; 
v_unused_4082_ = lean_ctor_get(v_code_3470_, 2);
lean_dec(v_unused_4082_);
v_unused_4083_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_4083_);
v_unused_4084_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_4084_);
v___x_4073_ = v_code_3470_;
v_isShared_4074_ = v_isSharedCheck_4081_;
goto v_resetjp_4072_;
}
else
{
lean_dec(v_code_3470_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4081_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
lean_ctor_set(v___x_4073_, 2, v_a_4050_);
lean_ctor_set(v___x_4073_, 0, v_fvarId_4048_);
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_fvarId_4048_);
lean_ctor_set(v_reuseFailAlloc_4080_, 1, v_n_4043_);
lean_ctor_set(v_reuseFailAlloc_4080_, 2, v_a_4050_);
lean_ctor_set_uint8(v_reuseFailAlloc_4080_, sizeof(void*)*3, v_check_4044_);
lean_ctor_set_uint8(v_reuseFailAlloc_4080_, sizeof(void*)*3 + 1, v_persistent_4045_);
v___x_4076_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
lean_object* v___x_4078_; 
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 0, v___x_4076_);
v___x_4078_ = v___x_4052_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v___x_4076_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
else
{
lean_object* v___x_4086_; 
lean_dec(v_a_4050_);
lean_dec(v_fvarId_4048_);
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 0, v_code_3470_);
v___x_4086_ = v___x_4052_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_code_3470_);
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
}
}
else
{
lean_dec(v_fvarId_4048_);
lean_dec_ref(v_code_3470_);
return v___x_4049_;
}
}
else
{
lean_object* v___x_4093_; 
lean_dec_ref(v_code_3470_);
v___x_4093_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3468_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
return v___x_4093_;
}
}
case 12:
{
lean_object* v_fvarId_4094_; lean_object* v_n_4095_; uint8_t v_check_4096_; uint8_t v_persistent_4097_; lean_object* v_k_4098_; lean_object* v___x_4099_; 
v_fvarId_4094_ = lean_ctor_get(v_code_3470_, 0);
v_n_4095_ = lean_ctor_get(v_code_3470_, 1);
v_check_4096_ = lean_ctor_get_uint8(v_code_3470_, sizeof(void*)*3);
v_persistent_4097_ = lean_ctor_get_uint8(v_code_3470_, sizeof(void*)*3 + 1);
v_k_4098_ = lean_ctor_get(v_code_3470_, 2);
lean_inc(v_fvarId_4094_);
v___x_4099_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3471_, v_fvarId_4094_, v_t_3469_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v_fvarId_4100_; lean_object* v___x_4101_; 
v_fvarId_4100_ = lean_ctor_get(v___x_4099_, 0);
lean_inc(v_fvarId_4100_);
lean_dec_ref(v___x_4099_);
lean_inc_ref(v_k_4098_);
v___x_4101_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3468_, v_t_3469_, v_k_4098_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v_a_4102_; lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4144_; 
v_a_4102_ = lean_ctor_get(v___x_4101_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4101_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4104_ = v___x_4101_;
v_isShared_4105_ = v_isSharedCheck_4144_;
goto v_resetjp_4103_;
}
else
{
lean_inc(v_a_4102_);
lean_dec(v___x_4101_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4144_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
uint8_t v___y_4107_; size_t v___x_4140_; size_t v___x_4141_; uint8_t v___x_4142_; 
v___x_4140_ = lean_ptr_addr(v_fvarId_4094_);
v___x_4141_ = lean_ptr_addr(v_fvarId_4100_);
v___x_4142_ = lean_usize_dec_eq(v___x_4140_, v___x_4141_);
if (v___x_4142_ == 0)
{
v___y_4107_ = v___x_4142_;
goto v___jp_4106_;
}
else
{
uint8_t v___x_4143_; 
v___x_4143_ = lean_nat_dec_eq(v_n_4095_, v_n_4095_);
v___y_4107_ = v___x_4143_;
goto v___jp_4106_;
}
v___jp_4106_:
{
if (v___y_4107_ == 0)
{
lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4117_; 
lean_inc(v_n_4095_);
v_isSharedCheck_4117_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_4117_ == 0)
{
lean_object* v_unused_4118_; lean_object* v_unused_4119_; lean_object* v_unused_4120_; 
v_unused_4118_ = lean_ctor_get(v_code_3470_, 2);
lean_dec(v_unused_4118_);
v_unused_4119_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_4119_);
v_unused_4120_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_4120_);
v___x_4109_ = v_code_3470_;
v_isShared_4110_ = v_isSharedCheck_4117_;
goto v_resetjp_4108_;
}
else
{
lean_dec(v_code_3470_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4117_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
lean_ctor_set(v___x_4109_, 2, v_a_4102_);
lean_ctor_set(v___x_4109_, 0, v_fvarId_4100_);
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_fvarId_4100_);
lean_ctor_set(v_reuseFailAlloc_4116_, 1, v_n_4095_);
lean_ctor_set(v_reuseFailAlloc_4116_, 2, v_a_4102_);
lean_ctor_set_uint8(v_reuseFailAlloc_4116_, sizeof(void*)*3, v_check_4096_);
lean_ctor_set_uint8(v_reuseFailAlloc_4116_, sizeof(void*)*3 + 1, v_persistent_4097_);
v___x_4112_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
lean_object* v___x_4114_; 
if (v_isShared_4105_ == 0)
{
lean_ctor_set(v___x_4104_, 0, v___x_4112_);
v___x_4114_ = v___x_4104_;
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
size_t v___x_4121_; size_t v___x_4122_; uint8_t v___x_4123_; 
v___x_4121_ = lean_ptr_addr(v_k_4098_);
v___x_4122_ = lean_ptr_addr(v_a_4102_);
v___x_4123_ = lean_usize_dec_eq(v___x_4121_, v___x_4122_);
if (v___x_4123_ == 0)
{
lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4133_; 
lean_inc(v_n_4095_);
v_isSharedCheck_4133_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_4133_ == 0)
{
lean_object* v_unused_4134_; lean_object* v_unused_4135_; lean_object* v_unused_4136_; 
v_unused_4134_ = lean_ctor_get(v_code_3470_, 2);
lean_dec(v_unused_4134_);
v_unused_4135_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_4135_);
v_unused_4136_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_4136_);
v___x_4125_ = v_code_3470_;
v_isShared_4126_ = v_isSharedCheck_4133_;
goto v_resetjp_4124_;
}
else
{
lean_dec(v_code_3470_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4133_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4128_; 
if (v_isShared_4126_ == 0)
{
lean_ctor_set(v___x_4125_, 2, v_a_4102_);
lean_ctor_set(v___x_4125_, 0, v_fvarId_4100_);
v___x_4128_ = v___x_4125_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_fvarId_4100_);
lean_ctor_set(v_reuseFailAlloc_4132_, 1, v_n_4095_);
lean_ctor_set(v_reuseFailAlloc_4132_, 2, v_a_4102_);
lean_ctor_set_uint8(v_reuseFailAlloc_4132_, sizeof(void*)*3, v_check_4096_);
lean_ctor_set_uint8(v_reuseFailAlloc_4132_, sizeof(void*)*3 + 1, v_persistent_4097_);
v___x_4128_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
lean_object* v___x_4130_; 
if (v_isShared_4105_ == 0)
{
lean_ctor_set(v___x_4104_, 0, v___x_4128_);
v___x_4130_ = v___x_4104_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v___x_4128_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
}
else
{
lean_object* v___x_4138_; 
lean_dec(v_a_4102_);
lean_dec(v_fvarId_4100_);
if (v_isShared_4105_ == 0)
{
lean_ctor_set(v___x_4104_, 0, v_code_3470_);
v___x_4138_ = v___x_4104_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_code_3470_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
return v___x_4138_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4100_);
lean_dec_ref(v_code_3470_);
return v___x_4101_;
}
}
else
{
lean_object* v___x_4145_; 
lean_dec_ref(v_code_3470_);
v___x_4145_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3468_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
return v___x_4145_;
}
}
default: 
{
lean_object* v_fvarId_4146_; lean_object* v_k_4147_; lean_object* v___x_4148_; 
v_fvarId_4146_ = lean_ctor_get(v_code_3470_, 0);
v_k_4147_ = lean_ctor_get(v_code_3470_, 1);
lean_inc(v_fvarId_4146_);
v___x_4148_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3471_, v_fvarId_4146_, v_t_3469_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_fvarId_4149_; lean_object* v___x_4150_; 
v_fvarId_4149_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_fvarId_4149_);
lean_dec_ref(v___x_4148_);
lean_inc_ref(v_k_4147_);
v___x_4150_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3468_, v_t_3469_, v_k_4147_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_4150_) == 0)
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4178_; 
v_a_4151_ = lean_ctor_get(v___x_4150_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4150_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4153_ = v___x_4150_;
v_isShared_4154_ = v_isSharedCheck_4178_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_a_4151_);
lean_dec(v___x_4150_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4178_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
uint8_t v___y_4156_; size_t v___x_4172_; size_t v___x_4173_; uint8_t v___x_4174_; 
v___x_4172_ = lean_ptr_addr(v_fvarId_4146_);
v___x_4173_ = lean_ptr_addr(v_fvarId_4149_);
v___x_4174_ = lean_usize_dec_eq(v___x_4172_, v___x_4173_);
if (v___x_4174_ == 0)
{
v___y_4156_ = v___x_4174_;
goto v___jp_4155_;
}
else
{
size_t v___x_4175_; size_t v___x_4176_; uint8_t v___x_4177_; 
v___x_4175_ = lean_ptr_addr(v_k_4147_);
v___x_4176_ = lean_ptr_addr(v_a_4151_);
v___x_4177_ = lean_usize_dec_eq(v___x_4175_, v___x_4176_);
v___y_4156_ = v___x_4177_;
goto v___jp_4155_;
}
v___jp_4155_:
{
if (v___y_4156_ == 0)
{
lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4166_; 
v_isSharedCheck_4166_ = !lean_is_exclusive(v_code_3470_);
if (v_isSharedCheck_4166_ == 0)
{
lean_object* v_unused_4167_; lean_object* v_unused_4168_; 
v_unused_4167_ = lean_ctor_get(v_code_3470_, 1);
lean_dec(v_unused_4167_);
v_unused_4168_ = lean_ctor_get(v_code_3470_, 0);
lean_dec(v_unused_4168_);
v___x_4158_ = v_code_3470_;
v_isShared_4159_ = v_isSharedCheck_4166_;
goto v_resetjp_4157_;
}
else
{
lean_dec(v_code_3470_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4166_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4161_; 
if (v_isShared_4159_ == 0)
{
lean_ctor_set(v___x_4158_, 1, v_a_4151_);
lean_ctor_set(v___x_4158_, 0, v_fvarId_4149_);
v___x_4161_ = v___x_4158_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_fvarId_4149_);
lean_ctor_set(v_reuseFailAlloc_4165_, 1, v_a_4151_);
v___x_4161_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
lean_object* v___x_4163_; 
if (v_isShared_4154_ == 0)
{
lean_ctor_set(v___x_4153_, 0, v___x_4161_);
v___x_4163_ = v___x_4153_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v___x_4161_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
else
{
lean_object* v___x_4170_; 
lean_dec(v_a_4151_);
lean_dec(v_fvarId_4149_);
if (v_isShared_4154_ == 0)
{
lean_ctor_set(v___x_4153_, 0, v_code_3470_);
v___x_4170_ = v___x_4153_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_code_3470_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_4149_);
lean_dec_ref(v_code_3470_);
return v___x_4150_;
}
}
else
{
lean_object* v___x_4179_; 
lean_dec_ref(v_code_3470_);
v___x_4179_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3468_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
return v___x_4179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t v_pu_4180_, uint8_t v_t_4181_, lean_object* v_decl_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_){
_start:
{
lean_object* v_params_4189_; lean_object* v_type_4190_; lean_object* v_value_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; 
v_params_4189_ = lean_ctor_get(v_decl_4182_, 2);
v_type_4190_ = lean_ctor_get(v_decl_4182_, 3);
v_value_4191_ = lean_ctor_get(v_decl_4182_, 4);
lean_inc_ref(v_type_4190_);
v___x_4192_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4180_, v_a_4183_, v_t_4181_, v_type_4190_);
lean_inc_ref(v_params_4189_);
v___x_4193_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4180_, v_t_4181_, v_params_4189_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_, v_a_4187_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_object* v_a_4194_; lean_object* v___x_4195_; 
v_a_4194_ = lean_ctor_get(v___x_4193_, 0);
lean_inc(v_a_4194_);
lean_dec_ref(v___x_4193_);
lean_inc_ref(v_value_4191_);
v___x_4195_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4180_, v_t_4181_, v_value_4191_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_, v_a_4187_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4197_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
lean_inc(v_a_4196_);
lean_dec_ref(v___x_4195_);
v___x_4197_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_4180_, v_decl_4182_, v___x_4192_, v_a_4194_, v_a_4196_, v_a_4185_);
return v___x_4197_;
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
lean_dec(v_a_4194_);
lean_dec_ref(v___x_4192_);
lean_dec_ref(v_decl_4182_);
v_a_4198_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_4195_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4195_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
lean_dec_ref(v___x_4192_);
lean_dec_ref(v_decl_4182_);
v_a_4206_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4193_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4193_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp___boxed(lean_object* v_pu_4214_, lean_object* v_t_4215_, lean_object* v_decl_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_){
_start:
{
uint8_t v_pu_boxed_4223_; uint8_t v_t_boxed_4224_; lean_object* v_res_4225_; 
v_pu_boxed_4223_ = lean_unbox(v_pu_4214_);
v_t_boxed_4224_ = lean_unbox(v_t_4215_);
v_res_4225_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_boxed_4223_, v_t_boxed_4224_, v_decl_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_);
lean_dec(v_a_4221_);
lean_dec_ref(v_a_4220_);
lean_dec(v_a_4219_);
lean_dec_ref(v_a_4218_);
lean_dec_ref(v_a_4217_);
return v_res_4225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4___boxed(lean_object* v_pu_4226_, lean_object* v_t_4227_, lean_object* v_i_4228_, lean_object* v_as_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_){
_start:
{
uint8_t v_pu_boxed_4236_; uint8_t v_t_boxed_4237_; lean_object* v_res_4238_; 
v_pu_boxed_4236_ = lean_unbox(v_pu_4226_);
v_t_boxed_4237_ = lean_unbox(v_t_4227_);
v_res_4238_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_boxed_4236_, v_t_boxed_4237_, v_i_4228_, v_as_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
lean_dec_ref(v___y_4230_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp___boxed(lean_object* v_pu_4239_, lean_object* v_t_4240_, lean_object* v_code_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_){
_start:
{
uint8_t v_pu_boxed_4248_; uint8_t v_t_boxed_4249_; lean_object* v_res_4250_; 
v_pu_boxed_4248_ = lean_unbox(v_pu_4239_);
v_t_boxed_4249_ = lean_unbox(v_t_4240_);
v_res_4250_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_boxed_4248_, v_t_boxed_4249_, v_code_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
lean_dec(v_a_4246_);
lean_dec_ref(v_a_4245_);
lean_dec(v_a_4244_);
lean_dec_ref(v_a_4243_);
lean_dec_ref(v_a_4242_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(uint8_t v_pu_4251_, uint8_t v_t_4252_, uint8_t v_pu_4253_, uint8_t v_t_4254_, lean_object* v_decl_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
lean_object* v___x_4262_; 
v___x_4262_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_4253_, v_t_4254_, v_decl_4255_, v___y_4256_, v___y_4258_);
return v___x_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___boxed(lean_object* v_pu_4263_, lean_object* v_t_4264_, lean_object* v_pu_4265_, lean_object* v_t_4266_, lean_object* v_decl_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
uint8_t v_pu_boxed_4274_; uint8_t v_t_boxed_4275_; uint8_t v_pu_boxed_4276_; uint8_t v_t_boxed_4277_; lean_object* v_res_4278_; 
v_pu_boxed_4274_ = lean_unbox(v_pu_4263_);
v_t_boxed_4275_ = lean_unbox(v_t_4264_);
v_pu_boxed_4276_ = lean_unbox(v_pu_4265_);
v_t_boxed_4277_ = lean_unbox(v_t_4266_);
v_res_4278_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(v_pu_boxed_4274_, v_t_boxed_4275_, v_pu_boxed_4276_, v_t_boxed_4277_, v_decl_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec_ref(v___y_4268_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(uint8_t v_pu_4279_, uint8_t v_t_4280_, uint8_t v_pu_4281_, uint8_t v_t_4282_, lean_object* v_args_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_){
_start:
{
lean_object* v___x_4290_; 
v___x_4290_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_4281_, v_t_4282_, v_args_4283_, v___y_4284_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___boxed(lean_object* v_pu_4291_, lean_object* v_t_4292_, lean_object* v_pu_4293_, lean_object* v_t_4294_, lean_object* v_args_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
uint8_t v_pu_boxed_4302_; uint8_t v_t_boxed_4303_; uint8_t v_pu_boxed_4304_; uint8_t v_t_boxed_4305_; lean_object* v_res_4306_; 
v_pu_boxed_4302_ = lean_unbox(v_pu_4291_);
v_t_boxed_4303_ = lean_unbox(v_t_4292_);
v_pu_boxed_4304_ = lean_unbox(v_pu_4293_);
v_t_boxed_4305_ = lean_unbox(v_t_4294_);
v_res_4306_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(v_pu_boxed_4302_, v_t_boxed_4303_, v_pu_boxed_4304_, v_t_boxed_4305_, v_args_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
lean_dec(v___y_4300_);
lean_dec_ref(v___y_4299_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec_ref(v___y_4296_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(uint8_t v_pu_4307_, uint8_t v_t_4308_, uint8_t v_pu_4309_, uint8_t v_t_4310_, lean_object* v_ps_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4309_, v_t_4310_, v_ps_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___boxed(lean_object* v_pu_4319_, lean_object* v_t_4320_, lean_object* v_pu_4321_, lean_object* v_t_4322_, lean_object* v_ps_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
uint8_t v_pu_boxed_4330_; uint8_t v_t_boxed_4331_; uint8_t v_pu_boxed_4332_; uint8_t v_t_boxed_4333_; lean_object* v_res_4334_; 
v_pu_boxed_4330_ = lean_unbox(v_pu_4319_);
v_t_boxed_4331_ = lean_unbox(v_t_4320_);
v_pu_boxed_4332_ = lean_unbox(v_pu_4321_);
v_t_boxed_4333_ = lean_unbox(v_t_4322_);
v_res_4334_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(v_pu_boxed_4330_, v_t_boxed_4331_, v_pu_boxed_4332_, v_t_boxed_4333_, v_ps_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec_ref(v___y_4324_);
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(uint8_t v_pu_4335_, uint8_t v_t_4336_, lean_object* v_i_4337_, lean_object* v_as_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_){
_start:
{
lean_object* v___x_4345_; 
v___x_4345_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_4335_, v_t_4336_, v_i_4337_, v_as_4338_, v___y_4339_, v___y_4341_);
return v___x_4345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___boxed(lean_object* v_pu_4346_, lean_object* v_t_4347_, lean_object* v_i_4348_, lean_object* v_as_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
uint8_t v_pu_boxed_4356_; uint8_t v_t_boxed_4357_; lean_object* v_res_4358_; 
v_pu_boxed_4356_ = lean_unbox(v_pu_4346_);
v_t_boxed_4357_ = lean_unbox(v_t_4347_);
v_res_4358_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(v_pu_boxed_4356_, v_t_boxed_4357_, v_i_4348_, v_as_4349_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
lean_dec_ref(v___y_4350_);
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(uint8_t v_pu_4359_, uint8_t v_t_4360_, lean_object* v_decl_4361_, lean_object* v_inst_4362_, lean_object* v_____do__lift_4363_){
_start:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4364_ = lean_box(v_pu_4359_);
v___x_4365_ = lean_box(v_t_4360_);
v___x_4366_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDeclImp___boxed), 9, 4);
lean_closure_set(v___x_4366_, 0, v___x_4364_);
lean_closure_set(v___x_4366_, 1, v___x_4365_);
lean_closure_set(v___x_4366_, 2, v_decl_4361_);
lean_closure_set(v___x_4366_, 3, v_____do__lift_4363_);
v___x_4367_ = lean_apply_2(v_inst_4362_, lean_box(0), v___x_4366_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed(lean_object* v_pu_4368_, lean_object* v_t_4369_, lean_object* v_decl_4370_, lean_object* v_inst_4371_, lean_object* v_____do__lift_4372_){
_start:
{
uint8_t v_pu_boxed_4373_; uint8_t v_t_boxed_4374_; lean_object* v_res_4375_; 
v_pu_boxed_4373_ = lean_unbox(v_pu_4368_);
v_t_boxed_4374_ = lean_unbox(v_t_4369_);
v_res_4375_ = l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(v_pu_boxed_4373_, v_t_boxed_4374_, v_decl_4370_, v_inst_4371_, v_____do__lift_4372_);
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg(uint8_t v_pu_4376_, uint8_t v_t_4377_, lean_object* v_inst_4378_, lean_object* v_inst_4379_, lean_object* v_inst_4380_, lean_object* v_decl_4381_){
_start:
{
lean_object* v_toBind_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___f_4385_; lean_object* v___x_4386_; 
v_toBind_4382_ = lean_ctor_get(v_inst_4379_, 1);
lean_inc(v_toBind_4382_);
lean_dec_ref(v_inst_4379_);
v___x_4383_ = lean_box(v_pu_4376_);
v___x_4384_ = lean_box(v_t_4377_);
v___f_4385_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4385_, 0, v___x_4383_);
lean_closure_set(v___f_4385_, 1, v___x_4384_);
lean_closure_set(v___f_4385_, 2, v_decl_4381_);
lean_closure_set(v___f_4385_, 3, v_inst_4378_);
v___x_4386_ = lean_apply_4(v_toBind_4382_, lean_box(0), lean_box(0), v_inst_4380_, v___f_4385_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___boxed(lean_object* v_pu_4387_, lean_object* v_t_4388_, lean_object* v_inst_4389_, lean_object* v_inst_4390_, lean_object* v_inst_4391_, lean_object* v_decl_4392_){
_start:
{
uint8_t v_pu_boxed_4393_; uint8_t v_t_boxed_4394_; lean_object* v_res_4395_; 
v_pu_boxed_4393_ = lean_unbox(v_pu_4387_);
v_t_boxed_4394_ = lean_unbox(v_t_4388_);
v_res_4395_ = l_Lean_Compiler_LCNF_normFunDecl___redArg(v_pu_boxed_4393_, v_t_boxed_4394_, v_inst_4389_, v_inst_4390_, v_inst_4391_, v_decl_4392_);
return v_res_4395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl(lean_object* v_m_4396_, uint8_t v_pu_4397_, uint8_t v_t_4398_, lean_object* v_inst_4399_, lean_object* v_inst_4400_, lean_object* v_inst_4401_, lean_object* v_decl_4402_){
_start:
{
lean_object* v_toBind_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___f_4406_; lean_object* v___x_4407_; 
v_toBind_4403_ = lean_ctor_get(v_inst_4400_, 1);
lean_inc(v_toBind_4403_);
lean_dec_ref(v_inst_4400_);
v___x_4404_ = lean_box(v_pu_4397_);
v___x_4405_ = lean_box(v_t_4398_);
v___f_4406_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4406_, 0, v___x_4404_);
lean_closure_set(v___f_4406_, 1, v___x_4405_);
lean_closure_set(v___f_4406_, 2, v_decl_4402_);
lean_closure_set(v___f_4406_, 3, v_inst_4399_);
v___x_4407_ = lean_apply_4(v_toBind_4403_, lean_box(0), lean_box(0), v_inst_4401_, v___f_4406_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___boxed(lean_object* v_m_4408_, lean_object* v_pu_4409_, lean_object* v_t_4410_, lean_object* v_inst_4411_, lean_object* v_inst_4412_, lean_object* v_inst_4413_, lean_object* v_decl_4414_){
_start:
{
uint8_t v_pu_boxed_4415_; uint8_t v_t_boxed_4416_; lean_object* v_res_4417_; 
v_pu_boxed_4415_ = lean_unbox(v_pu_4409_);
v_t_boxed_4416_ = lean_unbox(v_t_4410_);
v_res_4417_ = l_Lean_Compiler_LCNF_normFunDecl(v_m_4408_, v_pu_boxed_4415_, v_t_boxed_4416_, v_inst_4411_, v_inst_4412_, v_inst_4413_, v_decl_4414_);
return v_res_4417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0(uint8_t v_pu_4418_, uint8_t v_t_4419_, lean_object* v_code_4420_, lean_object* v_inst_4421_, lean_object* v_____do__lift_4422_){
_start:
{
lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; 
v___x_4423_ = lean_box(v_pu_4418_);
v___x_4424_ = lean_box(v_t_4419_);
v___x_4425_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCodeImp___boxed), 9, 4);
lean_closure_set(v___x_4425_, 0, v___x_4423_);
lean_closure_set(v___x_4425_, 1, v___x_4424_);
lean_closure_set(v___x_4425_, 2, v_code_4420_);
lean_closure_set(v___x_4425_, 3, v_____do__lift_4422_);
v___x_4426_ = lean_apply_2(v_inst_4421_, lean_box(0), v___x_4425_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed(lean_object* v_pu_4427_, lean_object* v_t_4428_, lean_object* v_code_4429_, lean_object* v_inst_4430_, lean_object* v_____do__lift_4431_){
_start:
{
uint8_t v_pu_boxed_4432_; uint8_t v_t_boxed_4433_; lean_object* v_res_4434_; 
v_pu_boxed_4432_ = lean_unbox(v_pu_4427_);
v_t_boxed_4433_ = lean_unbox(v_t_4428_);
v_res_4434_ = l_Lean_Compiler_LCNF_normCode___redArg___lam__0(v_pu_boxed_4432_, v_t_boxed_4433_, v_code_4429_, v_inst_4430_, v_____do__lift_4431_);
return v_res_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg(uint8_t v_pu_4435_, uint8_t v_t_4436_, lean_object* v_inst_4437_, lean_object* v_inst_4438_, lean_object* v_inst_4439_, lean_object* v_code_4440_){
_start:
{
lean_object* v_toBind_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___f_4444_; lean_object* v___x_4445_; 
v_toBind_4441_ = lean_ctor_get(v_inst_4438_, 1);
lean_inc(v_toBind_4441_);
lean_dec_ref(v_inst_4438_);
v___x_4442_ = lean_box(v_pu_4435_);
v___x_4443_ = lean_box(v_t_4436_);
v___f_4444_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4444_, 0, v___x_4442_);
lean_closure_set(v___f_4444_, 1, v___x_4443_);
lean_closure_set(v___f_4444_, 2, v_code_4440_);
lean_closure_set(v___f_4444_, 3, v_inst_4437_);
v___x_4445_ = lean_apply_4(v_toBind_4441_, lean_box(0), lean_box(0), v_inst_4439_, v___f_4444_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___boxed(lean_object* v_pu_4446_, lean_object* v_t_4447_, lean_object* v_inst_4448_, lean_object* v_inst_4449_, lean_object* v_inst_4450_, lean_object* v_code_4451_){
_start:
{
uint8_t v_pu_boxed_4452_; uint8_t v_t_boxed_4453_; lean_object* v_res_4454_; 
v_pu_boxed_4452_ = lean_unbox(v_pu_4446_);
v_t_boxed_4453_ = lean_unbox(v_t_4447_);
v_res_4454_ = l_Lean_Compiler_LCNF_normCode___redArg(v_pu_boxed_4452_, v_t_boxed_4453_, v_inst_4448_, v_inst_4449_, v_inst_4450_, v_code_4451_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode(lean_object* v_m_4455_, uint8_t v_pu_4456_, uint8_t v_t_4457_, lean_object* v_inst_4458_, lean_object* v_inst_4459_, lean_object* v_inst_4460_, lean_object* v_code_4461_){
_start:
{
lean_object* v_toBind_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___f_4465_; lean_object* v___x_4466_; 
v_toBind_4462_ = lean_ctor_get(v_inst_4459_, 1);
lean_inc(v_toBind_4462_);
lean_dec_ref(v_inst_4459_);
v___x_4463_ = lean_box(v_pu_4456_);
v___x_4464_ = lean_box(v_t_4457_);
v___f_4465_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4465_, 0, v___x_4463_);
lean_closure_set(v___f_4465_, 1, v___x_4464_);
lean_closure_set(v___f_4465_, 2, v_code_4461_);
lean_closure_set(v___f_4465_, 3, v_inst_4458_);
v___x_4466_ = lean_apply_4(v_toBind_4462_, lean_box(0), lean_box(0), v_inst_4460_, v___f_4465_);
return v___x_4466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___boxed(lean_object* v_m_4467_, lean_object* v_pu_4468_, lean_object* v_t_4469_, lean_object* v_inst_4470_, lean_object* v_inst_4471_, lean_object* v_inst_4472_, lean_object* v_code_4473_){
_start:
{
uint8_t v_pu_boxed_4474_; uint8_t v_t_boxed_4475_; lean_object* v_res_4476_; 
v_pu_boxed_4474_ = lean_unbox(v_pu_4468_);
v_t_boxed_4475_ = lean_unbox(v_t_4469_);
v_res_4476_ = l_Lean_Compiler_LCNF_normCode(v_m_4467_, v_pu_boxed_4474_, v_t_boxed_4475_, v_inst_4470_, v_inst_4471_, v_inst_4472_, v_code_4473_);
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t v_pu_4477_, lean_object* v_e_4478_, lean_object* v_s_4479_, uint8_t v_translator_4480_){
_start:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; 
v___x_4482_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4477_, v_s_4479_, v_translator_4480_, v_e_4478_);
v___x_4483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4483_, 0, v___x_4482_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg___boxed(lean_object* v_pu_4484_, lean_object* v_e_4485_, lean_object* v_s_4486_, lean_object* v_translator_4487_, lean_object* v_a_4488_){
_start:
{
uint8_t v_pu_boxed_4489_; uint8_t v_translator_boxed_4490_; lean_object* v_res_4491_; 
v_pu_boxed_4489_ = lean_unbox(v_pu_4484_);
v_translator_boxed_4490_ = lean_unbox(v_translator_4487_);
v_res_4491_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_boxed_4489_, v_e_4485_, v_s_4486_, v_translator_boxed_4490_);
lean_dec_ref(v_s_4486_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(uint8_t v_pu_4492_, lean_object* v_e_4493_, lean_object* v_s_4494_, uint8_t v_translator_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_){
_start:
{
lean_object* v___x_4501_; 
v___x_4501_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_4492_, v_e_4493_, v_s_4494_, v_translator_4495_);
return v___x_4501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___boxed(lean_object* v_pu_4502_, lean_object* v_e_4503_, lean_object* v_s_4504_, lean_object* v_translator_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_){
_start:
{
uint8_t v_pu_boxed_4511_; uint8_t v_translator_boxed_4512_; lean_object* v_res_4513_; 
v_pu_boxed_4511_ = lean_unbox(v_pu_4502_);
v_translator_boxed_4512_ = lean_unbox(v_translator_4505_);
v_res_4513_ = l_Lean_Compiler_LCNF_replaceExprFVars(v_pu_boxed_4511_, v_e_4503_, v_s_4504_, v_translator_boxed_4512_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_);
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec_ref(v_a_4506_);
lean_dec_ref(v_s_4504_);
return v_res_4513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t v_pu_4514_, lean_object* v_code_4515_, lean_object* v_s_4516_, uint8_t v_translator_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_){
_start:
{
lean_object* v___x_4523_; 
v___x_4523_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4514_, v_translator_4517_, v_code_4515_, v_s_4516_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars___boxed(lean_object* v_pu_4524_, lean_object* v_code_4525_, lean_object* v_s_4526_, lean_object* v_translator_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_){
_start:
{
uint8_t v_pu_boxed_4533_; uint8_t v_translator_boxed_4534_; lean_object* v_res_4535_; 
v_pu_boxed_4533_ = lean_unbox(v_pu_4524_);
v_translator_boxed_4534_ = lean_unbox(v_translator_4527_);
v_res_4535_ = l_Lean_Compiler_LCNF_replaceFVars(v_pu_boxed_4533_, v_code_4525_, v_s_4526_, v_translator_boxed_4534_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_);
lean_dec(v_a_4531_);
lean_dec_ref(v_a_4530_);
lean_dec(v_a_4529_);
lean_dec_ref(v_a_4528_);
lean_dec_ref(v_s_4526_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg(lean_object* v_a_4539_){
_start:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4541_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1));
v___x_4542_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4541_, v_a_4539_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___boxed(lean_object* v_a_4543_, lean_object* v_a_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4543_);
lean_dec(v_a_4543_);
return v_res_4545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName(lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_){
_start:
{
lean_object* v___x_4551_; 
v___x_4551_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4547_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___boxed(lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_){
_start:
{
lean_object* v_res_4557_; 
v_res_4557_ = l_Lean_Compiler_LCNF_mkFreshJpName(v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_);
lean_dec(v_a_4555_);
lean_dec_ref(v_a_4554_);
lean_dec(v_a_4553_);
lean_dec_ref(v_a_4552_);
return v_res_4557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t v_pu_4558_, lean_object* v_type_4559_, uint8_t v_borrow_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_){
_start:
{
lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v_a_4568_; lean_object* v___x_4569_; 
v___x_4566_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_4567_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4566_, v_a_4562_);
v_a_4568_ = lean_ctor_get(v___x_4567_, 0);
lean_inc(v_a_4568_);
lean_dec_ref(v___x_4567_);
v___x_4569_ = l_Lean_Compiler_LCNF_mkParam(v_pu_4558_, v_a_4568_, v_type_4559_, v_borrow_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_);
return v___x_4569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam___boxed(lean_object* v_pu_4570_, lean_object* v_type_4571_, lean_object* v_borrow_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_){
_start:
{
uint8_t v_pu_boxed_4578_; uint8_t v_borrow_boxed_4579_; lean_object* v_res_4580_; 
v_pu_boxed_4578_ = lean_unbox(v_pu_4570_);
v_borrow_boxed_4579_ = lean_unbox(v_borrow_4572_);
v_res_4580_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_boxed_4578_, v_type_4571_, v_borrow_boxed_4579_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_);
lean_dec(v_a_4576_);
lean_dec_ref(v_a_4575_);
lean_dec(v_a_4574_);
lean_dec_ref(v_a_4573_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object* v_a_4581_){
_start:
{
lean_object* v_config_4583_; lean_object* v___x_4584_; 
v_config_4583_ = lean_ctor_get(v_a_4581_, 0);
lean_inc_ref(v_config_4583_);
v___x_4584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4584_, 0, v_config_4583_);
return v___x_4584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg___boxed(lean_object* v_a_4585_, lean_object* v_a_4586_){
_start:
{
lean_object* v_res_4587_; 
v_res_4587_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4585_);
lean_dec_ref(v_a_4585_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig(lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_){
_start:
{
lean_object* v___x_4593_; 
v___x_4593_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4588_);
return v___x_4593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___boxed(lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_){
_start:
{
lean_object* v_res_4599_; 
v_res_4599_ = l_Lean_Compiler_LCNF_getConfig(v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_);
lean_dec(v_a_4597_);
lean_dec_ref(v_a_4596_);
lean_dec(v_a_4595_);
lean_dec_ref(v_a_4594_);
return v_res_4599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object* v_x_4600_, lean_object* v_s_4601_, uint8_t v_phase_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_){
_start:
{
lean_object* v___x_4606_; lean_object* v_options_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; 
v___x_4606_ = lean_st_mk_ref(v_s_4601_);
v_options_4607_ = lean_ctor_get(v_a_4603_, 2);
v___x_4608_ = l_Lean_Compiler_LCNF_toConfigOptions(v_options_4607_);
v___x_4609_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4609_, 0, v___x_4608_);
lean_ctor_set_uint8(v___x_4609_, sizeof(void*)*1, v_phase_4602_);
lean_inc(v_a_4604_);
lean_inc_ref(v_a_4603_);
lean_inc(v___x_4606_);
v___x_4610_ = lean_apply_5(v_x_4600_, v___x_4609_, v___x_4606_, v_a_4603_, v_a_4604_, lean_box(0));
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4619_; 
v_a_4611_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4619_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4613_ = v___x_4610_;
v_isShared_4614_ = v_isSharedCheck_4619_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4610_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4619_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4615_; lean_object* v___x_4617_; 
v___x_4615_ = lean_st_ref_get(v___x_4606_);
lean_dec(v___x_4606_);
lean_dec(v___x_4615_);
if (v_isShared_4614_ == 0)
{
v___x_4617_ = v___x_4613_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v_a_4611_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
}
}
}
else
{
lean_dec(v___x_4606_);
return v___x_4610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg___boxed(lean_object* v_x_4620_, lean_object* v_s_4621_, lean_object* v_phase_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_){
_start:
{
uint8_t v_phase_boxed_4626_; lean_object* v_res_4627_; 
v_phase_boxed_4626_ = lean_unbox(v_phase_4622_);
v_res_4627_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4620_, v_s_4621_, v_phase_boxed_4626_, v_a_4623_, v_a_4624_);
lean_dec(v_a_4624_);
lean_dec_ref(v_a_4623_);
return v_res_4627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run(lean_object* v_00_u03b1_4628_, lean_object* v_x_4629_, lean_object* v_s_4630_, uint8_t v_phase_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_){
_start:
{
lean_object* v___x_4635_; 
v___x_4635_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4629_, v_s_4630_, v_phase_4631_, v_a_4632_, v_a_4633_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___boxed(lean_object* v_00_u03b1_4636_, lean_object* v_x_4637_, lean_object* v_s_4638_, lean_object* v_phase_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_){
_start:
{
uint8_t v_phase_boxed_4643_; lean_object* v_res_4644_; 
v_phase_boxed_4643_ = lean_unbox(v_phase_4639_);
v_res_4644_ = l_Lean_Compiler_LCNF_CompilerM_run(v_00_u03b1_4636_, v_x_4637_, v_s_4638_, v_phase_boxed_4643_, v_a_4640_, v_a_4641_);
lean_dec(v_a_4641_);
lean_dec_ref(v_a_4640_);
return v_res_4644_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0(void){
_start:
{
lean_object* v___x_4645_; 
v___x_4645_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_4645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_){
_start:
{
lean_object* v___x_4650_; 
v___x_4650_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_){
_start:
{
lean_object* v_res_4655_; 
v_res_4655_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_);
lean_dec_ref(v_a_4654_);
lean_dec_ref(v_a_4653_);
return v_res_4655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension(lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_){
_start:
{
lean_object* v___x_4660_; 
v___x_4660_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___boxed(lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension(v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
lean_dec_ref(v_a_4664_);
lean_dec_ref(v_a_4663_);
return v_res_4665_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4669_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2));
v___x_4670_ = lean_unsigned_to_nat(14u);
v___x_4671_ = lean_unsigned_to_nat(177u);
v___x_4672_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1));
v___x_4673_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0));
v___x_4674_ = l_mkPanicMessageWithDecl(v___x_4673_, v___x_4672_, v___x_4671_, v___x_4670_, v___x_4669_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(lean_object* v_inst_4675_, lean_object* v_inst_4676_, lean_object* v_snd_4677_, lean_object* v_inst_4678_, lean_object* v_s_4679_, lean_object* v_e_4680_){
_start:
{
lean_object* v_fst_4681_; lean_object* v_snd_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4697_; 
v_fst_4681_ = lean_ctor_get(v_s_4679_, 0);
v_snd_4682_ = lean_ctor_get(v_s_4679_, 1);
v_isSharedCheck_4697_ = !lean_is_exclusive(v_s_4679_);
if (v_isSharedCheck_4697_ == 0)
{
v___x_4684_ = v_s_4679_;
v_isShared_4685_ = v_isSharedCheck_4697_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_snd_4682_);
lean_inc(v_fst_4681_);
lean_dec(v_s_4679_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4697_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4686_; lean_object* v___y_4688_; lean_object* v___x_4693_; 
lean_inc(v_e_4680_);
v___x_4686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4686_, 0, v_e_4680_);
lean_ctor_set(v___x_4686_, 1, v_fst_4681_);
lean_inc(v_e_4680_);
lean_inc_ref(v_inst_4676_);
lean_inc_ref(v_inst_4675_);
v___x_4693_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4675_, v_inst_4676_, v_snd_4677_, v_e_4680_);
if (lean_obj_tag(v___x_4693_) == 0)
{
lean_object* v___x_4694_; lean_object* v___x_4695_; 
v___x_4694_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3);
v___x_4695_ = l_panic___redArg(v_inst_4678_, v___x_4694_);
v___y_4688_ = v___x_4695_;
goto v___jp_4687_;
}
else
{
lean_object* v_val_4696_; 
lean_dec(v_inst_4678_);
v_val_4696_ = lean_ctor_get(v___x_4693_, 0);
lean_inc(v_val_4696_);
lean_dec_ref(v___x_4693_);
v___y_4688_ = v_val_4696_;
goto v___jp_4687_;
}
v___jp_4687_:
{
lean_object* v___x_4689_; lean_object* v___x_4691_; 
v___x_4689_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4675_, v_inst_4676_, v_snd_4682_, v_e_4680_, v___y_4688_);
if (v_isShared_4685_ == 0)
{
lean_ctor_set(v___x_4684_, 1, v___x_4689_);
lean_ctor_set(v___x_4684_, 0, v___x_4686_);
v___x_4691_ = v___x_4684_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v___x_4686_);
lean_ctor_set(v_reuseFailAlloc_4692_, 1, v___x_4689_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
return v___x_4691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(lean_object* v_inst_4700_, lean_object* v_inst_4701_, lean_object* v_inst_4702_, lean_object* v_oldState_4703_, lean_object* v_newState_4704_, lean_object* v_x_4705_, lean_object* v_s_4706_){
_start:
{
lean_object* v_fst_4707_; lean_object* v_snd_4708_; lean_object* v_fst_4709_; lean_object* v___f_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v_newEntries_4715_; lean_object* v___x_4716_; 
v_fst_4707_ = lean_ctor_get(v_newState_4704_, 0);
lean_inc(v_fst_4707_);
v_snd_4708_ = lean_ctor_get(v_newState_4704_, 1);
lean_inc(v_snd_4708_);
lean_dec_ref(v_newState_4704_);
v_fst_4709_ = lean_ctor_get(v_oldState_4703_, 0);
v___f_4710_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0), 6, 4);
lean_closure_set(v___f_4710_, 0, v_inst_4700_);
lean_closure_set(v___f_4710_, 1, v_inst_4701_);
lean_closure_set(v___f_4710_, 2, v_snd_4708_);
lean_closure_set(v___f_4710_, 3, v_inst_4702_);
v___x_4711_ = l_List_lengthTR___redArg(v_fst_4707_);
v___x_4712_ = l_List_lengthTR___redArg(v_fst_4709_);
v___x_4713_ = lean_nat_sub(v___x_4711_, v___x_4712_);
lean_dec(v___x_4712_);
lean_dec(v___x_4711_);
v___x_4714_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0));
lean_inc(v_fst_4707_);
v_newEntries_4715_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_fst_4707_, v_fst_4707_, v___x_4713_, v___x_4714_);
lean_dec(v_fst_4707_);
v___x_4716_ = l_List_foldl___redArg(v___f_4710_, v_s_4706_, v_newEntries_4715_);
return v___x_4716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(lean_object* v_inst_4717_, lean_object* v_inst_4718_, lean_object* v_inst_4719_, lean_object* v_oldState_4720_, lean_object* v_newState_4721_, lean_object* v_x_4722_, lean_object* v_s_4723_){
_start:
{
lean_object* v_res_4724_; 
v_res_4724_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(v_inst_4717_, v_inst_4718_, v_inst_4719_, v_oldState_4720_, v_newState_4721_, v_x_4722_, v_s_4723_);
lean_dec(v_x_4722_);
lean_dec_ref(v_oldState_4720_);
return v_res_4724_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0(void){
_start:
{
lean_object* v___x_4725_; 
v___x_4725_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4725_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1(void){
_start:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4726_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0);
v___x_4727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4727_, 0, v___x_4726_);
return v___x_4727_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2(void){
_start:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; 
v___x_4728_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1);
v___x_4729_ = lean_box(0);
v___x_4730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4730_, 0, v___x_4729_);
lean_ctor_set(v___x_4730_, 1, v___x_4728_);
return v___x_4730_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3(void){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; 
v___x_4731_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2);
v___x_4732_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_4732_, 0, lean_box(0));
lean_closure_set(v___x_4732_, 1, lean_box(0));
lean_closure_set(v___x_4732_, 2, v___x_4731_);
return v___x_4732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object* v_inst_4733_, lean_object* v_inst_4734_, lean_object* v_inst_4735_){
_start:
{
lean_object* v___f_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v___f_4737_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4737_, 0, v_inst_4733_);
lean_closure_set(v___f_4737_, 1, v_inst_4734_);
lean_closure_set(v___f_4737_, 2, v_inst_4735_);
v___x_4738_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3);
v___x_4739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4739_, 0, v___f_4737_);
v___x_4740_ = lean_box(0);
v___x_4741_ = l_Lean_registerEnvExtension___redArg(v___x_4738_, v___x_4739_, v___x_4740_);
if (lean_obj_tag(v___x_4741_) == 0)
{
lean_object* v_a_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4749_; 
v_a_4742_ = lean_ctor_get(v___x_4741_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4741_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4744_ = v___x_4741_;
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_a_4742_);
lean_dec(v___x_4741_);
v___x_4744_ = lean_box(0);
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
v_resetjp_4743_:
{
lean_object* v___x_4747_; 
if (v_isShared_4745_ == 0)
{
v___x_4747_ = v___x_4744_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_a_4742_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
else
{
lean_object* v_a_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4757_; 
v_a_4750_ = lean_ctor_get(v___x_4741_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4741_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4752_ = v___x_4741_;
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_a_4750_);
lean_dec(v___x_4741_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v___x_4755_; 
if (v_isShared_4753_ == 0)
{
v___x_4755_ = v___x_4752_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_a_4750_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object* v_inst_4758_, lean_object* v_inst_4759_, lean_object* v_inst_4760_, lean_object* v_a_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4758_, v_inst_4759_, v_inst_4760_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object* v_00_u03b1_4763_, lean_object* v_00_u03b2_4764_, lean_object* v_inst_4765_, lean_object* v_inst_4766_, lean_object* v_inst_4767_){
_start:
{
lean_object* v___x_4769_; 
v___x_4769_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4765_, v_inst_4766_, v_inst_4767_);
return v___x_4769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object* v_00_u03b1_4770_, lean_object* v_00_u03b2_4771_, lean_object* v_inst_4772_, lean_object* v_inst_4773_, lean_object* v_inst_4774_, lean_object* v_a_4775_){
_start:
{
lean_object* v_res_4776_; 
v_res_4776_ = l_Lean_Compiler_LCNF_CacheExtension_register(v_00_u03b1_4770_, v_00_u03b2_4771_, v_inst_4772_, v_inst_4773_, v_inst_4774_);
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object* v_a_4777_, lean_object* v_inst_4778_, lean_object* v_inst_4779_, lean_object* v_b_4780_, lean_object* v_x_4781_){
_start:
{
lean_object* v_fst_4782_; lean_object* v_snd_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4792_; 
v_fst_4782_ = lean_ctor_get(v_x_4781_, 0);
v_snd_4783_ = lean_ctor_get(v_x_4781_, 1);
v_isSharedCheck_4792_ = !lean_is_exclusive(v_x_4781_);
if (v_isSharedCheck_4792_ == 0)
{
v___x_4785_ = v_x_4781_;
v_isShared_4786_ = v_isSharedCheck_4792_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_snd_4783_);
lean_inc(v_fst_4782_);
lean_dec(v_x_4781_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4792_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4790_; 
lean_inc(v_a_4777_);
v___x_4787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4787_, 0, v_a_4777_);
lean_ctor_set(v___x_4787_, 1, v_fst_4782_);
v___x_4788_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4778_, v_inst_4779_, v_snd_4783_, v_a_4777_, v_b_4780_);
if (v_isShared_4786_ == 0)
{
lean_ctor_set(v___x_4785_, 1, v___x_4788_);
lean_ctor_set(v___x_4785_, 0, v___x_4787_);
v___x_4790_ = v___x_4785_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v___x_4787_);
lean_ctor_set(v_reuseFailAlloc_4791_, 1, v___x_4788_);
v___x_4790_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
return v___x_4790_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_4793_; 
v___x_4793_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4793_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___x_4794_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0);
v___x_4795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4795_, 0, v___x_4794_);
return v___x_4795_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2(void){
_start:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4796_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1);
v___x_4797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4797_, 0, v___x_4796_);
lean_ctor_set(v___x_4797_, 1, v___x_4796_);
return v___x_4797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object* v_inst_4798_, lean_object* v_inst_4799_, lean_object* v_ext_4800_, lean_object* v_a_4801_, lean_object* v_b_4802_, lean_object* v_a_4803_){
_start:
{
lean_object* v___x_4805_; lean_object* v_env_4806_; lean_object* v_nextMacroScope_4807_; lean_object* v_ngen_4808_; lean_object* v_auxDeclNGen_4809_; lean_object* v_traceState_4810_; lean_object* v_messages_4811_; lean_object* v_infoState_4812_; lean_object* v_snapshotTasks_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4828_; 
v___x_4805_ = lean_st_ref_take(v_a_4803_);
v_env_4806_ = lean_ctor_get(v___x_4805_, 0);
v_nextMacroScope_4807_ = lean_ctor_get(v___x_4805_, 1);
v_ngen_4808_ = lean_ctor_get(v___x_4805_, 2);
v_auxDeclNGen_4809_ = lean_ctor_get(v___x_4805_, 3);
v_traceState_4810_ = lean_ctor_get(v___x_4805_, 4);
v_messages_4811_ = lean_ctor_get(v___x_4805_, 6);
v_infoState_4812_ = lean_ctor_get(v___x_4805_, 7);
v_snapshotTasks_4813_ = lean_ctor_get(v___x_4805_, 8);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4805_);
if (v_isSharedCheck_4828_ == 0)
{
lean_object* v_unused_4829_; 
v_unused_4829_ = lean_ctor_get(v___x_4805_, 5);
lean_dec(v_unused_4829_);
v___x_4815_ = v___x_4805_;
v_isShared_4816_ = v_isSharedCheck_4828_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_snapshotTasks_4813_);
lean_inc(v_infoState_4812_);
lean_inc(v_messages_4811_);
lean_inc(v_traceState_4810_);
lean_inc(v_auxDeclNGen_4809_);
lean_inc(v_ngen_4808_);
lean_inc(v_nextMacroScope_4807_);
lean_inc(v_env_4806_);
lean_dec(v___x_4805_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4828_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v_asyncMode_4817_; lean_object* v___f_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4823_; 
v_asyncMode_4817_ = lean_ctor_get(v_ext_4800_, 2);
lean_inc(v_asyncMode_4817_);
v___f_4818_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4818_, 0, v_a_4801_);
lean_closure_set(v___f_4818_, 1, v_inst_4798_);
lean_closure_set(v___f_4818_, 2, v_inst_4799_);
lean_closure_set(v___f_4818_, 3, v_b_4802_);
v___x_4819_ = lean_box(0);
v___x_4820_ = l_Lean_EnvExtension_modifyState___redArg(v_ext_4800_, v_env_4806_, v___f_4818_, v_asyncMode_4817_, v___x_4819_);
lean_dec(v_asyncMode_4817_);
v___x_4821_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2);
if (v_isShared_4816_ == 0)
{
lean_ctor_set(v___x_4815_, 5, v___x_4821_);
lean_ctor_set(v___x_4815_, 0, v___x_4820_);
v___x_4823_ = v___x_4815_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v___x_4820_);
lean_ctor_set(v_reuseFailAlloc_4827_, 1, v_nextMacroScope_4807_);
lean_ctor_set(v_reuseFailAlloc_4827_, 2, v_ngen_4808_);
lean_ctor_set(v_reuseFailAlloc_4827_, 3, v_auxDeclNGen_4809_);
lean_ctor_set(v_reuseFailAlloc_4827_, 4, v_traceState_4810_);
lean_ctor_set(v_reuseFailAlloc_4827_, 5, v___x_4821_);
lean_ctor_set(v_reuseFailAlloc_4827_, 6, v_messages_4811_);
lean_ctor_set(v_reuseFailAlloc_4827_, 7, v_infoState_4812_);
lean_ctor_set(v_reuseFailAlloc_4827_, 8, v_snapshotTasks_4813_);
v___x_4823_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4824_ = lean_st_ref_set(v_a_4803_, v___x_4823_);
v___x_4825_ = lean_box(0);
v___x_4826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4825_);
return v___x_4826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object* v_inst_4830_, lean_object* v_inst_4831_, lean_object* v_ext_4832_, lean_object* v_a_4833_, lean_object* v_b_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_){
_start:
{
lean_object* v_res_4837_; 
v_res_4837_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4830_, v_inst_4831_, v_ext_4832_, v_a_4833_, v_b_4834_, v_a_4835_);
lean_dec(v_a_4835_);
return v_res_4837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object* v_00_u03b1_4838_, lean_object* v_00_u03b2_4839_, lean_object* v_inst_4840_, lean_object* v_inst_4841_, lean_object* v_inst_4842_, lean_object* v_ext_4843_, lean_object* v_a_4844_, lean_object* v_b_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_){
_start:
{
lean_object* v___x_4849_; 
v___x_4849_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4840_, v_inst_4841_, v_ext_4843_, v_a_4844_, v_b_4845_, v_a_4847_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object* v_00_u03b1_4850_, lean_object* v_00_u03b2_4851_, lean_object* v_inst_4852_, lean_object* v_inst_4853_, lean_object* v_inst_4854_, lean_object* v_ext_4855_, lean_object* v_a_4856_, lean_object* v_b_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_){
_start:
{
lean_object* v_res_4861_; 
v_res_4861_ = l_Lean_Compiler_LCNF_CacheExtension_insert(v_00_u03b1_4850_, v_00_u03b2_4851_, v_inst_4852_, v_inst_4853_, v_inst_4854_, v_ext_4855_, v_a_4856_, v_b_4857_, v_a_4858_, v_a_4859_);
lean_dec(v_a_4859_);
lean_dec_ref(v_a_4858_);
lean_dec(v_inst_4854_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(lean_object* v_inst_4862_, lean_object* v_inst_4863_, lean_object* v_ext_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_){
_start:
{
lean_object* v___x_4868_; lean_object* v_env_4869_; lean_object* v_asyncMode_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v_snd_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; 
v___x_4868_ = lean_st_ref_get(v_a_4866_);
v_env_4869_ = lean_ctor_get(v___x_4868_, 0);
lean_inc_ref(v_env_4869_);
lean_dec(v___x_4868_);
v_asyncMode_4870_ = lean_ctor_get(v_ext_4864_, 2);
v___x_4871_ = lean_box(0);
v___x_4872_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v_inst_4862_, v_inst_4863_);
v___x_4873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4871_);
lean_ctor_set(v___x_4873_, 1, v___x_4872_);
v___x_4874_ = lean_box(0);
v___x_4875_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4873_, v_ext_4864_, v_env_4869_, v_asyncMode_4870_, v___x_4874_);
v_snd_4876_ = lean_ctor_get(v___x_4875_, 1);
lean_inc(v_snd_4876_);
lean_dec(v___x_4875_);
v___x_4877_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4862_, v_inst_4863_, v_snd_4876_, v_a_4865_);
v___x_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4877_);
return v___x_4878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(lean_object* v_inst_4879_, lean_object* v_inst_4880_, lean_object* v_ext_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_){
_start:
{
lean_object* v_res_4885_; 
v_res_4885_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4879_, v_inst_4880_, v_ext_4881_, v_a_4882_, v_a_4883_);
lean_dec(v_a_4883_);
lean_dec_ref(v_ext_4881_);
return v_res_4885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_object* v_00_u03b1_4886_, lean_object* v_00_u03b2_4887_, lean_object* v_inst_4888_, lean_object* v_inst_4889_, lean_object* v_inst_4890_, lean_object* v_ext_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_){
_start:
{
lean_object* v___x_4896_; 
v___x_4896_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4888_, v_inst_4889_, v_ext_4891_, v_a_4892_, v_a_4894_);
return v___x_4896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(lean_object* v_00_u03b1_4897_, lean_object* v_00_u03b2_4898_, lean_object* v_inst_4899_, lean_object* v_inst_4900_, lean_object* v_inst_4901_, lean_object* v_ext_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_){
_start:
{
lean_object* v_res_4907_; 
v_res_4907_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f(v_00_u03b1_4897_, v_00_u03b2_4898_, v_inst_4899_, v_inst_4900_, v_inst_4901_, v_ext_4902_, v_a_4903_, v_a_4904_, v_a_4905_);
lean_dec(v_a_4905_);
lean_dec_ref(v_a_4904_);
lean_dec_ref(v_ext_4902_);
lean_dec(v_inst_4901_);
return v_res_4907_;
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
