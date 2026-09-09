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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
uint8_t v_x_20__boxed_82_; uint8_t v_y_21__boxed_83_; uint8_t v_res_84_; lean_object* v_r_85_; 
v_x_20__boxed_82_ = lean_unbox(v_x_80_);
v_y_21__boxed_83_ = lean_unbox(v_y_81_);
v_res_84_ = l_Lean_Compiler_LCNF_instDecidableEqPhase(v_x_20__boxed_82_, v_y_21__boxed_83_);
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
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_box(0);
v___x_94_ = lean_unsigned_to_nat(16u);
v___x_95_ = lean_mk_array(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0);
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1);
v___x_100_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
lean_ctor_set(v___x_100_, 2, v___x_99_);
lean_ctor_set(v___x_100_, 3, v___x_99_);
lean_ctor_set(v___x_100_, 4, v___x_99_);
lean_ctor_set(v___x_100_, 5, v___x_99_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_101_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default(void){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState(void){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default;
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0(void){
_start:
{
lean_object* v___x_106_; uint8_t v___x_107_; lean_object* v___x_108_; 
v___x_106_ = l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default;
v___x_107_ = 0;
v___x_108_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*1, v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default(void){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext(void){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default;
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(lean_object* v_00_u03b1_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v___y_112_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object* v_00_u03b1_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(v_00_u03b1_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object* v_00_u03b1_127_, lean_object* v_00_u03b2_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v___x_136_; 
lean_inc(v___y_134_);
lean_inc_ref(v___y_133_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
v___x_136_ = lean_apply_5(v___y_129_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, lean_box(0));
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v_a_137_; lean_object* v___x_138_; 
v_a_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_a_137_);
lean_dec_ref_known(v___x_136_, 1);
lean_inc(v___y_134_);
lean_inc_ref(v___y_133_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
v___x_138_ = lean_apply_6(v___y_130_, v_a_137_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, lean_box(0));
return v___x_138_;
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec_ref(v___y_130_);
v_a_139_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_136_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_136_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object* v_00_u03b1_147_, lean_object* v_00_u03b2_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(v_00_u03b1_147_, v_00_u03b2_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
return v_res_156_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0(void){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_instMonadEIO(lean_box(0));
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0);
v___x_159_ = l_StateRefT_x27_instMonad___redArg(v___x_158_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM(void){
_start:
{
lean_object* v___x_164_; lean_object* v_toApplicative_165_; lean_object* v_toFunctor_166_; lean_object* v_toSeq_167_; lean_object* v_toSeqLeft_168_; lean_object* v_toSeqRight_169_; lean_object* v___f_170_; lean_object* v___f_171_; lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___x_174_; lean_object* v___f_175_; lean_object* v___f_176_; lean_object* v___f_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v_toApplicative_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_208_; 
v___x_164_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_165_ = lean_ctor_get(v___x_164_, 0);
v_toFunctor_166_ = lean_ctor_get(v_toApplicative_165_, 0);
v_toSeq_167_ = lean_ctor_get(v_toApplicative_165_, 2);
v_toSeqLeft_168_ = lean_ctor_get(v_toApplicative_165_, 3);
v_toSeqRight_169_ = lean_ctor_get(v_toApplicative_165_, 4);
v___f_170_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_171_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_166_, 2);
v___f_172_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_172_, 0, v_toFunctor_166_);
v___f_173_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_173_, 0, v_toFunctor_166_);
v___x_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_174_, 0, v___f_172_);
lean_ctor_set(v___x_174_, 1, v___f_173_);
lean_inc(v_toSeqRight_169_);
v___f_175_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_175_, 0, v_toSeqRight_169_);
lean_inc(v_toSeqLeft_168_);
v___f_176_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_176_, 0, v_toSeqLeft_168_);
lean_inc(v_toSeq_167_);
v___f_177_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_177_, 0, v_toSeq_167_);
v___x_178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_178_, 0, v___x_174_);
lean_ctor_set(v___x_178_, 1, v___f_170_);
lean_ctor_set(v___x_178_, 2, v___f_177_);
lean_ctor_set(v___x_178_, 3, v___f_176_);
lean_ctor_set(v___x_178_, 4, v___f_175_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___f_171_);
v___x_180_ = l_StateRefT_x27_instMonad___redArg(v___x_179_);
v_toApplicative_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_208_ == 0)
{
lean_object* v_unused_209_; 
v_unused_209_ = lean_ctor_get(v___x_180_, 1);
lean_dec(v_unused_209_);
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_208_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_toApplicative_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_208_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v_toFunctor_185_; lean_object* v_toSeq_186_; lean_object* v_toSeqLeft_187_; lean_object* v_toSeqRight_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_206_; 
v_toFunctor_185_ = lean_ctor_get(v_toApplicative_181_, 0);
v_toSeq_186_ = lean_ctor_get(v_toApplicative_181_, 2);
v_toSeqLeft_187_ = lean_ctor_get(v_toApplicative_181_, 3);
v_toSeqRight_188_ = lean_ctor_get(v_toApplicative_181_, 4);
v_isSharedCheck_206_ = !lean_is_exclusive(v_toApplicative_181_);
if (v_isSharedCheck_206_ == 0)
{
lean_object* v_unused_207_; 
v_unused_207_ = lean_ctor_get(v_toApplicative_181_, 1);
lean_dec(v_unused_207_);
v___x_190_ = v_toApplicative_181_;
v_isShared_191_ = v_isSharedCheck_206_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_toSeqRight_188_);
lean_inc(v_toSeqLeft_187_);
lean_inc(v_toSeq_186_);
lean_inc(v_toFunctor_185_);
lean_dec(v_toApplicative_181_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_206_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___f_192_; lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___x_196_; lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___x_201_; 
v___f_192_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_193_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_185_);
v___f_194_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_194_, 0, v_toFunctor_185_);
v___f_195_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_195_, 0, v_toFunctor_185_);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___f_194_);
lean_ctor_set(v___x_196_, 1, v___f_195_);
v___f_197_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_197_, 0, v_toSeqRight_188_);
v___f_198_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_198_, 0, v_toSeqLeft_187_);
v___f_199_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_199_, 0, v_toSeq_186_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 4, v___f_197_);
lean_ctor_set(v___x_190_, 3, v___f_198_);
lean_ctor_set(v___x_190_, 2, v___f_199_);
lean_ctor_set(v___x_190_, 1, v___f_192_);
lean_ctor_set(v___x_190_, 0, v___x_196_);
v___x_201_ = v___x_190_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___f_192_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v___f_199_);
lean_ctor_set(v_reuseFailAlloc_205_, 3, v___f_198_);
lean_ctor_set(v_reuseFailAlloc_205_, 4, v___f_197_);
v___x_201_ = v_reuseFailAlloc_205_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_203_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v___f_193_);
lean_ctor_set(v___x_183_, 0, v___x_201_);
v___x_203_ = v___x_183_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v___f_193_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg(uint8_t v_phase_210_, lean_object* v_x_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_config_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_config_217_ = lean_ctor_get(v_a_212_, 0);
lean_inc_ref(v_config_217_);
v___x_218_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_218_, 0, v_config_217_);
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*1, v_phase_210_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
v___x_219_ = lean_apply_5(v_x_211_, v___x_218_, v_a_213_, v_a_214_, v_a_215_, lean_box(0));
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg___boxed(lean_object* v_phase_220_, lean_object* v_x_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
uint8_t v_phase_boxed_227_; lean_object* v_res_228_; 
v_phase_boxed_227_ = lean_unbox(v_phase_220_);
v_res_228_ = l_Lean_Compiler_LCNF_withPhase___redArg(v_phase_boxed_227_, v_x_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase(lean_object* v_00_u03b1_229_, uint8_t v_phase_230_, lean_object* v_x_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_config_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_config_237_ = lean_ctor_get(v_a_232_, 0);
lean_inc_ref(v_config_237_);
v___x_238_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_238_, 0, v_config_237_);
lean_ctor_set_uint8(v___x_238_, sizeof(void*)*1, v_phase_230_);
lean_inc(v_a_235_);
lean_inc_ref(v_a_234_);
lean_inc(v_a_233_);
v___x_239_ = lean_apply_5(v_x_231_, v___x_238_, v_a_233_, v_a_234_, v_a_235_, lean_box(0));
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___boxed(lean_object* v_00_u03b1_240_, lean_object* v_phase_241_, lean_object* v_x_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
uint8_t v_phase_boxed_248_; lean_object* v_res_249_; 
v_phase_boxed_248_ = lean_unbox(v_phase_241_);
v_res_249_ = l_Lean_Compiler_LCNF_withPhase(v_00_u03b1_240_, v_phase_boxed_248_, v_x_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object* v_a_250_){
_start:
{
uint8_t v_phase_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_phase_252_ = lean_ctor_get_uint8(v_a_250_, sizeof(void*)*1);
v___x_253_ = lean_box(v_phase_252_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg___boxed(lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_255_);
lean_dec_ref(v_a_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase(lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_258_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___boxed(lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Compiler_LCNF_getPhase(v_a_264_, v_a_265_, v_a_266_, v_a_267_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object* v_a_270_){
_start:
{
lean_object* v___x_272_; lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_283_; 
v___x_272_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_270_);
v_a_273_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_283_ == 0)
{
v___x_275_ = v___x_272_;
v_isShared_276_ = v_isSharedCheck_283_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_283_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
uint8_t v___x_277_; uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_277_ = lean_unbox(v_a_273_);
lean_dec(v_a_273_);
v___x_278_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_277_);
v___x_279_ = lean_box(v___x_278_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_279_);
v___x_281_ = v___x_275_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg___boxed(lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_284_);
lean_dec_ref(v_a_284_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity(lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_287_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___boxed(lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Compiler_LCNF_getPurity(v_a_293_, v_a_294_, v_a_295_, v_a_296_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg(lean_object* v_a_299_){
_start:
{
lean_object* v___x_301_; lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_317_; 
v___x_301_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_299_);
v_a_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_317_ == 0)
{
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_317_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_317_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
uint8_t v___x_306_; 
v___x_306_ = lean_unbox(v_a_302_);
lean_dec(v_a_302_);
if (v___x_306_ == 0)
{
uint8_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_307_ = 1;
v___x_308_ = lean_box(v___x_307_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_308_);
v___x_310_ = v___x_304_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
else
{
uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_312_ = 0;
v___x_313_ = lean_box(v___x_312_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_313_);
v___x_315_ = v___x_304_;
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg___boxed(lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_318_);
lean_dec_ref(v_a_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase(lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_321_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___boxed(lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_Compiler_LCNF_inBasePhase(v_a_327_, v_a_328_, v_a_329_, v_a_330_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
return v_res_332_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0(void){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_333_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
lean_ctor_set(v___x_338_, 2, v___x_337_);
lean_ctor_set(v___x_338_, 3, v___x_337_);
lean_ctor_set(v___x_338_, 4, v___x_336_);
lean_ctor_set(v___x_338_, 5, v___x_336_);
lean_ctor_set(v___x_338_, 6, v___x_336_);
lean_ctor_set(v___x_338_, 7, v___x_336_);
lean_ctor_set(v___x_338_, 8, v___x_336_);
lean_ctor_set(v___x_338_, 9, v___x_336_);
lean_ctor_set(v___x_338_, 10, v___x_336_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(lean_object* v_msgData_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = lean_st_ref_get(v___y_343_);
v___x_346_ = lean_st_ref_get(v___y_341_);
v___x_347_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_340_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_toCold_348_; lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_371_; 
v_toCold_348_ = lean_ctor_get(v___y_342_, 0);
v_a_349_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_371_ == 0)
{
v___x_351_ = v___x_347_;
v_isShared_352_ = v_isSharedCheck_371_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_347_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_371_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v_env_353_; lean_object* v_lctx_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_369_; 
v_env_353_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref(v_env_353_);
lean_dec(v___x_345_);
v_lctx_354_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; 
v_unused_370_ = lean_ctor_get(v___x_346_, 1);
lean_dec(v_unused_370_);
v___x_356_ = v___x_346_;
v_isShared_357_ = v_isSharedCheck_369_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_lctx_354_);
lean_dec(v___x_346_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_369_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v_options_358_; uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
v_options_358_ = lean_ctor_get(v_toCold_348_, 2);
v___x_359_ = lean_unbox(v_a_349_);
lean_dec(v_a_349_);
v___x_360_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_354_, v___x_359_);
lean_dec_ref(v_lctx_354_);
v___x_361_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_358_);
v___x_362_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_362_, 0, v_env_353_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
lean_ctor_set(v___x_362_, 2, v___x_360_);
lean_ctor_set(v___x_362_, 3, v_options_358_);
if (v_isShared_357_ == 0)
{
lean_ctor_set_tag(v___x_356_, 3);
lean_ctor_set(v___x_356_, 1, v_msgData_339_);
lean_ctor_set(v___x_356_, 0, v___x_362_);
v___x_364_ = v___x_356_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_msgData_339_);
v___x_364_ = v_reuseFailAlloc_368_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_366_; 
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_364_);
v___x_366_ = v___x_351_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec(v___x_346_);
lean_dec(v___x_345_);
lean_dec_ref(v_msgData_339_);
v_a_372_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_347_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_347_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed(lean_object* v_msgData_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(v_msgData_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(lean_object* v_msg_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_toCold_395_; lean_object* v_ref_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_toCold_395_ = lean_ctor_get(v___y_392_, 0);
v_ref_396_ = lean_ctor_get(v___y_392_, 2);
v___x_397_ = lean_st_ref_get(v___y_393_);
v___x_398_ = lean_st_ref_get(v___y_391_);
v___x_399_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_390_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_423_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_423_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_423_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_423_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v_env_404_; lean_object* v_lctx_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_421_; 
v_env_404_ = lean_ctor_get(v___x_397_, 0);
lean_inc_ref(v_env_404_);
lean_dec(v___x_397_);
v_lctx_405_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v___x_398_, 1);
lean_dec(v_unused_422_);
v___x_407_ = v___x_398_;
v_isShared_408_ = v_isSharedCheck_421_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_lctx_405_);
lean_dec(v___x_398_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_421_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v_options_409_; uint8_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v_options_409_ = lean_ctor_get(v_toCold_395_, 2);
v___x_410_ = lean_unbox(v_a_400_);
lean_dec(v_a_400_);
v___x_411_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_405_, v___x_410_);
lean_dec_ref(v_lctx_405_);
v___x_412_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_409_);
v___x_413_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_413_, 0, v_env_404_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
lean_ctor_set(v___x_413_, 2, v___x_411_);
lean_ctor_set(v___x_413_, 3, v_options_409_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 3);
lean_ctor_set(v___x_407_, 1, v_msg_389_);
lean_ctor_set(v___x_407_, 0, v___x_413_);
v___x_415_ = v___x_407_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_msg_389_);
v___x_415_ = v_reuseFailAlloc_420_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_416_; lean_object* v___x_418_; 
lean_inc(v_ref_396_);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v_ref_396_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
if (v_isShared_403_ == 0)
{
lean_ctor_set_tag(v___x_402_, 1);
lean_ctor_set(v___x_402_, 0, v___x_416_);
v___x_418_ = v___x_402_;
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
lean_dec(v___x_398_);
lean_dec(v___x_397_);
lean_dec_ref(v_msg_389_);
v_a_424_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_399_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_399_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(lean_object* v_a_455_, lean_object* v_x_456_){
_start:
{
if (lean_obj_tag(v_x_456_) == 0)
{
lean_object* v___x_457_; 
v___x_457_ = lean_box(0);
return v___x_457_;
}
else
{
lean_object* v_key_458_; lean_object* v_value_459_; lean_object* v_tail_460_; uint8_t v___x_461_; 
v_key_458_ = lean_ctor_get(v_x_456_, 0);
v_value_459_ = lean_ctor_get(v_x_456_, 1);
v_tail_460_ = lean_ctor_get(v_x_456_, 2);
v___x_461_ = l_Lean_instBEqFVarId_beq(v_key_458_, v_a_455_);
if (v___x_461_ == 0)
{
v_x_456_ = v_tail_460_;
goto _start;
}
else
{
lean_object* v___x_463_; 
lean_inc(v_value_459_);
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v_value_459_);
return v___x_463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg___boxed(lean_object* v_a_464_, lean_object* v_x_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_464_, v_x_465_);
lean_dec(v_x_465_);
lean_dec(v_a_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object* v_m_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_buckets_469_; lean_object* v___x_470_; uint64_t v___x_471_; uint64_t v___x_472_; uint64_t v___x_473_; uint64_t v_fold_474_; uint64_t v___x_475_; uint64_t v___x_476_; uint64_t v___x_477_; size_t v___x_478_; size_t v___x_479_; size_t v___x_480_; size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_buckets_469_ = lean_ctor_get(v_m_467_, 1);
v___x_470_ = lean_array_get_size(v_buckets_469_);
v___x_471_ = l_Lean_instHashableFVarId_hash(v_a_468_);
v___x_472_ = 32ULL;
v___x_473_ = lean_uint64_shift_right(v___x_471_, v___x_472_);
v_fold_474_ = lean_uint64_xor(v___x_471_, v___x_473_);
v___x_475_ = 16ULL;
v___x_476_ = lean_uint64_shift_right(v_fold_474_, v___x_475_);
v___x_477_ = lean_uint64_xor(v_fold_474_, v___x_476_);
v___x_478_ = lean_uint64_to_usize(v___x_477_);
v___x_479_ = lean_usize_of_nat(v___x_470_);
v___x_480_ = ((size_t)1ULL);
v___x_481_ = lean_usize_sub(v___x_479_, v___x_480_);
v___x_482_ = lean_usize_land(v___x_478_, v___x_481_);
v___x_483_ = lean_array_uget_borrowed(v_buckets_469_, v___x_482_);
v___x_484_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_468_, v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg___boxed(lean_object* v_m_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_485_, v_a_486_);
lean_dec(v_a_486_);
lean_dec_ref(v_m_485_);
return v_res_487_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getType___closed__1(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = ((lean_object*)(l_Lean_Compiler_LCNF_getType___closed__0));
v___x_490_ = l_Lean_stringToMessageData(v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType(lean_object* v_fvarId_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_st_ref_get(v_a_493_);
v___x_498_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_492_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_549_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_549_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_549_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_549_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___y_504_; lean_object* v_lctx_515_; lean_object* v___y_517_; lean_object* v___y_532_; uint8_t v___x_546_; 
v_lctx_515_ = lean_ctor_get(v___x_497_, 0);
lean_inc_ref(v_lctx_515_);
lean_dec(v___x_497_);
v___x_546_ = lean_unbox(v_a_499_);
if (v___x_546_ == 0)
{
lean_object* v_letDeclsPure_547_; 
v_letDeclsPure_547_ = lean_ctor_get(v_lctx_515_, 2);
lean_inc_ref(v_letDeclsPure_547_);
v___y_532_ = v_letDeclsPure_547_;
goto v___jp_531_;
}
else
{
lean_object* v_letDeclsImpure_548_; 
v_letDeclsImpure_548_ = lean_ctor_get(v_lctx_515_, 3);
lean_inc_ref(v_letDeclsImpure_548_);
v___y_532_ = v_letDeclsImpure_548_;
goto v___jp_531_;
}
v___jp_503_:
{
lean_object* v___x_505_; 
v___x_505_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_504_, v_fvarId_491_);
lean_dec_ref(v___y_504_);
if (lean_obj_tag(v___x_505_) == 1)
{
lean_object* v_val_506_; lean_object* v_type_507_; lean_object* v___x_509_; 
lean_dec(v_fvarId_491_);
v_val_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_val_506_);
lean_dec_ref_known(v___x_505_, 1);
v_type_507_ = lean_ctor_get(v_val_506_, 3);
lean_inc_ref(v_type_507_);
lean_dec(v_val_506_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v_type_507_);
v___x_509_ = v___x_501_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_type_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v___x_505_);
lean_del_object(v___x_501_);
v___x_511_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_512_ = l_Lean_MessageData_ofName(v_fvarId_491_);
v___x_513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_511_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_513_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
return v___x_514_;
}
}
v___jp_516_:
{
lean_object* v___x_518_; 
v___x_518_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_517_, v_fvarId_491_);
lean_dec_ref(v___y_517_);
if (lean_obj_tag(v___x_518_) == 1)
{
lean_object* v_val_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_527_; 
lean_dec_ref(v_lctx_515_);
lean_del_object(v___x_501_);
lean_dec(v_a_499_);
lean_dec(v_fvarId_491_);
v_val_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_527_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_527_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_val_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_527_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v_type_523_; lean_object* v___x_525_; 
v_type_523_ = lean_ctor_get(v_val_519_, 2);
lean_inc_ref(v_type_523_);
lean_dec(v_val_519_);
if (v_isShared_522_ == 0)
{
lean_ctor_set_tag(v___x_521_, 0);
lean_ctor_set(v___x_521_, 0, v_type_523_);
v___x_525_ = v___x_521_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_type_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
else
{
uint8_t v___x_528_; 
lean_dec(v___x_518_);
v___x_528_ = lean_unbox(v_a_499_);
lean_dec(v_a_499_);
if (v___x_528_ == 0)
{
lean_object* v_funDeclsPure_529_; 
v_funDeclsPure_529_ = lean_ctor_get(v_lctx_515_, 4);
lean_inc_ref(v_funDeclsPure_529_);
lean_dec_ref(v_lctx_515_);
v___y_504_ = v_funDeclsPure_529_;
goto v___jp_503_;
}
else
{
lean_object* v_funDeclsImpure_530_; 
v_funDeclsImpure_530_ = lean_ctor_get(v_lctx_515_, 5);
lean_inc_ref(v_funDeclsImpure_530_);
lean_dec_ref(v_lctx_515_);
v___y_504_ = v_funDeclsImpure_530_;
goto v___jp_503_;
}
}
}
v___jp_531_:
{
lean_object* v___x_533_; 
v___x_533_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_532_, v_fvarId_491_);
lean_dec_ref(v___y_532_);
if (lean_obj_tag(v___x_533_) == 1)
{
lean_object* v_val_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_542_; 
lean_dec_ref(v_lctx_515_);
lean_del_object(v___x_501_);
lean_dec(v_a_499_);
lean_dec(v_fvarId_491_);
v_val_534_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_542_ == 0)
{
v___x_536_ = v___x_533_;
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_val_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v_type_538_; lean_object* v___x_540_; 
v_type_538_ = lean_ctor_get(v_val_534_, 2);
lean_inc_ref(v_type_538_);
lean_dec(v_val_534_);
if (v_isShared_537_ == 0)
{
lean_ctor_set_tag(v___x_536_, 0);
lean_ctor_set(v___x_536_, 0, v_type_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_type_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
else
{
uint8_t v___x_543_; 
lean_dec(v___x_533_);
v___x_543_ = lean_unbox(v_a_499_);
if (v___x_543_ == 0)
{
lean_object* v_paramsPure_544_; 
v_paramsPure_544_ = lean_ctor_get(v_lctx_515_, 0);
lean_inc_ref(v_paramsPure_544_);
v___y_517_ = v_paramsPure_544_;
goto v___jp_516_;
}
else
{
lean_object* v_paramsImpure_545_; 
v_paramsImpure_545_ = lean_ctor_get(v_lctx_515_, 1);
lean_inc_ref(v_paramsImpure_545_);
v___y_517_ = v_paramsImpure_545_;
goto v___jp_516_;
}
}
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec(v___x_497_);
lean_dec(v_fvarId_491_);
v_a_550_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_498_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_498_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType___boxed(lean_object* v_fvarId_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Compiler_LCNF_getType(v_fvarId_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(lean_object* v_00_u03b2_565_, lean_object* v_m_566_, lean_object* v_a_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_566_, v_a_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___boxed(lean_object* v_00_u03b2_569_, lean_object* v_m_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(v_00_u03b2_569_, v_m_570_, v_a_571_);
lean_dec(v_a_571_);
lean_dec_ref(v_m_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(lean_object* v_00_u03b2_573_, lean_object* v_a_574_, lean_object* v_x_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_574_, v_x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_577_, lean_object* v_a_578_, lean_object* v_x_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(v_00_u03b2_577_, v_a_578_, v_x_579_);
lean_dec(v_x_579_);
lean_dec(v_a_578_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object* v_fvarId_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = lean_st_ref_get(v_a_583_);
v___x_588_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_582_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_639_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_639_ == 0)
{
v___x_591_ = v___x_588_;
v_isShared_592_ = v_isSharedCheck_639_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_639_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___y_594_; lean_object* v_lctx_605_; lean_object* v___y_607_; lean_object* v___y_622_; uint8_t v___x_636_; 
v_lctx_605_ = lean_ctor_get(v___x_587_, 0);
lean_inc_ref(v_lctx_605_);
lean_dec(v___x_587_);
v___x_636_ = lean_unbox(v_a_589_);
if (v___x_636_ == 0)
{
lean_object* v_letDeclsPure_637_; 
v_letDeclsPure_637_ = lean_ctor_get(v_lctx_605_, 2);
lean_inc_ref(v_letDeclsPure_637_);
v___y_622_ = v_letDeclsPure_637_;
goto v___jp_621_;
}
else
{
lean_object* v_letDeclsImpure_638_; 
v_letDeclsImpure_638_ = lean_ctor_get(v_lctx_605_, 3);
lean_inc_ref(v_letDeclsImpure_638_);
v___y_622_ = v_letDeclsImpure_638_;
goto v___jp_621_;
}
v___jp_593_:
{
lean_object* v___x_595_; 
v___x_595_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_594_, v_fvarId_581_);
lean_dec_ref(v___y_594_);
if (lean_obj_tag(v___x_595_) == 1)
{
lean_object* v_val_596_; lean_object* v_binderName_597_; lean_object* v___x_599_; 
lean_dec(v_fvarId_581_);
v_val_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_val_596_);
lean_dec_ref_known(v___x_595_, 1);
v_binderName_597_ = lean_ctor_get(v_val_596_, 1);
lean_inc(v_binderName_597_);
lean_dec(v_val_596_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v_binderName_597_);
v___x_599_ = v___x_591_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_binderName_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec(v___x_595_);
lean_del_object(v___x_591_);
v___x_601_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_602_ = l_Lean_MessageData_ofName(v_fvarId_581_);
v___x_603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_603_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
return v___x_604_;
}
}
v___jp_606_:
{
lean_object* v___x_608_; 
v___x_608_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_607_, v_fvarId_581_);
lean_dec_ref(v___y_607_);
if (lean_obj_tag(v___x_608_) == 1)
{
lean_object* v_val_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_617_; 
lean_dec_ref(v_lctx_605_);
lean_del_object(v___x_591_);
lean_dec(v_a_589_);
lean_dec(v_fvarId_581_);
v_val_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_617_ == 0)
{
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_617_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_val_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_617_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v_binderName_613_; lean_object* v___x_615_; 
v_binderName_613_ = lean_ctor_get(v_val_609_, 1);
lean_inc(v_binderName_613_);
lean_dec(v_val_609_);
if (v_isShared_612_ == 0)
{
lean_ctor_set_tag(v___x_611_, 0);
lean_ctor_set(v___x_611_, 0, v_binderName_613_);
v___x_615_ = v___x_611_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_binderName_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
else
{
uint8_t v___x_618_; 
lean_dec(v___x_608_);
v___x_618_ = lean_unbox(v_a_589_);
lean_dec(v_a_589_);
if (v___x_618_ == 0)
{
lean_object* v_funDeclsPure_619_; 
v_funDeclsPure_619_ = lean_ctor_get(v_lctx_605_, 4);
lean_inc_ref(v_funDeclsPure_619_);
lean_dec_ref(v_lctx_605_);
v___y_594_ = v_funDeclsPure_619_;
goto v___jp_593_;
}
else
{
lean_object* v_funDeclsImpure_620_; 
v_funDeclsImpure_620_ = lean_ctor_get(v_lctx_605_, 5);
lean_inc_ref(v_funDeclsImpure_620_);
lean_dec_ref(v_lctx_605_);
v___y_594_ = v_funDeclsImpure_620_;
goto v___jp_593_;
}
}
}
v___jp_621_:
{
lean_object* v___x_623_; 
v___x_623_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_622_, v_fvarId_581_);
lean_dec_ref(v___y_622_);
if (lean_obj_tag(v___x_623_) == 1)
{
lean_object* v_val_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_632_; 
lean_dec_ref(v_lctx_605_);
lean_del_object(v___x_591_);
lean_dec(v_a_589_);
lean_dec(v_fvarId_581_);
v_val_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_632_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_632_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_val_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_632_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v_binderName_628_; lean_object* v___x_630_; 
v_binderName_628_ = lean_ctor_get(v_val_624_, 1);
lean_inc(v_binderName_628_);
lean_dec(v_val_624_);
if (v_isShared_627_ == 0)
{
lean_ctor_set_tag(v___x_626_, 0);
lean_ctor_set(v___x_626_, 0, v_binderName_628_);
v___x_630_ = v___x_626_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_binderName_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
else
{
uint8_t v___x_633_; 
lean_dec(v___x_623_);
v___x_633_ = lean_unbox(v_a_589_);
if (v___x_633_ == 0)
{
lean_object* v_paramsPure_634_; 
v_paramsPure_634_ = lean_ctor_get(v_lctx_605_, 0);
lean_inc_ref(v_paramsPure_634_);
v___y_607_ = v_paramsPure_634_;
goto v___jp_606_;
}
else
{
lean_object* v_paramsImpure_635_; 
v_paramsImpure_635_ = lean_ctor_get(v_lctx_605_, 1);
lean_inc_ref(v_paramsImpure_635_);
v___y_607_ = v_paramsImpure_635_;
goto v___jp_606_;
}
}
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec(v___x_587_);
lean_dec(v_fvarId_581_);
v_a_640_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_588_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_588_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName___boxed(lean_object* v_fvarId_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t v_pu_655_, lean_object* v_fvarId_656_, lean_object* v_a_657_){
_start:
{
lean_object* v___x_659_; lean_object* v___y_661_; 
v___x_659_ = lean_st_ref_get(v_a_657_);
if (v_pu_655_ == 0)
{
lean_object* v_lctx_664_; lean_object* v_paramsPure_665_; 
v_lctx_664_ = lean_ctor_get(v___x_659_, 0);
lean_inc_ref(v_lctx_664_);
lean_dec(v___x_659_);
v_paramsPure_665_ = lean_ctor_get(v_lctx_664_, 0);
lean_inc_ref(v_paramsPure_665_);
lean_dec_ref(v_lctx_664_);
v___y_661_ = v_paramsPure_665_;
goto v___jp_660_;
}
else
{
lean_object* v_lctx_666_; lean_object* v_paramsImpure_667_; 
v_lctx_666_ = lean_ctor_get(v___x_659_, 0);
lean_inc_ref(v_lctx_666_);
lean_dec(v___x_659_);
v_paramsImpure_667_ = lean_ctor_get(v_lctx_666_, 1);
lean_inc_ref(v_paramsImpure_667_);
lean_dec_ref(v_lctx_666_);
v___y_661_ = v_paramsImpure_667_;
goto v___jp_660_;
}
v___jp_660_:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_661_, v_fvarId_656_);
lean_dec_ref(v___y_661_);
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg___boxed(lean_object* v_pu_668_, lean_object* v_fvarId_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
uint8_t v_pu_boxed_672_; lean_object* v_res_673_; 
v_pu_boxed_672_ = lean_unbox(v_pu_668_);
v_res_673_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_boxed_672_, v_fvarId_669_, v_a_670_);
lean_dec(v_a_670_);
lean_dec(v_fvarId_669_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f(uint8_t v_pu_674_, lean_object* v_fvarId_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_674_, v_fvarId_675_, v_a_677_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___boxed(lean_object* v_pu_682_, lean_object* v_fvarId_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
uint8_t v_pu_boxed_689_; lean_object* v_res_690_; 
v_pu_boxed_689_ = lean_unbox(v_pu_682_);
v_res_690_ = l_Lean_Compiler_LCNF_findParam_x3f(v_pu_boxed_689_, v_fvarId_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_fvarId_683_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t v_pu_691_, lean_object* v_fvarId_692_, lean_object* v_a_693_){
_start:
{
lean_object* v___x_695_; lean_object* v___y_697_; 
v___x_695_ = lean_st_ref_get(v_a_693_);
if (v_pu_691_ == 0)
{
lean_object* v_lctx_700_; lean_object* v_letDeclsPure_701_; 
v_lctx_700_ = lean_ctor_get(v___x_695_, 0);
lean_inc_ref(v_lctx_700_);
lean_dec(v___x_695_);
v_letDeclsPure_701_ = lean_ctor_get(v_lctx_700_, 2);
lean_inc_ref(v_letDeclsPure_701_);
lean_dec_ref(v_lctx_700_);
v___y_697_ = v_letDeclsPure_701_;
goto v___jp_696_;
}
else
{
lean_object* v_lctx_702_; lean_object* v_letDeclsImpure_703_; 
v_lctx_702_ = lean_ctor_get(v___x_695_, 0);
lean_inc_ref(v_lctx_702_);
lean_dec(v___x_695_);
v_letDeclsImpure_703_ = lean_ctor_get(v_lctx_702_, 3);
lean_inc_ref(v_letDeclsImpure_703_);
lean_dec_ref(v_lctx_702_);
v___y_697_ = v_letDeclsImpure_703_;
goto v___jp_696_;
}
v___jp_696_:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_697_, v_fvarId_692_);
lean_dec_ref(v___y_697_);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg___boxed(lean_object* v_pu_704_, lean_object* v_fvarId_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
uint8_t v_pu_boxed_708_; lean_object* v_res_709_; 
v_pu_boxed_708_ = lean_unbox(v_pu_704_);
v_res_709_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_boxed_708_, v_fvarId_705_, v_a_706_);
lean_dec(v_a_706_);
lean_dec(v_fvarId_705_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(uint8_t v_pu_710_, lean_object* v_fvarId_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_710_, v_fvarId_711_, v_a_713_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___boxed(lean_object* v_pu_718_, lean_object* v_fvarId_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
uint8_t v_pu_boxed_725_; lean_object* v_res_726_; 
v_pu_boxed_725_ = lean_unbox(v_pu_718_);
v_res_726_ = l_Lean_Compiler_LCNF_findLetDecl_x3f(v_pu_boxed_725_, v_fvarId_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_fvarId_719_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t v_pu_727_, lean_object* v_fvarId_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___x_731_; lean_object* v___y_733_; 
v___x_731_ = lean_st_ref_get(v_a_729_);
if (v_pu_727_ == 0)
{
lean_object* v_lctx_736_; lean_object* v_funDeclsPure_737_; 
v_lctx_736_ = lean_ctor_get(v___x_731_, 0);
lean_inc_ref(v_lctx_736_);
lean_dec(v___x_731_);
v_funDeclsPure_737_ = lean_ctor_get(v_lctx_736_, 4);
lean_inc_ref(v_funDeclsPure_737_);
lean_dec_ref(v_lctx_736_);
v___y_733_ = v_funDeclsPure_737_;
goto v___jp_732_;
}
else
{
lean_object* v_lctx_738_; lean_object* v_funDeclsImpure_739_; 
v_lctx_738_ = lean_ctor_get(v___x_731_, 0);
lean_inc_ref(v_lctx_738_);
lean_dec(v___x_731_);
v_funDeclsImpure_739_ = lean_ctor_get(v_lctx_738_, 5);
lean_inc_ref(v_funDeclsImpure_739_);
lean_dec_ref(v_lctx_738_);
v___y_733_ = v_funDeclsImpure_739_;
goto v___jp_732_;
}
v___jp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_733_, v_fvarId_728_);
lean_dec_ref(v___y_733_);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg___boxed(lean_object* v_pu_740_, lean_object* v_fvarId_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
uint8_t v_pu_boxed_744_; lean_object* v_res_745_; 
v_pu_boxed_744_ = lean_unbox(v_pu_740_);
v_res_745_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_boxed_744_, v_fvarId_741_, v_a_742_);
lean_dec(v_a_742_);
lean_dec(v_fvarId_741_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(uint8_t v_pu_746_, lean_object* v_fvarId_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_746_, v_fvarId_747_, v_a_749_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___boxed(lean_object* v_pu_754_, lean_object* v_fvarId_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
uint8_t v_pu_boxed_761_; lean_object* v_res_762_; 
v_pu_boxed_761_ = lean_unbox(v_pu_754_);
v_res_762_ = l_Lean_Compiler_LCNF_findFunDecl_x3f(v_pu_boxed_761_, v_fvarId_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_fvarId_755_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t v_pu_763_, lean_object* v_fvarId_764_, lean_object* v_a_765_){
_start:
{
lean_object* v___x_767_; lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_788_; 
v___x_767_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_763_, v_fvarId_764_, v_a_765_);
v_a_768_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_788_ == 0)
{
v___x_770_ = v___x_767_;
v_isShared_771_ = v_isSharedCheck_788_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_788_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
if (lean_obj_tag(v_a_768_) == 1)
{
lean_object* v_val_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_783_; 
v_val_772_ = lean_ctor_get(v_a_768_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v_a_768_);
if (v_isSharedCheck_783_ == 0)
{
v___x_774_ = v_a_768_;
v_isShared_775_ = v_isSharedCheck_783_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_val_772_);
lean_dec(v_a_768_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_783_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v_value_776_; lean_object* v___x_778_; 
v_value_776_ = lean_ctor_get(v_val_772_, 3);
lean_inc(v_value_776_);
lean_dec(v_val_772_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v_value_776_);
v___x_778_ = v___x_774_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_value_776_);
v___x_778_ = v_reuseFailAlloc_782_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_780_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_778_);
v___x_780_ = v___x_770_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
else
{
lean_object* v___x_784_; lean_object* v___x_786_; 
lean_dec(v_a_768_);
v___x_784_ = lean_box(0);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_784_);
v___x_786_ = v___x_770_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg___boxed(lean_object* v_pu_789_, lean_object* v_fvarId_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
uint8_t v_pu_boxed_793_; lean_object* v_res_794_; 
v_pu_boxed_793_ = lean_unbox(v_pu_789_);
v_res_794_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_boxed_793_, v_fvarId_790_, v_a_791_);
lean_dec(v_a_791_);
lean_dec(v_fvarId_790_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f(uint8_t v_pu_795_, lean_object* v_fvarId_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_795_, v_fvarId_796_, v_a_798_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___boxed(lean_object* v_pu_803_, lean_object* v_fvarId_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
uint8_t v_pu_boxed_810_; lean_object* v_res_811_; 
v_pu_boxed_810_ = lean_unbox(v_pu_803_);
v_res_811_ = l_Lean_Compiler_LCNF_findLetValue_x3f(v_pu_boxed_810_, v_fvarId_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_fvarId_804_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg(lean_object* v_fvarId_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
uint8_t v___x_816_; lean_object* v___x_817_; 
v___x_816_ = 0;
v___x_817_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_816_, v_fvarId_812_, v_a_813_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_855_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_855_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_855_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_855_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
if (lean_obj_tag(v_a_818_) == 1)
{
lean_object* v_val_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_854_; 
v_val_828_ = lean_ctor_get(v_a_818_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v_a_818_);
if (v_isSharedCheck_854_ == 0)
{
v___x_830_ = v_a_818_;
v_isShared_831_ = v_isSharedCheck_854_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_val_828_);
lean_dec(v_a_818_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_854_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
if (lean_obj_tag(v_val_828_) == 3)
{
lean_object* v_declName_832_; lean_object* v___x_833_; lean_object* v_env_840_; uint8_t v___x_841_; lean_object* v___x_842_; 
lean_del_object(v___x_820_);
v_declName_832_ = lean_ctor_get(v_val_828_, 0);
lean_inc(v_declName_832_);
lean_dec_ref_known(v_val_828_, 3);
v___x_833_ = lean_st_ref_get(v_a_814_);
v_env_840_ = lean_ctor_get(v___x_833_, 0);
lean_inc_ref(v_env_840_);
lean_dec(v___x_833_);
v___x_841_ = 0;
v___x_842_ = l_Lean_Environment_find_x3f(v_env_840_, v_declName_832_, v___x_841_);
if (lean_obj_tag(v___x_842_) == 1)
{
lean_object* v_val_843_; 
v_val_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_val_843_);
lean_dec_ref_known(v___x_842_, 1);
if (lean_obj_tag(v_val_843_) == 6)
{
lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_852_; 
lean_del_object(v___x_830_);
v_isSharedCheck_852_ = !lean_is_exclusive(v_val_843_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v_val_843_, 0);
lean_dec(v_unused_853_);
v___x_845_ = v_val_843_;
v_isShared_846_ = v_isSharedCheck_852_;
goto v_resetjp_844_;
}
else
{
lean_dec(v_val_843_);
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
lean_dec(v_val_843_);
goto v___jp_834_;
}
}
else
{
lean_dec(v___x_842_);
goto v___jp_834_;
}
v___jp_834_:
{
uint8_t v___x_835_; lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_835_ = 0;
v___x_836_ = lean_box(v___x_835_);
if (v_isShared_831_ == 0)
{
lean_ctor_set_tag(v___x_830_, 0);
lean_ctor_set(v___x_830_, 0, v___x_836_);
v___x_838_ = v___x_830_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
else
{
lean_del_object(v___x_830_);
lean_dec(v_val_828_);
goto v___jp_822_;
}
}
}
else
{
lean_dec(v_a_818_);
goto v___jp_822_;
}
v___jp_822_:
{
uint8_t v___x_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_823_ = 0;
v___x_824_ = lean_box(v___x_823_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_824_);
v___x_826_ = v___x_820_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
v_a_856_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_817_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_817_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg___boxed(lean_object* v_fvarId_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_864_, v_a_865_, v_a_866_);
lean_dec(v_a_866_);
lean_dec(v_a_865_);
lean_dec(v_fvarId_864_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp(lean_object* v_fvarId_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_869_, v_a_871_, v_a_873_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___boxed(lean_object* v_fvarId_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_Compiler_LCNF_isConstructorApp(v_fvarId_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_fvarId_876_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(lean_object* v_arg_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
if (lean_obj_tag(v_arg_883_) == 1)
{
lean_object* v_fvarId_887_; lean_object* v___x_888_; 
v_fvarId_887_ = lean_ctor_get(v_arg_883_, 0);
v___x_888_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_887_, v_a_884_, v_a_885_);
return v___x_888_;
}
else
{
uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = 0;
v___x_890_ = lean_box(v___x_889_);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg___boxed(lean_object* v_arg_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_892_, v_a_893_, v_a_894_);
lean_dec(v_a_894_);
lean_dec(v_a_893_);
lean_dec(v_arg_892_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp(uint8_t v_pu_897_, lean_object* v_arg_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_898_, v_a_900_, v_a_902_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___boxed(lean_object* v_pu_905_, lean_object* v_arg_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
uint8_t v_pu_boxed_912_; lean_object* v_res_913_; 
v_pu_boxed_912_ = lean_unbox(v_pu_905_);
v_res_913_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp(v_pu_boxed_912_, v_arg_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_arg_906_);
return v_res_913_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getParam___closed__1(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParam___closed__0));
v___x_916_ = l_Lean_stringToMessageData(v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam(uint8_t v_pu_917_, lean_object* v_fvarId_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v___x_924_; lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_937_; 
v___x_924_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_917_, v_fvarId_918_, v_a_920_);
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_937_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_937_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_937_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
if (lean_obj_tag(v_a_925_) == 1)
{
lean_object* v_val_929_; lean_object* v___x_931_; 
lean_dec(v_fvarId_918_);
v_val_929_ = lean_ctor_get(v_a_925_, 0);
lean_inc(v_val_929_);
lean_dec_ref_known(v_a_925_, 1);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v_val_929_);
v___x_931_ = v___x_927_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_val_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
lean_del_object(v___x_927_);
lean_dec(v_a_925_);
v___x_933_ = lean_obj_once(&l_Lean_Compiler_LCNF_getParam___closed__1, &l_Lean_Compiler_LCNF_getParam___closed__1_once, _init_l_Lean_Compiler_LCNF_getParam___closed__1);
v___x_934_ = l_Lean_MessageData_ofName(v_fvarId_918_);
v___x_935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_935_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
return v___x_936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam___boxed(lean_object* v_pu_938_, lean_object* v_fvarId_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
uint8_t v_pu_boxed_945_; lean_object* v_res_946_; 
v_pu_boxed_945_ = lean_unbox(v_pu_938_);
v_res_946_ = l_Lean_Compiler_LCNF_getParam(v_pu_boxed_945_, v_fvarId_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
return v_res_946_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = ((lean_object*)(l_Lean_Compiler_LCNF_getLetDecl___closed__0));
v___x_949_ = l_Lean_stringToMessageData(v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl(uint8_t v_pu_950_, lean_object* v_fvarId_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
lean_object* v___x_957_; lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_970_; 
v___x_957_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_950_, v_fvarId_951_, v_a_953_);
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_970_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_970_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_970_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
if (lean_obj_tag(v_a_958_) == 1)
{
lean_object* v_val_962_; lean_object* v___x_964_; 
lean_dec(v_fvarId_951_);
v_val_962_ = lean_ctor_get(v_a_958_, 0);
lean_inc(v_val_962_);
lean_dec_ref_known(v_a_958_, 1);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v_val_962_);
v___x_964_ = v___x_960_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_val_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
lean_del_object(v___x_960_);
lean_dec(v_a_958_);
v___x_966_ = lean_obj_once(&l_Lean_Compiler_LCNF_getLetDecl___closed__1, &l_Lean_Compiler_LCNF_getLetDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1);
v___x_967_ = l_Lean_MessageData_ofName(v_fvarId_951_);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_968_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
return v___x_969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl___boxed(lean_object* v_pu_971_, lean_object* v_fvarId_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
uint8_t v_pu_boxed_978_; lean_object* v_res_979_; 
v_pu_boxed_978_ = lean_unbox(v_pu_971_);
v_res_979_ = l_Lean_Compiler_LCNF_getLetDecl(v_pu_boxed_978_, v_fvarId_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
return v_res_979_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l_Lean_Compiler_LCNF_getFunDecl___closed__0));
v___x_982_ = l_Lean_stringToMessageData(v___x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t v_pu_983_, lean_object* v_fvarId_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___x_990_; lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1003_; 
v___x_990_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_983_, v_fvarId_984_, v_a_986_);
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_1003_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1003_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
if (lean_obj_tag(v_a_991_) == 1)
{
lean_object* v_val_995_; lean_object* v___x_997_; 
lean_dec(v_fvarId_984_);
v_val_995_ = lean_ctor_get(v_a_991_, 0);
lean_inc(v_val_995_);
lean_dec_ref_known(v_a_991_, 1);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v_val_995_);
v___x_997_ = v___x_993_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_val_995_);
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
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_del_object(v___x_993_);
lean_dec(v_a_991_);
v___x_999_ = lean_obj_once(&l_Lean_Compiler_LCNF_getFunDecl___closed__1, &l_Lean_Compiler_LCNF_getFunDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1);
v___x_1000_ = l_Lean_MessageData_ofName(v_fvarId_984_);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_1001_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
return v___x_1002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl___boxed(lean_object* v_pu_1004_, lean_object* v_fvarId_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
uint8_t v_pu_boxed_1011_; lean_object* v_res_1012_; 
v_pu_boxed_1011_ = lean_unbox(v_pu_1004_);
v_res_1012_ = l_Lean_Compiler_LCNF_getFunDecl(v_pu_boxed_1011_, v_fvarId_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg(lean_object* v_f_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v___x_1016_; lean_object* v_lctx_1017_; lean_object* v_nextIdx_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1029_; 
v___x_1016_ = lean_st_ref_take(v_a_1014_);
v_lctx_1017_ = lean_ctor_get(v___x_1016_, 0);
v_nextIdx_1018_ = lean_ctor_get(v___x_1016_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1020_ = v___x_1016_;
v_isShared_1021_ = v_isSharedCheck_1029_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_nextIdx_1018_);
lean_inc(v_lctx_1017_);
lean_dec(v___x_1016_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1029_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1022_ = lean_apply_1(v_f_1013_, v_lctx_1017_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v___x_1022_);
v___x_1024_ = v___x_1020_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_nextIdx_1018_);
v___x_1024_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = lean_st_ref_put(v_a_1014_, v___x_1024_);
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
return v___x_1027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg___boxed(lean_object* v_f_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_Compiler_LCNF_modifyLCtx___redArg(v_f_1030_, v_a_1031_);
lean_dec(v_a_1031_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx(lean_object* v_f_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v___x_1040_; lean_object* v_lctx_1041_; lean_object* v_nextIdx_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1053_; 
v___x_1040_ = lean_st_ref_take(v_a_1036_);
v_lctx_1041_ = lean_ctor_get(v___x_1040_, 0);
v_nextIdx_1042_ = lean_ctor_get(v___x_1040_, 1);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1044_ = v___x_1040_;
v_isShared_1045_ = v_isSharedCheck_1053_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_nextIdx_1042_);
lean_inc(v_lctx_1041_);
lean_dec(v___x_1040_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1053_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1046_ = lean_apply_1(v_f_1034_, v_lctx_1041_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1046_);
v___x_1048_ = v___x_1044_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_nextIdx_1042_);
v___x_1048_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = lean_st_ref_put(v_a_1036_, v___x_1048_);
v___x_1050_ = lean_box(0);
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___boxed(lean_object* v_f_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Compiler_LCNF_modifyLCtx(v_f_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t v_pu_1061_, lean_object* v_decl_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v___x_1065_; lean_object* v_lctx_1066_; lean_object* v_nextIdx_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1078_; 
v___x_1065_ = lean_st_ref_take(v_a_1063_);
v_lctx_1066_ = lean_ctor_get(v___x_1065_, 0);
v_nextIdx_1067_ = lean_ctor_get(v___x_1065_, 1);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1069_ = v___x_1065_;
v_isShared_1070_ = v_isSharedCheck_1078_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_nextIdx_1067_);
lean_inc(v_lctx_1066_);
lean_dec(v___x_1065_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1078_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1071_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_1061_, v_lctx_1066_, v_decl_1062_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1071_);
v___x_1073_ = v___x_1069_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_nextIdx_1067_);
v___x_1073_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = lean_st_ref_put(v_a_1063_, v___x_1073_);
v___x_1075_ = lean_box(0);
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
return v___x_1076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg___boxed(lean_object* v_pu_1079_, lean_object* v_decl_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
uint8_t v_pu_boxed_1083_; lean_object* v_res_1084_; 
v_pu_boxed_1083_ = lean_unbox(v_pu_1079_);
v_res_1084_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_boxed_1083_, v_decl_1080_, v_a_1081_);
lean_dec(v_a_1081_);
lean_dec_ref(v_decl_1080_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(uint8_t v_pu_1085_, lean_object* v_decl_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1085_, v_decl_1086_, v_a_1088_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___boxed(lean_object* v_pu_1093_, lean_object* v_decl_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
uint8_t v_pu_boxed_1100_; lean_object* v_res_1101_; 
v_pu_boxed_1100_ = lean_unbox(v_pu_1093_);
v_res_1101_ = l_Lean_Compiler_LCNF_eraseLetDecl(v_pu_boxed_1100_, v_decl_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec_ref(v_decl_1094_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t v_pu_1102_, lean_object* v_decl_1103_, uint8_t v_recursive_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v___x_1107_; lean_object* v_lctx_1108_; lean_object* v_nextIdx_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1120_; 
v___x_1107_ = lean_st_ref_take(v_a_1105_);
v_lctx_1108_ = lean_ctor_get(v___x_1107_, 0);
v_nextIdx_1109_ = lean_ctor_get(v___x_1107_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1111_ = v___x_1107_;
v_isShared_1112_ = v_isSharedCheck_1120_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_nextIdx_1109_);
lean_inc(v_lctx_1108_);
lean_dec(v___x_1107_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1120_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1113_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_1102_, v_lctx_1108_, v_decl_1103_, v_recursive_1104_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1113_);
v___x_1115_ = v___x_1111_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_nextIdx_1109_);
v___x_1115_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = lean_st_ref_put(v_a_1105_, v___x_1115_);
v___x_1117_ = lean_box(0);
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
return v___x_1118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg___boxed(lean_object* v_pu_1121_, lean_object* v_decl_1122_, lean_object* v_recursive_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
uint8_t v_pu_boxed_1126_; uint8_t v_recursive_boxed_1127_; lean_object* v_res_1128_; 
v_pu_boxed_1126_ = lean_unbox(v_pu_1121_);
v_recursive_boxed_1127_ = lean_unbox(v_recursive_1123_);
v_res_1128_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_boxed_1126_, v_decl_1122_, v_recursive_boxed_1127_, v_a_1124_);
lean_dec(v_a_1124_);
lean_dec_ref(v_decl_1122_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(uint8_t v_pu_1129_, lean_object* v_decl_1130_, uint8_t v_recursive_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1129_, v_decl_1130_, v_recursive_1131_, v_a_1133_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___boxed(lean_object* v_pu_1138_, lean_object* v_decl_1139_, lean_object* v_recursive_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
uint8_t v_pu_boxed_1146_; uint8_t v_recursive_boxed_1147_; lean_object* v_res_1148_; 
v_pu_boxed_1146_ = lean_unbox(v_pu_1138_);
v_recursive_boxed_1147_ = lean_unbox(v_recursive_1140_);
v_res_1148_ = l_Lean_Compiler_LCNF_eraseFunDecl(v_pu_boxed_1146_, v_decl_1139_, v_recursive_boxed_1147_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec_ref(v_decl_1139_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t v_pu_1149_, lean_object* v_code_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v___x_1153_; lean_object* v_lctx_1154_; lean_object* v_nextIdx_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1166_; 
v___x_1153_ = lean_st_ref_take(v_a_1151_);
v_lctx_1154_ = lean_ctor_get(v___x_1153_, 0);
v_nextIdx_1155_ = lean_ctor_get(v___x_1153_, 1);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1157_ = v___x_1153_;
v_isShared_1158_ = v_isSharedCheck_1166_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_nextIdx_1155_);
lean_inc(v_lctx_1154_);
lean_dec(v___x_1153_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1166_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_1149_, v_code_1150_, v_lctx_1154_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1159_);
v___x_1161_ = v___x_1157_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_nextIdx_1155_);
v___x_1161_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1162_ = lean_st_ref_put(v_a_1151_, v___x_1161_);
v___x_1163_ = lean_box(0);
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
return v___x_1164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg___boxed(lean_object* v_pu_1167_, lean_object* v_code_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
uint8_t v_pu_boxed_1171_; lean_object* v_res_1172_; 
v_pu_boxed_1171_ = lean_unbox(v_pu_1167_);
v_res_1172_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_boxed_1171_, v_code_1168_, v_a_1169_);
lean_dec(v_a_1169_);
lean_dec_ref(v_code_1168_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode(uint8_t v_pu_1173_, lean_object* v_code_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_1173_, v_code_1174_, v_a_1176_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___boxed(lean_object* v_pu_1181_, lean_object* v_code_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
uint8_t v_pu_boxed_1188_; lean_object* v_res_1189_; 
v_pu_boxed_1188_ = lean_unbox(v_pu_1181_);
v_res_1189_ = l_Lean_Compiler_LCNF_eraseCode(v_pu_boxed_1188_, v_code_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec_ref(v_code_1182_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t v_pu_1190_, lean_object* v_param_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v___x_1194_; lean_object* v_lctx_1195_; lean_object* v_nextIdx_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1207_; 
v___x_1194_ = lean_st_ref_take(v_a_1192_);
v_lctx_1195_ = lean_ctor_get(v___x_1194_, 0);
v_nextIdx_1196_ = lean_ctor_get(v___x_1194_, 1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1198_ = v___x_1194_;
v_isShared_1199_ = v_isSharedCheck_1207_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_nextIdx_1196_);
lean_inc(v_lctx_1195_);
lean_dec(v___x_1194_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1207_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1200_ = l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_1190_, v_lctx_1195_, v_param_1191_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1200_);
v___x_1202_ = v___x_1198_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_nextIdx_1196_);
v___x_1202_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = lean_st_ref_put(v_a_1192_, v___x_1202_);
v___x_1204_ = lean_box(0);
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg___boxed(lean_object* v_pu_1208_, lean_object* v_param_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
uint8_t v_pu_boxed_1212_; lean_object* v_res_1213_; 
v_pu_boxed_1212_ = lean_unbox(v_pu_1208_);
v_res_1213_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_boxed_1212_, v_param_1209_, v_a_1210_);
lean_dec(v_a_1210_);
lean_dec_ref(v_param_1209_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam(uint8_t v_pu_1214_, lean_object* v_param_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_1214_, v_param_1215_, v_a_1217_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___boxed(lean_object* v_pu_1222_, lean_object* v_param_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
uint8_t v_pu_boxed_1229_; lean_object* v_res_1230_; 
v_pu_boxed_1229_ = lean_unbox(v_pu_1222_);
v_res_1230_ = l_Lean_Compiler_LCNF_eraseParam(v_pu_boxed_1229_, v_param_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec_ref(v_param_1223_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t v_pu_1231_, lean_object* v_params_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v___x_1235_; lean_object* v_lctx_1236_; lean_object* v_nextIdx_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1248_; 
v___x_1235_ = lean_st_ref_take(v_a_1233_);
v_lctx_1236_ = lean_ctor_get(v___x_1235_, 0);
v_nextIdx_1237_ = lean_ctor_get(v___x_1235_, 1);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1239_ = v___x_1235_;
v_isShared_1240_ = v_isSharedCheck_1248_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_nextIdx_1237_);
lean_inc(v_lctx_1236_);
lean_dec(v___x_1235_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1248_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1241_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_1231_, v_lctx_1236_, v_params_1232_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1241_);
v___x_1243_ = v___x_1239_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1241_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_nextIdx_1237_);
v___x_1243_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = lean_st_ref_put(v_a_1233_, v___x_1243_);
v___x_1245_ = lean_box(0);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg___boxed(lean_object* v_pu_1249_, lean_object* v_params_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
uint8_t v_pu_boxed_1253_; lean_object* v_res_1254_; 
v_pu_boxed_1253_ = lean_unbox(v_pu_1249_);
v_res_1254_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_boxed_1253_, v_params_1250_, v_a_1251_);
lean_dec(v_a_1251_);
lean_dec_ref(v_params_1250_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams(uint8_t v_pu_1255_, lean_object* v_params_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1255_, v_params_1256_, v_a_1258_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___boxed(lean_object* v_pu_1263_, lean_object* v_params_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
uint8_t v_pu_boxed_1270_; lean_object* v_res_1271_; 
v_pu_boxed_1270_ = lean_unbox(v_pu_1263_);
v_res_1271_ = l_Lean_Compiler_LCNF_eraseParams(v_pu_boxed_1270_, v_params_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
lean_dec_ref(v_params_1264_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t v_pu_1272_, lean_object* v_decl_1273_, lean_object* v_a_1274_){
_start:
{
switch(lean_obj_tag(v_decl_1273_))
{
case 0:
{
lean_object* v_decl_1276_; lean_object* v___x_1277_; 
v_decl_1276_ = lean_ctor_get(v_decl_1273_, 0);
v___x_1277_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1272_, v_decl_1276_, v_a_1274_);
return v___x_1277_;
}
case 1:
{
lean_object* v_decl_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; 
v_decl_1278_ = lean_ctor_get(v_decl_1273_, 0);
v___x_1279_ = 1;
v___x_1280_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1272_, v_decl_1278_, v___x_1279_, v_a_1274_);
return v___x_1280_;
}
case 2:
{
lean_object* v_decl_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; 
v_decl_1281_ = lean_ctor_get(v_decl_1273_, 0);
v___x_1282_ = 1;
v___x_1283_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1272_, v_decl_1281_, v___x_1282_, v_a_1274_);
return v___x_1283_;
}
default: 
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_box(0);
v___x_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
return v___x_1285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg___boxed(lean_object* v_pu_1286_, lean_object* v_decl_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
uint8_t v_pu_boxed_1290_; lean_object* v_res_1291_; 
v_pu_boxed_1290_ = lean_unbox(v_pu_1286_);
v_res_1291_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_boxed_1290_, v_decl_1287_, v_a_1288_);
lean_dec(v_a_1288_);
lean_dec_ref(v_decl_1287_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl(uint8_t v_pu_1292_, lean_object* v_decl_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1292_, v_decl_1293_, v_a_1295_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___boxed(lean_object* v_pu_1300_, lean_object* v_decl_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
uint8_t v_pu_boxed_1307_; lean_object* v_res_1308_; 
v_pu_boxed_1307_ = lean_unbox(v_pu_1300_);
v_res_1308_ = l_Lean_Compiler_LCNF_eraseCodeDecl(v_pu_boxed_1307_, v_decl_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec_ref(v_decl_1301_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(uint8_t v_pu_1309_, lean_object* v_as_1310_, size_t v_i_1311_, size_t v_stop_1312_, lean_object* v_b_1313_, lean_object* v___y_1314_){
_start:
{
uint8_t v___x_1316_; 
v___x_1316_ = lean_usize_dec_eq(v_i_1311_, v_stop_1312_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_array_uget_borrowed(v_as_1310_, v_i_1311_);
v___x_1318_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1309_, v___x_1317_, v___y_1314_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; size_t v___x_1320_; size_t v___x_1321_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
v___x_1320_ = ((size_t)1ULL);
v___x_1321_ = lean_usize_add(v_i_1311_, v___x_1320_);
v_i_1311_ = v___x_1321_;
v_b_1313_ = v_a_1319_;
goto _start;
}
else
{
return v___x_1318_;
}
}
else
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v_b_1313_);
return v___x_1323_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg___boxed(lean_object* v_pu_1324_, lean_object* v_as_1325_, lean_object* v_i_1326_, lean_object* v_stop_1327_, lean_object* v_b_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
uint8_t v_pu_boxed_1331_; size_t v_i_boxed_1332_; size_t v_stop_boxed_1333_; lean_object* v_res_1334_; 
v_pu_boxed_1331_ = lean_unbox(v_pu_1324_);
v_i_boxed_1332_ = lean_unbox_usize(v_i_1326_);
lean_dec(v_i_1326_);
v_stop_boxed_1333_ = lean_unbox_usize(v_stop_1327_);
lean_dec(v_stop_1327_);
v_res_1334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_boxed_1331_, v_as_1325_, v_i_boxed_1332_, v_stop_boxed_1333_, v_b_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v_as_1325_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls(uint8_t v_pu_1335_, lean_object* v_decls_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1342_ = lean_unsigned_to_nat(0u);
v___x_1343_ = lean_array_get_size(v_decls_1336_);
v___x_1344_ = lean_box(0);
v___x_1345_ = lean_nat_dec_lt(v___x_1342_, v___x_1343_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1344_);
return v___x_1346_;
}
else
{
uint8_t v___x_1347_; 
v___x_1347_ = lean_nat_dec_le(v___x_1343_, v___x_1343_);
if (v___x_1347_ == 0)
{
if (v___x_1345_ == 0)
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1344_);
return v___x_1348_;
}
else
{
size_t v___x_1349_; size_t v___x_1350_; lean_object* v___x_1351_; 
v___x_1349_ = ((size_t)0ULL);
v___x_1350_ = lean_usize_of_nat(v___x_1343_);
v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1335_, v_decls_1336_, v___x_1349_, v___x_1350_, v___x_1344_, v_a_1338_);
return v___x_1351_;
}
}
else
{
size_t v___x_1352_; size_t v___x_1353_; lean_object* v___x_1354_; 
v___x_1352_ = ((size_t)0ULL);
v___x_1353_ = lean_usize_of_nat(v___x_1343_);
v___x_1354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1335_, v_decls_1336_, v___x_1352_, v___x_1353_, v___x_1344_, v_a_1338_);
return v___x_1354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls___boxed(lean_object* v_pu_1355_, lean_object* v_decls_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
uint8_t v_pu_boxed_1362_; lean_object* v_res_1363_; 
v_pu_boxed_1362_ = lean_unbox(v_pu_1355_);
v_res_1363_ = l_Lean_Compiler_LCNF_eraseCodeDecls(v_pu_boxed_1362_, v_decls_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
lean_dec_ref(v_decls_1356_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(uint8_t v_pu_1364_, lean_object* v_as_1365_, size_t v_i_1366_, size_t v_stop_1367_, lean_object* v_b_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1364_, v_as_1365_, v_i_1366_, v_stop_1367_, v_b_1368_, v___y_1370_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___boxed(lean_object* v_pu_1375_, lean_object* v_as_1376_, lean_object* v_i_1377_, lean_object* v_stop_1378_, lean_object* v_b_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
uint8_t v_pu_boxed_1385_; size_t v_i_boxed_1386_; size_t v_stop_boxed_1387_; lean_object* v_res_1388_; 
v_pu_boxed_1385_ = lean_unbox(v_pu_1375_);
v_i_boxed_1386_ = lean_unbox_usize(v_i_1377_);
lean_dec(v_i_1377_);
v_stop_boxed_1387_ = lean_unbox_usize(v_stop_1378_);
lean_dec(v_stop_1378_);
v_res_1388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(v_pu_boxed_1385_, v_as_1376_, v_i_boxed_1386_, v_stop_boxed_1387_, v_b_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec_ref(v_as_1376_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(lean_object* v_f_1389_, lean_object* v_v_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
if (lean_obj_tag(v_v_1390_) == 0)
{
lean_object* v_code_1396_; lean_object* v___x_1397_; 
v_code_1396_ = lean_ctor_get(v_v_1390_, 0);
lean_inc_ref(v_code_1396_);
lean_dec_ref_known(v_v_1390_, 1);
lean_inc(v___y_1394_);
lean_inc_ref(v___y_1393_);
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
v___x_1397_ = lean_apply_6(v_f_1389_, v_code_1396_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, lean_box(0));
return v___x_1397_;
}
else
{
lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1405_; 
lean_dec_ref(v_f_1389_);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_v_1390_);
if (v_isSharedCheck_1405_ == 0)
{
lean_object* v_unused_1406_; 
v_unused_1406_ = lean_ctor_get(v_v_1390_, 0);
lean_dec(v_unused_1406_);
v___x_1399_ = v_v_1390_;
v_isShared_1400_ = v_isSharedCheck_1405_;
goto v_resetjp_1398_;
}
else
{
lean_dec(v_v_1390_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1405_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1403_; 
v___x_1401_ = lean_box(0);
if (v_isShared_1400_ == 0)
{
lean_ctor_set_tag(v___x_1399_, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1401_);
v___x_1403_ = v___x_1399_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg___boxed(lean_object* v_f_1407_, lean_object* v_v_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1407_, v_v_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(uint8_t v_pu_1415_, lean_object* v_f_1416_, lean_object* v_v_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1416_, v_v_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___boxed(lean_object* v_pu_1424_, lean_object* v_f_1425_, lean_object* v_v_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
uint8_t v_pu_boxed_1432_; lean_object* v_res_1433_; 
v_pu_boxed_1432_ = lean_unbox(v_pu_1424_);
v_res_1433_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(v_pu_boxed_1432_, v_f_1425_, v_v_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t v_pu_1434_, lean_object* v_decl_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v_toSignature_1441_; lean_object* v_value_1442_; lean_object* v_params_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v_toSignature_1441_ = lean_ctor_get(v_decl_1435_, 0);
lean_inc_ref(v_toSignature_1441_);
v_value_1442_ = lean_ctor_get(v_decl_1435_, 1);
lean_inc_ref(v_value_1442_);
lean_dec_ref(v_decl_1435_);
v_params_1443_ = lean_ctor_get(v_toSignature_1441_, 3);
lean_inc_ref(v_params_1443_);
lean_dec_ref(v_toSignature_1441_);
v___x_1444_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1434_, v_params_1443_, v_a_1437_);
lean_dec_ref(v_params_1443_);
lean_dec_ref(v___x_1444_);
v___x_1445_ = lean_box(v_pu_1434_);
v___x_1446_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_eraseCode___boxed), 7, 1);
lean_closure_set(v___x_1446_, 0, v___x_1445_);
v___x_1447_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v___x_1446_, v_value_1442_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl___boxed(lean_object* v_pu_1448_, lean_object* v_decl_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_){
_start:
{
uint8_t v_pu_boxed_1455_; lean_object* v_res_1456_; 
v_pu_boxed_1455_ = lean_unbox(v_pu_1448_);
v_res_1456_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_boxed_1455_, v_decl_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase(uint8_t v_pu_1457_, lean_object* v_decl_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_1457_, v_decl_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase___boxed(lean_object* v_pu_1465_, lean_object* v_decl_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
uint8_t v_pu_boxed_1472_; lean_object* v_res_1473_; 
v_pu_boxed_1472_ = lean_unbox(v_pu_1465_);
v_res_1473_ = l_Lean_Compiler_LCNF_Decl_erase(v_pu_boxed_1472_, v_decl_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(lean_object* v_msg_1474_){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = l_Lean_instInhabitedExpr;
v___x_1476_ = lean_panic_fn_borrowed(v___x_1475_, v_msg_1474_);
return v___x_1476_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3(void){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1480_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2));
v___x_1481_ = lean_unsigned_to_nat(20u);
v___x_1482_ = lean_unsigned_to_nat(215u);
v___x_1483_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1));
v___x_1484_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0));
v___x_1485_ = l_mkPanicMessageWithDecl(v___x_1484_, v___x_1483_, v___x_1482_, v___x_1481_, v___x_1480_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t v_pu_1486_, lean_object* v_s_1487_, uint8_t v_translator_1488_, lean_object* v_e_1489_){
_start:
{
uint8_t v___x_1490_; 
v___x_1490_ = l_Lean_Expr_hasFVar(v_e_1489_);
if (v___x_1490_ == 0)
{
return v_e_1489_;
}
else
{
switch(lean_obj_tag(v_e_1489_))
{
case 1:
{
lean_object* v_fvarId_1491_; lean_object* v___x_1492_; 
v_fvarId_1491_ = lean_ctor_get(v_e_1489_, 0);
v___x_1492_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1487_, v_fvarId_1491_);
if (lean_obj_tag(v___x_1492_) == 0)
{
return v_e_1489_;
}
else
{
lean_object* v_val_1493_; 
lean_dec_ref_known(v_e_1489_, 1);
v_val_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_val_1493_);
lean_dec_ref_known(v___x_1492_, 1);
switch(lean_obj_tag(v_val_1493_))
{
case 0:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_Compiler_LCNF_erasedExpr;
return v___x_1494_;
}
case 1:
{
if (v_translator_1488_ == 0)
{
lean_object* v_fvarId_1495_; lean_object* v___x_1496_; 
v_fvarId_1495_ = lean_ctor_get(v_val_1493_, 0);
lean_inc(v_fvarId_1495_);
lean_dec_ref_known(v_val_1493_, 1);
v___x_1496_ = l_Lean_Expr_fvar___override(v_fvarId_1495_);
v_e_1489_ = v___x_1496_;
goto _start;
}
else
{
lean_object* v_fvarId_1498_; lean_object* v___x_1499_; 
v_fvarId_1498_ = lean_ctor_get(v_val_1493_, 0);
lean_inc(v_fvarId_1498_);
lean_dec_ref_known(v_val_1493_, 1);
v___x_1499_ = l_Lean_Expr_fvar___override(v_fvarId_1498_);
return v___x_1499_;
}
}
default: 
{
if (v_translator_1488_ == 0)
{
lean_object* v_expr_1500_; 
v_expr_1500_ = lean_ctor_get(v_val_1493_, 0);
lean_inc_ref(v_expr_1500_);
lean_dec_ref_known(v_val_1493_, 1);
v_e_1489_ = v_expr_1500_;
goto _start;
}
else
{
lean_object* v_expr_1502_; 
v_expr_1502_ = lean_ctor_get(v_val_1493_, 0);
lean_inc_ref(v_expr_1502_);
lean_dec_ref_known(v_val_1493_, 1);
return v_expr_1502_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_1503_; lean_object* v_arg_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; size_t v___x_1507_; size_t v___x_1508_; uint8_t v___x_1509_; 
v_fn_1503_ = lean_ctor_get(v_e_1489_, 0);
v_arg_1504_ = lean_ctor_get(v_e_1489_, 1);
lean_inc_ref(v_fn_1503_);
v___x_1505_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1486_, v_s_1487_, v_translator_1488_, v_fn_1503_);
lean_inc_ref(v_arg_1504_);
v___x_1506_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1486_, v_s_1487_, v_translator_1488_, v_arg_1504_);
v___x_1507_ = lean_ptr_addr(v_fn_1503_);
v___x_1508_ = lean_ptr_addr(v___x_1505_);
v___x_1509_ = lean_usize_dec_eq(v___x_1507_, v___x_1508_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec_ref_known(v_e_1489_, 2);
v___x_1510_ = l_Lean_Expr_app___override(v___x_1505_, v___x_1506_);
v___x_1511_ = l_Lean_Expr_headBeta(v___x_1510_);
return v___x_1511_;
}
else
{
size_t v___x_1512_; size_t v___x_1513_; uint8_t v___x_1514_; 
v___x_1512_ = lean_ptr_addr(v_arg_1504_);
v___x_1513_ = lean_ptr_addr(v___x_1506_);
v___x_1514_ = lean_usize_dec_eq(v___x_1512_, v___x_1513_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_dec_ref_known(v_e_1489_, 2);
v___x_1515_ = l_Lean_Expr_app___override(v___x_1505_, v___x_1506_);
v___x_1516_ = l_Lean_Expr_headBeta(v___x_1515_);
return v___x_1516_;
}
else
{
lean_object* v___x_1517_; 
lean_dec_ref(v___x_1506_);
lean_dec_ref(v___x_1505_);
v___x_1517_ = l_Lean_Expr_headBeta(v_e_1489_);
return v___x_1517_;
}
}
}
case 6:
{
lean_object* v_binderName_1518_; lean_object* v_binderType_1519_; lean_object* v_body_1520_; uint8_t v_binderInfo_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; size_t v___x_1524_; size_t v___x_1525_; uint8_t v___x_1526_; 
v_binderName_1518_ = lean_ctor_get(v_e_1489_, 0);
v_binderType_1519_ = lean_ctor_get(v_e_1489_, 1);
v_body_1520_ = lean_ctor_get(v_e_1489_, 2);
v_binderInfo_1521_ = lean_ctor_get_uint8(v_e_1489_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1519_);
v___x_1522_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1486_, v_s_1487_, v_translator_1488_, v_binderType_1519_);
lean_inc_ref(v_body_1520_);
v___x_1523_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1486_, v_s_1487_, v_translator_1488_, v_body_1520_);
v___x_1524_ = lean_ptr_addr(v_binderType_1519_);
v___x_1525_ = lean_ptr_addr(v___x_1522_);
v___x_1526_ = lean_usize_dec_eq(v___x_1524_, v___x_1525_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; 
lean_inc(v_binderName_1518_);
lean_dec_ref_known(v_e_1489_, 3);
v___x_1527_ = l_Lean_Expr_lam___override(v_binderName_1518_, v___x_1522_, v___x_1523_, v_binderInfo_1521_);
return v___x_1527_;
}
else
{
size_t v___x_1528_; size_t v___x_1529_; uint8_t v___x_1530_; 
v___x_1528_ = lean_ptr_addr(v_body_1520_);
v___x_1529_ = lean_ptr_addr(v___x_1523_);
v___x_1530_ = lean_usize_dec_eq(v___x_1528_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; 
lean_inc(v_binderName_1518_);
lean_dec_ref_known(v_e_1489_, 3);
v___x_1531_ = l_Lean_Expr_lam___override(v_binderName_1518_, v___x_1522_, v___x_1523_, v_binderInfo_1521_);
return v___x_1531_;
}
else
{
uint8_t v___x_1532_; 
v___x_1532_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1521_, v_binderInfo_1521_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; 
lean_inc(v_binderName_1518_);
lean_dec_ref_known(v_e_1489_, 3);
v___x_1533_ = l_Lean_Expr_lam___override(v_binderName_1518_, v___x_1522_, v___x_1523_, v_binderInfo_1521_);
return v___x_1533_;
}
else
{
lean_dec_ref(v___x_1523_);
lean_dec_ref(v___x_1522_);
return v_e_1489_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1534_; lean_object* v_binderType_1535_; lean_object* v_body_1536_; uint8_t v_binderInfo_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; size_t v___x_1540_; size_t v___x_1541_; uint8_t v___x_1542_; 
v_binderName_1534_ = lean_ctor_get(v_e_1489_, 0);
v_binderType_1535_ = lean_ctor_get(v_e_1489_, 1);
v_body_1536_ = lean_ctor_get(v_e_1489_, 2);
v_binderInfo_1537_ = lean_ctor_get_uint8(v_e_1489_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1535_);
v___x_1538_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1486_, v_s_1487_, v_translator_1488_, v_binderType_1535_);
lean_inc_ref(v_body_1536_);
v___x_1539_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1486_, v_s_1487_, v_translator_1488_, v_body_1536_);
v___x_1540_ = lean_ptr_addr(v_binderType_1535_);
v___x_1541_ = lean_ptr_addr(v___x_1538_);
v___x_1542_ = lean_usize_dec_eq(v___x_1540_, v___x_1541_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; 
lean_inc(v_binderName_1534_);
lean_dec_ref_known(v_e_1489_, 3);
v___x_1543_ = l_Lean_Expr_forallE___override(v_binderName_1534_, v___x_1538_, v___x_1539_, v_binderInfo_1537_);
return v___x_1543_;
}
else
{
size_t v___x_1544_; size_t v___x_1545_; uint8_t v___x_1546_; 
v___x_1544_ = lean_ptr_addr(v_body_1536_);
v___x_1545_ = lean_ptr_addr(v___x_1539_);
v___x_1546_ = lean_usize_dec_eq(v___x_1544_, v___x_1545_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; 
lean_inc(v_binderName_1534_);
lean_dec_ref_known(v_e_1489_, 3);
v___x_1547_ = l_Lean_Expr_forallE___override(v_binderName_1534_, v___x_1538_, v___x_1539_, v_binderInfo_1537_);
return v___x_1547_;
}
else
{
uint8_t v___x_1548_; 
v___x_1548_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1537_, v_binderInfo_1537_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; 
lean_inc(v_binderName_1534_);
lean_dec_ref_known(v_e_1489_, 3);
v___x_1549_ = l_Lean_Expr_forallE___override(v_binderName_1534_, v___x_1538_, v___x_1539_, v_binderInfo_1537_);
return v___x_1549_;
}
else
{
lean_dec_ref(v___x_1539_);
lean_dec_ref(v___x_1538_);
return v_e_1489_;
}
}
}
}
case 8:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec_ref_known(v_e_1489_, 4);
v___x_1550_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3, &l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3);
v___x_1551_ = l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(v___x_1550_);
return v___x_1551_;
}
case 10:
{
lean_object* v_data_1552_; lean_object* v_expr_1553_; lean_object* v___x_1554_; size_t v___x_1555_; size_t v___x_1556_; uint8_t v___x_1557_; 
v_data_1552_ = lean_ctor_get(v_e_1489_, 0);
v_expr_1553_ = lean_ctor_get(v_e_1489_, 1);
lean_inc_ref(v_expr_1553_);
v___x_1554_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1486_, v_s_1487_, v_translator_1488_, v_expr_1553_);
v___x_1555_ = lean_ptr_addr(v_expr_1553_);
v___x_1556_ = lean_ptr_addr(v___x_1554_);
v___x_1557_ = lean_usize_dec_eq(v___x_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; 
lean_inc(v_data_1552_);
lean_dec_ref_known(v_e_1489_, 2);
v___x_1558_ = l_Lean_Expr_mdata___override(v_data_1552_, v___x_1554_);
return v___x_1558_;
}
else
{
lean_dec_ref(v___x_1554_);
return v_e_1489_;
}
}
case 11:
{
lean_object* v_typeName_1559_; lean_object* v_idx_1560_; lean_object* v_struct_1561_; lean_object* v___x_1562_; size_t v___x_1563_; size_t v___x_1564_; uint8_t v___x_1565_; 
v_typeName_1559_ = lean_ctor_get(v_e_1489_, 0);
v_idx_1560_ = lean_ctor_get(v_e_1489_, 1);
v_struct_1561_ = lean_ctor_get(v_e_1489_, 2);
lean_inc_ref(v_struct_1561_);
v___x_1562_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1486_, v_s_1487_, v_translator_1488_, v_struct_1561_);
v___x_1563_ = lean_ptr_addr(v_struct_1561_);
v___x_1564_ = lean_ptr_addr(v___x_1562_);
v___x_1565_ = lean_usize_dec_eq(v___x_1563_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; 
lean_inc(v_idx_1560_);
lean_inc(v_typeName_1559_);
lean_dec_ref_known(v_e_1489_, 3);
v___x_1566_ = l_Lean_Expr_proj___override(v_typeName_1559_, v_idx_1560_, v___x_1562_);
return v___x_1566_;
}
else
{
lean_dec_ref(v___x_1562_);
return v_e_1489_;
}
}
default: 
{
return v_e_1489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(uint8_t v_pu_1567_, lean_object* v_s_1568_, uint8_t v_translator_1569_, lean_object* v_e_1570_){
_start:
{
if (lean_obj_tag(v_e_1570_) == 5)
{
lean_object* v_fn_1571_; lean_object* v_arg_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; size_t v___x_1575_; size_t v___x_1576_; uint8_t v___x_1577_; 
v_fn_1571_ = lean_ctor_get(v_e_1570_, 0);
v_arg_1572_ = lean_ctor_get(v_e_1570_, 1);
lean_inc_ref(v_fn_1571_);
v___x_1573_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1567_, v_s_1568_, v_translator_1569_, v_fn_1571_);
lean_inc_ref(v_arg_1572_);
v___x_1574_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1567_, v_s_1568_, v_translator_1569_, v_arg_1572_);
v___x_1575_ = lean_ptr_addr(v_fn_1571_);
v___x_1576_ = lean_ptr_addr(v___x_1573_);
v___x_1577_ = lean_usize_dec_eq(v___x_1575_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; 
lean_dec_ref_known(v_e_1570_, 2);
v___x_1578_ = l_Lean_Expr_app___override(v___x_1573_, v___x_1574_);
return v___x_1578_;
}
else
{
size_t v___x_1579_; size_t v___x_1580_; uint8_t v___x_1581_; 
v___x_1579_ = lean_ptr_addr(v_arg_1572_);
v___x_1580_ = lean_ptr_addr(v___x_1574_);
v___x_1581_ = lean_usize_dec_eq(v___x_1579_, v___x_1580_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; 
lean_dec_ref_known(v_e_1570_, 2);
v___x_1582_ = l_Lean_Expr_app___override(v___x_1573_, v___x_1574_);
return v___x_1582_;
}
else
{
lean_dec_ref(v___x_1574_);
lean_dec_ref(v___x_1573_);
return v_e_1570_;
}
}
}
else
{
lean_object* v___x_1583_; 
v___x_1583_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1567_, v_s_1568_, v_translator_1569_, v_e_1570_);
return v___x_1583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(lean_object* v_pu_1584_, lean_object* v_s_1585_, lean_object* v_translator_1586_, lean_object* v_e_1587_){
_start:
{
uint8_t v_pu_boxed_1588_; uint8_t v_translator_boxed_1589_; lean_object* v_res_1590_; 
v_pu_boxed_1588_ = lean_unbox(v_pu_1584_);
v_translator_boxed_1589_ = lean_unbox(v_translator_1586_);
v_res_1590_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_boxed_1588_, v_s_1585_, v_translator_boxed_1589_, v_e_1587_);
lean_dec_ref(v_s_1585_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(lean_object* v_pu_1591_, lean_object* v_s_1592_, lean_object* v_translator_1593_, lean_object* v_e_1594_){
_start:
{
uint8_t v_pu_boxed_1595_; uint8_t v_translator_boxed_1596_; lean_object* v_res_1597_; 
v_pu_boxed_1595_ = lean_unbox(v_pu_1591_);
v_translator_boxed_1596_ = lean_unbox(v_translator_1593_);
v_res_1597_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_boxed_1595_, v_s_1592_, v_translator_boxed_1596_, v_e_1594_);
lean_dec_ref(v_s_1592_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(uint8_t v_pu_1598_, lean_object* v_s_1599_, lean_object* v_e_1600_, uint8_t v_translator_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1598_, v_s_1599_, v_translator_1601_, v_e_1600_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(lean_object* v_pu_1603_, lean_object* v_s_1604_, lean_object* v_e_1605_, lean_object* v_translator_1606_){
_start:
{
uint8_t v_pu_boxed_1607_; uint8_t v_translator_boxed_1608_; lean_object* v_res_1609_; 
v_pu_boxed_1607_ = lean_unbox(v_pu_1603_);
v_translator_boxed_1608_ = lean_unbox(v_translator_1606_);
v_res_1609_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(v_pu_boxed_1607_, v_s_1604_, v_e_1605_, v_translator_boxed_1608_);
lean_dec_ref(v_s_1604_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(lean_object* v_x_1610_){
_start:
{
if (lean_obj_tag(v_x_1610_) == 0)
{
lean_object* v___x_1611_; 
v___x_1611_ = lean_unsigned_to_nat(0u);
return v___x_1611_;
}
else
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_unsigned_to_nat(1u);
return v___x_1612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___boxed(lean_object* v_x_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(v_x_1613_);
lean_dec(v_x_1613_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(lean_object* v_t_1615_, lean_object* v_k_1616_){
_start:
{
if (lean_obj_tag(v_t_1615_) == 0)
{
lean_object* v_fvarId_1617_; lean_object* v___x_1618_; 
v_fvarId_1617_ = lean_ctor_get(v_t_1615_, 0);
lean_inc(v_fvarId_1617_);
lean_dec_ref_known(v_t_1615_, 1);
v___x_1618_ = lean_apply_1(v_k_1616_, v_fvarId_1617_);
return v___x_1618_;
}
else
{
return v_k_1616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(lean_object* v_motive_1619_, lean_object* v_ctorIdx_1620_, lean_object* v_t_1621_, lean_object* v_h_1622_, lean_object* v_k_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1621_, v_k_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___boxed(lean_object* v_motive_1625_, lean_object* v_ctorIdx_1626_, lean_object* v_t_1627_, lean_object* v_h_1628_, lean_object* v_k_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(v_motive_1625_, v_ctorIdx_1626_, v_t_1627_, v_h_1628_, v_k_1629_);
lean_dec(v_ctorIdx_1626_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim___redArg(lean_object* v_t_1631_, lean_object* v_fvar_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1631_, v_fvar_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim(lean_object* v_motive_1634_, lean_object* v_t_1635_, lean_object* v_h_1636_, lean_object* v_fvar_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1635_, v_fvar_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim___redArg(lean_object* v_t_1639_, lean_object* v_erased_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1639_, v_erased_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim(lean_object* v_motive_1642_, lean_object* v_t_1643_, lean_object* v_h_1644_, lean_object* v_erased_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1643_, v_erased_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object* v_s_1651_, lean_object* v_fvarId_1652_, uint8_t v_translator_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1651_, v_fvarId_1652_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v_fvarId_1652_);
return v___x_1655_;
}
else
{
lean_object* v_val_1656_; 
lean_dec(v_fvarId_1652_);
v_val_1656_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_val_1656_);
lean_dec_ref_known(v___x_1654_, 1);
if (lean_obj_tag(v_val_1656_) == 1)
{
if (v_translator_1653_ == 0)
{
lean_object* v_fvarId_1657_; 
v_fvarId_1657_ = lean_ctor_get(v_val_1656_, 0);
lean_inc(v_fvarId_1657_);
lean_dec_ref_known(v_val_1656_, 1);
v_fvarId_1652_ = v_fvarId_1657_;
goto _start;
}
else
{
lean_object* v_fvarId_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
v_fvarId_1659_ = lean_ctor_get(v_val_1656_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_val_1656_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v_val_1656_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_fvarId_1659_);
lean_dec(v_val_1656_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set_tag(v___x_1661_, 0);
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_fvarId_1659_);
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
else
{
lean_object* v___x_1667_; 
lean_dec(v_val_1656_);
v___x_1667_ = lean_box(1);
return v___x_1667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg___boxed(lean_object* v_s_1668_, lean_object* v_fvarId_1669_, lean_object* v_translator_1670_){
_start:
{
uint8_t v_translator_boxed_1671_; lean_object* v_res_1672_; 
v_translator_boxed_1671_ = lean_unbox(v_translator_1670_);
v_res_1672_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1668_, v_fvarId_1669_, v_translator_boxed_1671_);
lean_dec_ref(v_s_1668_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp(uint8_t v_pu_1673_, lean_object* v_s_1674_, lean_object* v_fvarId_1675_, uint8_t v_translator_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1674_, v_fvarId_1675_, v_translator_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___boxed(lean_object* v_pu_1678_, lean_object* v_s_1679_, lean_object* v_fvarId_1680_, lean_object* v_translator_1681_){
_start:
{
uint8_t v_pu_boxed_1682_; uint8_t v_translator_boxed_1683_; lean_object* v_res_1684_; 
v_pu_boxed_1682_ = lean_unbox(v_pu_1678_);
v_translator_boxed_1683_ = lean_unbox(v_translator_1681_);
v_res_1684_ = l_Lean_Compiler_LCNF_normFVarImp(v_pu_boxed_1682_, v_s_1679_, v_fvarId_1680_, v_translator_boxed_1683_);
lean_dec_ref(v_s_1679_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t v_pu_1685_, lean_object* v_s_1686_, lean_object* v_arg_1687_, uint8_t v_translator_1688_){
_start:
{
switch(lean_obj_tag(v_arg_1687_))
{
case 0:
{
return v_arg_1687_;
}
case 1:
{
lean_object* v_fvarId_1689_; lean_object* v___x_1690_; 
v_fvarId_1689_ = lean_ctor_get(v_arg_1687_, 0);
v___x_1690_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1686_, v_fvarId_1689_);
if (lean_obj_tag(v___x_1690_) == 0)
{
return v_arg_1687_;
}
else
{
lean_object* v_val_1691_; 
lean_dec_ref_known(v_arg_1687_, 1);
v_val_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_val_1691_);
lean_dec_ref_known(v___x_1690_, 1);
switch(lean_obj_tag(v_val_1691_))
{
case 0:
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_box(0);
return v___x_1692_;
}
case 1:
{
lean_object* v_fvarId_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1701_; 
v_fvarId_1693_ = lean_ctor_get(v_val_1691_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_val_1691_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1695_ = v_val_1691_;
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_fvarId_1693_);
lean_dec(v_val_1691_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_fvarId_1693_);
v___x_1698_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
if (v_translator_1688_ == 0)
{
v_arg_1687_ = v___x_1698_;
goto _start;
}
else
{
return v___x_1698_;
}
}
}
}
default: 
{
lean_object* v_expr_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
v_expr_1702_ = lean_ctor_get(v_val_1691_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_val_1691_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v_val_1691_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_expr_1702_);
lean_dec(v_val_1691_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_expr_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
}
default: 
{
lean_object* v_expr_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_expr_1710_ = lean_ctor_get(v_arg_1687_, 0);
lean_inc_ref(v_expr_1710_);
v___x_1711_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1685_, v_s_1686_, v_translator_1688_, v_expr_1710_);
v___x_1712_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1685_, v_arg_1687_, v___x_1711_);
return v___x_1712_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp___boxed(lean_object* v_pu_1713_, lean_object* v_s_1714_, lean_object* v_arg_1715_, lean_object* v_translator_1716_){
_start:
{
uint8_t v_pu_boxed_1717_; uint8_t v_translator_boxed_1718_; lean_object* v_res_1719_; 
v_pu_boxed_1717_ = lean_unbox(v_pu_1713_);
v_translator_boxed_1718_ = lean_unbox(v_translator_1716_);
v_res_1719_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_boxed_1717_, v_s_1714_, v_arg_1715_, v_translator_boxed_1718_);
lean_dec_ref(v_s_1714_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(uint8_t v_pu_1720_, lean_object* v_s_1721_, uint8_t v_translator_1722_, lean_object* v_i_1723_, lean_object* v_as_1724_){
_start:
{
lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1725_ = lean_array_get_size(v_as_1724_);
v___x_1726_ = lean_nat_dec_lt(v_i_1723_, v___x_1725_);
if (v___x_1726_ == 0)
{
lean_dec(v_i_1723_);
return v_as_1724_;
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1728_; size_t v___x_1729_; size_t v___x_1730_; uint8_t v___x_1731_; 
v_a_1727_ = lean_array_fget_borrowed(v_as_1724_, v_i_1723_);
lean_inc(v_a_1727_);
v___x_1728_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1720_, v_s_1721_, v_a_1727_, v_translator_1722_);
v___x_1729_ = lean_ptr_addr(v_a_1727_);
v___x_1730_ = lean_ptr_addr(v___x_1728_);
v___x_1731_ = lean_usize_dec_eq(v___x_1729_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1732_ = lean_unsigned_to_nat(1u);
v___x_1733_ = lean_nat_add(v_i_1723_, v___x_1732_);
v___x_1734_ = lean_array_fset(v_as_1724_, v_i_1723_, v___x_1728_);
lean_dec(v_i_1723_);
v_i_1723_ = v___x_1733_;
v_as_1724_ = v___x_1734_;
goto _start;
}
else
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_dec(v___x_1728_);
v___x_1736_ = lean_unsigned_to_nat(1u);
v___x_1737_ = lean_nat_add(v_i_1723_, v___x_1736_);
lean_dec(v_i_1723_);
v_i_1723_ = v___x_1737_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0___boxed(lean_object* v_pu_1739_, lean_object* v_s_1740_, lean_object* v_translator_1741_, lean_object* v_i_1742_, lean_object* v_as_1743_){
_start:
{
uint8_t v_pu_boxed_1744_; uint8_t v_translator_boxed_1745_; lean_object* v_res_1746_; 
v_pu_boxed_1744_ = lean_unbox(v_pu_1739_);
v_translator_boxed_1745_ = lean_unbox(v_translator_1741_);
v_res_1746_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_boxed_1744_, v_s_1740_, v_translator_boxed_1745_, v_i_1742_, v_as_1743_);
lean_dec_ref(v_s_1740_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t v_pu_1747_, lean_object* v_s_1748_, lean_object* v_args_1749_, uint8_t v_translator_1750_){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_unsigned_to_nat(0u);
v___x_1752_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_1747_, v_s_1748_, v_translator_1750_, v___x_1751_, v_args_1749_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp___boxed(lean_object* v_pu_1753_, lean_object* v_s_1754_, lean_object* v_args_1755_, lean_object* v_translator_1756_){
_start:
{
uint8_t v_pu_boxed_1757_; uint8_t v_translator_boxed_1758_; lean_object* v_res_1759_; 
v_pu_boxed_1757_ = lean_unbox(v_pu_1753_);
v_translator_boxed_1758_ = lean_unbox(v_translator_1756_);
v_res_1759_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_boxed_1757_, v_s_1754_, v_args_1755_, v_translator_boxed_1758_);
lean_dec_ref(v_s_1754_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t v_pu_1760_, lean_object* v_s_1761_, lean_object* v_e_1762_, uint8_t v_translator_1763_){
_start:
{
lean_object* v_fvarId_1765_; lean_object* v_args_1771_; 
switch(lean_obj_tag(v_e_1762_))
{
case 2:
{
lean_object* v_struct_1774_; lean_object* v___x_1775_; 
v_struct_1774_ = lean_ctor_get(v_e_1762_, 2);
lean_inc(v_struct_1774_);
v___x_1775_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1761_, v_struct_1774_, v_translator_1763_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_fvarId_1776_; lean_object* v___x_1777_; 
v_fvarId_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_fvarId_1776_);
lean_dec_ref_known(v___x_1775_, 1);
v___x_1777_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1760_, v_e_1762_, v_fvarId_1776_);
return v___x_1777_;
}
else
{
lean_object* v___x_1778_; 
lean_dec_ref_known(v_e_1762_, 3);
v___x_1778_ = lean_box(1);
return v___x_1778_;
}
}
case 3:
{
lean_object* v_args_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v_args_1779_ = lean_ctor_get(v_e_1762_, 2);
lean_inc_ref(v_args_1779_);
v___x_1780_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1760_, v_s_1761_, v_args_1779_, v_translator_1763_);
v___x_1781_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1760_, v_e_1762_, v___x_1780_);
return v___x_1781_;
}
case 4:
{
lean_object* v_fvarId_1782_; lean_object* v_args_1783_; lean_object* v___x_1784_; 
v_fvarId_1782_ = lean_ctor_get(v_e_1762_, 0);
v_args_1783_ = lean_ctor_get(v_e_1762_, 1);
lean_inc(v_fvarId_1782_);
v___x_1784_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1761_, v_fvarId_1782_, v_translator_1763_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_fvarId_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v_fvarId_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_fvarId_1785_);
lean_dec_ref_known(v___x_1784_, 1);
lean_inc_ref(v_args_1783_);
v___x_1786_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1760_, v_s_1761_, v_args_1783_, v_translator_1763_);
v___x_1787_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_1760_, v_e_1762_, v_fvarId_1785_, v___x_1786_);
lean_dec_ref_known(v_e_1762_, 2);
return v___x_1787_;
}
else
{
lean_object* v___x_1788_; 
lean_dec_ref_known(v_e_1762_, 2);
v___x_1788_ = lean_box(1);
return v___x_1788_;
}
}
case 5:
{
lean_object* v_args_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v_args_1789_ = lean_ctor_get(v_e_1762_, 1);
lean_inc_ref(v_args_1789_);
v___x_1790_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1760_, v_s_1761_, v_args_1789_, v_translator_1763_);
v___x_1791_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1760_, v_e_1762_, v___x_1790_);
return v___x_1791_;
}
case 6:
{
lean_object* v_var_1792_; 
v_var_1792_ = lean_ctor_get(v_e_1762_, 1);
lean_inc(v_var_1792_);
v_fvarId_1765_ = v_var_1792_;
goto v___jp_1764_;
}
case 7:
{
lean_object* v_var_1793_; 
v_var_1793_ = lean_ctor_get(v_e_1762_, 1);
lean_inc(v_var_1793_);
v_fvarId_1765_ = v_var_1793_;
goto v___jp_1764_;
}
case 8:
{
lean_object* v_var_1794_; lean_object* v___x_1795_; 
v_var_1794_ = lean_ctor_get(v_e_1762_, 2);
lean_inc(v_var_1794_);
v___x_1795_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1761_, v_var_1794_, v_translator_1763_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_fvarId_1796_; lean_object* v___x_1797_; 
v_fvarId_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_fvarId_1796_);
lean_dec_ref_known(v___x_1795_, 1);
v___x_1797_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1760_, v_e_1762_, v_fvarId_1796_);
return v___x_1797_;
}
else
{
lean_object* v___x_1798_; 
lean_dec_ref_known(v_e_1762_, 3);
v___x_1798_ = lean_box(1);
return v___x_1798_;
}
}
case 9:
{
lean_object* v_args_1799_; 
v_args_1799_ = lean_ctor_get(v_e_1762_, 1);
lean_inc_ref(v_args_1799_);
v_args_1771_ = v_args_1799_;
goto v___jp_1770_;
}
case 10:
{
lean_object* v_args_1800_; 
v_args_1800_ = lean_ctor_get(v_e_1762_, 1);
lean_inc_ref(v_args_1800_);
v_args_1771_ = v_args_1800_;
goto v___jp_1770_;
}
case 11:
{
lean_object* v_n_1801_; lean_object* v_var_1802_; lean_object* v___x_1803_; 
v_n_1801_ = lean_ctor_get(v_e_1762_, 0);
lean_inc(v_n_1801_);
v_var_1802_ = lean_ctor_get(v_e_1762_, 1);
lean_inc(v_var_1802_);
v___x_1803_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1761_, v_var_1802_, v_translator_1763_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_fvarId_1804_; lean_object* v___x_1805_; 
v_fvarId_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_fvarId_1804_);
lean_dec_ref_known(v___x_1803_, 1);
v___x_1805_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_1760_, v_e_1762_, v_n_1801_, v_fvarId_1804_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; 
lean_dec(v_n_1801_);
lean_dec_ref_known(v_e_1762_, 2);
v___x_1806_ = lean_box(1);
return v___x_1806_;
}
}
case 12:
{
lean_object* v_var_1807_; lean_object* v_i_1808_; uint8_t v_updateHeader_1809_; lean_object* v_args_1810_; lean_object* v___x_1811_; 
v_var_1807_ = lean_ctor_get(v_e_1762_, 0);
v_i_1808_ = lean_ctor_get(v_e_1762_, 1);
lean_inc_ref(v_i_1808_);
v_updateHeader_1809_ = lean_ctor_get_uint8(v_e_1762_, sizeof(void*)*3);
v_args_1810_ = lean_ctor_get(v_e_1762_, 2);
lean_inc(v_var_1807_);
v___x_1811_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1761_, v_var_1807_, v_translator_1763_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_fvarId_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v_fvarId_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_fvarId_1812_);
lean_dec_ref_known(v___x_1811_, 1);
lean_inc_ref(v_args_1810_);
v___x_1813_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1760_, v_s_1761_, v_args_1810_, v_translator_1763_);
v___x_1814_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_1760_, v_e_1762_, v_fvarId_1812_, v_i_1808_, v_updateHeader_1809_, v___x_1813_);
return v___x_1814_;
}
else
{
lean_object* v___x_1815_; 
lean_dec_ref(v_i_1808_);
lean_dec_ref_known(v_e_1762_, 3);
v___x_1815_ = lean_box(1);
return v___x_1815_;
}
}
case 13:
{
lean_object* v_ty_1816_; lean_object* v_fvarId_1817_; lean_object* v___x_1818_; 
v_ty_1816_ = lean_ctor_get(v_e_1762_, 0);
lean_inc_ref(v_ty_1816_);
v_fvarId_1817_ = lean_ctor_get(v_e_1762_, 1);
lean_inc(v_fvarId_1817_);
v___x_1818_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1761_, v_fvarId_1817_, v_translator_1763_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_fvarId_1819_; lean_object* v___x_1820_; 
v_fvarId_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_fvarId_1819_);
lean_dec_ref_known(v___x_1818_, 1);
v___x_1820_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_1760_, v_e_1762_, v_ty_1816_, v_fvarId_1819_);
return v___x_1820_;
}
else
{
lean_object* v___x_1821_; 
lean_dec_ref(v_ty_1816_);
lean_dec_ref_known(v_e_1762_, 2);
v___x_1821_ = lean_box(1);
return v___x_1821_;
}
}
case 14:
{
lean_object* v_fvarId_1822_; lean_object* v___x_1823_; 
v_fvarId_1822_ = lean_ctor_get(v_e_1762_, 0);
lean_inc(v_fvarId_1822_);
v___x_1823_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1761_, v_fvarId_1822_, v_translator_1763_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_fvarId_1824_; lean_object* v___x_1825_; 
v_fvarId_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_fvarId_1824_);
lean_dec_ref_known(v___x_1823_, 1);
v___x_1825_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_1760_, v_e_1762_, v_fvarId_1824_);
return v___x_1825_;
}
else
{
lean_object* v___x_1826_; 
lean_dec_ref_known(v_e_1762_, 1);
v___x_1826_ = lean_box(1);
return v___x_1826_;
}
}
case 15:
{
lean_object* v_fvarId_1827_; lean_object* v___x_1828_; 
v_fvarId_1827_ = lean_ctor_get(v_e_1762_, 0);
lean_inc(v_fvarId_1827_);
v___x_1828_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1761_, v_fvarId_1827_, v_translator_1763_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_fvarId_1829_; lean_object* v___x_1830_; 
v_fvarId_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_fvarId_1829_);
lean_dec_ref_known(v___x_1828_, 1);
v___x_1830_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_1760_, v_e_1762_, v_fvarId_1829_);
return v___x_1830_;
}
else
{
lean_object* v___x_1831_; 
lean_dec_ref_known(v_e_1762_, 1);
v___x_1831_ = lean_box(1);
return v___x_1831_;
}
}
default: 
{
return v_e_1762_;
}
}
v___jp_1764_:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1761_, v_fvarId_1765_, v_translator_1763_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_fvarId_1767_; lean_object* v___x_1768_; 
v_fvarId_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_fvarId_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1760_, v_e_1762_, v_fvarId_1767_);
return v___x_1768_;
}
else
{
lean_object* v___x_1769_; 
lean_dec(v_e_1762_);
v___x_1769_ = lean_box(1);
return v___x_1769_;
}
}
v___jp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1760_, v_s_1761_, v_args_1771_, v_translator_1763_);
v___x_1773_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1760_, v_e_1762_, v___x_1772_);
return v___x_1773_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp___boxed(lean_object* v_pu_1832_, lean_object* v_s_1833_, lean_object* v_e_1834_, lean_object* v_translator_1835_){
_start:
{
uint8_t v_pu_boxed_1836_; uint8_t v_translator_boxed_1837_; lean_object* v_res_1838_; 
v_pu_boxed_1836_ = lean_unbox(v_pu_1832_);
v_translator_boxed_1837_ = lean_unbox(v_translator_1835_);
v_res_1838_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_boxed_1836_, v_s_1833_, v_e_1834_, v_translator_boxed_1837_);
lean_dec_ref(v_s_1833_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___redArg(lean_object* v_inst_1839_, lean_object* v_inst_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_apply_2(v_inst_1839_, lean_box(0), v_inst_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(uint8_t v_pu_1842_, uint8_t v_t_1843_, lean_object* v_m_1844_, lean_object* v_n_1845_, lean_object* v_inst_1846_, lean_object* v_inst_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_apply_2(v_inst_1846_, lean_box(0), v_inst_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___boxed(lean_object* v_pu_1849_, lean_object* v_t_1850_, lean_object* v_m_1851_, lean_object* v_n_1852_, lean_object* v_inst_1853_, lean_object* v_inst_1854_){
_start:
{
uint8_t v_pu_boxed_1855_; uint8_t v_t_boxed_1856_; lean_object* v_res_1857_; 
v_pu_boxed_1855_ = lean_unbox(v_pu_1849_);
v_t_boxed_1856_ = lean_unbox(v_t_1850_);
v_res_1857_ = l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(v_pu_boxed_1855_, v_t_boxed_1856_, v_m_1851_, v_n_1852_, v_inst_1853_, v_inst_1854_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0(lean_object* v_inst_1858_, lean_object* v_inst_1859_, lean_object* v_f_1860_){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1861_ = lean_apply_1(v_inst_1858_, v_f_1860_);
v___x_1862_ = lean_apply_2(v_inst_1859_, lean_box(0), v___x_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg(lean_object* v_inst_1863_, lean_object* v_inst_1864_){
_start:
{
lean_object* v___f_1865_; 
v___f_1865_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1865_, 0, v_inst_1864_);
lean_closure_set(v___f_1865_, 1, v_inst_1863_);
return v___f_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(uint8_t v_pu_1866_, lean_object* v_m_1867_, lean_object* v_n_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_){
_start:
{
lean_object* v___f_1871_; 
v___f_1871_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1871_, 0, v_inst_1870_);
lean_closure_set(v___f_1871_, 1, v_inst_1869_);
return v___f_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___boxed(lean_object* v_pu_1872_, lean_object* v_m_1873_, lean_object* v_n_1874_, lean_object* v_inst_1875_, lean_object* v_inst_1876_){
_start:
{
uint8_t v_pu_boxed_1877_; lean_object* v_res_1878_; 
v_pu_boxed_1877_ = lean_unbox(v_pu_1872_);
v_res_1878_ = l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(v_pu_boxed_1877_, v_m_1873_, v_n_1874_, v_inst_1875_, v_inst_1876_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___lam__0(lean_object* v___x_1879_, lean_object* v___x_1880_, lean_object* v_fvarId_1881_, lean_object* v_arg_1882_, lean_object* v_s_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1879_, v___x_1880_, v_s_1883_, v_fvarId_1881_, v_arg_1882_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg(lean_object* v_inst_1887_, lean_object* v_fvarId_1888_, lean_object* v_arg_1889_){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___f_1892_; lean_object* v___x_1893_; 
v___x_1890_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1891_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1892_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1892_, 0, v___x_1890_);
lean_closure_set(v___f_1892_, 1, v___x_1891_);
lean_closure_set(v___f_1892_, 2, v_fvarId_1888_);
lean_closure_set(v___f_1892_, 3, v_arg_1889_);
v___x_1893_ = lean_apply_1(v_inst_1887_, v___f_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst(lean_object* v_m_1894_, uint8_t v_pu_1895_, lean_object* v_inst_1896_, lean_object* v_fvarId_1897_, lean_object* v_arg_1898_){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___f_1901_; lean_object* v___x_1902_; 
v___x_1899_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1900_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1901_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1901_, 0, v___x_1899_);
lean_closure_set(v___f_1901_, 1, v___x_1900_);
lean_closure_set(v___f_1901_, 2, v_fvarId_1897_);
lean_closure_set(v___f_1901_, 3, v_arg_1898_);
v___x_1902_ = lean_apply_1(v_inst_1896_, v___f_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___boxed(lean_object* v_m_1903_, lean_object* v_pu_1904_, lean_object* v_inst_1905_, lean_object* v_fvarId_1906_, lean_object* v_arg_1907_){
_start:
{
uint8_t v_pu_boxed_1908_; lean_object* v_res_1909_; 
v_pu_boxed_1908_ = lean_unbox(v_pu_1904_);
v_res_1909_ = l_Lean_Compiler_LCNF_addSubst(v_m_1903_, v_pu_boxed_1908_, v_inst_1905_, v_fvarId_1906_, v_arg_1907_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0(lean_object* v_fvarId_x27_1910_, lean_object* v___x_1911_, lean_object* v___x_1912_, lean_object* v_fvarId_1913_, lean_object* v_s_1914_){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1915_, 0, v_fvarId_x27_1910_);
v___x_1916_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1911_, v___x_1912_, v_s_1914_, v_fvarId_1913_, v___x_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg(lean_object* v_inst_1917_, lean_object* v_fvarId_1918_, lean_object* v_fvarId_x27_1919_){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___f_1922_; lean_object* v___x_1923_; 
v___x_1920_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1921_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1922_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1922_, 0, v_fvarId_x27_1919_);
lean_closure_set(v___f_1922_, 1, v___x_1920_);
lean_closure_set(v___f_1922_, 2, v___x_1921_);
lean_closure_set(v___f_1922_, 3, v_fvarId_1918_);
v___x_1923_ = lean_apply_1(v_inst_1917_, v___f_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst(lean_object* v_m_1924_, uint8_t v_ph_1925_, lean_object* v_inst_1926_, lean_object* v_fvarId_1927_, lean_object* v_fvarId_x27_1928_){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___f_1931_; lean_object* v___x_1932_; 
v___x_1929_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1930_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1931_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1931_, 0, v_fvarId_x27_1928_);
lean_closure_set(v___f_1931_, 1, v___x_1929_);
lean_closure_set(v___f_1931_, 2, v___x_1930_);
lean_closure_set(v___f_1931_, 3, v_fvarId_1927_);
v___x_1932_ = lean_apply_1(v_inst_1926_, v___f_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___boxed(lean_object* v_m_1933_, lean_object* v_ph_1934_, lean_object* v_inst_1935_, lean_object* v_fvarId_1936_, lean_object* v_fvarId_x27_1937_){
_start:
{
uint8_t v_ph_boxed_1938_; lean_object* v_res_1939_; 
v_ph_boxed_1938_ = lean_unbox(v_ph_1934_);
v_res_1939_ = l_Lean_Compiler_LCNF_addFVarSubst(v_m_1933_, v_ph_boxed_1938_, v_inst_1935_, v_fvarId_1936_, v_fvarId_x27_1937_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(lean_object* v_fvarId_1940_, uint8_t v_t_1941_, lean_object* v_toPure_1942_, lean_object* v_____do__lift_1943_){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_____do__lift_1943_, v_fvarId_1940_, v_t_1941_);
v___x_1945_ = lean_apply_2(v_toPure_1942_, lean_box(0), v___x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed(lean_object* v_fvarId_1946_, lean_object* v_t_1947_, lean_object* v_toPure_1948_, lean_object* v_____do__lift_1949_){
_start:
{
uint8_t v_t_boxed_1950_; lean_object* v_res_1951_; 
v_t_boxed_1950_ = lean_unbox(v_t_1947_);
v_res_1951_ = l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(v_fvarId_1946_, v_t_boxed_1950_, v_toPure_1948_, v_____do__lift_1949_);
lean_dec_ref(v_____do__lift_1949_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg(uint8_t v_t_1952_, lean_object* v_inst_1953_, lean_object* v_inst_1954_, lean_object* v_fvarId_1955_){
_start:
{
lean_object* v_toApplicative_1956_; lean_object* v_toBind_1957_; lean_object* v_toPure_1958_; lean_object* v___x_1959_; lean_object* v___f_1960_; lean_object* v___x_1961_; 
v_toApplicative_1956_ = lean_ctor_get(v_inst_1954_, 0);
lean_inc_ref(v_toApplicative_1956_);
v_toBind_1957_ = lean_ctor_get(v_inst_1954_, 1);
lean_inc(v_toBind_1957_);
lean_dec_ref(v_inst_1954_);
v_toPure_1958_ = lean_ctor_get(v_toApplicative_1956_, 1);
lean_inc(v_toPure_1958_);
lean_dec_ref(v_toApplicative_1956_);
v___x_1959_ = lean_box(v_t_1952_);
v___f_1960_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1960_, 0, v_fvarId_1955_);
lean_closure_set(v___f_1960_, 1, v___x_1959_);
lean_closure_set(v___f_1960_, 2, v_toPure_1958_);
v___x_1961_ = lean_apply_4(v_toBind_1957_, lean_box(0), lean_box(0), v_inst_1953_, v___f_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___boxed(lean_object* v_t_1962_, lean_object* v_inst_1963_, lean_object* v_inst_1964_, lean_object* v_fvarId_1965_){
_start:
{
uint8_t v_t_boxed_1966_; lean_object* v_res_1967_; 
v_t_boxed_1966_ = lean_unbox(v_t_1962_);
v_res_1967_ = l_Lean_Compiler_LCNF_normFVar___redArg(v_t_boxed_1966_, v_inst_1963_, v_inst_1964_, v_fvarId_1965_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar(lean_object* v_m_1968_, uint8_t v_pu_1969_, uint8_t v_t_1970_, lean_object* v_inst_1971_, lean_object* v_inst_1972_, lean_object* v_fvarId_1973_){
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___boxed(lean_object* v_m_1980_, lean_object* v_pu_1981_, lean_object* v_t_1982_, lean_object* v_inst_1983_, lean_object* v_inst_1984_, lean_object* v_fvarId_1985_){
_start:
{
uint8_t v_pu_boxed_1986_; uint8_t v_t_boxed_1987_; lean_object* v_res_1988_; 
v_pu_boxed_1986_ = lean_unbox(v_pu_1981_);
v_t_boxed_1987_ = lean_unbox(v_t_1982_);
v_res_1988_ = l_Lean_Compiler_LCNF_normFVar(v_m_1980_, v_pu_boxed_1986_, v_t_boxed_1987_, v_inst_1983_, v_inst_1984_, v_fvarId_1985_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(uint8_t v_pu_1989_, uint8_t v_t_1990_, lean_object* v_e_1991_, lean_object* v_toPure_1992_, lean_object* v_____do__lift_1993_){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1989_, v_____do__lift_1993_, v_t_1990_, v_e_1991_);
v___x_1995_ = lean_apply_2(v_toPure_1992_, lean_box(0), v___x_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed(lean_object* v_pu_1996_, lean_object* v_t_1997_, lean_object* v_e_1998_, lean_object* v_toPure_1999_, lean_object* v_____do__lift_2000_){
_start:
{
uint8_t v_pu_boxed_2001_; uint8_t v_t_boxed_2002_; lean_object* v_res_2003_; 
v_pu_boxed_2001_ = lean_unbox(v_pu_1996_);
v_t_boxed_2002_ = lean_unbox(v_t_1997_);
v_res_2003_ = l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(v_pu_boxed_2001_, v_t_boxed_2002_, v_e_1998_, v_toPure_1999_, v_____do__lift_2000_);
lean_dec_ref(v_____do__lift_2000_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg(uint8_t v_pu_2004_, uint8_t v_t_2005_, lean_object* v_inst_2006_, lean_object* v_inst_2007_, lean_object* v_e_2008_){
_start:
{
lean_object* v_toApplicative_2009_; lean_object* v_toBind_2010_; lean_object* v_toPure_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___f_2014_; lean_object* v___x_2015_; 
v_toApplicative_2009_ = lean_ctor_get(v_inst_2007_, 0);
lean_inc_ref(v_toApplicative_2009_);
v_toBind_2010_ = lean_ctor_get(v_inst_2007_, 1);
lean_inc(v_toBind_2010_);
lean_dec_ref(v_inst_2007_);
v_toPure_2011_ = lean_ctor_get(v_toApplicative_2009_, 1);
lean_inc(v_toPure_2011_);
lean_dec_ref(v_toApplicative_2009_);
v___x_2012_ = lean_box(v_pu_2004_);
v___x_2013_ = lean_box(v_t_2005_);
v___f_2014_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2014_, 0, v___x_2012_);
lean_closure_set(v___f_2014_, 1, v___x_2013_);
lean_closure_set(v___f_2014_, 2, v_e_2008_);
lean_closure_set(v___f_2014_, 3, v_toPure_2011_);
v___x_2015_ = lean_apply_4(v_toBind_2010_, lean_box(0), lean_box(0), v_inst_2006_, v___f_2014_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___boxed(lean_object* v_pu_2016_, lean_object* v_t_2017_, lean_object* v_inst_2018_, lean_object* v_inst_2019_, lean_object* v_e_2020_){
_start:
{
uint8_t v_pu_boxed_2021_; uint8_t v_t_boxed_2022_; lean_object* v_res_2023_; 
v_pu_boxed_2021_ = lean_unbox(v_pu_2016_);
v_t_boxed_2022_ = lean_unbox(v_t_2017_);
v_res_2023_ = l_Lean_Compiler_LCNF_normExpr___redArg(v_pu_boxed_2021_, v_t_boxed_2022_, v_inst_2018_, v_inst_2019_, v_e_2020_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr(lean_object* v_m_2024_, uint8_t v_pu_2025_, uint8_t v_t_2026_, lean_object* v_inst_2027_, lean_object* v_inst_2028_, lean_object* v_e_2029_){
_start:
{
lean_object* v_toApplicative_2030_; lean_object* v_toBind_2031_; lean_object* v_toPure_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___f_2035_; lean_object* v___x_2036_; 
v_toApplicative_2030_ = lean_ctor_get(v_inst_2028_, 0);
lean_inc_ref(v_toApplicative_2030_);
v_toBind_2031_ = lean_ctor_get(v_inst_2028_, 1);
lean_inc(v_toBind_2031_);
lean_dec_ref(v_inst_2028_);
v_toPure_2032_ = lean_ctor_get(v_toApplicative_2030_, 1);
lean_inc(v_toPure_2032_);
lean_dec_ref(v_toApplicative_2030_);
v___x_2033_ = lean_box(v_pu_2025_);
v___x_2034_ = lean_box(v_t_2026_);
v___f_2035_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2035_, 0, v___x_2033_);
lean_closure_set(v___f_2035_, 1, v___x_2034_);
lean_closure_set(v___f_2035_, 2, v_e_2029_);
lean_closure_set(v___f_2035_, 3, v_toPure_2032_);
v___x_2036_ = lean_apply_4(v_toBind_2031_, lean_box(0), lean_box(0), v_inst_2027_, v___f_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___boxed(lean_object* v_m_2037_, lean_object* v_pu_2038_, lean_object* v_t_2039_, lean_object* v_inst_2040_, lean_object* v_inst_2041_, lean_object* v_e_2042_){
_start:
{
uint8_t v_pu_boxed_2043_; uint8_t v_t_boxed_2044_; lean_object* v_res_2045_; 
v_pu_boxed_2043_ = lean_unbox(v_pu_2038_);
v_t_boxed_2044_ = lean_unbox(v_t_2039_);
v_res_2045_ = l_Lean_Compiler_LCNF_normExpr(v_m_2037_, v_pu_boxed_2043_, v_t_boxed_2044_, v_inst_2040_, v_inst_2041_, v_e_2042_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0(uint8_t v_pu_2046_, lean_object* v_arg_2047_, uint8_t v_t_2048_, lean_object* v_toPure_2049_, lean_object* v_____do__lift_2050_){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2046_, v_____do__lift_2050_, v_arg_2047_, v_t_2048_);
v___x_2052_ = lean_apply_2(v_toPure_2049_, lean_box(0), v___x_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed(lean_object* v_pu_2053_, lean_object* v_arg_2054_, lean_object* v_t_2055_, lean_object* v_toPure_2056_, lean_object* v_____do__lift_2057_){
_start:
{
uint8_t v_pu_boxed_2058_; uint8_t v_t_boxed_2059_; lean_object* v_res_2060_; 
v_pu_boxed_2058_ = lean_unbox(v_pu_2053_);
v_t_boxed_2059_ = lean_unbox(v_t_2055_);
v_res_2060_ = l_Lean_Compiler_LCNF_normArg___redArg___lam__0(v_pu_boxed_2058_, v_arg_2054_, v_t_boxed_2059_, v_toPure_2056_, v_____do__lift_2057_);
lean_dec_ref(v_____do__lift_2057_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg(uint8_t v_pu_2061_, uint8_t v_t_2062_, lean_object* v_inst_2063_, lean_object* v_inst_2064_, lean_object* v_arg_2065_){
_start:
{
lean_object* v_toApplicative_2066_; lean_object* v_toBind_2067_; lean_object* v_toPure_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___f_2071_; lean_object* v___x_2072_; 
v_toApplicative_2066_ = lean_ctor_get(v_inst_2064_, 0);
lean_inc_ref(v_toApplicative_2066_);
v_toBind_2067_ = lean_ctor_get(v_inst_2064_, 1);
lean_inc(v_toBind_2067_);
lean_dec_ref(v_inst_2064_);
v_toPure_2068_ = lean_ctor_get(v_toApplicative_2066_, 1);
lean_inc(v_toPure_2068_);
lean_dec_ref(v_toApplicative_2066_);
v___x_2069_ = lean_box(v_pu_2061_);
v___x_2070_ = lean_box(v_t_2062_);
v___f_2071_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2071_, 0, v___x_2069_);
lean_closure_set(v___f_2071_, 1, v_arg_2065_);
lean_closure_set(v___f_2071_, 2, v___x_2070_);
lean_closure_set(v___f_2071_, 3, v_toPure_2068_);
v___x_2072_ = lean_apply_4(v_toBind_2067_, lean_box(0), lean_box(0), v_inst_2063_, v___f_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___boxed(lean_object* v_pu_2073_, lean_object* v_t_2074_, lean_object* v_inst_2075_, lean_object* v_inst_2076_, lean_object* v_arg_2077_){
_start:
{
uint8_t v_pu_boxed_2078_; uint8_t v_t_boxed_2079_; lean_object* v_res_2080_; 
v_pu_boxed_2078_ = lean_unbox(v_pu_2073_);
v_t_boxed_2079_ = lean_unbox(v_t_2074_);
v_res_2080_ = l_Lean_Compiler_LCNF_normArg___redArg(v_pu_boxed_2078_, v_t_boxed_2079_, v_inst_2075_, v_inst_2076_, v_arg_2077_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg(lean_object* v_m_2081_, uint8_t v_pu_2082_, uint8_t v_t_2083_, lean_object* v_inst_2084_, lean_object* v_inst_2085_, lean_object* v_arg_2086_){
_start:
{
lean_object* v_toApplicative_2087_; lean_object* v_toBind_2088_; lean_object* v_toPure_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___f_2092_; lean_object* v___x_2093_; 
v_toApplicative_2087_ = lean_ctor_get(v_inst_2085_, 0);
lean_inc_ref(v_toApplicative_2087_);
v_toBind_2088_ = lean_ctor_get(v_inst_2085_, 1);
lean_inc(v_toBind_2088_);
lean_dec_ref(v_inst_2085_);
v_toPure_2089_ = lean_ctor_get(v_toApplicative_2087_, 1);
lean_inc(v_toPure_2089_);
lean_dec_ref(v_toApplicative_2087_);
v___x_2090_ = lean_box(v_pu_2082_);
v___x_2091_ = lean_box(v_t_2083_);
v___f_2092_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2092_, 0, v___x_2090_);
lean_closure_set(v___f_2092_, 1, v_arg_2086_);
lean_closure_set(v___f_2092_, 2, v___x_2091_);
lean_closure_set(v___f_2092_, 3, v_toPure_2089_);
v___x_2093_ = lean_apply_4(v_toBind_2088_, lean_box(0), lean_box(0), v_inst_2084_, v___f_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___boxed(lean_object* v_m_2094_, lean_object* v_pu_2095_, lean_object* v_t_2096_, lean_object* v_inst_2097_, lean_object* v_inst_2098_, lean_object* v_arg_2099_){
_start:
{
uint8_t v_pu_boxed_2100_; uint8_t v_t_boxed_2101_; lean_object* v_res_2102_; 
v_pu_boxed_2100_ = lean_unbox(v_pu_2095_);
v_t_boxed_2101_ = lean_unbox(v_t_2096_);
v_res_2102_ = l_Lean_Compiler_LCNF_normArg(v_m_2094_, v_pu_boxed_2100_, v_t_boxed_2101_, v_inst_2097_, v_inst_2098_, v_arg_2099_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(uint8_t v_pu_2103_, lean_object* v_e_2104_, uint8_t v_t_2105_, lean_object* v_toPure_2106_, lean_object* v_____do__lift_2107_){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_2103_, v_____do__lift_2107_, v_e_2104_, v_t_2105_);
v___x_2109_ = lean_apply_2(v_toPure_2106_, lean_box(0), v___x_2108_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed(lean_object* v_pu_2110_, lean_object* v_e_2111_, lean_object* v_t_2112_, lean_object* v_toPure_2113_, lean_object* v_____do__lift_2114_){
_start:
{
uint8_t v_pu_boxed_2115_; uint8_t v_t_boxed_2116_; lean_object* v_res_2117_; 
v_pu_boxed_2115_ = lean_unbox(v_pu_2110_);
v_t_boxed_2116_ = lean_unbox(v_t_2112_);
v_res_2117_ = l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(v_pu_boxed_2115_, v_e_2111_, v_t_boxed_2116_, v_toPure_2113_, v_____do__lift_2114_);
lean_dec_ref(v_____do__lift_2114_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg(uint8_t v_pu_2118_, uint8_t v_t_2119_, lean_object* v_inst_2120_, lean_object* v_inst_2121_, lean_object* v_e_2122_){
_start:
{
lean_object* v_toApplicative_2123_; lean_object* v_toBind_2124_; lean_object* v_toPure_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___f_2128_; lean_object* v___x_2129_; 
v_toApplicative_2123_ = lean_ctor_get(v_inst_2121_, 0);
lean_inc_ref(v_toApplicative_2123_);
v_toBind_2124_ = lean_ctor_get(v_inst_2121_, 1);
lean_inc(v_toBind_2124_);
lean_dec_ref(v_inst_2121_);
v_toPure_2125_ = lean_ctor_get(v_toApplicative_2123_, 1);
lean_inc(v_toPure_2125_);
lean_dec_ref(v_toApplicative_2123_);
v___x_2126_ = lean_box(v_pu_2118_);
v___x_2127_ = lean_box(v_t_2119_);
v___f_2128_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2128_, 0, v___x_2126_);
lean_closure_set(v___f_2128_, 1, v_e_2122_);
lean_closure_set(v___f_2128_, 2, v___x_2127_);
lean_closure_set(v___f_2128_, 3, v_toPure_2125_);
v___x_2129_ = lean_apply_4(v_toBind_2124_, lean_box(0), lean_box(0), v_inst_2120_, v___f_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___boxed(lean_object* v_pu_2130_, lean_object* v_t_2131_, lean_object* v_inst_2132_, lean_object* v_inst_2133_, lean_object* v_e_2134_){
_start:
{
uint8_t v_pu_boxed_2135_; uint8_t v_t_boxed_2136_; lean_object* v_res_2137_; 
v_pu_boxed_2135_ = lean_unbox(v_pu_2130_);
v_t_boxed_2136_ = lean_unbox(v_t_2131_);
v_res_2137_ = l_Lean_Compiler_LCNF_normLetValue___redArg(v_pu_boxed_2135_, v_t_boxed_2136_, v_inst_2132_, v_inst_2133_, v_e_2134_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue(lean_object* v_m_2138_, uint8_t v_pu_2139_, uint8_t v_t_2140_, lean_object* v_inst_2141_, lean_object* v_inst_2142_, lean_object* v_e_2143_){
_start:
{
lean_object* v_toApplicative_2144_; lean_object* v_toBind_2145_; lean_object* v_toPure_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___f_2149_; lean_object* v___x_2150_; 
v_toApplicative_2144_ = lean_ctor_get(v_inst_2142_, 0);
lean_inc_ref(v_toApplicative_2144_);
v_toBind_2145_ = lean_ctor_get(v_inst_2142_, 1);
lean_inc(v_toBind_2145_);
lean_dec_ref(v_inst_2142_);
v_toPure_2146_ = lean_ctor_get(v_toApplicative_2144_, 1);
lean_inc(v_toPure_2146_);
lean_dec_ref(v_toApplicative_2144_);
v___x_2147_ = lean_box(v_pu_2139_);
v___x_2148_ = lean_box(v_t_2140_);
v___f_2149_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2149_, 0, v___x_2147_);
lean_closure_set(v___f_2149_, 1, v_e_2143_);
lean_closure_set(v___f_2149_, 2, v___x_2148_);
lean_closure_set(v___f_2149_, 3, v_toPure_2146_);
v___x_2150_ = lean_apply_4(v_toBind_2145_, lean_box(0), lean_box(0), v_inst_2141_, v___f_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___boxed(lean_object* v_m_2151_, lean_object* v_pu_2152_, lean_object* v_t_2153_, lean_object* v_inst_2154_, lean_object* v_inst_2155_, lean_object* v_e_2156_){
_start:
{
uint8_t v_pu_boxed_2157_; uint8_t v_t_boxed_2158_; lean_object* v_res_2159_; 
v_pu_boxed_2157_ = lean_unbox(v_pu_2152_);
v_t_boxed_2158_ = lean_unbox(v_t_2153_);
v_res_2159_ = l_Lean_Compiler_LCNF_normLetValue(v_m_2151_, v_pu_boxed_2157_, v_t_boxed_2158_, v_inst_2154_, v_inst_2155_, v_e_2156_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore(uint8_t v_pu_2160_, lean_object* v_s_2161_, lean_object* v_e_2162_, uint8_t v_translator_2163_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2160_, v_s_2161_, v_translator_2163_, v_e_2162_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore___boxed(lean_object* v_pu_2165_, lean_object* v_s_2166_, lean_object* v_e_2167_, lean_object* v_translator_2168_){
_start:
{
uint8_t v_pu_boxed_2169_; uint8_t v_translator_boxed_2170_; lean_object* v_res_2171_; 
v_pu_boxed_2169_ = lean_unbox(v_pu_2165_);
v_translator_boxed_2170_ = lean_unbox(v_translator_2168_);
v_res_2171_ = l_Lean_Compiler_LCNF_normExprCore(v_pu_boxed_2169_, v_s_2166_, v_e_2167_, v_translator_boxed_2170_);
lean_dec_ref(v_s_2166_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(uint8_t v_pu_2172_, lean_object* v_args_2173_, uint8_t v_t_2174_, lean_object* v_toPure_2175_, lean_object* v_____do__lift_2176_){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_2172_, v_____do__lift_2176_, v_args_2173_, v_t_2174_);
v___x_2178_ = lean_apply_2(v_toPure_2175_, lean_box(0), v___x_2177_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed(lean_object* v_pu_2179_, lean_object* v_args_2180_, lean_object* v_t_2181_, lean_object* v_toPure_2182_, lean_object* v_____do__lift_2183_){
_start:
{
uint8_t v_pu_boxed_2184_; uint8_t v_t_boxed_2185_; lean_object* v_res_2186_; 
v_pu_boxed_2184_ = lean_unbox(v_pu_2179_);
v_t_boxed_2185_ = lean_unbox(v_t_2181_);
v_res_2186_ = l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(v_pu_boxed_2184_, v_args_2180_, v_t_boxed_2185_, v_toPure_2182_, v_____do__lift_2183_);
lean_dec_ref(v_____do__lift_2183_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg(uint8_t v_pu_2187_, uint8_t v_t_2188_, lean_object* v_inst_2189_, lean_object* v_inst_2190_, lean_object* v_args_2191_){
_start:
{
lean_object* v_toApplicative_2192_; lean_object* v_toBind_2193_; lean_object* v_toPure_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___f_2197_; lean_object* v___x_2198_; 
v_toApplicative_2192_ = lean_ctor_get(v_inst_2190_, 0);
lean_inc_ref(v_toApplicative_2192_);
v_toBind_2193_ = lean_ctor_get(v_inst_2190_, 1);
lean_inc(v_toBind_2193_);
lean_dec_ref(v_inst_2190_);
v_toPure_2194_ = lean_ctor_get(v_toApplicative_2192_, 1);
lean_inc(v_toPure_2194_);
lean_dec_ref(v_toApplicative_2192_);
v___x_2195_ = lean_box(v_pu_2187_);
v___x_2196_ = lean_box(v_t_2188_);
v___f_2197_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2197_, 0, v___x_2195_);
lean_closure_set(v___f_2197_, 1, v_args_2191_);
lean_closure_set(v___f_2197_, 2, v___x_2196_);
lean_closure_set(v___f_2197_, 3, v_toPure_2194_);
v___x_2198_ = lean_apply_4(v_toBind_2193_, lean_box(0), lean_box(0), v_inst_2189_, v___f_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___boxed(lean_object* v_pu_2199_, lean_object* v_t_2200_, lean_object* v_inst_2201_, lean_object* v_inst_2202_, lean_object* v_args_2203_){
_start:
{
uint8_t v_pu_boxed_2204_; uint8_t v_t_boxed_2205_; lean_object* v_res_2206_; 
v_pu_boxed_2204_ = lean_unbox(v_pu_2199_);
v_t_boxed_2205_ = lean_unbox(v_t_2200_);
v_res_2206_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_boxed_2204_, v_t_boxed_2205_, v_inst_2201_, v_inst_2202_, v_args_2203_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs(lean_object* v_m_2207_, uint8_t v_pu_2208_, uint8_t v_t_2209_, lean_object* v_inst_2210_, lean_object* v_inst_2211_, lean_object* v_args_2212_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_2208_, v_t_2209_, v_inst_2210_, v_inst_2211_, v_args_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___boxed(lean_object* v_m_2214_, lean_object* v_pu_2215_, lean_object* v_t_2216_, lean_object* v_inst_2217_, lean_object* v_inst_2218_, lean_object* v_args_2219_){
_start:
{
uint8_t v_pu_boxed_2220_; uint8_t v_t_boxed_2221_; lean_object* v_res_2222_; 
v_pu_boxed_2220_ = lean_unbox(v_pu_2215_);
v_t_boxed_2221_ = lean_unbox(v_t_2216_);
v_res_2222_ = l_Lean_Compiler_LCNF_normArgs(v_m_2214_, v_pu_boxed_2220_, v_t_boxed_2221_, v_inst_2217_, v_inst_2218_, v_args_2219_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object* v_binderName_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v_lctx_2228_; lean_object* v_nextIdx_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2242_; 
v___x_2226_ = lean_st_ref_get(v_a_2224_);
v___x_2227_ = lean_st_ref_take(v_a_2224_);
v_lctx_2228_ = lean_ctor_get(v___x_2227_, 0);
v_nextIdx_2229_ = lean_ctor_get(v___x_2227_, 1);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2231_ = v___x_2227_;
v_isShared_2232_ = v_isSharedCheck_2242_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_nextIdx_2229_);
lean_inc(v_lctx_2228_);
lean_dec(v___x_2227_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2242_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2233_ = lean_unsigned_to_nat(1u);
v___x_2234_ = lean_nat_add(v_nextIdx_2229_, v___x_2233_);
lean_dec(v_nextIdx_2229_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 1, v___x_2234_);
v___x_2236_ = v___x_2231_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_lctx_2228_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2237_; lean_object* v_nextIdx_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2237_ = lean_st_ref_put(v_a_2224_, v___x_2236_);
v_nextIdx_2238_ = lean_ctor_get(v___x_2226_, 1);
lean_inc(v_nextIdx_2238_);
lean_dec(v___x_2226_);
v___x_2239_ = l_Lean_Name_num___override(v_binderName_2223_, v_nextIdx_2238_);
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
return v___x_2240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg___boxed(lean_object* v_binderName_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2243_, v_a_2244_);
lean_dec(v_a_2244_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object* v_binderName_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2247_, v_a_2249_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___boxed(lean_object* v_binderName_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_Compiler_LCNF_mkFreshBinderName(v_binderName_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_);
lean_dec(v_a_2258_);
lean_dec_ref(v_a_2257_);
lean_dec(v_a_2256_);
lean_dec_ref(v_a_2255_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(lean_object* v_binderName_2261_, lean_object* v_baseName_2262_, lean_object* v_a_2263_){
_start:
{
uint8_t v___x_2265_; 
v___x_2265_ = l_Lean_Name_isAnonymous(v_binderName_2261_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2266_; 
lean_dec(v_baseName_2262_);
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v_binderName_2261_);
return v___x_2266_;
}
else
{
lean_object* v___x_2267_; 
lean_dec(v_binderName_2261_);
v___x_2267_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_baseName_2262_, v_a_2263_);
return v___x_2267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg___boxed(lean_object* v_binderName_2268_, lean_object* v_baseName_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2268_, v_baseName_2269_, v_a_2270_);
lean_dec(v_a_2270_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous(lean_object* v_binderName_2273_, lean_object* v_baseName_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2273_, v_baseName_2274_, v_a_2276_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___boxed(lean_object* v_binderName_2281_, lean_object* v_baseName_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_Compiler_LCNF_ensureNotAnonymous(v_binderName_2281_, v_baseName_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; lean_object* v_ngen_2292_; lean_object* v_namePrefix_2293_; lean_object* v_idx_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2323_; 
v___x_2291_ = lean_st_ref_get(v___y_2289_);
v_ngen_2292_ = lean_ctor_get(v___x_2291_, 2);
lean_inc_ref(v_ngen_2292_);
lean_dec(v___x_2291_);
v_namePrefix_2293_ = lean_ctor_get(v_ngen_2292_, 0);
v_idx_2294_ = lean_ctor_get(v_ngen_2292_, 1);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_ngen_2292_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2296_ = v_ngen_2292_;
v_isShared_2297_ = v_isSharedCheck_2323_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_idx_2294_);
lean_inc(v_namePrefix_2293_);
lean_dec(v_ngen_2292_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2323_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v_env_2299_; lean_object* v_nextMacroScope_2300_; lean_object* v_auxDeclNGen_2301_; lean_object* v_traceState_2302_; lean_object* v_cache_2303_; lean_object* v_messages_2304_; lean_object* v_infoState_2305_; lean_object* v_snapshotTasks_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2321_; 
v___x_2298_ = lean_st_ref_take(v___y_2289_);
v_env_2299_ = lean_ctor_get(v___x_2298_, 0);
v_nextMacroScope_2300_ = lean_ctor_get(v___x_2298_, 1);
v_auxDeclNGen_2301_ = lean_ctor_get(v___x_2298_, 3);
v_traceState_2302_ = lean_ctor_get(v___x_2298_, 4);
v_cache_2303_ = lean_ctor_get(v___x_2298_, 5);
v_messages_2304_ = lean_ctor_get(v___x_2298_, 6);
v_infoState_2305_ = lean_ctor_get(v___x_2298_, 7);
v_snapshotTasks_2306_ = lean_ctor_get(v___x_2298_, 8);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2321_ == 0)
{
lean_object* v_unused_2322_; 
v_unused_2322_ = lean_ctor_get(v___x_2298_, 2);
lean_dec(v_unused_2322_);
v___x_2308_ = v___x_2298_;
v_isShared_2309_ = v_isSharedCheck_2321_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_snapshotTasks_2306_);
lean_inc(v_infoState_2305_);
lean_inc(v_messages_2304_);
lean_inc(v_cache_2303_);
lean_inc(v_traceState_2302_);
lean_inc(v_auxDeclNGen_2301_);
lean_inc(v_nextMacroScope_2300_);
lean_inc(v_env_2299_);
lean_dec(v___x_2298_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2321_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v_r_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2314_; 
lean_inc(v_idx_2294_);
lean_inc(v_namePrefix_2293_);
v_r_2310_ = l_Lean_Name_num___override(v_namePrefix_2293_, v_idx_2294_);
v___x_2311_ = lean_unsigned_to_nat(1u);
v___x_2312_ = lean_nat_add(v_idx_2294_, v___x_2311_);
lean_dec(v_idx_2294_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 1, v___x_2312_);
v___x_2314_ = v___x_2296_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_namePrefix_2293_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v___x_2312_);
v___x_2314_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
lean_object* v___x_2316_; 
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 2, v___x_2314_);
v___x_2316_ = v___x_2308_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_env_2299_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_nextMacroScope_2300_);
lean_ctor_set(v_reuseFailAlloc_2319_, 2, v___x_2314_);
lean_ctor_set(v_reuseFailAlloc_2319_, 3, v_auxDeclNGen_2301_);
lean_ctor_set(v_reuseFailAlloc_2319_, 4, v_traceState_2302_);
lean_ctor_set(v_reuseFailAlloc_2319_, 5, v_cache_2303_);
lean_ctor_set(v_reuseFailAlloc_2319_, 6, v_messages_2304_);
lean_ctor_set(v_reuseFailAlloc_2319_, 7, v_infoState_2305_);
lean_ctor_set(v_reuseFailAlloc_2319_, 8, v_snapshotTasks_2306_);
v___x_2316_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = lean_st_ref_put(v___y_2289_, v___x_2316_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v_r_2310_);
return v___x_2318_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg___boxed(lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2324_);
lean_dec(v___y_2324_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v___x_2332_; lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
v___x_2332_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2330_);
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2332_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2332_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0___boxed(lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t v_pu_2350_, lean_object* v_binderName_2351_, lean_object* v_type_2352_, uint8_t v_borrow_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2383_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v___x_2359_, 1);
v___x_2361_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_2362_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2351_, v___x_2361_, v_a_2355_);
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2365_ = v___x_2362_;
v_isShared_2366_ = v_isSharedCheck_2383_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2383_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2367_; lean_object* v_lctx_2368_; lean_object* v_nextIdx_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2382_; 
v___x_2367_ = lean_st_ref_take(v_a_2355_);
v_lctx_2368_ = lean_ctor_get(v___x_2367_, 0);
v_nextIdx_2369_ = lean_ctor_get(v___x_2367_, 1);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2371_ = v___x_2367_;
v_isShared_2372_ = v_isSharedCheck_2382_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_nextIdx_2369_);
lean_inc(v_lctx_2368_);
lean_dec(v___x_2367_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2382_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2376_; 
v___x_2373_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2373_, 0, v_a_2360_);
lean_ctor_set(v___x_2373_, 1, v_a_2363_);
lean_ctor_set(v___x_2373_, 2, v_type_2352_);
lean_ctor_set_uint8(v___x_2373_, sizeof(void*)*3, v_borrow_2353_);
lean_inc_ref(v___x_2373_);
v___x_2374_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2350_, v_lctx_2368_, v___x_2373_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v___x_2374_);
v___x_2376_ = v___x_2371_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2381_, 1, v_nextIdx_2369_);
v___x_2376_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2377_; lean_object* v___x_2379_; 
v___x_2377_ = lean_st_ref_put(v_a_2355_, v___x_2376_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2373_);
v___x_2379_ = v___x_2365_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2373_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_dec_ref(v_type_2352_);
lean_dec(v_binderName_2351_);
v_a_2384_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2359_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2359_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam___boxed(lean_object* v_pu_2392_, lean_object* v_binderName_2393_, lean_object* v_type_2394_, lean_object* v_borrow_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_){
_start:
{
uint8_t v_pu_boxed_2401_; uint8_t v_borrow_boxed_2402_; lean_object* v_res_2403_; 
v_pu_boxed_2401_ = lean_unbox(v_pu_2392_);
v_borrow_boxed_2402_ = lean_unbox(v_borrow_2395_);
v_res_2403_ = l_Lean_Compiler_LCNF_mkParam(v_pu_boxed_2401_, v_binderName_2393_, v_type_2394_, v_borrow_boxed_2402_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
lean_dec(v_a_2399_);
lean_dec_ref(v_a_2398_);
lean_dec(v_a_2397_);
lean_dec_ref(v_a_2396_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2407_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___boxed(lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t v_pu_2419_, lean_object* v_binderName_2420_, lean_object* v_type_2421_, lean_object* v_value_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2452_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2429_);
lean_dec_ref_known(v___x_2428_, 1);
v___x_2430_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2431_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2420_, v___x_2430_, v_a_2424_);
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_2452_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2452_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2436_; lean_object* v_lctx_2437_; lean_object* v_nextIdx_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2451_; 
v___x_2436_ = lean_st_ref_take(v_a_2424_);
v_lctx_2437_ = lean_ctor_get(v___x_2436_, 0);
v_nextIdx_2438_ = lean_ctor_get(v___x_2436_, 1);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2440_ = v___x_2436_;
v_isShared_2441_ = v_isSharedCheck_2451_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_nextIdx_2438_);
lean_inc(v_lctx_2437_);
lean_dec(v___x_2436_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2451_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2445_; 
v___x_2442_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2442_, 0, v_a_2429_);
lean_ctor_set(v___x_2442_, 1, v_a_2432_);
lean_ctor_set(v___x_2442_, 2, v_type_2421_);
lean_ctor_set(v___x_2442_, 3, v_value_2422_);
lean_inc_ref(v___x_2442_);
v___x_2443_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2419_, v_lctx_2437_, v___x_2442_);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v___x_2443_);
v___x_2445_ = v___x_2440_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2443_);
lean_ctor_set(v_reuseFailAlloc_2450_, 1, v_nextIdx_2438_);
v___x_2445_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2446_ = lean_st_ref_put(v_a_2424_, v___x_2445_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 0, v___x_2442_);
v___x_2448_ = v___x_2434_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2442_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_dec(v_value_2422_);
lean_dec_ref(v_type_2421_);
lean_dec(v_binderName_2420_);
v_a_2453_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2428_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2428_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl___boxed(lean_object* v_pu_2461_, lean_object* v_binderName_2462_, lean_object* v_type_2463_, lean_object* v_value_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_){
_start:
{
uint8_t v_pu_boxed_2470_; lean_object* v_res_2471_; 
v_pu_boxed_2470_ = lean_unbox(v_pu_2461_);
v_res_2471_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_boxed_2470_, v_binderName_2462_, v_type_2463_, v_value_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_);
lean_dec(v_a_2468_);
lean_dec_ref(v_a_2467_);
lean_dec(v_a_2466_);
lean_dec_ref(v_a_2465_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t v_pu_2475_, lean_object* v_binderName_2476_, lean_object* v_type_2477_, lean_object* v_params_2478_, lean_object* v_value_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_){
_start:
{
lean_object* v___x_2485_; 
v___x_2485_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2509_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_a_2486_);
lean_dec_ref_known(v___x_2485_, 1);
v___x_2487_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFunDecl___closed__1));
v___x_2488_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2476_, v___x_2487_, v_a_2481_);
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2491_ = v___x_2488_;
v_isShared_2492_ = v_isSharedCheck_2509_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2488_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2509_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2493_; lean_object* v_lctx_2494_; lean_object* v_nextIdx_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2508_; 
v___x_2493_ = lean_st_ref_take(v_a_2481_);
v_lctx_2494_ = lean_ctor_get(v___x_2493_, 0);
v_nextIdx_2495_ = lean_ctor_get(v___x_2493_, 1);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2497_ = v___x_2493_;
v_isShared_2498_ = v_isSharedCheck_2508_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_nextIdx_2495_);
lean_inc(v_lctx_2494_);
lean_dec(v___x_2493_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2508_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2499_, 0, v_a_2486_);
lean_ctor_set(v___x_2499_, 1, v_a_2489_);
lean_ctor_set(v___x_2499_, 2, v_params_2478_);
lean_ctor_set(v___x_2499_, 3, v_type_2477_);
lean_ctor_set(v___x_2499_, 4, v_value_2479_);
lean_inc_ref(v___x_2499_);
v___x_2500_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2475_, v_lctx_2494_, v___x_2499_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 0, v___x_2500_);
v___x_2502_ = v___x_2497_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2500_);
lean_ctor_set(v_reuseFailAlloc_2507_, 1, v_nextIdx_2495_);
v___x_2502_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_object* v___x_2503_; lean_object* v___x_2505_; 
v___x_2503_ = lean_st_ref_put(v_a_2481_, v___x_2502_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 0, v___x_2499_);
v___x_2505_ = v___x_2491_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2499_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
}
else
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
lean_dec_ref(v_value_2479_);
lean_dec_ref(v_params_2478_);
lean_dec_ref(v_type_2477_);
lean_dec(v_binderName_2476_);
v_a_2510_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2485_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2485_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl___boxed(lean_object* v_pu_2518_, lean_object* v_binderName_2519_, lean_object* v_type_2520_, lean_object* v_params_2521_, lean_object* v_value_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_){
_start:
{
uint8_t v_pu_boxed_2528_; lean_object* v_res_2529_; 
v_pu_boxed_2528_ = lean_unbox(v_pu_2518_);
v_res_2529_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_boxed_2528_, v_binderName_2519_, v_type_2520_, v_params_2521_, v_value_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2523_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(uint8_t v_pu_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v_a_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2536_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2537_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2536_, v_a_2532_);
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2538_);
lean_dec_ref(v___x_2537_);
v___x_2539_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2540_ = lean_box(1);
v___x_2541_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2530_, v_a_2538_, v___x_2539_, v___x_2540_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased___boxed(lean_object* v_pu_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
uint8_t v_pu_boxed_2548_; lean_object* v_res_2549_; 
v_pu_boxed_2548_ = lean_unbox(v_pu_2542_);
v_res_2549_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_boxed_2548_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
lean_dec(v_a_2546_);
lean_dec_ref(v_a_2545_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t v_pu_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2567_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2567_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2567_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v_fvarId_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2565_; 
v_fvarId_2561_ = lean_ctor_get(v_a_2557_, 0);
lean_inc(v_fvarId_2561_);
v___x_2562_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2562_, 0, v_fvarId_2561_);
v___x_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2563_, 0, v_a_2557_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2563_);
v___x_2565_ = v___x_2559_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2563_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
v_a_2568_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2556_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2556_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased___boxed(lean_object* v_pu_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_){
_start:
{
uint8_t v_pu_boxed_2582_; lean_object* v_res_2583_; 
v_pu_boxed_2582_ = lean_unbox(v_pu_2576_);
v_res_2583_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_boxed_2582_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t v_pu_2584_, lean_object* v_p_2585_, lean_object* v_type_2586_, lean_object* v_a_2587_){
_start:
{
lean_object* v_fvarId_2589_; lean_object* v_binderName_2590_; lean_object* v_type_2591_; uint8_t v_borrow_2592_; size_t v___x_2593_; size_t v___x_2594_; uint8_t v___x_2595_; 
v_fvarId_2589_ = lean_ctor_get(v_p_2585_, 0);
v_binderName_2590_ = lean_ctor_get(v_p_2585_, 1);
v_type_2591_ = lean_ctor_get(v_p_2585_, 2);
v_borrow_2592_ = lean_ctor_get_uint8(v_p_2585_, sizeof(void*)*3);
v___x_2593_ = lean_ptr_addr(v_type_2586_);
v___x_2594_ = lean_ptr_addr(v_type_2591_);
v___x_2595_ = lean_usize_dec_eq(v___x_2593_, v___x_2594_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2615_; 
lean_inc(v_binderName_2590_);
lean_inc(v_fvarId_2589_);
v_isSharedCheck_2615_ = !lean_is_exclusive(v_p_2585_);
if (v_isSharedCheck_2615_ == 0)
{
lean_object* v_unused_2616_; lean_object* v_unused_2617_; lean_object* v_unused_2618_; 
v_unused_2616_ = lean_ctor_get(v_p_2585_, 2);
lean_dec(v_unused_2616_);
v_unused_2617_ = lean_ctor_get(v_p_2585_, 1);
lean_dec(v_unused_2617_);
v_unused_2618_ = lean_ctor_get(v_p_2585_, 0);
lean_dec(v_unused_2618_);
v___x_2597_ = v_p_2585_;
v_isShared_2598_ = v_isSharedCheck_2615_;
goto v_resetjp_2596_;
}
else
{
lean_dec(v_p_2585_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2615_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2599_; lean_object* v_lctx_2600_; lean_object* v_nextIdx_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2614_; 
v___x_2599_ = lean_st_ref_take(v_a_2587_);
v_lctx_2600_ = lean_ctor_get(v___x_2599_, 0);
v_nextIdx_2601_ = lean_ctor_get(v___x_2599_, 1);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2603_ = v___x_2599_;
v_isShared_2604_ = v_isSharedCheck_2614_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_nextIdx_2601_);
lean_inc(v_lctx_2600_);
lean_dec(v___x_2599_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2614_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v_p_2606_; 
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 2, v_type_2586_);
v_p_2606_ = v___x_2597_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_fvarId_2589_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v_binderName_2590_);
lean_ctor_set(v_reuseFailAlloc_2613_, 2, v_type_2586_);
lean_ctor_set_uint8(v_reuseFailAlloc_2613_, sizeof(void*)*3, v_borrow_2592_);
v_p_2606_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
lean_object* v___x_2607_; lean_object* v___x_2609_; 
lean_inc_ref(v_p_2606_);
v___x_2607_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2584_, v_lctx_2600_, v_p_2606_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2607_);
v___x_2609_ = v___x_2603_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2607_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_nextIdx_2601_);
v___x_2609_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = lean_st_ref_put(v_a_2587_, v___x_2609_);
v___x_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2611_, 0, v_p_2606_);
return v___x_2611_;
}
}
}
}
}
else
{
lean_object* v___x_2619_; 
lean_dec_ref(v_type_2586_);
v___x_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2619_, 0, v_p_2585_);
return v___x_2619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg___boxed(lean_object* v_pu_2620_, lean_object* v_p_2621_, lean_object* v_type_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_){
_start:
{
uint8_t v_pu_boxed_2625_; lean_object* v_res_2626_; 
v_pu_boxed_2625_ = lean_unbox(v_pu_2620_);
v_res_2626_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_boxed_2625_, v_p_2621_, v_type_2622_, v_a_2623_);
lean_dec(v_a_2623_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(uint8_t v_pu_2627_, lean_object* v_p_2628_, lean_object* v_type_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_2627_, v_p_2628_, v_type_2629_, v_a_2631_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(lean_object* v_pu_2636_, lean_object* v_p_2637_, lean_object* v_type_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_){
_start:
{
uint8_t v_pu_boxed_2644_; lean_object* v_res_2645_; 
v_pu_boxed_2644_ = lean_unbox(v_pu_2636_);
v_res_2645_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(v_pu_boxed_2644_, v_p_2637_, v_type_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec(v_a_2640_);
lean_dec_ref(v_a_2639_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t v_pu_2646_, lean_object* v_p_2647_, uint8_t v_borrow_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v_fvarId_2651_; lean_object* v_binderName_2652_; lean_object* v_type_2653_; uint8_t v_borrow_2654_; 
v_fvarId_2651_ = lean_ctor_get(v_p_2647_, 0);
v_binderName_2652_ = lean_ctor_get(v_p_2647_, 1);
v_type_2653_ = lean_ctor_get(v_p_2647_, 2);
v_borrow_2654_ = lean_ctor_get_uint8(v_p_2647_, sizeof(void*)*3);
if (v_borrow_2654_ == 0)
{
if (v_borrow_2648_ == 0)
{
lean_object* v___x_2670_; 
v___x_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2670_, 0, v_p_2647_);
return v___x_2670_;
}
else
{
lean_inc_ref(v_type_2653_);
lean_inc(v_binderName_2652_);
lean_inc(v_fvarId_2651_);
lean_dec_ref(v_p_2647_);
goto v___jp_2655_;
}
}
else
{
if (v_borrow_2648_ == 0)
{
lean_inc_ref(v_type_2653_);
lean_inc(v_binderName_2652_);
lean_inc(v_fvarId_2651_);
lean_dec_ref(v_p_2647_);
goto v___jp_2655_;
}
else
{
lean_object* v___x_2671_; 
v___x_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2671_, 0, v_p_2647_);
return v___x_2671_;
}
}
v___jp_2655_:
{
lean_object* v___x_2656_; lean_object* v_lctx_2657_; lean_object* v_nextIdx_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2669_; 
v___x_2656_ = lean_st_ref_take(v_a_2649_);
v_lctx_2657_ = lean_ctor_get(v___x_2656_, 0);
v_nextIdx_2658_ = lean_ctor_get(v___x_2656_, 1);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2660_ = v___x_2656_;
v_isShared_2661_ = v_isSharedCheck_2669_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_nextIdx_2658_);
lean_inc(v_lctx_2657_);
lean_dec(v___x_2656_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2669_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v_p_2662_; lean_object* v___x_2663_; lean_object* v___x_2665_; 
v_p_2662_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_p_2662_, 0, v_fvarId_2651_);
lean_ctor_set(v_p_2662_, 1, v_binderName_2652_);
lean_ctor_set(v_p_2662_, 2, v_type_2653_);
lean_ctor_set_uint8(v_p_2662_, sizeof(void*)*3, v_borrow_2648_);
lean_inc_ref(v_p_2662_);
v___x_2663_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2646_, v_lctx_2657_, v_p_2662_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2663_);
v___x_2665_ = v___x_2660_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2663_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v_nextIdx_2658_);
v___x_2665_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = lean_st_ref_put(v_a_2649_, v___x_2665_);
v___x_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2667_, 0, v_p_2662_);
return v___x_2667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg___boxed(lean_object* v_pu_2672_, lean_object* v_p_2673_, lean_object* v_borrow_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_){
_start:
{
uint8_t v_pu_boxed_2677_; uint8_t v_borrow_boxed_2678_; lean_object* v_res_2679_; 
v_pu_boxed_2677_ = lean_unbox(v_pu_2672_);
v_borrow_boxed_2678_ = lean_unbox(v_borrow_2674_);
v_res_2679_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_boxed_2677_, v_p_2673_, v_borrow_boxed_2678_, v_a_2675_);
lean_dec(v_a_2675_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(uint8_t v_pu_2680_, lean_object* v_p_2681_, uint8_t v_borrow_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_2680_, v_p_2681_, v_borrow_2682_, v_a_2684_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___boxed(lean_object* v_pu_2689_, lean_object* v_p_2690_, lean_object* v_borrow_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
uint8_t v_pu_boxed_2697_; uint8_t v_borrow_boxed_2698_; lean_object* v_res_2699_; 
v_pu_boxed_2697_ = lean_unbox(v_pu_2689_);
v_borrow_boxed_2698_ = lean_unbox(v_borrow_2691_);
v_res_2699_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(v_pu_boxed_2697_, v_p_2690_, v_borrow_boxed_2698_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t v_pu_2700_, lean_object* v_decl_2701_, lean_object* v_type_2702_, lean_object* v_value_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v_fvarId_2706_; lean_object* v_binderName_2707_; lean_object* v_type_2708_; lean_object* v_value_2709_; size_t v___x_2725_; size_t v___x_2726_; uint8_t v___x_2727_; 
v_fvarId_2706_ = lean_ctor_get(v_decl_2701_, 0);
v_binderName_2707_ = lean_ctor_get(v_decl_2701_, 1);
v_type_2708_ = lean_ctor_get(v_decl_2701_, 2);
v_value_2709_ = lean_ctor_get(v_decl_2701_, 3);
v___x_2725_ = lean_ptr_addr(v_type_2702_);
v___x_2726_ = lean_ptr_addr(v_type_2708_);
v___x_2727_ = lean_usize_dec_eq(v___x_2725_, v___x_2726_);
if (v___x_2727_ == 0)
{
lean_inc(v_binderName_2707_);
lean_inc(v_fvarId_2706_);
lean_dec_ref(v_decl_2701_);
goto v___jp_2710_;
}
else
{
size_t v___x_2728_; size_t v___x_2729_; uint8_t v___x_2730_; 
v___x_2728_ = lean_ptr_addr(v_value_2703_);
v___x_2729_ = lean_ptr_addr(v_value_2709_);
v___x_2730_ = lean_usize_dec_eq(v___x_2728_, v___x_2729_);
if (v___x_2730_ == 0)
{
lean_inc(v_binderName_2707_);
lean_inc(v_fvarId_2706_);
lean_dec_ref(v_decl_2701_);
goto v___jp_2710_;
}
else
{
lean_object* v___x_2731_; 
lean_dec(v_value_2703_);
lean_dec_ref(v_type_2702_);
v___x_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2731_, 0, v_decl_2701_);
return v___x_2731_;
}
}
v___jp_2710_:
{
lean_object* v___x_2711_; lean_object* v_lctx_2712_; lean_object* v_nextIdx_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2724_; 
v___x_2711_ = lean_st_ref_take(v_a_2704_);
v_lctx_2712_ = lean_ctor_get(v___x_2711_, 0);
v_nextIdx_2713_ = lean_ctor_get(v___x_2711_, 1);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2715_ = v___x_2711_;
v_isShared_2716_ = v_isSharedCheck_2724_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_nextIdx_2713_);
lean_inc(v_lctx_2712_);
lean_dec(v___x_2711_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2724_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v_decl_2717_; lean_object* v___x_2718_; lean_object* v___x_2720_; 
v_decl_2717_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_decl_2717_, 0, v_fvarId_2706_);
lean_ctor_set(v_decl_2717_, 1, v_binderName_2707_);
lean_ctor_set(v_decl_2717_, 2, v_type_2702_);
lean_ctor_set(v_decl_2717_, 3, v_value_2703_);
lean_inc_ref(v_decl_2717_);
v___x_2718_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2700_, v_lctx_2712_, v_decl_2717_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 0, v___x_2718_);
v___x_2720_ = v___x_2715_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2718_);
lean_ctor_set(v_reuseFailAlloc_2723_, 1, v_nextIdx_2713_);
v___x_2720_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2721_ = lean_st_ref_put(v_a_2704_, v___x_2720_);
v___x_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2722_, 0, v_decl_2717_);
return v___x_2722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg___boxed(lean_object* v_pu_2732_, lean_object* v_decl_2733_, lean_object* v_type_2734_, lean_object* v_value_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
uint8_t v_pu_boxed_2738_; lean_object* v_res_2739_; 
v_pu_boxed_2738_ = lean_unbox(v_pu_2732_);
v_res_2739_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_boxed_2738_, v_decl_2733_, v_type_2734_, v_value_2735_, v_a_2736_);
lean_dec(v_a_2736_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(uint8_t v_pu_2740_, lean_object* v_decl_2741_, lean_object* v_type_2742_, lean_object* v_value_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2740_, v_decl_2741_, v_type_2742_, v_value_2743_, v_a_2745_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(lean_object* v_pu_2750_, lean_object* v_decl_2751_, lean_object* v_type_2752_, lean_object* v_value_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
uint8_t v_pu_boxed_2759_; lean_object* v_res_2760_; 
v_pu_boxed_2759_ = lean_unbox(v_pu_2750_);
v_res_2760_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(v_pu_boxed_2759_, v_decl_2751_, v_type_2752_, v_value_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_);
lean_dec(v_a_2757_);
lean_dec_ref(v_a_2756_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t v_pu_2761_, lean_object* v_decl_2762_, lean_object* v_value_2763_, lean_object* v_a_2764_){
_start:
{
lean_object* v_type_2766_; lean_object* v___x_2767_; 
v_type_2766_ = lean_ctor_get(v_decl_2762_, 2);
lean_inc_ref(v_type_2766_);
v___x_2767_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2761_, v_decl_2762_, v_type_2766_, v_value_2763_, v_a_2764_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg___boxed(lean_object* v_pu_2768_, lean_object* v_decl_2769_, lean_object* v_value_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
uint8_t v_pu_boxed_2773_; lean_object* v_res_2774_; 
v_pu_boxed_2773_ = lean_unbox(v_pu_2768_);
v_res_2774_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_boxed_2773_, v_decl_2769_, v_value_2770_, v_a_2771_);
lean_dec(v_a_2771_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(uint8_t v_pu_2775_, lean_object* v_decl_2776_, lean_object* v_value_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_){
_start:
{
lean_object* v___x_2783_; 
v___x_2783_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_2775_, v_decl_2776_, v_value_2777_, v_a_2779_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___boxed(lean_object* v_pu_2784_, lean_object* v_decl_2785_, lean_object* v_value_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
uint8_t v_pu_boxed_2792_; lean_object* v_res_2793_; 
v_pu_boxed_2792_ = lean_unbox(v_pu_2784_);
v_res_2793_ = l_Lean_Compiler_LCNF_LetDecl_updateValue(v_pu_boxed_2792_, v_decl_2785_, v_value_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_);
lean_dec(v_a_2790_);
lean_dec_ref(v_a_2789_);
lean_dec(v_a_2788_);
lean_dec_ref(v_a_2787_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t v_pu_2794_, lean_object* v_decl_2795_, lean_object* v_type_2796_, lean_object* v_params_2797_, lean_object* v_value_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v_fvarId_2801_; lean_object* v_binderName_2802_; lean_object* v_params_2803_; lean_object* v_type_2804_; lean_object* v_value_2805_; size_t v___x_2821_; size_t v___x_2822_; uint8_t v___x_2823_; 
v_fvarId_2801_ = lean_ctor_get(v_decl_2795_, 0);
v_binderName_2802_ = lean_ctor_get(v_decl_2795_, 1);
v_params_2803_ = lean_ctor_get(v_decl_2795_, 2);
v_type_2804_ = lean_ctor_get(v_decl_2795_, 3);
v_value_2805_ = lean_ctor_get(v_decl_2795_, 4);
v___x_2821_ = lean_ptr_addr(v_type_2796_);
v___x_2822_ = lean_ptr_addr(v_type_2804_);
v___x_2823_ = lean_usize_dec_eq(v___x_2821_, v___x_2822_);
if (v___x_2823_ == 0)
{
lean_inc(v_binderName_2802_);
lean_inc(v_fvarId_2801_);
lean_dec_ref(v_decl_2795_);
goto v___jp_2806_;
}
else
{
size_t v___x_2824_; size_t v___x_2825_; uint8_t v___x_2826_; 
v___x_2824_ = lean_ptr_addr(v_params_2797_);
v___x_2825_ = lean_ptr_addr(v_params_2803_);
v___x_2826_ = lean_usize_dec_eq(v___x_2824_, v___x_2825_);
if (v___x_2826_ == 0)
{
lean_inc(v_binderName_2802_);
lean_inc(v_fvarId_2801_);
lean_dec_ref(v_decl_2795_);
goto v___jp_2806_;
}
else
{
size_t v___x_2827_; size_t v___x_2828_; uint8_t v___x_2829_; 
v___x_2827_ = lean_ptr_addr(v_value_2798_);
v___x_2828_ = lean_ptr_addr(v_value_2805_);
v___x_2829_ = lean_usize_dec_eq(v___x_2827_, v___x_2828_);
if (v___x_2829_ == 0)
{
lean_inc(v_binderName_2802_);
lean_inc(v_fvarId_2801_);
lean_dec_ref(v_decl_2795_);
goto v___jp_2806_;
}
else
{
lean_object* v___x_2830_; 
lean_dec_ref(v_value_2798_);
lean_dec_ref(v_params_2797_);
lean_dec_ref(v_type_2796_);
v___x_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2830_, 0, v_decl_2795_);
return v___x_2830_;
}
}
}
v___jp_2806_:
{
lean_object* v___x_2807_; lean_object* v_lctx_2808_; lean_object* v_nextIdx_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2820_; 
v___x_2807_ = lean_st_ref_take(v_a_2799_);
v_lctx_2808_ = lean_ctor_get(v___x_2807_, 0);
v_nextIdx_2809_ = lean_ctor_get(v___x_2807_, 1);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2811_ = v___x_2807_;
v_isShared_2812_ = v_isSharedCheck_2820_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_nextIdx_2809_);
lean_inc(v_lctx_2808_);
lean_dec(v___x_2807_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2820_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v_decl_2813_; lean_object* v___x_2814_; lean_object* v___x_2816_; 
v_decl_2813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_decl_2813_, 0, v_fvarId_2801_);
lean_ctor_set(v_decl_2813_, 1, v_binderName_2802_);
lean_ctor_set(v_decl_2813_, 2, v_params_2797_);
lean_ctor_set(v_decl_2813_, 3, v_type_2796_);
lean_ctor_set(v_decl_2813_, 4, v_value_2798_);
lean_inc_ref(v_decl_2813_);
v___x_2814_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2794_, v_lctx_2808_, v_decl_2813_);
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 0, v___x_2814_);
v___x_2816_ = v___x_2811_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2814_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v_nextIdx_2809_);
v___x_2816_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = lean_st_ref_put(v_a_2799_, v___x_2816_);
v___x_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2818_, 0, v_decl_2813_);
return v___x_2818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg___boxed(lean_object* v_pu_2831_, lean_object* v_decl_2832_, lean_object* v_type_2833_, lean_object* v_params_2834_, lean_object* v_value_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_){
_start:
{
uint8_t v_pu_boxed_2838_; lean_object* v_res_2839_; 
v_pu_boxed_2838_ = lean_unbox(v_pu_2831_);
v_res_2839_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_boxed_2838_, v_decl_2832_, v_type_2833_, v_params_2834_, v_value_2835_, v_a_2836_);
lean_dec(v_a_2836_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(uint8_t v_pu_2840_, lean_object* v_decl_2841_, lean_object* v_type_2842_, lean_object* v_params_2843_, lean_object* v_value_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2840_, v_decl_2841_, v_type_2842_, v_params_2843_, v_value_2844_, v_a_2846_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(lean_object* v_pu_2851_, lean_object* v_decl_2852_, lean_object* v_type_2853_, lean_object* v_params_2854_, lean_object* v_value_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
uint8_t v_pu_boxed_2861_; lean_object* v_res_2862_; 
v_pu_boxed_2861_ = lean_unbox(v_pu_2851_);
v_res_2862_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(v_pu_boxed_2861_, v_decl_2852_, v_type_2853_, v_params_2854_, v_value_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_);
lean_dec(v_a_2859_);
lean_dec_ref(v_a_2858_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(uint8_t v_pu_2863_, lean_object* v_decl_2864_, lean_object* v_type_2865_, lean_object* v_value_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v_params_2869_; lean_object* v___x_2870_; 
v_params_2869_ = lean_ctor_get(v_decl_2864_, 2);
lean_inc_ref(v_params_2869_);
v___x_2870_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2863_, v_decl_2864_, v_type_2865_, v_params_2869_, v_value_2866_, v_a_2867_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg___boxed(lean_object* v_pu_2871_, lean_object* v_decl_2872_, lean_object* v_type_2873_, lean_object* v_value_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_){
_start:
{
uint8_t v_pu_boxed_2877_; lean_object* v_res_2878_; 
v_pu_boxed_2877_ = lean_unbox(v_pu_2871_);
v_res_2878_ = l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(v_pu_boxed_2877_, v_decl_2872_, v_type_2873_, v_value_2874_, v_a_2875_);
lean_dec(v_a_2875_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27(uint8_t v_pu_2879_, lean_object* v_decl_2880_, lean_object* v_type_2881_, lean_object* v_value_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v_params_2888_; lean_object* v___x_2889_; 
v_params_2888_ = lean_ctor_get(v_decl_2880_, 2);
lean_inc_ref(v_params_2888_);
v___x_2889_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2879_, v_decl_2880_, v_type_2881_, v_params_2888_, v_value_2882_, v_a_2884_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___boxed(lean_object* v_pu_2890_, lean_object* v_decl_2891_, lean_object* v_type_2892_, lean_object* v_value_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_){
_start:
{
uint8_t v_pu_boxed_2899_; lean_object* v_res_2900_; 
v_pu_boxed_2899_ = lean_unbox(v_pu_2890_);
v_res_2900_ = l_Lean_Compiler_LCNF_FunDecl_update_x27(v_pu_boxed_2899_, v_decl_2891_, v_type_2892_, v_value_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
lean_dec(v_a_2897_);
lean_dec_ref(v_a_2896_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(uint8_t v_pu_2901_, lean_object* v_decl_2902_, lean_object* v_value_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v_params_2906_; lean_object* v_type_2907_; lean_object* v___x_2908_; 
v_params_2906_ = lean_ctor_get(v_decl_2902_, 2);
lean_inc_ref(v_params_2906_);
v_type_2907_ = lean_ctor_get(v_decl_2902_, 3);
lean_inc_ref(v_type_2907_);
v___x_2908_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2901_, v_decl_2902_, v_type_2907_, v_params_2906_, v_value_2903_, v_a_2904_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg___boxed(lean_object* v_pu_2909_, lean_object* v_decl_2910_, lean_object* v_value_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_){
_start:
{
uint8_t v_pu_boxed_2914_; lean_object* v_res_2915_; 
v_pu_boxed_2914_ = lean_unbox(v_pu_2909_);
v_res_2915_ = l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(v_pu_boxed_2914_, v_decl_2910_, v_value_2911_, v_a_2912_);
lean_dec(v_a_2912_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue(uint8_t v_pu_2916_, lean_object* v_decl_2917_, lean_object* v_value_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_){
_start:
{
lean_object* v_params_2924_; lean_object* v_type_2925_; lean_object* v___x_2926_; 
v_params_2924_ = lean_ctor_get(v_decl_2917_, 2);
lean_inc_ref(v_params_2924_);
v_type_2925_ = lean_ctor_get(v_decl_2917_, 3);
lean_inc_ref(v_type_2925_);
v___x_2926_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2916_, v_decl_2917_, v_type_2925_, v_params_2924_, v_value_2918_, v_a_2920_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___boxed(lean_object* v_pu_2927_, lean_object* v_decl_2928_, lean_object* v_value_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_){
_start:
{
uint8_t v_pu_boxed_2935_; lean_object* v_res_2936_; 
v_pu_boxed_2935_ = lean_unbox(v_pu_2927_);
v_res_2936_ = l_Lean_Compiler_LCNF_FunDecl_updateValue(v_pu_boxed_2935_, v_decl_2928_, v_value_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_);
lean_dec(v_a_2933_);
lean_dec_ref(v_a_2932_);
lean_dec(v_a_2931_);
lean_dec_ref(v_a_2930_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0(uint8_t v_pu_2937_, lean_object* v_p_2938_, lean_object* v_inst_2939_, lean_object* v_____do__lift_2940_){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2941_ = lean_box(v_pu_2937_);
v___x_2942_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_2942_, 0, v___x_2941_);
lean_closure_set(v___x_2942_, 1, v_p_2938_);
lean_closure_set(v___x_2942_, 2, v_____do__lift_2940_);
v___x_2943_ = lean_apply_2(v_inst_2939_, lean_box(0), v___x_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed(lean_object* v_pu_2944_, lean_object* v_p_2945_, lean_object* v_inst_2946_, lean_object* v_____do__lift_2947_){
_start:
{
uint8_t v_pu_boxed_2948_; lean_object* v_res_2949_; 
v_pu_boxed_2948_ = lean_unbox(v_pu_2944_);
v_res_2949_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__0(v_pu_boxed_2948_, v_p_2945_, v_inst_2946_, v_____do__lift_2947_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1(uint8_t v_pu_2950_, uint8_t v_t_2951_, lean_object* v_type_2952_, lean_object* v_toPure_2953_, lean_object* v_____do__lift_2954_){
_start:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2950_, v_____do__lift_2954_, v_t_2951_, v_type_2952_);
v___x_2956_ = lean_apply_2(v_toPure_2953_, lean_box(0), v___x_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed(lean_object* v_pu_2957_, lean_object* v_t_2958_, lean_object* v_type_2959_, lean_object* v_toPure_2960_, lean_object* v_____do__lift_2961_){
_start:
{
uint8_t v_pu_boxed_2962_; uint8_t v_t_boxed_2963_; lean_object* v_res_2964_; 
v_pu_boxed_2962_ = lean_unbox(v_pu_2957_);
v_t_boxed_2963_ = lean_unbox(v_t_2958_);
v_res_2964_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__1(v_pu_boxed_2962_, v_t_boxed_2963_, v_type_2959_, v_toPure_2960_, v_____do__lift_2961_);
lean_dec_ref(v_____do__lift_2961_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg(uint8_t v_pu_2965_, uint8_t v_t_2966_, lean_object* v_inst_2967_, lean_object* v_inst_2968_, lean_object* v_inst_2969_, lean_object* v_p_2970_){
_start:
{
lean_object* v_toApplicative_2971_; lean_object* v_toBind_2972_; lean_object* v_type_2973_; lean_object* v_toPure_2974_; lean_object* v___x_2975_; lean_object* v___f_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___f_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v_toApplicative_2971_ = lean_ctor_get(v_inst_2968_, 0);
lean_inc_ref(v_toApplicative_2971_);
v_toBind_2972_ = lean_ctor_get(v_inst_2968_, 1);
lean_inc_n(v_toBind_2972_, 2);
lean_dec_ref(v_inst_2968_);
v_type_2973_ = lean_ctor_get(v_p_2970_, 2);
lean_inc_ref(v_type_2973_);
v_toPure_2974_ = lean_ctor_get(v_toApplicative_2971_, 1);
lean_inc(v_toPure_2974_);
lean_dec_ref(v_toApplicative_2971_);
v___x_2975_ = lean_box(v_pu_2965_);
v___f_2976_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2976_, 0, v___x_2975_);
lean_closure_set(v___f_2976_, 1, v_p_2970_);
lean_closure_set(v___f_2976_, 2, v_inst_2967_);
v___x_2977_ = lean_box(v_pu_2965_);
v___x_2978_ = lean_box(v_t_2966_);
v___f_2979_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2979_, 0, v___x_2977_);
lean_closure_set(v___f_2979_, 1, v___x_2978_);
lean_closure_set(v___f_2979_, 2, v_type_2973_);
lean_closure_set(v___f_2979_, 3, v_toPure_2974_);
v___x_2980_ = lean_apply_4(v_toBind_2972_, lean_box(0), lean_box(0), v_inst_2969_, v___f_2979_);
v___x_2981_ = lean_apply_4(v_toBind_2972_, lean_box(0), lean_box(0), v___x_2980_, v___f_2976_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___boxed(lean_object* v_pu_2982_, lean_object* v_t_2983_, lean_object* v_inst_2984_, lean_object* v_inst_2985_, lean_object* v_inst_2986_, lean_object* v_p_2987_){
_start:
{
uint8_t v_pu_boxed_2988_; uint8_t v_t_boxed_2989_; lean_object* v_res_2990_; 
v_pu_boxed_2988_ = lean_unbox(v_pu_2982_);
v_t_boxed_2989_ = lean_unbox(v_t_2983_);
v_res_2990_ = l_Lean_Compiler_LCNF_normParam___redArg(v_pu_boxed_2988_, v_t_boxed_2989_, v_inst_2984_, v_inst_2985_, v_inst_2986_, v_p_2987_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam(lean_object* v_m_2991_, uint8_t v_pu_2992_, uint8_t v_t_2993_, lean_object* v_inst_2994_, lean_object* v_inst_2995_, lean_object* v_inst_2996_, lean_object* v_p_2997_){
_start:
{
lean_object* v_toApplicative_2998_; lean_object* v_toBind_2999_; lean_object* v_type_3000_; lean_object* v_toPure_3001_; lean_object* v___x_3002_; lean_object* v___f_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___f_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v_toApplicative_2998_ = lean_ctor_get(v_inst_2995_, 0);
lean_inc_ref(v_toApplicative_2998_);
v_toBind_2999_ = lean_ctor_get(v_inst_2995_, 1);
lean_inc_n(v_toBind_2999_, 2);
lean_dec_ref(v_inst_2995_);
v_type_3000_ = lean_ctor_get(v_p_2997_, 2);
lean_inc_ref(v_type_3000_);
v_toPure_3001_ = lean_ctor_get(v_toApplicative_2998_, 1);
lean_inc(v_toPure_3001_);
lean_dec_ref(v_toApplicative_2998_);
v___x_3002_ = lean_box(v_pu_2992_);
v___f_3003_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3003_, 0, v___x_3002_);
lean_closure_set(v___f_3003_, 1, v_p_2997_);
lean_closure_set(v___f_3003_, 2, v_inst_2994_);
v___x_3004_ = lean_box(v_pu_2992_);
v___x_3005_ = lean_box(v_t_2993_);
v___f_3006_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3006_, 0, v___x_3004_);
lean_closure_set(v___f_3006_, 1, v___x_3005_);
lean_closure_set(v___f_3006_, 2, v_type_3000_);
lean_closure_set(v___f_3006_, 3, v_toPure_3001_);
v___x_3007_ = lean_apply_4(v_toBind_2999_, lean_box(0), lean_box(0), v_inst_2996_, v___f_3006_);
v___x_3008_ = lean_apply_4(v_toBind_2999_, lean_box(0), lean_box(0), v___x_3007_, v___f_3003_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___boxed(lean_object* v_m_3009_, lean_object* v_pu_3010_, lean_object* v_t_3011_, lean_object* v_inst_3012_, lean_object* v_inst_3013_, lean_object* v_inst_3014_, lean_object* v_p_3015_){
_start:
{
uint8_t v_pu_boxed_3016_; uint8_t v_t_boxed_3017_; lean_object* v_res_3018_; 
v_pu_boxed_3016_ = lean_unbox(v_pu_3010_);
v_t_boxed_3017_ = lean_unbox(v_t_3011_);
v_res_3018_ = l_Lean_Compiler_LCNF_normParam(v_m_3009_, v_pu_boxed_3016_, v_t_boxed_3017_, v_inst_3012_, v_inst_3013_, v_inst_3014_, v_p_3015_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg(uint8_t v_pu_3019_, uint8_t v_t_3020_, lean_object* v_inst_3021_, lean_object* v_inst_3022_, lean_object* v_inst_3023_, lean_object* v_ps_3024_){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3025_ = lean_box(v_pu_3019_);
v___x_3026_ = lean_box(v_t_3020_);
lean_inc_ref(v_inst_3022_);
v___x_3027_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___boxed), 7, 6);
lean_closure_set(v___x_3027_, 0, lean_box(0));
lean_closure_set(v___x_3027_, 1, v___x_3025_);
lean_closure_set(v___x_3027_, 2, v___x_3026_);
lean_closure_set(v___x_3027_, 3, v_inst_3021_);
lean_closure_set(v___x_3027_, 4, v_inst_3022_);
lean_closure_set(v___x_3027_, 5, v_inst_3023_);
v___x_3028_ = lean_unsigned_to_nat(0u);
v___x_3029_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_3022_, v___x_3027_, v___x_3028_, v_ps_3024_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg___boxed(lean_object* v_pu_3030_, lean_object* v_t_3031_, lean_object* v_inst_3032_, lean_object* v_inst_3033_, lean_object* v_inst_3034_, lean_object* v_ps_3035_){
_start:
{
uint8_t v_pu_boxed_3036_; uint8_t v_t_boxed_3037_; lean_object* v_res_3038_; 
v_pu_boxed_3036_ = lean_unbox(v_pu_3030_);
v_t_boxed_3037_ = lean_unbox(v_t_3031_);
v_res_3038_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_boxed_3036_, v_t_boxed_3037_, v_inst_3032_, v_inst_3033_, v_inst_3034_, v_ps_3035_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams(lean_object* v_m_3039_, uint8_t v_pu_3040_, uint8_t v_t_3041_, lean_object* v_inst_3042_, lean_object* v_inst_3043_, lean_object* v_inst_3044_, lean_object* v_ps_3045_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_3040_, v_t_3041_, v_inst_3042_, v_inst_3043_, v_inst_3044_, v_ps_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___boxed(lean_object* v_m_3047_, lean_object* v_pu_3048_, lean_object* v_t_3049_, lean_object* v_inst_3050_, lean_object* v_inst_3051_, lean_object* v_inst_3052_, lean_object* v_ps_3053_){
_start:
{
uint8_t v_pu_boxed_3054_; uint8_t v_t_boxed_3055_; lean_object* v_res_3056_; 
v_pu_boxed_3054_ = lean_unbox(v_pu_3048_);
v_t_boxed_3055_ = lean_unbox(v_t_3049_);
v_res_3056_ = l_Lean_Compiler_LCNF_normParams(v_m_3047_, v_pu_boxed_3054_, v_t_boxed_3055_, v_inst_3050_, v_inst_3051_, v_inst_3052_, v_ps_3053_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(uint8_t v_pu_3057_, lean_object* v_decl_3058_, lean_object* v_____do__lift_3059_, lean_object* v_inst_3060_, lean_object* v_____do__lift_3061_){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3062_ = lean_box(v_pu_3057_);
v___x_3063_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_3063_, 0, v___x_3062_);
lean_closure_set(v___x_3063_, 1, v_decl_3058_);
lean_closure_set(v___x_3063_, 2, v_____do__lift_3059_);
lean_closure_set(v___x_3063_, 3, v_____do__lift_3061_);
v___x_3064_ = lean_apply_2(v_inst_3060_, lean_box(0), v___x_3063_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed(lean_object* v_pu_3065_, lean_object* v_decl_3066_, lean_object* v_____do__lift_3067_, lean_object* v_inst_3068_, lean_object* v_____do__lift_3069_){
_start:
{
uint8_t v_pu_boxed_3070_; lean_object* v_res_3071_; 
v_pu_boxed_3070_ = lean_unbox(v_pu_3065_);
v_res_3071_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(v_pu_boxed_3070_, v_decl_3066_, v_____do__lift_3067_, v_inst_3068_, v_____do__lift_3069_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(uint8_t v_pu_3072_, lean_object* v_value_3073_, uint8_t v_t_3074_, lean_object* v_toPure_3075_, lean_object* v_____do__lift_3076_){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3072_, v_____do__lift_3076_, v_value_3073_, v_t_3074_);
v___x_3078_ = lean_apply_2(v_toPure_3075_, lean_box(0), v___x_3077_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed(lean_object* v_pu_3079_, lean_object* v_value_3080_, lean_object* v_t_3081_, lean_object* v_toPure_3082_, lean_object* v_____do__lift_3083_){
_start:
{
uint8_t v_pu_boxed_3084_; uint8_t v_t_boxed_3085_; lean_object* v_res_3086_; 
v_pu_boxed_3084_ = lean_unbox(v_pu_3079_);
v_t_boxed_3085_ = lean_unbox(v_t_3081_);
v_res_3086_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(v_pu_boxed_3084_, v_value_3080_, v_t_boxed_3085_, v_toPure_3082_, v_____do__lift_3083_);
lean_dec_ref(v_____do__lift_3083_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(uint8_t v_pu_3087_, lean_object* v_decl_3088_, lean_object* v_inst_3089_, lean_object* v_value_3090_, uint8_t v_t_3091_, lean_object* v_toPure_3092_, lean_object* v_toBind_3093_, lean_object* v_inst_3094_, lean_object* v_____do__lift_3095_){
_start:
{
lean_object* v___x_3096_; lean_object* v___f_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___f_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3096_ = lean_box(v_pu_3087_);
v___f_3097_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3097_, 0, v___x_3096_);
lean_closure_set(v___f_3097_, 1, v_decl_3088_);
lean_closure_set(v___f_3097_, 2, v_____do__lift_3095_);
lean_closure_set(v___f_3097_, 3, v_inst_3089_);
v___x_3098_ = lean_box(v_pu_3087_);
v___x_3099_ = lean_box(v_t_3091_);
v___f_3100_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3100_, 0, v___x_3098_);
lean_closure_set(v___f_3100_, 1, v_value_3090_);
lean_closure_set(v___f_3100_, 2, v___x_3099_);
lean_closure_set(v___f_3100_, 3, v_toPure_3092_);
lean_inc(v_toBind_3093_);
v___x_3101_ = lean_apply_4(v_toBind_3093_, lean_box(0), lean_box(0), v_inst_3094_, v___f_3100_);
v___x_3102_ = lean_apply_4(v_toBind_3093_, lean_box(0), lean_box(0), v___x_3101_, v___f_3097_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed(lean_object* v_pu_3103_, lean_object* v_decl_3104_, lean_object* v_inst_3105_, lean_object* v_value_3106_, lean_object* v_t_3107_, lean_object* v_toPure_3108_, lean_object* v_toBind_3109_, lean_object* v_inst_3110_, lean_object* v_____do__lift_3111_){
_start:
{
uint8_t v_pu_boxed_3112_; uint8_t v_t_boxed_3113_; lean_object* v_res_3114_; 
v_pu_boxed_3112_ = lean_unbox(v_pu_3103_);
v_t_boxed_3113_ = lean_unbox(v_t_3107_);
v_res_3114_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(v_pu_boxed_3112_, v_decl_3104_, v_inst_3105_, v_value_3106_, v_t_boxed_3113_, v_toPure_3108_, v_toBind_3109_, v_inst_3110_, v_____do__lift_3111_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg(uint8_t v_pu_3115_, uint8_t v_t_3116_, lean_object* v_inst_3117_, lean_object* v_inst_3118_, lean_object* v_inst_3119_, lean_object* v_decl_3120_){
_start:
{
lean_object* v_toApplicative_3121_; lean_object* v_toBind_3122_; lean_object* v_type_3123_; lean_object* v_value_3124_; lean_object* v_toPure_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___f_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___f_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v_toApplicative_3121_ = lean_ctor_get(v_inst_3118_, 0);
lean_inc_ref(v_toApplicative_3121_);
v_toBind_3122_ = lean_ctor_get(v_inst_3118_, 1);
lean_inc_n(v_toBind_3122_, 3);
lean_dec_ref(v_inst_3118_);
v_type_3123_ = lean_ctor_get(v_decl_3120_, 2);
lean_inc_ref(v_type_3123_);
v_value_3124_ = lean_ctor_get(v_decl_3120_, 3);
lean_inc(v_value_3124_);
v_toPure_3125_ = lean_ctor_get(v_toApplicative_3121_, 1);
lean_inc_n(v_toPure_3125_, 2);
lean_dec_ref(v_toApplicative_3121_);
v___x_3126_ = lean_box(v_pu_3115_);
v___x_3127_ = lean_box(v_t_3116_);
lean_inc(v_inst_3119_);
v___f_3128_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_3128_, 0, v___x_3126_);
lean_closure_set(v___f_3128_, 1, v_decl_3120_);
lean_closure_set(v___f_3128_, 2, v_inst_3117_);
lean_closure_set(v___f_3128_, 3, v_value_3124_);
lean_closure_set(v___f_3128_, 4, v___x_3127_);
lean_closure_set(v___f_3128_, 5, v_toPure_3125_);
lean_closure_set(v___f_3128_, 6, v_toBind_3122_);
lean_closure_set(v___f_3128_, 7, v_inst_3119_);
v___x_3129_ = lean_box(v_pu_3115_);
v___x_3130_ = lean_box(v_t_3116_);
v___f_3131_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3131_, 0, v___x_3129_);
lean_closure_set(v___f_3131_, 1, v___x_3130_);
lean_closure_set(v___f_3131_, 2, v_type_3123_);
lean_closure_set(v___f_3131_, 3, v_toPure_3125_);
v___x_3132_ = lean_apply_4(v_toBind_3122_, lean_box(0), lean_box(0), v_inst_3119_, v___f_3131_);
v___x_3133_ = lean_apply_4(v_toBind_3122_, lean_box(0), lean_box(0), v___x_3132_, v___f_3128_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___boxed(lean_object* v_pu_3134_, lean_object* v_t_3135_, lean_object* v_inst_3136_, lean_object* v_inst_3137_, lean_object* v_inst_3138_, lean_object* v_decl_3139_){
_start:
{
uint8_t v_pu_boxed_3140_; uint8_t v_t_boxed_3141_; lean_object* v_res_3142_; 
v_pu_boxed_3140_ = lean_unbox(v_pu_3134_);
v_t_boxed_3141_ = lean_unbox(v_t_3135_);
v_res_3142_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_boxed_3140_, v_t_boxed_3141_, v_inst_3136_, v_inst_3137_, v_inst_3138_, v_decl_3139_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl(lean_object* v_m_3143_, uint8_t v_pu_3144_, uint8_t v_t_3145_, lean_object* v_inst_3146_, lean_object* v_inst_3147_, lean_object* v_inst_3148_, lean_object* v_decl_3149_){
_start:
{
lean_object* v___x_3150_; 
v___x_3150_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_3144_, v_t_3145_, v_inst_3146_, v_inst_3147_, v_inst_3148_, v_decl_3149_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___boxed(lean_object* v_m_3151_, lean_object* v_pu_3152_, lean_object* v_t_3153_, lean_object* v_inst_3154_, lean_object* v_inst_3155_, lean_object* v_inst_3156_, lean_object* v_decl_3157_){
_start:
{
uint8_t v_pu_boxed_3158_; uint8_t v_t_boxed_3159_; lean_object* v_res_3160_; 
v_pu_boxed_3158_ = lean_unbox(v_pu_3152_);
v_t_boxed_3159_ = lean_unbox(v_t_3153_);
v_res_3160_ = l_Lean_Compiler_LCNF_normLetDecl(v_m_3151_, v_pu_boxed_3158_, v_t_boxed_3159_, v_inst_3154_, v_inst_3155_, v_inst_3156_, v_decl_3157_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(uint8_t v_pu_3161_, uint8_t v_t_3162_){
_start:
{
lean_object* v___x_3163_; lean_object* v_toApplicative_3164_; lean_object* v_toFunctor_3165_; lean_object* v_toSeq_3166_; lean_object* v_toSeqLeft_3167_; lean_object* v_toSeqRight_3168_; lean_object* v___f_3169_; lean_object* v___f_3170_; lean_object* v___f_3171_; lean_object* v___f_3172_; lean_object* v___x_3173_; lean_object* v___f_3174_; lean_object* v___f_3175_; lean_object* v___f_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v_toApplicative_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3208_; 
v___x_3163_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_3164_ = lean_ctor_get(v___x_3163_, 0);
v_toFunctor_3165_ = lean_ctor_get(v_toApplicative_3164_, 0);
v_toSeq_3166_ = lean_ctor_get(v_toApplicative_3164_, 2);
v_toSeqLeft_3167_ = lean_ctor_get(v_toApplicative_3164_, 3);
v_toSeqRight_3168_ = lean_ctor_get(v_toApplicative_3164_, 4);
v___f_3169_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_3170_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_3165_, 2);
v___f_3171_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3171_, 0, v_toFunctor_3165_);
v___f_3172_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3172_, 0, v_toFunctor_3165_);
v___x_3173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___f_3171_);
lean_ctor_set(v___x_3173_, 1, v___f_3172_);
lean_inc(v_toSeqRight_3168_);
v___f_3174_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3174_, 0, v_toSeqRight_3168_);
lean_inc(v_toSeqLeft_3167_);
v___f_3175_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3175_, 0, v_toSeqLeft_3167_);
lean_inc(v_toSeq_3166_);
v___f_3176_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3176_, 0, v_toSeq_3166_);
v___x_3177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3173_);
lean_ctor_set(v___x_3177_, 1, v___f_3169_);
lean_ctor_set(v___x_3177_, 2, v___f_3176_);
lean_ctor_set(v___x_3177_, 3, v___f_3175_);
lean_ctor_set(v___x_3177_, 4, v___f_3174_);
v___x_3178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
lean_ctor_set(v___x_3178_, 1, v___f_3170_);
v___x_3179_ = l_StateRefT_x27_instMonad___redArg(v___x_3178_);
v_toApplicative_3180_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3208_ == 0)
{
lean_object* v_unused_3209_; 
v_unused_3209_ = lean_ctor_get(v___x_3179_, 1);
lean_dec(v_unused_3209_);
v___x_3182_ = v___x_3179_;
v_isShared_3183_ = v_isSharedCheck_3208_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_toApplicative_3180_);
lean_dec(v___x_3179_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3208_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v_toFunctor_3184_; lean_object* v_toSeq_3185_; lean_object* v_toSeqLeft_3186_; lean_object* v_toSeqRight_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3206_; 
v_toFunctor_3184_ = lean_ctor_get(v_toApplicative_3180_, 0);
v_toSeq_3185_ = lean_ctor_get(v_toApplicative_3180_, 2);
v_toSeqLeft_3186_ = lean_ctor_get(v_toApplicative_3180_, 3);
v_toSeqRight_3187_ = lean_ctor_get(v_toApplicative_3180_, 4);
v_isSharedCheck_3206_ = !lean_is_exclusive(v_toApplicative_3180_);
if (v_isSharedCheck_3206_ == 0)
{
lean_object* v_unused_3207_; 
v_unused_3207_ = lean_ctor_get(v_toApplicative_3180_, 1);
lean_dec(v_unused_3207_);
v___x_3189_ = v_toApplicative_3180_;
v_isShared_3190_ = v_isSharedCheck_3206_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_toSeqRight_3187_);
lean_inc(v_toSeqLeft_3186_);
lean_inc(v_toSeq_3185_);
lean_inc(v_toFunctor_3184_);
lean_dec(v_toApplicative_3180_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3206_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___f_3191_; lean_object* v___f_3192_; lean_object* v___f_3193_; lean_object* v___f_3194_; lean_object* v___x_3195_; lean_object* v___f_3196_; lean_object* v___f_3197_; lean_object* v___f_3198_; lean_object* v___x_3200_; 
v___f_3191_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_3192_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_3184_);
v___f_3193_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3193_, 0, v_toFunctor_3184_);
v___f_3194_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3194_, 0, v_toFunctor_3184_);
v___x_3195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___f_3193_);
lean_ctor_set(v___x_3195_, 1, v___f_3194_);
v___f_3196_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3196_, 0, v_toSeqRight_3187_);
v___f_3197_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3197_, 0, v_toSeqLeft_3186_);
v___f_3198_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3198_, 0, v_toSeq_3185_);
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 4, v___f_3196_);
lean_ctor_set(v___x_3189_, 3, v___f_3197_);
lean_ctor_set(v___x_3189_, 2, v___f_3198_);
lean_ctor_set(v___x_3189_, 1, v___f_3191_);
lean_ctor_set(v___x_3189_, 0, v___x_3195_);
v___x_3200_ = v___x_3189_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3195_);
lean_ctor_set(v_reuseFailAlloc_3205_, 1, v___f_3191_);
lean_ctor_set(v_reuseFailAlloc_3205_, 2, v___f_3198_);
lean_ctor_set(v_reuseFailAlloc_3205_, 3, v___f_3197_);
lean_ctor_set(v_reuseFailAlloc_3205_, 4, v___f_3196_);
v___x_3200_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
lean_object* v___x_3202_; 
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 1, v___f_3192_);
lean_ctor_set(v___x_3182_, 0, v___x_3200_);
v___x_3202_ = v___x_3182_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3200_);
lean_ctor_set(v_reuseFailAlloc_3204_, 1, v___f_3192_);
v___x_3202_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
lean_object* v___x_3203_; 
v___x_3203_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_3203_, 0, lean_box(0));
lean_closure_set(v___x_3203_, 1, lean_box(0));
lean_closure_set(v___x_3203_, 2, v___x_3202_);
return v___x_3203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___boxed(lean_object* v_pu_3210_, lean_object* v_t_3211_){
_start:
{
uint8_t v_pu_boxed_3212_; uint8_t v_t_boxed_3213_; lean_object* v_res_3214_; 
v_pu_boxed_3212_ = lean_unbox(v_pu_3210_);
v_t_boxed_3213_ = lean_unbox(v_t_3211_);
v_res_3214_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(v_pu_boxed_3212_, v_t_boxed_3213_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg(uint8_t v_pu_3215_, lean_object* v_inst_3216_, lean_object* v_result_3217_, lean_object* v_x_3218_){
_start:
{
if (lean_obj_tag(v_result_3217_) == 0)
{
lean_object* v_fvarId_3219_; lean_object* v___x_3220_; 
lean_dec(v_inst_3216_);
v_fvarId_3219_ = lean_ctor_get(v_result_3217_, 0);
lean_inc(v_fvarId_3219_);
lean_dec_ref_known(v_result_3217_, 1);
v___x_3220_ = lean_apply_1(v_x_3218_, v_fvarId_3219_);
return v___x_3220_;
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
lean_dec(v_x_3218_);
v___x_3221_ = lean_box(v_pu_3215_);
v___x_3222_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3222_, 0, v___x_3221_);
v___x_3223_ = lean_apply_2(v_inst_3216_, lean_box(0), v___x_3222_);
return v___x_3223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg___boxed(lean_object* v_pu_3224_, lean_object* v_inst_3225_, lean_object* v_result_3226_, lean_object* v_x_3227_){
_start:
{
uint8_t v_pu_boxed_3228_; lean_object* v_res_3229_; 
v_pu_boxed_3228_ = lean_unbox(v_pu_3224_);
v_res_3229_ = l_Lean_Compiler_LCNF_withNormFVarResult___redArg(v_pu_boxed_3228_, v_inst_3225_, v_result_3226_, v_x_3227_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult(lean_object* v_m_3230_, uint8_t v_pu_3231_, lean_object* v_inst_3232_, lean_object* v_inst_3233_, lean_object* v_result_3234_, lean_object* v_x_3235_){
_start:
{
if (lean_obj_tag(v_result_3234_) == 0)
{
lean_object* v_fvarId_3236_; lean_object* v___x_3237_; 
lean_dec(v_inst_3232_);
v_fvarId_3236_ = lean_ctor_get(v_result_3234_, 0);
lean_inc(v_fvarId_3236_);
lean_dec_ref_known(v_result_3234_, 1);
v___x_3237_ = lean_apply_1(v_x_3235_, v_fvarId_3236_);
return v___x_3237_;
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
lean_dec(v_x_3235_);
v___x_3238_ = lean_box(v_pu_3231_);
v___x_3239_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3239_, 0, v___x_3238_);
v___x_3240_ = lean_apply_2(v_inst_3232_, lean_box(0), v___x_3239_);
return v___x_3240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___boxed(lean_object* v_m_3241_, lean_object* v_pu_3242_, lean_object* v_inst_3243_, lean_object* v_inst_3244_, lean_object* v_result_3245_, lean_object* v_x_3246_){
_start:
{
uint8_t v_pu_boxed_3247_; lean_object* v_res_3248_; 
v_pu_boxed_3247_ = lean_unbox(v_pu_3242_);
v_res_3248_ = l_Lean_Compiler_LCNF_withNormFVarResult(v_m_3241_, v_pu_boxed_3247_, v_inst_3243_, v_inst_3244_, v_result_3245_, v_x_3246_);
lean_dec_ref(v_inst_3244_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(uint8_t v_pu_3249_, uint8_t v_t_3250_, lean_object* v_args_3251_, lean_object* v___y_3252_){
_start:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3254_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_3249_, v___y_3252_, v_args_3251_, v_t_3250_);
v___x_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg___boxed(lean_object* v_pu_3256_, lean_object* v_t_3257_, lean_object* v_args_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
uint8_t v_pu_boxed_3261_; uint8_t v_t_boxed_3262_; lean_object* v_res_3263_; 
v_pu_boxed_3261_ = lean_unbox(v_pu_3256_);
v_t_boxed_3262_ = lean_unbox(v_t_3257_);
v_res_3263_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_boxed_3261_, v_t_boxed_3262_, v_args_3258_, v___y_3259_);
lean_dec_ref(v___y_3259_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(uint8_t v_pu_3264_, uint8_t v_t_3265_, lean_object* v_i_3266_, lean_object* v_as_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v___x_3271_; uint8_t v___x_3272_; 
v___x_3271_ = lean_array_get_size(v_as_3267_);
v___x_3272_ = lean_nat_dec_lt(v_i_3266_, v___x_3271_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3273_; 
lean_dec(v_i_3266_);
v___x_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3273_, 0, v_as_3267_);
return v___x_3273_;
}
else
{
lean_object* v_a_3274_; lean_object* v_type_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v_a_3274_ = lean_array_fget_borrowed(v_as_3267_, v_i_3266_);
v_type_3275_ = lean_ctor_get(v_a_3274_, 2);
lean_inc_ref(v_type_3275_);
v___x_3276_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3264_, v___y_3268_, v_t_3265_, v_type_3275_);
lean_inc(v_a_3274_);
v___x_3277_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_3264_, v_a_3274_, v___x_3276_, v___y_3269_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; size_t v___x_3279_; size_t v___x_3280_; uint8_t v___x_3281_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref_known(v___x_3277_, 1);
v___x_3279_ = lean_ptr_addr(v_a_3274_);
v___x_3280_ = lean_ptr_addr(v_a_3278_);
v___x_3281_ = lean_usize_dec_eq(v___x_3279_, v___x_3280_);
if (v___x_3281_ == 0)
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3282_ = lean_unsigned_to_nat(1u);
v___x_3283_ = lean_nat_add(v_i_3266_, v___x_3282_);
v___x_3284_ = lean_array_fset(v_as_3267_, v_i_3266_, v_a_3278_);
lean_dec(v_i_3266_);
v_i_3266_ = v___x_3283_;
v_as_3267_ = v___x_3284_;
goto _start;
}
else
{
lean_object* v___x_3286_; lean_object* v___x_3287_; 
lean_dec(v_a_3278_);
v___x_3286_ = lean_unsigned_to_nat(1u);
v___x_3287_ = lean_nat_add(v_i_3266_, v___x_3286_);
lean_dec(v_i_3266_);
v_i_3266_ = v___x_3287_;
goto _start;
}
}
else
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
lean_dec_ref(v_as_3267_);
lean_dec(v_i_3266_);
v_a_3289_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3277_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3277_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg___boxed(lean_object* v_pu_3297_, lean_object* v_t_3298_, lean_object* v_i_3299_, lean_object* v_as_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
uint8_t v_pu_boxed_3304_; uint8_t v_t_boxed_3305_; lean_object* v_res_3306_; 
v_pu_boxed_3304_ = lean_unbox(v_pu_3297_);
v_t_boxed_3305_ = lean_unbox(v_t_3298_);
v_res_3306_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_boxed_3304_, v_t_boxed_3305_, v_i_3299_, v_as_3300_, v___y_3301_, v___y_3302_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(uint8_t v_pu_3307_, uint8_t v_t_3308_, lean_object* v_ps_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = lean_unsigned_to_nat(0u);
v___x_3317_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_3307_, v_t_3308_, v___x_3316_, v_ps_3309_, v___y_3310_, v___y_3312_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg___boxed(lean_object* v_pu_3318_, lean_object* v_t_3319_, lean_object* v_ps_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
uint8_t v_pu_boxed_3327_; uint8_t v_t_boxed_3328_; lean_object* v_res_3329_; 
v_pu_boxed_3327_ = lean_unbox(v_pu_3318_);
v_t_boxed_3328_ = lean_unbox(v_t_3319_);
v_res_3329_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_boxed_3327_, v_t_boxed_3328_, v_ps_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec_ref(v___y_3321_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(uint8_t v_pu_3330_, uint8_t v_t_3331_, lean_object* v_decl_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v_type_3336_; lean_object* v_value_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v_type_3336_ = lean_ctor_get(v_decl_3332_, 2);
v_value_3337_ = lean_ctor_get(v_decl_3332_, 3);
lean_inc_ref(v_type_3336_);
v___x_3338_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3330_, v___y_3333_, v_t_3331_, v_type_3336_);
lean_inc(v_value_3337_);
v___x_3339_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3330_, v___y_3333_, v_value_3337_, v_t_3331_);
v___x_3340_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_3330_, v_decl_3332_, v___x_3338_, v___x_3339_, v___y_3334_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg___boxed(lean_object* v_pu_3341_, lean_object* v_t_3342_, lean_object* v_decl_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
uint8_t v_pu_boxed_3347_; uint8_t v_t_boxed_3348_; lean_object* v_res_3349_; 
v_pu_boxed_3347_ = lean_unbox(v_pu_3341_);
v_t_boxed_3348_ = lean_unbox(v_t_3342_);
v_res_3349_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_boxed_3347_, v_t_boxed_3348_, v_decl_3343_, v___y_3344_, v___y_3345_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(uint8_t v_pu_3350_, uint8_t v_t_3351_, lean_object* v_i_3352_, lean_object* v_as_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v___x_3360_; uint8_t v___x_3361_; 
v___x_3360_ = lean_array_get_size(v_as_3353_);
v___x_3361_ = lean_nat_dec_lt(v_i_3352_, v___x_3360_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3362_; 
lean_dec(v_i_3352_);
v___x_3362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3362_, 0, v_as_3353_);
return v___x_3362_;
}
else
{
lean_object* v_a_3363_; lean_object* v_a_3365_; 
v_a_3363_ = lean_array_fget_borrowed(v_as_3353_, v_i_3352_);
switch(lean_obj_tag(v_a_3363_))
{
case 0:
{
lean_object* v_params_3376_; lean_object* v_code_3377_; lean_object* v___x_3378_; 
v_params_3376_ = lean_ctor_get(v_a_3363_, 1);
v_code_3377_ = lean_ctor_get(v_a_3363_, 2);
lean_inc_ref(v_params_3376_);
v___x_3378_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_3350_, v_t_3351_, v_params_3376_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3380_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3379_);
lean_dec_ref_known(v___x_3378_, 1);
lean_inc_ref(v_code_3377_);
v___x_3380_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3350_, v_t_3351_, v_code_3377_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3382_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_a_3381_);
lean_dec_ref_known(v___x_3380_, 1);
lean_inc_ref(v_a_3363_);
v___x_3382_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_3350_, v_a_3363_, v_a_3379_, v_a_3381_);
v_a_3365_ = v___x_3382_;
goto v___jp_3364_;
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
lean_dec(v_a_3379_);
lean_dec_ref(v_as_3353_);
lean_dec(v_i_3352_);
v_a_3383_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3380_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3380_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
lean_dec_ref(v_as_3353_);
lean_dec(v_i_3352_);
v_a_3391_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3378_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3378_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
case 1:
{
lean_object* v_code_3399_; lean_object* v___x_3400_; 
v_code_3399_ = lean_ctor_get(v_a_3363_, 1);
lean_inc_ref(v_code_3399_);
v___x_3400_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3350_, v_t_3351_, v_code_3399_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3402_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3401_);
lean_dec_ref_known(v___x_3400_, 1);
lean_inc_ref(v_a_3363_);
v___x_3402_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3363_, v_a_3401_);
v_a_3365_ = v___x_3402_;
goto v___jp_3364_;
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec_ref(v_as_3353_);
lean_dec(v_i_3352_);
v_a_3403_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3400_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3400_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
default: 
{
lean_object* v_code_3411_; lean_object* v___x_3412_; 
v_code_3411_ = lean_ctor_get(v_a_3363_, 0);
lean_inc_ref(v_code_3411_);
v___x_3412_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3350_, v_t_3351_, v_code_3411_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_a_3413_; lean_object* v___x_3414_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3413_);
lean_dec_ref_known(v___x_3412_, 1);
lean_inc_ref(v_a_3363_);
v___x_3414_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3363_, v_a_3413_);
v_a_3365_ = v___x_3414_;
goto v___jp_3364_;
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec_ref(v_as_3353_);
lean_dec(v_i_3352_);
v_a_3415_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3412_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3412_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
}
v___jp_3364_:
{
size_t v___x_3366_; size_t v___x_3367_; uint8_t v___x_3368_; 
v___x_3366_ = lean_ptr_addr(v_a_3363_);
v___x_3367_ = lean_ptr_addr(v_a_3365_);
v___x_3368_ = lean_usize_dec_eq(v___x_3366_, v___x_3367_);
if (v___x_3368_ == 0)
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3369_ = lean_unsigned_to_nat(1u);
v___x_3370_ = lean_nat_add(v_i_3352_, v___x_3369_);
v___x_3371_ = lean_array_fset(v_as_3353_, v_i_3352_, v_a_3365_);
lean_dec(v_i_3352_);
v_i_3352_ = v___x_3370_;
v_as_3353_ = v___x_3371_;
goto _start;
}
else
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
lean_dec_ref(v_a_3365_);
v___x_3373_ = lean_unsigned_to_nat(1u);
v___x_3374_ = lean_nat_add(v_i_3352_, v___x_3373_);
lean_dec(v_i_3352_);
v_i_3352_ = v___x_3374_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp(uint8_t v_pu_3423_, uint8_t v_t_3424_, lean_object* v_code_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_){
_start:
{
switch(lean_obj_tag(v_code_3425_))
{
case 0:
{
lean_object* v_decl_3432_; lean_object* v_k_3433_; lean_object* v___x_3434_; 
v_decl_3432_ = lean_ctor_get(v_code_3425_, 0);
v_k_3433_ = lean_ctor_get(v_code_3425_, 1);
lean_inc_ref(v_decl_3432_);
v___x_3434_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_3423_, v_t_3424_, v_decl_3432_, v_a_3426_, v_a_3428_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3436_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
lean_dec_ref_known(v___x_3434_, 1);
lean_inc_ref(v_k_3433_);
v___x_3436_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3423_, v_t_3424_, v_k_3433_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3474_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3439_ = v___x_3436_;
v_isShared_3440_ = v_isSharedCheck_3474_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3436_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3474_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
size_t v___x_3441_; size_t v___x_3442_; uint8_t v___x_3443_; 
v___x_3441_ = lean_ptr_addr(v_k_3433_);
v___x_3442_ = lean_ptr_addr(v_a_3437_);
v___x_3443_ = lean_usize_dec_eq(v___x_3441_, v___x_3442_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3453_; 
v_isSharedCheck_3453_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3453_ == 0)
{
lean_object* v_unused_3454_; lean_object* v_unused_3455_; 
v_unused_3454_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3454_);
v_unused_3455_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3455_);
v___x_3445_ = v_code_3425_;
v_isShared_3446_ = v_isSharedCheck_3453_;
goto v_resetjp_3444_;
}
else
{
lean_dec(v_code_3425_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3453_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 1, v_a_3437_);
lean_ctor_set(v___x_3445_, 0, v_a_3435_);
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3435_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v_a_3437_);
v___x_3448_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
lean_object* v___x_3450_; 
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 0, v___x_3448_);
v___x_3450_ = v___x_3439_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
else
{
size_t v___x_3456_; size_t v___x_3457_; uint8_t v___x_3458_; 
v___x_3456_ = lean_ptr_addr(v_decl_3432_);
v___x_3457_ = lean_ptr_addr(v_a_3435_);
v___x_3458_ = lean_usize_dec_eq(v___x_3456_, v___x_3457_);
if (v___x_3458_ == 0)
{
lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3468_; 
v_isSharedCheck_3468_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3468_ == 0)
{
lean_object* v_unused_3469_; lean_object* v_unused_3470_; 
v_unused_3469_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3469_);
v_unused_3470_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3470_);
v___x_3460_ = v_code_3425_;
v_isShared_3461_ = v_isSharedCheck_3468_;
goto v_resetjp_3459_;
}
else
{
lean_dec(v_code_3425_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3468_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 1, v_a_3437_);
lean_ctor_set(v___x_3460_, 0, v_a_3435_);
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3435_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_a_3437_);
v___x_3463_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3465_; 
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 0, v___x_3463_);
v___x_3465_ = v___x_3439_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3463_);
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
else
{
lean_object* v___x_3472_; 
lean_dec(v_a_3437_);
lean_dec(v_a_3435_);
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 0, v_code_3425_);
v___x_3472_ = v___x_3439_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_code_3425_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
}
else
{
lean_dec(v_a_3435_);
lean_dec_ref_known(v_code_3425_, 2);
return v___x_3436_;
}
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
lean_dec_ref_known(v_code_3425_, 2);
v_a_3475_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3434_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3434_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
case 1:
{
lean_object* v_decl_3483_; lean_object* v_k_3484_; lean_object* v___x_3485_; 
v_decl_3483_ = lean_ctor_get(v_code_3425_, 0);
v_k_3484_ = lean_ctor_get(v_code_3425_, 1);
lean_inc_ref(v_decl_3483_);
v___x_3485_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3423_, v_t_3424_, v_decl_3483_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3487_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v___x_3485_, 1);
lean_inc_ref(v_k_3484_);
v___x_3487_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3423_, v_t_3424_, v_k_3484_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3525_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3490_ = v___x_3487_;
v_isShared_3491_ = v_isSharedCheck_3525_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3487_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3525_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
size_t v___x_3492_; size_t v___x_3493_; uint8_t v___x_3494_; 
v___x_3492_ = lean_ptr_addr(v_k_3484_);
v___x_3493_ = lean_ptr_addr(v_a_3488_);
v___x_3494_ = lean_usize_dec_eq(v___x_3492_, v___x_3493_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3504_; 
v_isSharedCheck_3504_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3504_ == 0)
{
lean_object* v_unused_3505_; lean_object* v_unused_3506_; 
v_unused_3505_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3505_);
v_unused_3506_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3506_);
v___x_3496_ = v_code_3425_;
v_isShared_3497_ = v_isSharedCheck_3504_;
goto v_resetjp_3495_;
}
else
{
lean_dec(v_code_3425_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3504_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 1, v_a_3488_);
lean_ctor_set(v___x_3496_, 0, v_a_3486_);
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3486_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v_a_3488_);
v___x_3499_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
lean_object* v___x_3501_; 
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 0, v___x_3499_);
v___x_3501_ = v___x_3490_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3499_);
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
else
{
size_t v___x_3507_; size_t v___x_3508_; uint8_t v___x_3509_; 
v___x_3507_ = lean_ptr_addr(v_decl_3483_);
v___x_3508_ = lean_ptr_addr(v_a_3486_);
v___x_3509_ = lean_usize_dec_eq(v___x_3507_, v___x_3508_);
if (v___x_3509_ == 0)
{
lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3519_; 
v_isSharedCheck_3519_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3519_ == 0)
{
lean_object* v_unused_3520_; lean_object* v_unused_3521_; 
v_unused_3520_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3520_);
v_unused_3521_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3521_);
v___x_3511_ = v_code_3425_;
v_isShared_3512_ = v_isSharedCheck_3519_;
goto v_resetjp_3510_;
}
else
{
lean_dec(v_code_3425_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3519_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 1, v_a_3488_);
lean_ctor_set(v___x_3511_, 0, v_a_3486_);
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3486_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v_a_3488_);
v___x_3514_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
lean_object* v___x_3516_; 
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 0, v___x_3514_);
v___x_3516_ = v___x_3490_;
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
lean_dec(v_a_3488_);
lean_dec(v_a_3486_);
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 0, v_code_3425_);
v___x_3523_ = v___x_3490_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_code_3425_);
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
lean_dec(v_a_3486_);
lean_dec_ref_known(v_code_3425_, 2);
return v___x_3487_;
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec_ref_known(v_code_3425_, 2);
v_a_3526_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3485_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3485_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
case 2:
{
lean_object* v_decl_3534_; lean_object* v_k_3535_; lean_object* v___x_3536_; 
v_decl_3534_ = lean_ctor_get(v_code_3425_, 0);
v_k_3535_ = lean_ctor_get(v_code_3425_, 1);
lean_inc_ref(v_decl_3534_);
v___x_3536_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3423_, v_t_3424_, v_decl_3534_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3538_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3537_);
lean_dec_ref_known(v___x_3536_, 1);
lean_inc_ref(v_k_3535_);
v___x_3538_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3423_, v_t_3424_, v_k_3535_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3576_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3541_ = v___x_3538_;
v_isShared_3542_ = v_isSharedCheck_3576_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3538_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3576_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
size_t v___x_3543_; size_t v___x_3544_; uint8_t v___x_3545_; 
v___x_3543_ = lean_ptr_addr(v_k_3535_);
v___x_3544_ = lean_ptr_addr(v_a_3539_);
v___x_3545_ = lean_usize_dec_eq(v___x_3543_, v___x_3544_);
if (v___x_3545_ == 0)
{
lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3555_; 
v_isSharedCheck_3555_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3555_ == 0)
{
lean_object* v_unused_3556_; lean_object* v_unused_3557_; 
v_unused_3556_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3556_);
v_unused_3557_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3557_);
v___x_3547_ = v_code_3425_;
v_isShared_3548_ = v_isSharedCheck_3555_;
goto v_resetjp_3546_;
}
else
{
lean_dec(v_code_3425_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3555_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 1, v_a_3539_);
lean_ctor_set(v___x_3547_, 0, v_a_3537_);
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3537_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v_a_3539_);
v___x_3550_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
lean_object* v___x_3552_; 
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 0, v___x_3550_);
v___x_3552_ = v___x_3541_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
else
{
size_t v___x_3558_; size_t v___x_3559_; uint8_t v___x_3560_; 
v___x_3558_ = lean_ptr_addr(v_decl_3534_);
v___x_3559_ = lean_ptr_addr(v_a_3537_);
v___x_3560_ = lean_usize_dec_eq(v___x_3558_, v___x_3559_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3570_; 
v_isSharedCheck_3570_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3570_ == 0)
{
lean_object* v_unused_3571_; lean_object* v_unused_3572_; 
v_unused_3571_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3571_);
v_unused_3572_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3572_);
v___x_3562_ = v_code_3425_;
v_isShared_3563_ = v_isSharedCheck_3570_;
goto v_resetjp_3561_;
}
else
{
lean_dec(v_code_3425_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3570_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3565_; 
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 1, v_a_3539_);
lean_ctor_set(v___x_3562_, 0, v_a_3537_);
v___x_3565_ = v___x_3562_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3537_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_a_3539_);
v___x_3565_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
lean_object* v___x_3567_; 
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 0, v___x_3565_);
v___x_3567_ = v___x_3541_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3565_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
else
{
lean_object* v___x_3574_; 
lean_dec(v_a_3539_);
lean_dec(v_a_3537_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 0, v_code_3425_);
v___x_3574_ = v___x_3541_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_code_3425_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
}
else
{
lean_dec(v_a_3537_);
lean_dec_ref_known(v_code_3425_, 2);
return v___x_3538_;
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec_ref_known(v_code_3425_, 2);
v_a_3577_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3536_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3536_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3585_; lean_object* v_args_3586_; lean_object* v___x_3587_; 
v_fvarId_3585_ = lean_ctor_get(v_code_3425_, 0);
v_args_3586_ = lean_ctor_get(v_code_3425_, 1);
lean_inc(v_fvarId_3585_);
v___x_3587_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3426_, v_fvarId_3585_, v_t_3424_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v_fvarId_3588_; lean_object* v___x_3589_; 
v_fvarId_3588_ = lean_ctor_get(v___x_3587_, 0);
lean_inc(v_fvarId_3588_);
lean_dec_ref_known(v___x_3587_, 1);
lean_inc_ref(v_args_3586_);
v___x_3589_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_3423_, v_t_3424_, v_args_3586_, v_a_3426_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3615_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3592_ = v___x_3589_;
v_isShared_3593_ = v_isSharedCheck_3615_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3589_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3615_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
uint8_t v___y_3595_; uint8_t v___x_3611_; 
v___x_3611_ = l_Lean_instBEqFVarId_beq(v_fvarId_3585_, v_fvarId_3588_);
if (v___x_3611_ == 0)
{
v___y_3595_ = v___x_3611_;
goto v___jp_3594_;
}
else
{
size_t v___x_3612_; size_t v___x_3613_; uint8_t v___x_3614_; 
v___x_3612_ = lean_ptr_addr(v_args_3586_);
v___x_3613_ = lean_ptr_addr(v_a_3590_);
v___x_3614_ = lean_usize_dec_eq(v___x_3612_, v___x_3613_);
v___y_3595_ = v___x_3614_;
goto v___jp_3594_;
}
v___jp_3594_:
{
if (v___y_3595_ == 0)
{
lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3605_; 
v_isSharedCheck_3605_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3605_ == 0)
{
lean_object* v_unused_3606_; lean_object* v_unused_3607_; 
v_unused_3606_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3606_);
v_unused_3607_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3607_);
v___x_3597_ = v_code_3425_;
v_isShared_3598_ = v_isSharedCheck_3605_;
goto v_resetjp_3596_;
}
else
{
lean_dec(v_code_3425_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3605_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 1, v_a_3590_);
lean_ctor_set(v___x_3597_, 0, v_fvarId_3588_);
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_fvarId_3588_);
lean_ctor_set(v_reuseFailAlloc_3604_, 1, v_a_3590_);
v___x_3600_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
lean_object* v___x_3602_; 
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 0, v___x_3600_);
v___x_3602_ = v___x_3592_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v___x_3600_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
}
else
{
lean_object* v___x_3609_; 
lean_dec(v_a_3590_);
lean_dec(v_fvarId_3588_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 0, v_code_3425_);
v___x_3609_ = v___x_3592_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_code_3425_);
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
}
else
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
lean_dec(v_fvarId_3588_);
lean_dec_ref_known(v_code_3425_, 2);
v_a_3616_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3589_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3589_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
else
{
lean_object* v___x_3624_; 
lean_dec_ref_known(v_code_3425_, 2);
v___x_3624_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3423_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
return v___x_3624_;
}
}
case 4:
{
lean_object* v_cases_3625_; lean_object* v_typeName_3626_; lean_object* v_resultType_3627_; lean_object* v_discr_3628_; lean_object* v_alts_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3674_; 
v_cases_3625_ = lean_ctor_get(v_code_3425_, 0);
lean_inc_ref(v_cases_3625_);
v_typeName_3626_ = lean_ctor_get(v_cases_3625_, 0);
v_resultType_3627_ = lean_ctor_get(v_cases_3625_, 1);
v_discr_3628_ = lean_ctor_get(v_cases_3625_, 2);
v_alts_3629_ = lean_ctor_get(v_cases_3625_, 3);
v_isSharedCheck_3674_ = !lean_is_exclusive(v_cases_3625_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3631_ = v_cases_3625_;
v_isShared_3632_ = v_isSharedCheck_3674_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_alts_3629_);
lean_inc(v_discr_3628_);
lean_inc(v_resultType_3627_);
lean_inc(v_typeName_3626_);
lean_dec(v_cases_3625_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3674_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
lean_inc_ref(v_resultType_3627_);
v___x_3633_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3423_, v_a_3426_, v_t_3424_, v_resultType_3627_);
lean_inc(v_discr_3628_);
v___x_3634_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3426_, v_discr_3628_, v_t_3424_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v_fvarId_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3672_; 
v_fvarId_3635_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3637_ = v___x_3634_;
v_isShared_3638_ = v_isSharedCheck_3672_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_fvarId_3635_);
lean_dec(v___x_3634_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3672_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3639_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3629_);
v___x_3640_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_3423_, v_t_3424_, v___x_3639_, v_alts_3629_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3663_; 
v_a_3641_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3643_ = v___x_3640_;
v_isShared_3644_ = v_isSharedCheck_3663_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3640_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3663_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
size_t v___x_3655_; size_t v___x_3656_; uint8_t v___x_3657_; 
v___x_3655_ = lean_ptr_addr(v_alts_3629_);
lean_dec_ref(v_alts_3629_);
v___x_3656_ = lean_ptr_addr(v_a_3641_);
v___x_3657_ = lean_usize_dec_eq(v___x_3655_, v___x_3656_);
if (v___x_3657_ == 0)
{
lean_dec(v_discr_3628_);
lean_dec_ref(v_resultType_3627_);
lean_dec_ref_known(v_code_3425_, 1);
goto v___jp_3645_;
}
else
{
size_t v___x_3658_; size_t v___x_3659_; uint8_t v___x_3660_; 
v___x_3658_ = lean_ptr_addr(v_resultType_3627_);
lean_dec_ref(v_resultType_3627_);
v___x_3659_ = lean_ptr_addr(v___x_3633_);
v___x_3660_ = lean_usize_dec_eq(v___x_3658_, v___x_3659_);
if (v___x_3660_ == 0)
{
lean_dec(v_discr_3628_);
lean_dec_ref_known(v_code_3425_, 1);
goto v___jp_3645_;
}
else
{
uint8_t v___x_3661_; 
v___x_3661_ = l_Lean_instBEqFVarId_beq(v_discr_3628_, v_fvarId_3635_);
lean_dec(v_discr_3628_);
if (v___x_3661_ == 0)
{
lean_dec_ref_known(v_code_3425_, 1);
goto v___jp_3645_;
}
else
{
lean_object* v___x_3662_; 
lean_del_object(v___x_3643_);
lean_dec(v_a_3641_);
lean_del_object(v___x_3637_);
lean_dec(v_fvarId_3635_);
lean_dec_ref(v___x_3633_);
lean_del_object(v___x_3631_);
lean_dec(v_typeName_3626_);
v___x_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3662_, 0, v_code_3425_);
return v___x_3662_;
}
}
}
v___jp_3645_:
{
lean_object* v___x_3647_; 
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 3, v_a_3641_);
lean_ctor_set(v___x_3631_, 2, v_fvarId_3635_);
lean_ctor_set(v___x_3631_, 1, v___x_3633_);
v___x_3647_ = v___x_3631_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_typeName_3626_);
lean_ctor_set(v_reuseFailAlloc_3654_, 1, v___x_3633_);
lean_ctor_set(v_reuseFailAlloc_3654_, 2, v_fvarId_3635_);
lean_ctor_set(v_reuseFailAlloc_3654_, 3, v_a_3641_);
v___x_3647_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3649_; 
if (v_isShared_3638_ == 0)
{
lean_ctor_set_tag(v___x_3637_, 4);
lean_ctor_set(v___x_3637_, 0, v___x_3647_);
v___x_3649_ = v___x_3637_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3647_);
v___x_3649_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
lean_object* v___x_3651_; 
if (v_isShared_3644_ == 0)
{
lean_ctor_set(v___x_3643_, 0, v___x_3649_);
v___x_3651_ = v___x_3643_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
}
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_del_object(v___x_3637_);
lean_dec(v_fvarId_3635_);
lean_dec_ref(v___x_3633_);
lean_del_object(v___x_3631_);
lean_dec_ref(v_alts_3629_);
lean_dec(v_discr_3628_);
lean_dec_ref(v_resultType_3627_);
lean_dec(v_typeName_3626_);
lean_dec_ref_known(v_code_3425_, 1);
v_a_3664_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3640_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3640_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
}
else
{
lean_object* v___x_3673_; 
lean_dec_ref(v___x_3633_);
lean_del_object(v___x_3631_);
lean_dec_ref(v_alts_3629_);
lean_dec(v_discr_3628_);
lean_dec_ref(v_resultType_3627_);
lean_dec(v_typeName_3626_);
lean_dec_ref_known(v_code_3425_, 1);
v___x_3673_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3423_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
return v___x_3673_;
}
}
}
case 5:
{
lean_object* v_fvarId_3675_; lean_object* v___x_3676_; 
v_fvarId_3675_ = lean_ctor_get(v_code_3425_, 0);
lean_inc(v_fvarId_3675_);
v___x_3676_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3426_, v_fvarId_3675_, v_t_3424_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_fvarId_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3696_; 
v_fvarId_3677_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3679_ = v___x_3676_;
v_isShared_3680_ = v_isSharedCheck_3696_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_fvarId_3677_);
lean_dec(v___x_3676_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3696_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
uint8_t v___x_3681_; 
v___x_3681_ = l_Lean_instBEqFVarId_beq(v_fvarId_3675_, v_fvarId_3677_);
if (v___x_3681_ == 0)
{
lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3691_; 
v_isSharedCheck_3691_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3691_ == 0)
{
lean_object* v_unused_3692_; 
v_unused_3692_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3692_);
v___x_3683_ = v_code_3425_;
v_isShared_3684_ = v_isSharedCheck_3691_;
goto v_resetjp_3682_;
}
else
{
lean_dec(v_code_3425_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3691_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 0, v_fvarId_3677_);
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_fvarId_3677_);
v___x_3686_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
lean_object* v___x_3688_; 
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 0, v___x_3686_);
v___x_3688_ = v___x_3679_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3686_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
else
{
lean_object* v___x_3694_; 
lean_dec(v_fvarId_3677_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 0, v_code_3425_);
v___x_3694_ = v___x_3679_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_code_3425_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
else
{
lean_object* v___x_3697_; 
lean_dec_ref_known(v_code_3425_, 1);
v___x_3697_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3423_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
return v___x_3697_;
}
}
case 6:
{
lean_object* v_type_3698_; lean_object* v___x_3699_; size_t v___x_3700_; size_t v___x_3701_; uint8_t v___x_3702_; 
v_type_3698_ = lean_ctor_get(v_code_3425_, 0);
lean_inc_ref(v_type_3698_);
v___x_3699_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3423_, v_a_3426_, v_t_3424_, v_type_3698_);
v___x_3700_ = lean_ptr_addr(v_type_3698_);
v___x_3701_ = lean_ptr_addr(v___x_3699_);
v___x_3702_ = lean_usize_dec_eq(v___x_3700_, v___x_3701_);
if (v___x_3702_ == 0)
{
lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3710_; 
v_isSharedCheck_3710_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3710_ == 0)
{
lean_object* v_unused_3711_; 
v_unused_3711_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3711_);
v___x_3704_ = v_code_3425_;
v_isShared_3705_ = v_isSharedCheck_3710_;
goto v_resetjp_3703_;
}
else
{
lean_dec(v_code_3425_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3710_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3707_; 
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 0, v___x_3699_);
v___x_3707_ = v___x_3704_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3699_);
v___x_3707_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
lean_object* v___x_3708_; 
v___x_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3707_);
return v___x_3708_;
}
}
}
else
{
lean_object* v___x_3712_; 
lean_dec_ref(v___x_3699_);
v___x_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3712_, 0, v_code_3425_);
return v___x_3712_;
}
}
case 7:
{
lean_object* v_fvarId_3713_; lean_object* v_i_3714_; lean_object* v_y_3715_; lean_object* v_k_3716_; lean_object* v___x_3717_; 
v_fvarId_3713_ = lean_ctor_get(v_code_3425_, 0);
v_i_3714_ = lean_ctor_get(v_code_3425_, 1);
v_y_3715_ = lean_ctor_get(v_code_3425_, 2);
v_k_3716_ = lean_ctor_get(v_code_3425_, 3);
lean_inc(v_fvarId_3713_);
v___x_3717_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3426_, v_fvarId_3713_, v_t_3424_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_fvarId_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v_fvarId_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_fvarId_3718_);
lean_dec_ref_known(v___x_3717_, 1);
lean_inc(v_y_3715_);
v___x_3719_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_3423_, v_a_3426_, v_y_3715_, v_t_3424_);
lean_inc_ref(v_k_3716_);
v___x_3720_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3423_, v_t_3424_, v_k_3716_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3794_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3723_ = v___x_3720_;
v_isShared_3724_ = v_isSharedCheck_3794_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3720_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3794_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
size_t v___x_3725_; size_t v___x_3726_; uint8_t v___x_3727_; 
v___x_3725_ = lean_ptr_addr(v_fvarId_3713_);
v___x_3726_ = lean_ptr_addr(v_fvarId_3718_);
v___x_3727_ = lean_usize_dec_eq(v___x_3725_, v___x_3726_);
if (v___x_3727_ == 0)
{
lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3737_; 
lean_inc(v_i_3714_);
v_isSharedCheck_3737_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3737_ == 0)
{
lean_object* v_unused_3738_; lean_object* v_unused_3739_; lean_object* v_unused_3740_; lean_object* v_unused_3741_; 
v_unused_3738_ = lean_ctor_get(v_code_3425_, 3);
lean_dec(v_unused_3738_);
v_unused_3739_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_3739_);
v_unused_3740_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3740_);
v_unused_3741_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3741_);
v___x_3729_ = v_code_3425_;
v_isShared_3730_ = v_isSharedCheck_3737_;
goto v_resetjp_3728_;
}
else
{
lean_dec(v_code_3425_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3737_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 3, v_a_3721_);
lean_ctor_set(v___x_3729_, 2, v___x_3719_);
lean_ctor_set(v___x_3729_, 0, v_fvarId_3718_);
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_fvarId_3718_);
lean_ctor_set(v_reuseFailAlloc_3736_, 1, v_i_3714_);
lean_ctor_set(v_reuseFailAlloc_3736_, 2, v___x_3719_);
lean_ctor_set(v_reuseFailAlloc_3736_, 3, v_a_3721_);
v___x_3732_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
lean_object* v___x_3734_; 
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v___x_3732_);
v___x_3734_ = v___x_3723_;
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
uint8_t v___x_3742_; 
v___x_3742_ = lean_nat_dec_eq(v_i_3714_, v_i_3714_);
if (v___x_3742_ == 0)
{
lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3752_; 
lean_inc(v_i_3714_);
v_isSharedCheck_3752_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3752_ == 0)
{
lean_object* v_unused_3753_; lean_object* v_unused_3754_; lean_object* v_unused_3755_; lean_object* v_unused_3756_; 
v_unused_3753_ = lean_ctor_get(v_code_3425_, 3);
lean_dec(v_unused_3753_);
v_unused_3754_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_3754_);
v_unused_3755_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3755_);
v_unused_3756_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3756_);
v___x_3744_ = v_code_3425_;
v_isShared_3745_ = v_isSharedCheck_3752_;
goto v_resetjp_3743_;
}
else
{
lean_dec(v_code_3425_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3752_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 3, v_a_3721_);
lean_ctor_set(v___x_3744_, 2, v___x_3719_);
lean_ctor_set(v___x_3744_, 0, v_fvarId_3718_);
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_fvarId_3718_);
lean_ctor_set(v_reuseFailAlloc_3751_, 1, v_i_3714_);
lean_ctor_set(v_reuseFailAlloc_3751_, 2, v___x_3719_);
lean_ctor_set(v_reuseFailAlloc_3751_, 3, v_a_3721_);
v___x_3747_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
lean_object* v___x_3749_; 
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v___x_3747_);
v___x_3749_ = v___x_3723_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
else
{
size_t v___x_3757_; size_t v___x_3758_; uint8_t v___x_3759_; 
v___x_3757_ = lean_ptr_addr(v_y_3715_);
v___x_3758_ = lean_ptr_addr(v___x_3719_);
v___x_3759_ = lean_usize_dec_eq(v___x_3757_, v___x_3758_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3769_; 
lean_inc(v_i_3714_);
v_isSharedCheck_3769_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3769_ == 0)
{
lean_object* v_unused_3770_; lean_object* v_unused_3771_; lean_object* v_unused_3772_; lean_object* v_unused_3773_; 
v_unused_3770_ = lean_ctor_get(v_code_3425_, 3);
lean_dec(v_unused_3770_);
v_unused_3771_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_3771_);
v_unused_3772_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3772_);
v_unused_3773_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3773_);
v___x_3761_ = v_code_3425_;
v_isShared_3762_ = v_isSharedCheck_3769_;
goto v_resetjp_3760_;
}
else
{
lean_dec(v_code_3425_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3769_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
lean_ctor_set(v___x_3761_, 3, v_a_3721_);
lean_ctor_set(v___x_3761_, 2, v___x_3719_);
lean_ctor_set(v___x_3761_, 0, v_fvarId_3718_);
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_fvarId_3718_);
lean_ctor_set(v_reuseFailAlloc_3768_, 1, v_i_3714_);
lean_ctor_set(v_reuseFailAlloc_3768_, 2, v___x_3719_);
lean_ctor_set(v_reuseFailAlloc_3768_, 3, v_a_3721_);
v___x_3764_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
lean_object* v___x_3766_; 
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v___x_3764_);
v___x_3766_ = v___x_3723_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3764_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
else
{
size_t v___x_3774_; size_t v___x_3775_; uint8_t v___x_3776_; 
v___x_3774_ = lean_ptr_addr(v_k_3716_);
v___x_3775_ = lean_ptr_addr(v_a_3721_);
v___x_3776_ = lean_usize_dec_eq(v___x_3774_, v___x_3775_);
if (v___x_3776_ == 0)
{
lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3786_; 
lean_inc(v_i_3714_);
v_isSharedCheck_3786_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3786_ == 0)
{
lean_object* v_unused_3787_; lean_object* v_unused_3788_; lean_object* v_unused_3789_; lean_object* v_unused_3790_; 
v_unused_3787_ = lean_ctor_get(v_code_3425_, 3);
lean_dec(v_unused_3787_);
v_unused_3788_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_3788_);
v_unused_3789_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3789_);
v_unused_3790_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3790_);
v___x_3778_ = v_code_3425_;
v_isShared_3779_ = v_isSharedCheck_3786_;
goto v_resetjp_3777_;
}
else
{
lean_dec(v_code_3425_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3786_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 3, v_a_3721_);
lean_ctor_set(v___x_3778_, 2, v___x_3719_);
lean_ctor_set(v___x_3778_, 0, v_fvarId_3718_);
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_fvarId_3718_);
lean_ctor_set(v_reuseFailAlloc_3785_, 1, v_i_3714_);
lean_ctor_set(v_reuseFailAlloc_3785_, 2, v___x_3719_);
lean_ctor_set(v_reuseFailAlloc_3785_, 3, v_a_3721_);
v___x_3781_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
lean_object* v___x_3783_; 
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v___x_3781_);
v___x_3783_ = v___x_3723_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3781_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
}
else
{
lean_object* v___x_3792_; 
lean_dec(v_a_3721_);
lean_dec(v___x_3719_);
lean_dec(v_fvarId_3718_);
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v_code_3425_);
v___x_3792_ = v___x_3723_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_code_3425_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3719_);
lean_dec(v_fvarId_3718_);
lean_dec_ref_known(v_code_3425_, 4);
return v___x_3720_;
}
}
else
{
lean_object* v___x_3795_; 
lean_dec_ref_known(v_code_3425_, 4);
v___x_3795_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3423_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
return v___x_3795_;
}
}
case 8:
{
lean_object* v_fvarId_3796_; lean_object* v_i_3797_; lean_object* v_y_3798_; lean_object* v_k_3799_; lean_object* v___x_3800_; 
v_fvarId_3796_ = lean_ctor_get(v_code_3425_, 0);
v_i_3797_ = lean_ctor_get(v_code_3425_, 1);
v_y_3798_ = lean_ctor_get(v_code_3425_, 2);
v_k_3799_ = lean_ctor_get(v_code_3425_, 3);
lean_inc(v_fvarId_3796_);
v___x_3800_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3426_, v_fvarId_3796_, v_t_3424_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v_fvarId_3801_; lean_object* v___x_3802_; 
v_fvarId_3801_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_fvarId_3801_);
lean_dec_ref_known(v___x_3800_, 1);
lean_inc(v_y_3798_);
v___x_3802_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3426_, v_y_3798_, v_t_3424_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_fvarId_3803_; lean_object* v___x_3804_; 
v_fvarId_3803_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_fvarId_3803_);
lean_dec_ref_known(v___x_3802_, 1);
lean_inc_ref(v_k_3799_);
v___x_3804_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3423_, v_t_3424_, v_k_3799_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3878_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3807_ = v___x_3804_;
v_isShared_3808_ = v_isSharedCheck_3878_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3804_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3878_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
size_t v___x_3809_; size_t v___x_3810_; uint8_t v___x_3811_; 
v___x_3809_ = lean_ptr_addr(v_fvarId_3796_);
v___x_3810_ = lean_ptr_addr(v_fvarId_3801_);
v___x_3811_ = lean_usize_dec_eq(v___x_3809_, v___x_3810_);
if (v___x_3811_ == 0)
{
lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3821_; 
lean_inc(v_i_3797_);
v_isSharedCheck_3821_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3821_ == 0)
{
lean_object* v_unused_3822_; lean_object* v_unused_3823_; lean_object* v_unused_3824_; lean_object* v_unused_3825_; 
v_unused_3822_ = lean_ctor_get(v_code_3425_, 3);
lean_dec(v_unused_3822_);
v_unused_3823_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_3823_);
v_unused_3824_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3824_);
v_unused_3825_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3825_);
v___x_3813_ = v_code_3425_;
v_isShared_3814_ = v_isSharedCheck_3821_;
goto v_resetjp_3812_;
}
else
{
lean_dec(v_code_3425_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3821_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
lean_ctor_set(v___x_3813_, 3, v_a_3805_);
lean_ctor_set(v___x_3813_, 2, v_fvarId_3803_);
lean_ctor_set(v___x_3813_, 0, v_fvarId_3801_);
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_fvarId_3801_);
lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_i_3797_);
lean_ctor_set(v_reuseFailAlloc_3820_, 2, v_fvarId_3803_);
lean_ctor_set(v_reuseFailAlloc_3820_, 3, v_a_3805_);
v___x_3816_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
lean_object* v___x_3818_; 
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v___x_3816_);
v___x_3818_ = v___x_3807_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3816_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
else
{
uint8_t v___x_3826_; 
v___x_3826_ = lean_nat_dec_eq(v_i_3797_, v_i_3797_);
if (v___x_3826_ == 0)
{
lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3836_; 
lean_inc(v_i_3797_);
v_isSharedCheck_3836_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3836_ == 0)
{
lean_object* v_unused_3837_; lean_object* v_unused_3838_; lean_object* v_unused_3839_; lean_object* v_unused_3840_; 
v_unused_3837_ = lean_ctor_get(v_code_3425_, 3);
lean_dec(v_unused_3837_);
v_unused_3838_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_3838_);
v_unused_3839_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3839_);
v_unused_3840_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3840_);
v___x_3828_ = v_code_3425_;
v_isShared_3829_ = v_isSharedCheck_3836_;
goto v_resetjp_3827_;
}
else
{
lean_dec(v_code_3425_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3836_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 3, v_a_3805_);
lean_ctor_set(v___x_3828_, 2, v_fvarId_3803_);
lean_ctor_set(v___x_3828_, 0, v_fvarId_3801_);
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_fvarId_3801_);
lean_ctor_set(v_reuseFailAlloc_3835_, 1, v_i_3797_);
lean_ctor_set(v_reuseFailAlloc_3835_, 2, v_fvarId_3803_);
lean_ctor_set(v_reuseFailAlloc_3835_, 3, v_a_3805_);
v___x_3831_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
lean_object* v___x_3833_; 
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v___x_3831_);
v___x_3833_ = v___x_3807_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3831_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
else
{
size_t v___x_3841_; size_t v___x_3842_; uint8_t v___x_3843_; 
v___x_3841_ = lean_ptr_addr(v_y_3798_);
v___x_3842_ = lean_ptr_addr(v_fvarId_3803_);
v___x_3843_ = lean_usize_dec_eq(v___x_3841_, v___x_3842_);
if (v___x_3843_ == 0)
{
lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3853_; 
lean_inc(v_i_3797_);
v_isSharedCheck_3853_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3853_ == 0)
{
lean_object* v_unused_3854_; lean_object* v_unused_3855_; lean_object* v_unused_3856_; lean_object* v_unused_3857_; 
v_unused_3854_ = lean_ctor_get(v_code_3425_, 3);
lean_dec(v_unused_3854_);
v_unused_3855_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_3855_);
v_unused_3856_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3856_);
v_unused_3857_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3857_);
v___x_3845_ = v_code_3425_;
v_isShared_3846_ = v_isSharedCheck_3853_;
goto v_resetjp_3844_;
}
else
{
lean_dec(v_code_3425_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3853_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 3, v_a_3805_);
lean_ctor_set(v___x_3845_, 2, v_fvarId_3803_);
lean_ctor_set(v___x_3845_, 0, v_fvarId_3801_);
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_fvarId_3801_);
lean_ctor_set(v_reuseFailAlloc_3852_, 1, v_i_3797_);
lean_ctor_set(v_reuseFailAlloc_3852_, 2, v_fvarId_3803_);
lean_ctor_set(v_reuseFailAlloc_3852_, 3, v_a_3805_);
v___x_3848_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
lean_object* v___x_3850_; 
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v___x_3848_);
v___x_3850_ = v___x_3807_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3848_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
else
{
size_t v___x_3858_; size_t v___x_3859_; uint8_t v___x_3860_; 
v___x_3858_ = lean_ptr_addr(v_k_3799_);
v___x_3859_ = lean_ptr_addr(v_a_3805_);
v___x_3860_ = lean_usize_dec_eq(v___x_3858_, v___x_3859_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3870_; 
lean_inc(v_i_3797_);
v_isSharedCheck_3870_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3870_ == 0)
{
lean_object* v_unused_3871_; lean_object* v_unused_3872_; lean_object* v_unused_3873_; lean_object* v_unused_3874_; 
v_unused_3871_ = lean_ctor_get(v_code_3425_, 3);
lean_dec(v_unused_3871_);
v_unused_3872_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_3872_);
v_unused_3873_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3873_);
v_unused_3874_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3874_);
v___x_3862_ = v_code_3425_;
v_isShared_3863_ = v_isSharedCheck_3870_;
goto v_resetjp_3861_;
}
else
{
lean_dec(v_code_3425_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3870_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 3, v_a_3805_);
lean_ctor_set(v___x_3862_, 2, v_fvarId_3803_);
lean_ctor_set(v___x_3862_, 0, v_fvarId_3801_);
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_fvarId_3801_);
lean_ctor_set(v_reuseFailAlloc_3869_, 1, v_i_3797_);
lean_ctor_set(v_reuseFailAlloc_3869_, 2, v_fvarId_3803_);
lean_ctor_set(v_reuseFailAlloc_3869_, 3, v_a_3805_);
v___x_3865_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
lean_object* v___x_3867_; 
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v___x_3865_);
v___x_3867_ = v___x_3807_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3865_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
else
{
lean_object* v___x_3876_; 
lean_dec(v_a_3805_);
lean_dec(v_fvarId_3803_);
lean_dec(v_fvarId_3801_);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v_code_3425_);
v___x_3876_ = v___x_3807_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_code_3425_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
return v___x_3876_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_3803_);
lean_dec(v_fvarId_3801_);
lean_dec_ref_known(v_code_3425_, 4);
return v___x_3804_;
}
}
else
{
lean_object* v___x_3879_; 
lean_dec(v_fvarId_3801_);
lean_dec_ref_known(v_code_3425_, 4);
v___x_3879_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3423_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
return v___x_3879_;
}
}
else
{
lean_object* v___x_3880_; 
lean_dec_ref_known(v_code_3425_, 4);
v___x_3880_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3423_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
return v___x_3880_;
}
}
case 9:
{
lean_object* v_fvarId_3881_; lean_object* v_i_3882_; lean_object* v_offset_3883_; lean_object* v_y_3884_; lean_object* v_ty_3885_; lean_object* v_k_3886_; lean_object* v___x_3887_; 
v_fvarId_3881_ = lean_ctor_get(v_code_3425_, 0);
v_i_3882_ = lean_ctor_get(v_code_3425_, 1);
v_offset_3883_ = lean_ctor_get(v_code_3425_, 2);
v_y_3884_ = lean_ctor_get(v_code_3425_, 3);
v_ty_3885_ = lean_ctor_get(v_code_3425_, 4);
v_k_3886_ = lean_ctor_get(v_code_3425_, 5);
lean_inc(v_fvarId_3881_);
v___x_3887_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3426_, v_fvarId_3881_, v_t_3424_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_fvarId_3888_; lean_object* v___x_3889_; 
v_fvarId_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_fvarId_3888_);
lean_dec_ref_known(v___x_3887_, 1);
lean_inc(v_y_3884_);
v___x_3889_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3426_, v_y_3884_, v_t_3424_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_fvarId_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v_fvarId_3890_ = lean_ctor_get(v___x_3889_, 0);
lean_inc(v_fvarId_3890_);
lean_dec_ref_known(v___x_3889_, 1);
lean_inc_ref(v_ty_3885_);
v___x_3891_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3423_, v_a_3426_, v_t_3424_, v_ty_3885_);
lean_inc_ref(v_k_3886_);
v___x_3892_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3423_, v_t_3424_, v_k_3886_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_4010_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_3895_ = v___x_3892_;
v_isShared_3896_ = v_isSharedCheck_4010_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3892_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_4010_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
size_t v___x_3897_; size_t v___x_3898_; uint8_t v___x_3899_; 
v___x_3897_ = lean_ptr_addr(v_fvarId_3881_);
v___x_3898_ = lean_ptr_addr(v_fvarId_3888_);
v___x_3899_ = lean_usize_dec_eq(v___x_3897_, v___x_3898_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3909_; 
lean_inc(v_offset_3883_);
lean_inc(v_i_3882_);
v_isSharedCheck_3909_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3909_ == 0)
{
lean_object* v_unused_3910_; lean_object* v_unused_3911_; lean_object* v_unused_3912_; lean_object* v_unused_3913_; lean_object* v_unused_3914_; lean_object* v_unused_3915_; 
v_unused_3910_ = lean_ctor_get(v_code_3425_, 5);
lean_dec(v_unused_3910_);
v_unused_3911_ = lean_ctor_get(v_code_3425_, 4);
lean_dec(v_unused_3911_);
v_unused_3912_ = lean_ctor_get(v_code_3425_, 3);
lean_dec(v_unused_3912_);
v_unused_3913_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_3913_);
v_unused_3914_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3914_);
v_unused_3915_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3915_);
v___x_3901_ = v_code_3425_;
v_isShared_3902_ = v_isSharedCheck_3909_;
goto v_resetjp_3900_;
}
else
{
lean_dec(v_code_3425_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3909_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 5, v_a_3893_);
lean_ctor_set(v___x_3901_, 4, v___x_3891_);
lean_ctor_set(v___x_3901_, 3, v_fvarId_3890_);
lean_ctor_set(v___x_3901_, 0, v_fvarId_3888_);
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_fvarId_3888_);
lean_ctor_set(v_reuseFailAlloc_3908_, 1, v_i_3882_);
lean_ctor_set(v_reuseFailAlloc_3908_, 2, v_offset_3883_);
lean_ctor_set(v_reuseFailAlloc_3908_, 3, v_fvarId_3890_);
lean_ctor_set(v_reuseFailAlloc_3908_, 4, v___x_3891_);
lean_ctor_set(v_reuseFailAlloc_3908_, 5, v_a_3893_);
v___x_3904_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
lean_object* v___x_3906_; 
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 0, v___x_3904_);
v___x_3906_ = v___x_3895_;
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
uint8_t v___x_3916_; 
v___x_3916_ = lean_nat_dec_eq(v_i_3882_, v_i_3882_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3926_; 
lean_inc(v_offset_3883_);
lean_inc(v_i_3882_);
v_isSharedCheck_3926_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3926_ == 0)
{
lean_object* v_unused_3927_; lean_object* v_unused_3928_; lean_object* v_unused_3929_; lean_object* v_unused_3930_; lean_object* v_unused_3931_; lean_object* v_unused_3932_; 
v_unused_3927_ = lean_ctor_get(v_code_3425_, 5);
lean_dec(v_unused_3927_);
v_unused_3928_ = lean_ctor_get(v_code_3425_, 4);
lean_dec(v_unused_3928_);
v_unused_3929_ = lean_ctor_get(v_code_3425_, 3);
lean_dec(v_unused_3929_);
v_unused_3930_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_3930_);
v_unused_3931_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3931_);
v_unused_3932_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3932_);
v___x_3918_ = v_code_3425_;
v_isShared_3919_ = v_isSharedCheck_3926_;
goto v_resetjp_3917_;
}
else
{
lean_dec(v_code_3425_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3926_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 5, v_a_3893_);
lean_ctor_set(v___x_3918_, 4, v___x_3891_);
lean_ctor_set(v___x_3918_, 3, v_fvarId_3890_);
lean_ctor_set(v___x_3918_, 0, v_fvarId_3888_);
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_fvarId_3888_);
lean_ctor_set(v_reuseFailAlloc_3925_, 1, v_i_3882_);
lean_ctor_set(v_reuseFailAlloc_3925_, 2, v_offset_3883_);
lean_ctor_set(v_reuseFailAlloc_3925_, 3, v_fvarId_3890_);
lean_ctor_set(v_reuseFailAlloc_3925_, 4, v___x_3891_);
lean_ctor_set(v_reuseFailAlloc_3925_, 5, v_a_3893_);
v___x_3921_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
lean_object* v___x_3923_; 
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 0, v___x_3921_);
v___x_3923_ = v___x_3895_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3921_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
else
{
uint8_t v___x_3933_; 
v___x_3933_ = lean_nat_dec_eq(v_offset_3883_, v_offset_3883_);
if (v___x_3933_ == 0)
{
lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3943_; 
lean_inc(v_offset_3883_);
lean_inc(v_i_3882_);
v_isSharedCheck_3943_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3943_ == 0)
{
lean_object* v_unused_3944_; lean_object* v_unused_3945_; lean_object* v_unused_3946_; lean_object* v_unused_3947_; lean_object* v_unused_3948_; lean_object* v_unused_3949_; 
v_unused_3944_ = lean_ctor_get(v_code_3425_, 5);
lean_dec(v_unused_3944_);
v_unused_3945_ = lean_ctor_get(v_code_3425_, 4);
lean_dec(v_unused_3945_);
v_unused_3946_ = lean_ctor_get(v_code_3425_, 3);
lean_dec(v_unused_3946_);
v_unused_3947_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_3947_);
v_unused_3948_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3948_);
v_unused_3949_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3949_);
v___x_3935_ = v_code_3425_;
v_isShared_3936_ = v_isSharedCheck_3943_;
goto v_resetjp_3934_;
}
else
{
lean_dec(v_code_3425_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3943_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
lean_ctor_set(v___x_3935_, 5, v_a_3893_);
lean_ctor_set(v___x_3935_, 4, v___x_3891_);
lean_ctor_set(v___x_3935_, 3, v_fvarId_3890_);
lean_ctor_set(v___x_3935_, 0, v_fvarId_3888_);
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_fvarId_3888_);
lean_ctor_set(v_reuseFailAlloc_3942_, 1, v_i_3882_);
lean_ctor_set(v_reuseFailAlloc_3942_, 2, v_offset_3883_);
lean_ctor_set(v_reuseFailAlloc_3942_, 3, v_fvarId_3890_);
lean_ctor_set(v_reuseFailAlloc_3942_, 4, v___x_3891_);
lean_ctor_set(v_reuseFailAlloc_3942_, 5, v_a_3893_);
v___x_3938_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
lean_object* v___x_3940_; 
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 0, v___x_3938_);
v___x_3940_ = v___x_3895_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v___x_3938_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
else
{
size_t v___x_3950_; size_t v___x_3951_; uint8_t v___x_3952_; 
v___x_3950_ = lean_ptr_addr(v_y_3884_);
v___x_3951_ = lean_ptr_addr(v_fvarId_3890_);
v___x_3952_ = lean_usize_dec_eq(v___x_3950_, v___x_3951_);
if (v___x_3952_ == 0)
{
lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3962_; 
lean_inc(v_offset_3883_);
lean_inc(v_i_3882_);
v_isSharedCheck_3962_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3962_ == 0)
{
lean_object* v_unused_3963_; lean_object* v_unused_3964_; lean_object* v_unused_3965_; lean_object* v_unused_3966_; lean_object* v_unused_3967_; lean_object* v_unused_3968_; 
v_unused_3963_ = lean_ctor_get(v_code_3425_, 5);
lean_dec(v_unused_3963_);
v_unused_3964_ = lean_ctor_get(v_code_3425_, 4);
lean_dec(v_unused_3964_);
v_unused_3965_ = lean_ctor_get(v_code_3425_, 3);
lean_dec(v_unused_3965_);
v_unused_3966_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_3966_);
v_unused_3967_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3967_);
v_unused_3968_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3968_);
v___x_3954_ = v_code_3425_;
v_isShared_3955_ = v_isSharedCheck_3962_;
goto v_resetjp_3953_;
}
else
{
lean_dec(v_code_3425_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3962_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3957_; 
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 5, v_a_3893_);
lean_ctor_set(v___x_3954_, 4, v___x_3891_);
lean_ctor_set(v___x_3954_, 3, v_fvarId_3890_);
lean_ctor_set(v___x_3954_, 0, v_fvarId_3888_);
v___x_3957_ = v___x_3954_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_fvarId_3888_);
lean_ctor_set(v_reuseFailAlloc_3961_, 1, v_i_3882_);
lean_ctor_set(v_reuseFailAlloc_3961_, 2, v_offset_3883_);
lean_ctor_set(v_reuseFailAlloc_3961_, 3, v_fvarId_3890_);
lean_ctor_set(v_reuseFailAlloc_3961_, 4, v___x_3891_);
lean_ctor_set(v_reuseFailAlloc_3961_, 5, v_a_3893_);
v___x_3957_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
lean_object* v___x_3959_; 
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 0, v___x_3957_);
v___x_3959_ = v___x_3895_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v___x_3957_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
else
{
size_t v___x_3969_; size_t v___x_3970_; uint8_t v___x_3971_; 
v___x_3969_ = lean_ptr_addr(v_ty_3885_);
v___x_3970_ = lean_ptr_addr(v___x_3891_);
v___x_3971_ = lean_usize_dec_eq(v___x_3969_, v___x_3970_);
if (v___x_3971_ == 0)
{
lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3981_; 
lean_inc(v_offset_3883_);
lean_inc(v_i_3882_);
v_isSharedCheck_3981_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_3981_ == 0)
{
lean_object* v_unused_3982_; lean_object* v_unused_3983_; lean_object* v_unused_3984_; lean_object* v_unused_3985_; lean_object* v_unused_3986_; lean_object* v_unused_3987_; 
v_unused_3982_ = lean_ctor_get(v_code_3425_, 5);
lean_dec(v_unused_3982_);
v_unused_3983_ = lean_ctor_get(v_code_3425_, 4);
lean_dec(v_unused_3983_);
v_unused_3984_ = lean_ctor_get(v_code_3425_, 3);
lean_dec(v_unused_3984_);
v_unused_3985_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_3985_);
v_unused_3986_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_3986_);
v_unused_3987_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_3987_);
v___x_3973_ = v_code_3425_;
v_isShared_3974_ = v_isSharedCheck_3981_;
goto v_resetjp_3972_;
}
else
{
lean_dec(v_code_3425_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3981_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
lean_ctor_set(v___x_3973_, 5, v_a_3893_);
lean_ctor_set(v___x_3973_, 4, v___x_3891_);
lean_ctor_set(v___x_3973_, 3, v_fvarId_3890_);
lean_ctor_set(v___x_3973_, 0, v_fvarId_3888_);
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_fvarId_3888_);
lean_ctor_set(v_reuseFailAlloc_3980_, 1, v_i_3882_);
lean_ctor_set(v_reuseFailAlloc_3980_, 2, v_offset_3883_);
lean_ctor_set(v_reuseFailAlloc_3980_, 3, v_fvarId_3890_);
lean_ctor_set(v_reuseFailAlloc_3980_, 4, v___x_3891_);
lean_ctor_set(v_reuseFailAlloc_3980_, 5, v_a_3893_);
v___x_3976_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
lean_object* v___x_3978_; 
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 0, v___x_3976_);
v___x_3978_ = v___x_3895_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3976_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
else
{
size_t v___x_3988_; size_t v___x_3989_; uint8_t v___x_3990_; 
v___x_3988_ = lean_ptr_addr(v_k_3886_);
v___x_3989_ = lean_ptr_addr(v_a_3893_);
v___x_3990_ = lean_usize_dec_eq(v___x_3988_, v___x_3989_);
if (v___x_3990_ == 0)
{
lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4000_; 
lean_inc(v_offset_3883_);
lean_inc(v_i_3882_);
v_isSharedCheck_4000_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_4000_ == 0)
{
lean_object* v_unused_4001_; lean_object* v_unused_4002_; lean_object* v_unused_4003_; lean_object* v_unused_4004_; lean_object* v_unused_4005_; lean_object* v_unused_4006_; 
v_unused_4001_ = lean_ctor_get(v_code_3425_, 5);
lean_dec(v_unused_4001_);
v_unused_4002_ = lean_ctor_get(v_code_3425_, 4);
lean_dec(v_unused_4002_);
v_unused_4003_ = lean_ctor_get(v_code_3425_, 3);
lean_dec(v_unused_4003_);
v_unused_4004_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_4004_);
v_unused_4005_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_4005_);
v_unused_4006_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_4006_);
v___x_3992_ = v_code_3425_;
v_isShared_3993_ = v_isSharedCheck_4000_;
goto v_resetjp_3991_;
}
else
{
lean_dec(v_code_3425_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4000_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 5, v_a_3893_);
lean_ctor_set(v___x_3992_, 4, v___x_3891_);
lean_ctor_set(v___x_3992_, 3, v_fvarId_3890_);
lean_ctor_set(v___x_3992_, 0, v_fvarId_3888_);
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_fvarId_3888_);
lean_ctor_set(v_reuseFailAlloc_3999_, 1, v_i_3882_);
lean_ctor_set(v_reuseFailAlloc_3999_, 2, v_offset_3883_);
lean_ctor_set(v_reuseFailAlloc_3999_, 3, v_fvarId_3890_);
lean_ctor_set(v_reuseFailAlloc_3999_, 4, v___x_3891_);
lean_ctor_set(v_reuseFailAlloc_3999_, 5, v_a_3893_);
v___x_3995_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
lean_object* v___x_3997_; 
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 0, v___x_3995_);
v___x_3997_ = v___x_3895_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3995_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
}
else
{
lean_object* v___x_4008_; 
lean_dec(v_a_3893_);
lean_dec_ref(v___x_3891_);
lean_dec(v_fvarId_3890_);
lean_dec(v_fvarId_3888_);
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 0, v_code_3425_);
v___x_4008_ = v___x_3895_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_code_3425_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
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
lean_dec_ref(v___x_3891_);
lean_dec(v_fvarId_3890_);
lean_dec(v_fvarId_3888_);
lean_dec_ref_known(v_code_3425_, 6);
return v___x_3892_;
}
}
else
{
lean_object* v___x_4011_; 
lean_dec(v_fvarId_3888_);
lean_dec_ref_known(v_code_3425_, 6);
v___x_4011_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3423_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
return v___x_4011_;
}
}
else
{
lean_object* v___x_4012_; 
lean_dec_ref_known(v_code_3425_, 6);
v___x_4012_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3423_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
return v___x_4012_;
}
}
case 10:
{
lean_object* v_fvarId_4013_; lean_object* v_cidx_4014_; lean_object* v_k_4015_; lean_object* v___x_4016_; 
v_fvarId_4013_ = lean_ctor_get(v_code_3425_, 0);
v_cidx_4014_ = lean_ctor_get(v_code_3425_, 1);
v_k_4015_ = lean_ctor_get(v_code_3425_, 2);
lean_inc(v_fvarId_4013_);
v___x_4016_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3426_, v_fvarId_4013_, v_t_3424_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_fvarId_4017_; lean_object* v___x_4018_; 
v_fvarId_4017_ = lean_ctor_get(v___x_4016_, 0);
lean_inc(v_fvarId_4017_);
lean_dec_ref_known(v___x_4016_, 1);
lean_inc_ref(v_k_4015_);
v___x_4018_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3423_, v_t_3424_, v_k_4015_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v_a_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4072_; 
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4021_ = v___x_4018_;
v_isShared_4022_ = v_isSharedCheck_4072_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_a_4019_);
lean_dec(v___x_4018_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4072_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
size_t v___x_4023_; size_t v___x_4024_; uint8_t v___x_4025_; 
v___x_4023_ = lean_ptr_addr(v_fvarId_4013_);
v___x_4024_ = lean_ptr_addr(v_fvarId_4017_);
v___x_4025_ = lean_usize_dec_eq(v___x_4023_, v___x_4024_);
if (v___x_4025_ == 0)
{
lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4035_; 
lean_inc(v_cidx_4014_);
v_isSharedCheck_4035_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_4035_ == 0)
{
lean_object* v_unused_4036_; lean_object* v_unused_4037_; lean_object* v_unused_4038_; 
v_unused_4036_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_4036_);
v_unused_4037_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_4037_);
v_unused_4038_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_4038_);
v___x_4027_ = v_code_3425_;
v_isShared_4028_ = v_isSharedCheck_4035_;
goto v_resetjp_4026_;
}
else
{
lean_dec(v_code_3425_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4035_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4030_; 
if (v_isShared_4028_ == 0)
{
lean_ctor_set(v___x_4027_, 2, v_a_4019_);
lean_ctor_set(v___x_4027_, 0, v_fvarId_4017_);
v___x_4030_ = v___x_4027_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_fvarId_4017_);
lean_ctor_set(v_reuseFailAlloc_4034_, 1, v_cidx_4014_);
lean_ctor_set(v_reuseFailAlloc_4034_, 2, v_a_4019_);
v___x_4030_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
lean_object* v___x_4032_; 
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v___x_4030_);
v___x_4032_ = v___x_4021_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4030_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
else
{
uint8_t v___x_4039_; 
v___x_4039_ = lean_nat_dec_eq(v_cidx_4014_, v_cidx_4014_);
if (v___x_4039_ == 0)
{
lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4049_; 
lean_inc(v_cidx_4014_);
v_isSharedCheck_4049_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_4049_ == 0)
{
lean_object* v_unused_4050_; lean_object* v_unused_4051_; lean_object* v_unused_4052_; 
v_unused_4050_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_4050_);
v_unused_4051_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_4051_);
v_unused_4052_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_4052_);
v___x_4041_ = v_code_3425_;
v_isShared_4042_ = v_isSharedCheck_4049_;
goto v_resetjp_4040_;
}
else
{
lean_dec(v_code_3425_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4049_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4044_; 
if (v_isShared_4042_ == 0)
{
lean_ctor_set(v___x_4041_, 2, v_a_4019_);
lean_ctor_set(v___x_4041_, 0, v_fvarId_4017_);
v___x_4044_ = v___x_4041_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_fvarId_4017_);
lean_ctor_set(v_reuseFailAlloc_4048_, 1, v_cidx_4014_);
lean_ctor_set(v_reuseFailAlloc_4048_, 2, v_a_4019_);
v___x_4044_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
lean_object* v___x_4046_; 
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v___x_4044_);
v___x_4046_ = v___x_4021_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v___x_4044_);
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
else
{
size_t v___x_4053_; size_t v___x_4054_; uint8_t v___x_4055_; 
v___x_4053_ = lean_ptr_addr(v_k_4015_);
v___x_4054_ = lean_ptr_addr(v_a_4019_);
v___x_4055_ = lean_usize_dec_eq(v___x_4053_, v___x_4054_);
if (v___x_4055_ == 0)
{
lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4065_; 
lean_inc(v_cidx_4014_);
v_isSharedCheck_4065_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_4065_ == 0)
{
lean_object* v_unused_4066_; lean_object* v_unused_4067_; lean_object* v_unused_4068_; 
v_unused_4066_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_4066_);
v_unused_4067_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_4067_);
v_unused_4068_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_4068_);
v___x_4057_ = v_code_3425_;
v_isShared_4058_ = v_isSharedCheck_4065_;
goto v_resetjp_4056_;
}
else
{
lean_dec(v_code_3425_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4065_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
lean_ctor_set(v___x_4057_, 2, v_a_4019_);
lean_ctor_set(v___x_4057_, 0, v_fvarId_4017_);
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_fvarId_4017_);
lean_ctor_set(v_reuseFailAlloc_4064_, 1, v_cidx_4014_);
lean_ctor_set(v_reuseFailAlloc_4064_, 2, v_a_4019_);
v___x_4060_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
lean_object* v___x_4062_; 
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v___x_4060_);
v___x_4062_ = v___x_4021_;
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
lean_object* v___x_4070_; 
lean_dec(v_a_4019_);
lean_dec(v_fvarId_4017_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v_code_3425_);
v___x_4070_ = v___x_4021_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_code_3425_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4017_);
lean_dec_ref_known(v_code_3425_, 3);
return v___x_4018_;
}
}
else
{
lean_object* v___x_4073_; 
lean_dec_ref_known(v_code_3425_, 3);
v___x_4073_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3423_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
return v___x_4073_;
}
}
case 11:
{
lean_object* v_fvarId_4074_; lean_object* v_n_4075_; uint8_t v_check_4076_; uint8_t v_persistent_4077_; lean_object* v_k_4078_; lean_object* v___x_4079_; 
v_fvarId_4074_ = lean_ctor_get(v_code_3425_, 0);
v_n_4075_ = lean_ctor_get(v_code_3425_, 1);
v_check_4076_ = lean_ctor_get_uint8(v_code_3425_, sizeof(void*)*3);
v_persistent_4077_ = lean_ctor_get_uint8(v_code_3425_, sizeof(void*)*3 + 1);
v_k_4078_ = lean_ctor_get(v_code_3425_, 2);
lean_inc(v_fvarId_4074_);
v___x_4079_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3426_, v_fvarId_4074_, v_t_3424_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_fvarId_4080_; lean_object* v___x_4081_; 
v_fvarId_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_fvarId_4080_);
lean_dec_ref_known(v___x_4079_, 1);
lean_inc_ref(v_k_4078_);
v___x_4081_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3423_, v_t_3424_, v_k_4078_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4135_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4084_ = v___x_4081_;
v_isShared_4085_ = v_isSharedCheck_4135_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4081_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4135_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
size_t v___x_4086_; size_t v___x_4087_; uint8_t v___x_4088_; 
v___x_4086_ = lean_ptr_addr(v_fvarId_4074_);
v___x_4087_ = lean_ptr_addr(v_fvarId_4080_);
v___x_4088_ = lean_usize_dec_eq(v___x_4086_, v___x_4087_);
if (v___x_4088_ == 0)
{
lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4098_; 
lean_inc(v_n_4075_);
v_isSharedCheck_4098_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_4098_ == 0)
{
lean_object* v_unused_4099_; lean_object* v_unused_4100_; lean_object* v_unused_4101_; 
v_unused_4099_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_4099_);
v_unused_4100_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_4100_);
v_unused_4101_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_4101_);
v___x_4090_ = v_code_3425_;
v_isShared_4091_ = v_isSharedCheck_4098_;
goto v_resetjp_4089_;
}
else
{
lean_dec(v_code_3425_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4098_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v___x_4093_; 
if (v_isShared_4091_ == 0)
{
lean_ctor_set(v___x_4090_, 2, v_a_4082_);
lean_ctor_set(v___x_4090_, 0, v_fvarId_4080_);
v___x_4093_ = v___x_4090_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_fvarId_4080_);
lean_ctor_set(v_reuseFailAlloc_4097_, 1, v_n_4075_);
lean_ctor_set(v_reuseFailAlloc_4097_, 2, v_a_4082_);
lean_ctor_set_uint8(v_reuseFailAlloc_4097_, sizeof(void*)*3, v_check_4076_);
lean_ctor_set_uint8(v_reuseFailAlloc_4097_, sizeof(void*)*3 + 1, v_persistent_4077_);
v___x_4093_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
lean_object* v___x_4095_; 
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 0, v___x_4093_);
v___x_4095_ = v___x_4084_;
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
uint8_t v___x_4102_; 
v___x_4102_ = lean_nat_dec_eq(v_n_4075_, v_n_4075_);
if (v___x_4102_ == 0)
{
lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4112_; 
lean_inc(v_n_4075_);
v_isSharedCheck_4112_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_4112_ == 0)
{
lean_object* v_unused_4113_; lean_object* v_unused_4114_; lean_object* v_unused_4115_; 
v_unused_4113_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_4113_);
v_unused_4114_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_4114_);
v_unused_4115_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_4115_);
v___x_4104_ = v_code_3425_;
v_isShared_4105_ = v_isSharedCheck_4112_;
goto v_resetjp_4103_;
}
else
{
lean_dec(v_code_3425_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4112_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v___x_4107_; 
if (v_isShared_4105_ == 0)
{
lean_ctor_set(v___x_4104_, 2, v_a_4082_);
lean_ctor_set(v___x_4104_, 0, v_fvarId_4080_);
v___x_4107_ = v___x_4104_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_fvarId_4080_);
lean_ctor_set(v_reuseFailAlloc_4111_, 1, v_n_4075_);
lean_ctor_set(v_reuseFailAlloc_4111_, 2, v_a_4082_);
lean_ctor_set_uint8(v_reuseFailAlloc_4111_, sizeof(void*)*3, v_check_4076_);
lean_ctor_set_uint8(v_reuseFailAlloc_4111_, sizeof(void*)*3 + 1, v_persistent_4077_);
v___x_4107_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
lean_object* v___x_4109_; 
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 0, v___x_4107_);
v___x_4109_ = v___x_4084_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v___x_4107_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
else
{
size_t v___x_4116_; size_t v___x_4117_; uint8_t v___x_4118_; 
v___x_4116_ = lean_ptr_addr(v_k_4078_);
v___x_4117_ = lean_ptr_addr(v_a_4082_);
v___x_4118_ = lean_usize_dec_eq(v___x_4116_, v___x_4117_);
if (v___x_4118_ == 0)
{
lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4128_; 
lean_inc(v_n_4075_);
v_isSharedCheck_4128_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_4128_ == 0)
{
lean_object* v_unused_4129_; lean_object* v_unused_4130_; lean_object* v_unused_4131_; 
v_unused_4129_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_4129_);
v_unused_4130_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_4130_);
v_unused_4131_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_4131_);
v___x_4120_ = v_code_3425_;
v_isShared_4121_ = v_isSharedCheck_4128_;
goto v_resetjp_4119_;
}
else
{
lean_dec(v_code_3425_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4128_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 2, v_a_4082_);
lean_ctor_set(v___x_4120_, 0, v_fvarId_4080_);
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_fvarId_4080_);
lean_ctor_set(v_reuseFailAlloc_4127_, 1, v_n_4075_);
lean_ctor_set(v_reuseFailAlloc_4127_, 2, v_a_4082_);
lean_ctor_set_uint8(v_reuseFailAlloc_4127_, sizeof(void*)*3, v_check_4076_);
lean_ctor_set_uint8(v_reuseFailAlloc_4127_, sizeof(void*)*3 + 1, v_persistent_4077_);
v___x_4123_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
lean_object* v___x_4125_; 
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 0, v___x_4123_);
v___x_4125_ = v___x_4084_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4123_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
else
{
lean_object* v___x_4133_; 
lean_dec(v_a_4082_);
lean_dec(v_fvarId_4080_);
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 0, v_code_3425_);
v___x_4133_ = v___x_4084_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_code_3425_);
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
}
}
else
{
lean_dec(v_fvarId_4080_);
lean_dec_ref_known(v_code_3425_, 3);
return v___x_4081_;
}
}
else
{
lean_object* v___x_4136_; 
lean_dec_ref_known(v_code_3425_, 3);
v___x_4136_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3423_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
return v___x_4136_;
}
}
case 12:
{
lean_object* v_fvarId_4137_; lean_object* v_n_4138_; uint8_t v_check_4139_; uint8_t v_persistent_4140_; lean_object* v_objs_x3f_4141_; lean_object* v_k_4142_; lean_object* v___x_4143_; 
v_fvarId_4137_ = lean_ctor_get(v_code_3425_, 0);
v_n_4138_ = lean_ctor_get(v_code_3425_, 1);
v_check_4139_ = lean_ctor_get_uint8(v_code_3425_, sizeof(void*)*4);
v_persistent_4140_ = lean_ctor_get_uint8(v_code_3425_, sizeof(void*)*4 + 1);
v_objs_x3f_4141_ = lean_ctor_get(v_code_3425_, 2);
v_k_4142_ = lean_ctor_get(v_code_3425_, 3);
lean_inc(v_fvarId_4137_);
v___x_4143_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3426_, v_fvarId_4137_, v_t_3424_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_fvarId_4144_; lean_object* v___x_4145_; 
v_fvarId_4144_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_fvarId_4144_);
lean_dec_ref_known(v___x_4143_, 1);
lean_inc_ref(v_k_4142_);
v___x_4145_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3423_, v_t_3424_, v_k_4142_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4218_; 
v_a_4146_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4148_ = v___x_4145_;
v_isShared_4149_ = v_isSharedCheck_4218_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4145_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4218_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
size_t v___x_4150_; size_t v___x_4151_; uint8_t v___x_4152_; 
v___x_4150_ = lean_ptr_addr(v_fvarId_4137_);
v___x_4151_ = lean_ptr_addr(v_fvarId_4144_);
v___x_4152_ = lean_usize_dec_eq(v___x_4150_, v___x_4151_);
if (v___x_4152_ == 0)
{
lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4162_; 
lean_inc(v_objs_x3f_4141_);
lean_inc(v_n_4138_);
v_isSharedCheck_4162_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_4162_ == 0)
{
lean_object* v_unused_4163_; lean_object* v_unused_4164_; lean_object* v_unused_4165_; lean_object* v_unused_4166_; 
v_unused_4163_ = lean_ctor_get(v_code_3425_, 3);
lean_dec(v_unused_4163_);
v_unused_4164_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_4164_);
v_unused_4165_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_4165_);
v_unused_4166_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_4166_);
v___x_4154_ = v_code_3425_;
v_isShared_4155_ = v_isSharedCheck_4162_;
goto v_resetjp_4153_;
}
else
{
lean_dec(v_code_3425_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4162_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
lean_ctor_set(v___x_4154_, 3, v_a_4146_);
lean_ctor_set(v___x_4154_, 0, v_fvarId_4144_);
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_fvarId_4144_);
lean_ctor_set(v_reuseFailAlloc_4161_, 1, v_n_4138_);
lean_ctor_set(v_reuseFailAlloc_4161_, 2, v_objs_x3f_4141_);
lean_ctor_set(v_reuseFailAlloc_4161_, 3, v_a_4146_);
lean_ctor_set_uint8(v_reuseFailAlloc_4161_, sizeof(void*)*4, v_check_4139_);
lean_ctor_set_uint8(v_reuseFailAlloc_4161_, sizeof(void*)*4 + 1, v_persistent_4140_);
v___x_4157_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
lean_object* v___x_4159_; 
if (v_isShared_4149_ == 0)
{
lean_ctor_set(v___x_4148_, 0, v___x_4157_);
v___x_4159_ = v___x_4148_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4157_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
else
{
uint8_t v___x_4167_; 
v___x_4167_ = lean_nat_dec_eq(v_n_4138_, v_n_4138_);
if (v___x_4167_ == 0)
{
lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4177_; 
lean_inc(v_objs_x3f_4141_);
lean_inc(v_n_4138_);
v_isSharedCheck_4177_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_4177_ == 0)
{
lean_object* v_unused_4178_; lean_object* v_unused_4179_; lean_object* v_unused_4180_; lean_object* v_unused_4181_; 
v_unused_4178_ = lean_ctor_get(v_code_3425_, 3);
lean_dec(v_unused_4178_);
v_unused_4179_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_4179_);
v_unused_4180_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_4180_);
v_unused_4181_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_4181_);
v___x_4169_ = v_code_3425_;
v_isShared_4170_ = v_isSharedCheck_4177_;
goto v_resetjp_4168_;
}
else
{
lean_dec(v_code_3425_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4177_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4172_; 
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 3, v_a_4146_);
lean_ctor_set(v___x_4169_, 0, v_fvarId_4144_);
v___x_4172_ = v___x_4169_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_fvarId_4144_);
lean_ctor_set(v_reuseFailAlloc_4176_, 1, v_n_4138_);
lean_ctor_set(v_reuseFailAlloc_4176_, 2, v_objs_x3f_4141_);
lean_ctor_set(v_reuseFailAlloc_4176_, 3, v_a_4146_);
lean_ctor_set_uint8(v_reuseFailAlloc_4176_, sizeof(void*)*4, v_check_4139_);
lean_ctor_set_uint8(v_reuseFailAlloc_4176_, sizeof(void*)*4 + 1, v_persistent_4140_);
v___x_4172_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
lean_object* v___x_4174_; 
if (v_isShared_4149_ == 0)
{
lean_ctor_set(v___x_4148_, 0, v___x_4172_);
v___x_4174_ = v___x_4148_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v___x_4172_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
else
{
size_t v___x_4182_; uint8_t v___x_4183_; 
v___x_4182_ = lean_ptr_addr(v_objs_x3f_4141_);
v___x_4183_ = lean_usize_dec_eq(v___x_4182_, v___x_4182_);
if (v___x_4183_ == 0)
{
lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4193_; 
lean_inc(v_objs_x3f_4141_);
lean_inc(v_n_4138_);
v_isSharedCheck_4193_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_4193_ == 0)
{
lean_object* v_unused_4194_; lean_object* v_unused_4195_; lean_object* v_unused_4196_; lean_object* v_unused_4197_; 
v_unused_4194_ = lean_ctor_get(v_code_3425_, 3);
lean_dec(v_unused_4194_);
v_unused_4195_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_4195_);
v_unused_4196_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_4196_);
v_unused_4197_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_4197_);
v___x_4185_ = v_code_3425_;
v_isShared_4186_ = v_isSharedCheck_4193_;
goto v_resetjp_4184_;
}
else
{
lean_dec(v_code_3425_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4193_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 3, v_a_4146_);
lean_ctor_set(v___x_4185_, 0, v_fvarId_4144_);
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_fvarId_4144_);
lean_ctor_set(v_reuseFailAlloc_4192_, 1, v_n_4138_);
lean_ctor_set(v_reuseFailAlloc_4192_, 2, v_objs_x3f_4141_);
lean_ctor_set(v_reuseFailAlloc_4192_, 3, v_a_4146_);
lean_ctor_set_uint8(v_reuseFailAlloc_4192_, sizeof(void*)*4, v_check_4139_);
lean_ctor_set_uint8(v_reuseFailAlloc_4192_, sizeof(void*)*4 + 1, v_persistent_4140_);
v___x_4188_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
lean_object* v___x_4190_; 
if (v_isShared_4149_ == 0)
{
lean_ctor_set(v___x_4148_, 0, v___x_4188_);
v___x_4190_ = v___x_4148_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v___x_4188_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
else
{
size_t v___x_4198_; size_t v___x_4199_; uint8_t v___x_4200_; 
v___x_4198_ = lean_ptr_addr(v_k_4142_);
v___x_4199_ = lean_ptr_addr(v_a_4146_);
v___x_4200_ = lean_usize_dec_eq(v___x_4198_, v___x_4199_);
if (v___x_4200_ == 0)
{
lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4210_; 
lean_inc(v_objs_x3f_4141_);
lean_inc(v_n_4138_);
v_isSharedCheck_4210_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_4210_ == 0)
{
lean_object* v_unused_4211_; lean_object* v_unused_4212_; lean_object* v_unused_4213_; lean_object* v_unused_4214_; 
v_unused_4211_ = lean_ctor_get(v_code_3425_, 3);
lean_dec(v_unused_4211_);
v_unused_4212_ = lean_ctor_get(v_code_3425_, 2);
lean_dec(v_unused_4212_);
v_unused_4213_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_4213_);
v_unused_4214_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_4214_);
v___x_4202_ = v_code_3425_;
v_isShared_4203_ = v_isSharedCheck_4210_;
goto v_resetjp_4201_;
}
else
{
lean_dec(v_code_3425_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4210_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4205_; 
if (v_isShared_4203_ == 0)
{
lean_ctor_set(v___x_4202_, 3, v_a_4146_);
lean_ctor_set(v___x_4202_, 0, v_fvarId_4144_);
v___x_4205_ = v___x_4202_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_fvarId_4144_);
lean_ctor_set(v_reuseFailAlloc_4209_, 1, v_n_4138_);
lean_ctor_set(v_reuseFailAlloc_4209_, 2, v_objs_x3f_4141_);
lean_ctor_set(v_reuseFailAlloc_4209_, 3, v_a_4146_);
lean_ctor_set_uint8(v_reuseFailAlloc_4209_, sizeof(void*)*4, v_check_4139_);
lean_ctor_set_uint8(v_reuseFailAlloc_4209_, sizeof(void*)*4 + 1, v_persistent_4140_);
v___x_4205_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
lean_object* v___x_4207_; 
if (v_isShared_4149_ == 0)
{
lean_ctor_set(v___x_4148_, 0, v___x_4205_);
v___x_4207_ = v___x_4148_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4205_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
else
{
lean_object* v___x_4216_; 
lean_dec(v_a_4146_);
lean_dec(v_fvarId_4144_);
if (v_isShared_4149_ == 0)
{
lean_ctor_set(v___x_4148_, 0, v_code_3425_);
v___x_4216_ = v___x_4148_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_code_3425_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4144_);
lean_dec_ref_known(v_code_3425_, 4);
return v___x_4145_;
}
}
else
{
lean_object* v___x_4219_; 
lean_dec_ref_known(v_code_3425_, 4);
v___x_4219_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3423_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
return v___x_4219_;
}
}
default: 
{
lean_object* v_fvarId_4220_; lean_object* v_k_4221_; lean_object* v___x_4222_; 
v_fvarId_4220_ = lean_ctor_get(v_code_3425_, 0);
v_k_4221_ = lean_ctor_get(v_code_3425_, 1);
lean_inc(v_fvarId_4220_);
v___x_4222_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3426_, v_fvarId_4220_, v_t_3424_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_fvarId_4223_; lean_object* v___x_4224_; 
v_fvarId_4223_ = lean_ctor_get(v___x_4222_, 0);
lean_inc(v_fvarId_4223_);
lean_dec_ref_known(v___x_4222_, 1);
lean_inc_ref(v_k_4221_);
v___x_4224_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3423_, v_t_3424_, v_k_4221_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4262_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4262_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4227_ = v___x_4224_;
v_isShared_4228_ = v_isSharedCheck_4262_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4224_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4262_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
size_t v___x_4229_; size_t v___x_4230_; uint8_t v___x_4231_; 
v___x_4229_ = lean_ptr_addr(v_fvarId_4220_);
v___x_4230_ = lean_ptr_addr(v_fvarId_4223_);
v___x_4231_ = lean_usize_dec_eq(v___x_4229_, v___x_4230_);
if (v___x_4231_ == 0)
{
lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4241_; 
v_isSharedCheck_4241_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_4241_ == 0)
{
lean_object* v_unused_4242_; lean_object* v_unused_4243_; 
v_unused_4242_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_4242_);
v_unused_4243_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_4243_);
v___x_4233_ = v_code_3425_;
v_isShared_4234_ = v_isSharedCheck_4241_;
goto v_resetjp_4232_;
}
else
{
lean_dec(v_code_3425_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4241_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4236_; 
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 1, v_a_4225_);
lean_ctor_set(v___x_4233_, 0, v_fvarId_4223_);
v___x_4236_ = v___x_4233_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_fvarId_4223_);
lean_ctor_set(v_reuseFailAlloc_4240_, 1, v_a_4225_);
v___x_4236_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
lean_object* v___x_4238_; 
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 0, v___x_4236_);
v___x_4238_ = v___x_4227_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v___x_4236_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
}
else
{
size_t v___x_4244_; size_t v___x_4245_; uint8_t v___x_4246_; 
v___x_4244_ = lean_ptr_addr(v_k_4221_);
v___x_4245_ = lean_ptr_addr(v_a_4225_);
v___x_4246_ = lean_usize_dec_eq(v___x_4244_, v___x_4245_);
if (v___x_4246_ == 0)
{
lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4256_; 
v_isSharedCheck_4256_ = !lean_is_exclusive(v_code_3425_);
if (v_isSharedCheck_4256_ == 0)
{
lean_object* v_unused_4257_; lean_object* v_unused_4258_; 
v_unused_4257_ = lean_ctor_get(v_code_3425_, 1);
lean_dec(v_unused_4257_);
v_unused_4258_ = lean_ctor_get(v_code_3425_, 0);
lean_dec(v_unused_4258_);
v___x_4248_ = v_code_3425_;
v_isShared_4249_ = v_isSharedCheck_4256_;
goto v_resetjp_4247_;
}
else
{
lean_dec(v_code_3425_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4256_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
lean_ctor_set(v___x_4248_, 1, v_a_4225_);
lean_ctor_set(v___x_4248_, 0, v_fvarId_4223_);
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_fvarId_4223_);
lean_ctor_set(v_reuseFailAlloc_4255_, 1, v_a_4225_);
v___x_4251_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
lean_object* v___x_4253_; 
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 0, v___x_4251_);
v___x_4253_ = v___x_4227_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4251_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
}
else
{
lean_object* v___x_4260_; 
lean_dec(v_a_4225_);
lean_dec(v_fvarId_4223_);
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 0, v_code_3425_);
v___x_4260_ = v___x_4227_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_code_3425_);
v___x_4260_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
return v___x_4260_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_4223_);
lean_dec_ref_known(v_code_3425_, 2);
return v___x_4224_;
}
}
else
{
lean_object* v___x_4263_; 
lean_dec_ref_known(v_code_3425_, 2);
v___x_4263_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3423_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
return v___x_4263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t v_pu_4264_, uint8_t v_t_4265_, lean_object* v_decl_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_){
_start:
{
lean_object* v_params_4273_; lean_object* v_type_4274_; lean_object* v_value_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v_params_4273_ = lean_ctor_get(v_decl_4266_, 2);
v_type_4274_ = lean_ctor_get(v_decl_4266_, 3);
v_value_4275_ = lean_ctor_get(v_decl_4266_, 4);
lean_inc_ref(v_type_4274_);
v___x_4276_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4264_, v_a_4267_, v_t_4265_, v_type_4274_);
lean_inc_ref(v_params_4273_);
v___x_4277_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4264_, v_t_4265_, v_params_4273_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; lean_object* v___x_4279_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4278_);
lean_dec_ref_known(v___x_4277_, 1);
lean_inc_ref(v_value_4275_);
v___x_4279_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4264_, v_t_4265_, v_value_4275_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; lean_object* v___x_4281_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
lean_inc(v_a_4280_);
lean_dec_ref_known(v___x_4279_, 1);
v___x_4281_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_4264_, v_decl_4266_, v___x_4276_, v_a_4278_, v_a_4280_, v_a_4269_);
return v___x_4281_;
}
else
{
lean_object* v_a_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4289_; 
lean_dec(v_a_4278_);
lean_dec_ref(v___x_4276_);
lean_dec_ref(v_decl_4266_);
v_a_4282_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4289_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4284_ = v___x_4279_;
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_a_4282_);
lean_dec(v___x_4279_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4287_; 
if (v_isShared_4285_ == 0)
{
v___x_4287_ = v___x_4284_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v_a_4282_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
return v___x_4287_;
}
}
}
}
else
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4297_; 
lean_dec_ref(v___x_4276_);
lean_dec_ref(v_decl_4266_);
v_a_4290_ = lean_ctor_get(v___x_4277_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4292_ = v___x_4277_;
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v___x_4277_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4295_; 
if (v_isShared_4293_ == 0)
{
v___x_4295_ = v___x_4292_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_a_4290_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
return v___x_4295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp___boxed(lean_object* v_pu_4298_, lean_object* v_t_4299_, lean_object* v_decl_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_){
_start:
{
uint8_t v_pu_boxed_4307_; uint8_t v_t_boxed_4308_; lean_object* v_res_4309_; 
v_pu_boxed_4307_ = lean_unbox(v_pu_4298_);
v_t_boxed_4308_ = lean_unbox(v_t_4299_);
v_res_4309_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_boxed_4307_, v_t_boxed_4308_, v_decl_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_, v_a_4305_);
lean_dec(v_a_4305_);
lean_dec_ref(v_a_4304_);
lean_dec(v_a_4303_);
lean_dec_ref(v_a_4302_);
lean_dec_ref(v_a_4301_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4___boxed(lean_object* v_pu_4310_, lean_object* v_t_4311_, lean_object* v_i_4312_, lean_object* v_as_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
uint8_t v_pu_boxed_4320_; uint8_t v_t_boxed_4321_; lean_object* v_res_4322_; 
v_pu_boxed_4320_ = lean_unbox(v_pu_4310_);
v_t_boxed_4321_ = lean_unbox(v_t_4311_);
v_res_4322_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_boxed_4320_, v_t_boxed_4321_, v_i_4312_, v_as_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
lean_dec_ref(v___y_4314_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp___boxed(lean_object* v_pu_4323_, lean_object* v_t_4324_, lean_object* v_code_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_){
_start:
{
uint8_t v_pu_boxed_4332_; uint8_t v_t_boxed_4333_; lean_object* v_res_4334_; 
v_pu_boxed_4332_ = lean_unbox(v_pu_4323_);
v_t_boxed_4333_ = lean_unbox(v_t_4324_);
v_res_4334_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_boxed_4332_, v_t_boxed_4333_, v_code_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_);
lean_dec(v_a_4330_);
lean_dec_ref(v_a_4329_);
lean_dec(v_a_4328_);
lean_dec_ref(v_a_4327_);
lean_dec_ref(v_a_4326_);
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(uint8_t v_pu_4335_, uint8_t v_t_4336_, uint8_t v_pu_4337_, uint8_t v_t_4338_, lean_object* v_decl_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
lean_object* v___x_4346_; 
v___x_4346_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_4337_, v_t_4338_, v_decl_4339_, v___y_4340_, v___y_4342_);
return v___x_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___boxed(lean_object* v_pu_4347_, lean_object* v_t_4348_, lean_object* v_pu_4349_, lean_object* v_t_4350_, lean_object* v_decl_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_){
_start:
{
uint8_t v_pu_boxed_4358_; uint8_t v_t_boxed_4359_; uint8_t v_pu_boxed_4360_; uint8_t v_t_boxed_4361_; lean_object* v_res_4362_; 
v_pu_boxed_4358_ = lean_unbox(v_pu_4347_);
v_t_boxed_4359_ = lean_unbox(v_t_4348_);
v_pu_boxed_4360_ = lean_unbox(v_pu_4349_);
v_t_boxed_4361_ = lean_unbox(v_t_4350_);
v_res_4362_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(v_pu_boxed_4358_, v_t_boxed_4359_, v_pu_boxed_4360_, v_t_boxed_4361_, v_decl_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
lean_dec(v___y_4356_);
lean_dec_ref(v___y_4355_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
lean_dec_ref(v___y_4352_);
return v_res_4362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(uint8_t v_pu_4363_, uint8_t v_t_4364_, uint8_t v_pu_4365_, uint8_t v_t_4366_, lean_object* v_args_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v___x_4374_; 
v___x_4374_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_4365_, v_t_4366_, v_args_4367_, v___y_4368_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___boxed(lean_object* v_pu_4375_, lean_object* v_t_4376_, lean_object* v_pu_4377_, lean_object* v_t_4378_, lean_object* v_args_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
uint8_t v_pu_boxed_4386_; uint8_t v_t_boxed_4387_; uint8_t v_pu_boxed_4388_; uint8_t v_t_boxed_4389_; lean_object* v_res_4390_; 
v_pu_boxed_4386_ = lean_unbox(v_pu_4375_);
v_t_boxed_4387_ = lean_unbox(v_t_4376_);
v_pu_boxed_4388_ = lean_unbox(v_pu_4377_);
v_t_boxed_4389_ = lean_unbox(v_t_4378_);
v_res_4390_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(v_pu_boxed_4386_, v_t_boxed_4387_, v_pu_boxed_4388_, v_t_boxed_4389_, v_args_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec_ref(v___y_4380_);
return v_res_4390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(uint8_t v_pu_4391_, uint8_t v_t_4392_, uint8_t v_pu_4393_, uint8_t v_t_4394_, lean_object* v_ps_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_){
_start:
{
lean_object* v___x_4402_; 
v___x_4402_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4393_, v_t_4394_, v_ps_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___boxed(lean_object* v_pu_4403_, lean_object* v_t_4404_, lean_object* v_pu_4405_, lean_object* v_t_4406_, lean_object* v_ps_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
uint8_t v_pu_boxed_4414_; uint8_t v_t_boxed_4415_; uint8_t v_pu_boxed_4416_; uint8_t v_t_boxed_4417_; lean_object* v_res_4418_; 
v_pu_boxed_4414_ = lean_unbox(v_pu_4403_);
v_t_boxed_4415_ = lean_unbox(v_t_4404_);
v_pu_boxed_4416_ = lean_unbox(v_pu_4405_);
v_t_boxed_4417_ = lean_unbox(v_t_4406_);
v_res_4418_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(v_pu_boxed_4414_, v_t_boxed_4415_, v_pu_boxed_4416_, v_t_boxed_4417_, v_ps_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
lean_dec(v___y_4412_);
lean_dec_ref(v___y_4411_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec_ref(v___y_4408_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(uint8_t v_pu_4419_, uint8_t v_t_4420_, lean_object* v_i_4421_, lean_object* v_as_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
lean_object* v___x_4429_; 
v___x_4429_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_4419_, v_t_4420_, v_i_4421_, v_as_4422_, v___y_4423_, v___y_4425_);
return v___x_4429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___boxed(lean_object* v_pu_4430_, lean_object* v_t_4431_, lean_object* v_i_4432_, lean_object* v_as_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
uint8_t v_pu_boxed_4440_; uint8_t v_t_boxed_4441_; lean_object* v_res_4442_; 
v_pu_boxed_4440_ = lean_unbox(v_pu_4430_);
v_t_boxed_4441_ = lean_unbox(v_t_4431_);
v_res_4442_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(v_pu_boxed_4440_, v_t_boxed_4441_, v_i_4432_, v_as_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec_ref(v___y_4434_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(uint8_t v_pu_4443_, uint8_t v_t_4444_, lean_object* v_decl_4445_, lean_object* v_inst_4446_, lean_object* v_____do__lift_4447_){
_start:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4448_ = lean_box(v_pu_4443_);
v___x_4449_ = lean_box(v_t_4444_);
v___x_4450_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDeclImp___boxed), 9, 4);
lean_closure_set(v___x_4450_, 0, v___x_4448_);
lean_closure_set(v___x_4450_, 1, v___x_4449_);
lean_closure_set(v___x_4450_, 2, v_decl_4445_);
lean_closure_set(v___x_4450_, 3, v_____do__lift_4447_);
v___x_4451_ = lean_apply_2(v_inst_4446_, lean_box(0), v___x_4450_);
return v___x_4451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed(lean_object* v_pu_4452_, lean_object* v_t_4453_, lean_object* v_decl_4454_, lean_object* v_inst_4455_, lean_object* v_____do__lift_4456_){
_start:
{
uint8_t v_pu_boxed_4457_; uint8_t v_t_boxed_4458_; lean_object* v_res_4459_; 
v_pu_boxed_4457_ = lean_unbox(v_pu_4452_);
v_t_boxed_4458_ = lean_unbox(v_t_4453_);
v_res_4459_ = l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(v_pu_boxed_4457_, v_t_boxed_4458_, v_decl_4454_, v_inst_4455_, v_____do__lift_4456_);
return v_res_4459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg(uint8_t v_pu_4460_, uint8_t v_t_4461_, lean_object* v_inst_4462_, lean_object* v_inst_4463_, lean_object* v_inst_4464_, lean_object* v_decl_4465_){
_start:
{
lean_object* v_toBind_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___f_4469_; lean_object* v___x_4470_; 
v_toBind_4466_ = lean_ctor_get(v_inst_4463_, 1);
lean_inc(v_toBind_4466_);
lean_dec_ref(v_inst_4463_);
v___x_4467_ = lean_box(v_pu_4460_);
v___x_4468_ = lean_box(v_t_4461_);
v___f_4469_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4469_, 0, v___x_4467_);
lean_closure_set(v___f_4469_, 1, v___x_4468_);
lean_closure_set(v___f_4469_, 2, v_decl_4465_);
lean_closure_set(v___f_4469_, 3, v_inst_4462_);
v___x_4470_ = lean_apply_4(v_toBind_4466_, lean_box(0), lean_box(0), v_inst_4464_, v___f_4469_);
return v___x_4470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___boxed(lean_object* v_pu_4471_, lean_object* v_t_4472_, lean_object* v_inst_4473_, lean_object* v_inst_4474_, lean_object* v_inst_4475_, lean_object* v_decl_4476_){
_start:
{
uint8_t v_pu_boxed_4477_; uint8_t v_t_boxed_4478_; lean_object* v_res_4479_; 
v_pu_boxed_4477_ = lean_unbox(v_pu_4471_);
v_t_boxed_4478_ = lean_unbox(v_t_4472_);
v_res_4479_ = l_Lean_Compiler_LCNF_normFunDecl___redArg(v_pu_boxed_4477_, v_t_boxed_4478_, v_inst_4473_, v_inst_4474_, v_inst_4475_, v_decl_4476_);
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl(lean_object* v_m_4480_, uint8_t v_pu_4481_, uint8_t v_t_4482_, lean_object* v_inst_4483_, lean_object* v_inst_4484_, lean_object* v_inst_4485_, lean_object* v_decl_4486_){
_start:
{
lean_object* v_toBind_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___f_4490_; lean_object* v___x_4491_; 
v_toBind_4487_ = lean_ctor_get(v_inst_4484_, 1);
lean_inc(v_toBind_4487_);
lean_dec_ref(v_inst_4484_);
v___x_4488_ = lean_box(v_pu_4481_);
v___x_4489_ = lean_box(v_t_4482_);
v___f_4490_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4490_, 0, v___x_4488_);
lean_closure_set(v___f_4490_, 1, v___x_4489_);
lean_closure_set(v___f_4490_, 2, v_decl_4486_);
lean_closure_set(v___f_4490_, 3, v_inst_4483_);
v___x_4491_ = lean_apply_4(v_toBind_4487_, lean_box(0), lean_box(0), v_inst_4485_, v___f_4490_);
return v___x_4491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___boxed(lean_object* v_m_4492_, lean_object* v_pu_4493_, lean_object* v_t_4494_, lean_object* v_inst_4495_, lean_object* v_inst_4496_, lean_object* v_inst_4497_, lean_object* v_decl_4498_){
_start:
{
uint8_t v_pu_boxed_4499_; uint8_t v_t_boxed_4500_; lean_object* v_res_4501_; 
v_pu_boxed_4499_ = lean_unbox(v_pu_4493_);
v_t_boxed_4500_ = lean_unbox(v_t_4494_);
v_res_4501_ = l_Lean_Compiler_LCNF_normFunDecl(v_m_4492_, v_pu_boxed_4499_, v_t_boxed_4500_, v_inst_4495_, v_inst_4496_, v_inst_4497_, v_decl_4498_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0(uint8_t v_pu_4502_, uint8_t v_t_4503_, lean_object* v_code_4504_, lean_object* v_inst_4505_, lean_object* v_____do__lift_4506_){
_start:
{
lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4507_ = lean_box(v_pu_4502_);
v___x_4508_ = lean_box(v_t_4503_);
v___x_4509_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCodeImp___boxed), 9, 4);
lean_closure_set(v___x_4509_, 0, v___x_4507_);
lean_closure_set(v___x_4509_, 1, v___x_4508_);
lean_closure_set(v___x_4509_, 2, v_code_4504_);
lean_closure_set(v___x_4509_, 3, v_____do__lift_4506_);
v___x_4510_ = lean_apply_2(v_inst_4505_, lean_box(0), v___x_4509_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed(lean_object* v_pu_4511_, lean_object* v_t_4512_, lean_object* v_code_4513_, lean_object* v_inst_4514_, lean_object* v_____do__lift_4515_){
_start:
{
uint8_t v_pu_boxed_4516_; uint8_t v_t_boxed_4517_; lean_object* v_res_4518_; 
v_pu_boxed_4516_ = lean_unbox(v_pu_4511_);
v_t_boxed_4517_ = lean_unbox(v_t_4512_);
v_res_4518_ = l_Lean_Compiler_LCNF_normCode___redArg___lam__0(v_pu_boxed_4516_, v_t_boxed_4517_, v_code_4513_, v_inst_4514_, v_____do__lift_4515_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg(uint8_t v_pu_4519_, uint8_t v_t_4520_, lean_object* v_inst_4521_, lean_object* v_inst_4522_, lean_object* v_inst_4523_, lean_object* v_code_4524_){
_start:
{
lean_object* v_toBind_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___f_4528_; lean_object* v___x_4529_; 
v_toBind_4525_ = lean_ctor_get(v_inst_4522_, 1);
lean_inc(v_toBind_4525_);
lean_dec_ref(v_inst_4522_);
v___x_4526_ = lean_box(v_pu_4519_);
v___x_4527_ = lean_box(v_t_4520_);
v___f_4528_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4528_, 0, v___x_4526_);
lean_closure_set(v___f_4528_, 1, v___x_4527_);
lean_closure_set(v___f_4528_, 2, v_code_4524_);
lean_closure_set(v___f_4528_, 3, v_inst_4521_);
v___x_4529_ = lean_apply_4(v_toBind_4525_, lean_box(0), lean_box(0), v_inst_4523_, v___f_4528_);
return v___x_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___boxed(lean_object* v_pu_4530_, lean_object* v_t_4531_, lean_object* v_inst_4532_, lean_object* v_inst_4533_, lean_object* v_inst_4534_, lean_object* v_code_4535_){
_start:
{
uint8_t v_pu_boxed_4536_; uint8_t v_t_boxed_4537_; lean_object* v_res_4538_; 
v_pu_boxed_4536_ = lean_unbox(v_pu_4530_);
v_t_boxed_4537_ = lean_unbox(v_t_4531_);
v_res_4538_ = l_Lean_Compiler_LCNF_normCode___redArg(v_pu_boxed_4536_, v_t_boxed_4537_, v_inst_4532_, v_inst_4533_, v_inst_4534_, v_code_4535_);
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode(lean_object* v_m_4539_, uint8_t v_pu_4540_, uint8_t v_t_4541_, lean_object* v_inst_4542_, lean_object* v_inst_4543_, lean_object* v_inst_4544_, lean_object* v_code_4545_){
_start:
{
lean_object* v_toBind_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___f_4549_; lean_object* v___x_4550_; 
v_toBind_4546_ = lean_ctor_get(v_inst_4543_, 1);
lean_inc(v_toBind_4546_);
lean_dec_ref(v_inst_4543_);
v___x_4547_ = lean_box(v_pu_4540_);
v___x_4548_ = lean_box(v_t_4541_);
v___f_4549_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4549_, 0, v___x_4547_);
lean_closure_set(v___f_4549_, 1, v___x_4548_);
lean_closure_set(v___f_4549_, 2, v_code_4545_);
lean_closure_set(v___f_4549_, 3, v_inst_4542_);
v___x_4550_ = lean_apply_4(v_toBind_4546_, lean_box(0), lean_box(0), v_inst_4544_, v___f_4549_);
return v___x_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___boxed(lean_object* v_m_4551_, lean_object* v_pu_4552_, lean_object* v_t_4553_, lean_object* v_inst_4554_, lean_object* v_inst_4555_, lean_object* v_inst_4556_, lean_object* v_code_4557_){
_start:
{
uint8_t v_pu_boxed_4558_; uint8_t v_t_boxed_4559_; lean_object* v_res_4560_; 
v_pu_boxed_4558_ = lean_unbox(v_pu_4552_);
v_t_boxed_4559_ = lean_unbox(v_t_4553_);
v_res_4560_ = l_Lean_Compiler_LCNF_normCode(v_m_4551_, v_pu_boxed_4558_, v_t_boxed_4559_, v_inst_4554_, v_inst_4555_, v_inst_4556_, v_code_4557_);
return v_res_4560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t v_pu_4561_, lean_object* v_e_4562_, lean_object* v_s_4563_, uint8_t v_translator_4564_){
_start:
{
lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___x_4566_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4561_, v_s_4563_, v_translator_4564_, v_e_4562_);
v___x_4567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4566_);
return v___x_4567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg___boxed(lean_object* v_pu_4568_, lean_object* v_e_4569_, lean_object* v_s_4570_, lean_object* v_translator_4571_, lean_object* v_a_4572_){
_start:
{
uint8_t v_pu_boxed_4573_; uint8_t v_translator_boxed_4574_; lean_object* v_res_4575_; 
v_pu_boxed_4573_ = lean_unbox(v_pu_4568_);
v_translator_boxed_4574_ = lean_unbox(v_translator_4571_);
v_res_4575_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_boxed_4573_, v_e_4569_, v_s_4570_, v_translator_boxed_4574_);
lean_dec_ref(v_s_4570_);
return v_res_4575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(uint8_t v_pu_4576_, lean_object* v_e_4577_, lean_object* v_s_4578_, uint8_t v_translator_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_){
_start:
{
lean_object* v___x_4585_; 
v___x_4585_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_4576_, v_e_4577_, v_s_4578_, v_translator_4579_);
return v___x_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___boxed(lean_object* v_pu_4586_, lean_object* v_e_4587_, lean_object* v_s_4588_, lean_object* v_translator_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_){
_start:
{
uint8_t v_pu_boxed_4595_; uint8_t v_translator_boxed_4596_; lean_object* v_res_4597_; 
v_pu_boxed_4595_ = lean_unbox(v_pu_4586_);
v_translator_boxed_4596_ = lean_unbox(v_translator_4589_);
v_res_4597_ = l_Lean_Compiler_LCNF_replaceExprFVars(v_pu_boxed_4595_, v_e_4587_, v_s_4588_, v_translator_boxed_4596_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_);
lean_dec(v_a_4593_);
lean_dec_ref(v_a_4592_);
lean_dec(v_a_4591_);
lean_dec_ref(v_a_4590_);
lean_dec_ref(v_s_4588_);
return v_res_4597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t v_pu_4598_, lean_object* v_code_4599_, lean_object* v_s_4600_, uint8_t v_translator_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_){
_start:
{
lean_object* v___x_4607_; 
v___x_4607_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4598_, v_translator_4601_, v_code_4599_, v_s_4600_, v_a_4602_, v_a_4603_, v_a_4604_, v_a_4605_);
return v___x_4607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars___boxed(lean_object* v_pu_4608_, lean_object* v_code_4609_, lean_object* v_s_4610_, lean_object* v_translator_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_){
_start:
{
uint8_t v_pu_boxed_4617_; uint8_t v_translator_boxed_4618_; lean_object* v_res_4619_; 
v_pu_boxed_4617_ = lean_unbox(v_pu_4608_);
v_translator_boxed_4618_ = lean_unbox(v_translator_4611_);
v_res_4619_ = l_Lean_Compiler_LCNF_replaceFVars(v_pu_boxed_4617_, v_code_4609_, v_s_4610_, v_translator_boxed_4618_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_);
lean_dec(v_a_4615_);
lean_dec_ref(v_a_4614_);
lean_dec(v_a_4613_);
lean_dec_ref(v_a_4612_);
lean_dec_ref(v_s_4610_);
return v_res_4619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg(lean_object* v_a_4623_){
_start:
{
lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4625_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1));
v___x_4626_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4625_, v_a_4623_);
return v___x_4626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___boxed(lean_object* v_a_4627_, lean_object* v_a_4628_){
_start:
{
lean_object* v_res_4629_; 
v_res_4629_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4627_);
lean_dec(v_a_4627_);
return v_res_4629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName(lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_){
_start:
{
lean_object* v___x_4635_; 
v___x_4635_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4631_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___boxed(lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_){
_start:
{
lean_object* v_res_4641_; 
v_res_4641_ = l_Lean_Compiler_LCNF_mkFreshJpName(v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_);
lean_dec(v_a_4639_);
lean_dec_ref(v_a_4638_);
lean_dec(v_a_4637_);
lean_dec_ref(v_a_4636_);
return v_res_4641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t v_pu_4642_, lean_object* v_type_4643_, uint8_t v_borrow_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_){
_start:
{
lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v_a_4652_; lean_object* v___x_4653_; 
v___x_4650_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_4651_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4650_, v_a_4646_);
v_a_4652_ = lean_ctor_get(v___x_4651_, 0);
lean_inc(v_a_4652_);
lean_dec_ref(v___x_4651_);
v___x_4653_ = l_Lean_Compiler_LCNF_mkParam(v_pu_4642_, v_a_4652_, v_type_4643_, v_borrow_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam___boxed(lean_object* v_pu_4654_, lean_object* v_type_4655_, lean_object* v_borrow_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_){
_start:
{
uint8_t v_pu_boxed_4662_; uint8_t v_borrow_boxed_4663_; lean_object* v_res_4664_; 
v_pu_boxed_4662_ = lean_unbox(v_pu_4654_);
v_borrow_boxed_4663_ = lean_unbox(v_borrow_4656_);
v_res_4664_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_boxed_4662_, v_type_4655_, v_borrow_boxed_4663_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_);
lean_dec(v_a_4660_);
lean_dec_ref(v_a_4659_);
lean_dec(v_a_4658_);
lean_dec_ref(v_a_4657_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object* v_a_4665_){
_start:
{
lean_object* v_config_4667_; lean_object* v___x_4668_; 
v_config_4667_ = lean_ctor_get(v_a_4665_, 0);
lean_inc_ref(v_config_4667_);
v___x_4668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4668_, 0, v_config_4667_);
return v___x_4668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg___boxed(lean_object* v_a_4669_, lean_object* v_a_4670_){
_start:
{
lean_object* v_res_4671_; 
v_res_4671_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4669_);
lean_dec_ref(v_a_4669_);
return v_res_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig(lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_){
_start:
{
lean_object* v___x_4677_; 
v___x_4677_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4672_);
return v___x_4677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___boxed(lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_){
_start:
{
lean_object* v_res_4683_; 
v_res_4683_ = l_Lean_Compiler_LCNF_getConfig(v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_);
lean_dec(v_a_4681_);
lean_dec_ref(v_a_4680_);
lean_dec(v_a_4679_);
lean_dec_ref(v_a_4678_);
return v_res_4683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object* v_x_4684_, lean_object* v_s_4685_, uint8_t v_phase_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_){
_start:
{
lean_object* v___x_4690_; lean_object* v_toCold_4691_; lean_object* v_options_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v___x_4690_ = lean_st_mk_ref(v_s_4685_);
v_toCold_4691_ = lean_ctor_get(v_a_4687_, 0);
v_options_4692_ = lean_ctor_get(v_toCold_4691_, 2);
v___x_4693_ = l_Lean_Compiler_LCNF_toConfigOptions(v_options_4692_);
v___x_4694_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4694_, 0, v___x_4693_);
lean_ctor_set_uint8(v___x_4694_, sizeof(void*)*1, v_phase_4686_);
lean_inc(v_a_4688_);
lean_inc_ref(v_a_4687_);
lean_inc(v___x_4690_);
v___x_4695_ = lean_apply_5(v_x_4684_, v___x_4694_, v___x_4690_, v_a_4687_, v_a_4688_, lean_box(0));
if (lean_obj_tag(v___x_4695_) == 0)
{
lean_object* v_a_4696_; lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4704_; 
v_a_4696_ = lean_ctor_get(v___x_4695_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4695_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4698_ = v___x_4695_;
v_isShared_4699_ = v_isSharedCheck_4704_;
goto v_resetjp_4697_;
}
else
{
lean_inc(v_a_4696_);
lean_dec(v___x_4695_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4704_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v___x_4700_; lean_object* v___x_4702_; 
v___x_4700_ = lean_st_ref_get(v___x_4690_);
lean_dec(v___x_4690_);
lean_dec(v___x_4700_);
if (v_isShared_4699_ == 0)
{
v___x_4702_ = v___x_4698_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_a_4696_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
else
{
lean_dec(v___x_4690_);
return v___x_4695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg___boxed(lean_object* v_x_4705_, lean_object* v_s_4706_, lean_object* v_phase_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_){
_start:
{
uint8_t v_phase_boxed_4711_; lean_object* v_res_4712_; 
v_phase_boxed_4711_ = lean_unbox(v_phase_4707_);
v_res_4712_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4705_, v_s_4706_, v_phase_boxed_4711_, v_a_4708_, v_a_4709_);
lean_dec(v_a_4709_);
lean_dec_ref(v_a_4708_);
return v_res_4712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run(lean_object* v_00_u03b1_4713_, lean_object* v_x_4714_, lean_object* v_s_4715_, uint8_t v_phase_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_){
_start:
{
lean_object* v___x_4720_; 
v___x_4720_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4714_, v_s_4715_, v_phase_4716_, v_a_4717_, v_a_4718_);
return v___x_4720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___boxed(lean_object* v_00_u03b1_4721_, lean_object* v_x_4722_, lean_object* v_s_4723_, lean_object* v_phase_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_){
_start:
{
uint8_t v_phase_boxed_4728_; lean_object* v_res_4729_; 
v_phase_boxed_4728_ = lean_unbox(v_phase_4724_);
v_res_4729_ = l_Lean_Compiler_LCNF_CompilerM_run(v_00_u03b1_4721_, v_x_4722_, v_s_4723_, v_phase_boxed_4728_, v_a_4725_, v_a_4726_);
lean_dec(v_a_4726_);
lean_dec_ref(v_a_4725_);
return v_res_4729_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0(void){
_start:
{
lean_object* v___x_4730_; 
v___x_4730_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_4730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(lean_object* v_00_u03b1_4731_, lean_object* v_00_u03b2_4732_, lean_object* v_inst_4733_, lean_object* v_inst_4734_){
_start:
{
lean_object* v___x_4735_; 
v___x_4735_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(lean_object* v_00_u03b1_4736_, lean_object* v_00_u03b2_4737_, lean_object* v_inst_4738_, lean_object* v_inst_4739_){
_start:
{
lean_object* v_res_4740_; 
v_res_4740_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(v_00_u03b1_4736_, v_00_u03b2_4737_, v_inst_4738_, v_inst_4739_);
lean_dec_ref(v_inst_4739_);
lean_dec_ref(v_inst_4738_);
return v_res_4740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension(lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_){
_start:
{
lean_object* v___x_4745_; 
v___x_4745_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___boxed(lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_){
_start:
{
lean_object* v_res_4750_; 
v_res_4750_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension(v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_);
lean_dec_ref(v_a_4749_);
lean_dec_ref(v_a_4748_);
return v_res_4750_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
v___x_4754_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2));
v___x_4755_ = lean_unsigned_to_nat(14u);
v___x_4756_ = lean_unsigned_to_nat(178u);
v___x_4757_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1));
v___x_4758_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0));
v___x_4759_ = l_mkPanicMessageWithDecl(v___x_4758_, v___x_4757_, v___x_4756_, v___x_4755_, v___x_4754_);
return v___x_4759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(lean_object* v_inst_4760_, lean_object* v_inst_4761_, lean_object* v_snd_4762_, lean_object* v_inst_4763_, lean_object* v_s_4764_, lean_object* v_e_4765_){
_start:
{
lean_object* v_fst_4766_; lean_object* v_snd_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4782_; 
v_fst_4766_ = lean_ctor_get(v_s_4764_, 0);
v_snd_4767_ = lean_ctor_get(v_s_4764_, 1);
v_isSharedCheck_4782_ = !lean_is_exclusive(v_s_4764_);
if (v_isSharedCheck_4782_ == 0)
{
v___x_4769_ = v_s_4764_;
v_isShared_4770_ = v_isSharedCheck_4782_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_snd_4767_);
lean_inc(v_fst_4766_);
lean_dec(v_s_4764_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4782_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
lean_object* v___x_4771_; lean_object* v___y_4773_; lean_object* v___x_4778_; 
lean_inc_n(v_e_4765_, 2);
v___x_4771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4771_, 0, v_e_4765_);
lean_ctor_set(v___x_4771_, 1, v_fst_4766_);
lean_inc_ref(v_inst_4761_);
lean_inc_ref(v_inst_4760_);
v___x_4778_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4760_, v_inst_4761_, v_snd_4762_, v_e_4765_);
if (lean_obj_tag(v___x_4778_) == 0)
{
lean_object* v___x_4779_; lean_object* v___x_4780_; 
v___x_4779_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3);
v___x_4780_ = l_panic___redArg(v_inst_4763_, v___x_4779_);
v___y_4773_ = v___x_4780_;
goto v___jp_4772_;
}
else
{
lean_object* v_val_4781_; 
v_val_4781_ = lean_ctor_get(v___x_4778_, 0);
lean_inc(v_val_4781_);
lean_dec_ref_known(v___x_4778_, 1);
v___y_4773_ = v_val_4781_;
goto v___jp_4772_;
}
v___jp_4772_:
{
lean_object* v___x_4774_; lean_object* v___x_4776_; 
v___x_4774_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4760_, v_inst_4761_, v_snd_4767_, v_e_4765_, v___y_4773_);
if (v_isShared_4770_ == 0)
{
lean_ctor_set(v___x_4769_, 1, v___x_4774_);
lean_ctor_set(v___x_4769_, 0, v___x_4771_);
v___x_4776_ = v___x_4769_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v___x_4771_);
lean_ctor_set(v_reuseFailAlloc_4777_, 1, v___x_4774_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed(lean_object* v_inst_4783_, lean_object* v_inst_4784_, lean_object* v_snd_4785_, lean_object* v_inst_4786_, lean_object* v_s_4787_, lean_object* v_e_4788_){
_start:
{
lean_object* v_res_4789_; 
v_res_4789_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(v_inst_4783_, v_inst_4784_, v_snd_4785_, v_inst_4786_, v_s_4787_, v_e_4788_);
lean_dec(v_inst_4786_);
lean_dec(v_snd_4785_);
return v_res_4789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(lean_object* v_inst_4792_, lean_object* v_inst_4793_, lean_object* v_inst_4794_, lean_object* v_oldState_4795_, lean_object* v_newState_4796_, lean_object* v_x_4797_, lean_object* v_s_4798_){
_start:
{
lean_object* v_fst_4799_; lean_object* v_snd_4800_; lean_object* v_fst_4801_; lean_object* v___f_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v_newEntries_4807_; lean_object* v___x_4808_; 
v_fst_4799_ = lean_ctor_get(v_newState_4796_, 0);
lean_inc_n(v_fst_4799_, 2);
v_snd_4800_ = lean_ctor_get(v_newState_4796_, 1);
lean_inc(v_snd_4800_);
lean_dec_ref(v_newState_4796_);
v_fst_4801_ = lean_ctor_get(v_oldState_4795_, 0);
v___f_4802_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_4802_, 0, v_inst_4792_);
lean_closure_set(v___f_4802_, 1, v_inst_4793_);
lean_closure_set(v___f_4802_, 2, v_snd_4800_);
lean_closure_set(v___f_4802_, 3, v_inst_4794_);
v___x_4803_ = l_List_lengthTR___redArg(v_fst_4799_);
v___x_4804_ = l_List_lengthTR___redArg(v_fst_4801_);
v___x_4805_ = lean_nat_sub(v___x_4803_, v___x_4804_);
lean_dec(v___x_4804_);
lean_dec(v___x_4803_);
v___x_4806_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0));
v_newEntries_4807_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_fst_4799_, v_fst_4799_, v___x_4805_, v___x_4806_);
lean_dec(v_fst_4799_);
v___x_4808_ = l_List_foldl___redArg(v___f_4802_, v_s_4798_, v_newEntries_4807_);
return v___x_4808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(lean_object* v_inst_4809_, lean_object* v_inst_4810_, lean_object* v_inst_4811_, lean_object* v_oldState_4812_, lean_object* v_newState_4813_, lean_object* v_x_4814_, lean_object* v_s_4815_){
_start:
{
lean_object* v_res_4816_; 
v_res_4816_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(v_inst_4809_, v_inst_4810_, v_inst_4811_, v_oldState_4812_, v_newState_4813_, v_x_4814_, v_s_4815_);
lean_dec(v_x_4814_);
lean_dec_ref(v_oldState_4812_);
return v_res_4816_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0(void){
_start:
{
lean_object* v___x_4817_; 
v___x_4817_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4817_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1(void){
_start:
{
lean_object* v___x_4818_; lean_object* v___x_4819_; 
v___x_4818_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0);
v___x_4819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4819_, 0, v___x_4818_);
return v___x_4819_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2(void){
_start:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; 
v___x_4820_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1);
v___x_4821_ = lean_box(0);
v___x_4822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4822_, 0, v___x_4821_);
lean_ctor_set(v___x_4822_, 1, v___x_4820_);
return v___x_4822_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3(void){
_start:
{
lean_object* v___x_4823_; lean_object* v___x_4824_; 
v___x_4823_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2);
v___x_4824_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_4824_, 0, lean_box(0));
lean_closure_set(v___x_4824_, 1, lean_box(0));
lean_closure_set(v___x_4824_, 2, v___x_4823_);
return v___x_4824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object* v_inst_4825_, lean_object* v_inst_4826_, lean_object* v_inst_4827_){
_start:
{
lean_object* v___f_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; 
v___f_4829_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4829_, 0, v_inst_4825_);
lean_closure_set(v___f_4829_, 1, v_inst_4826_);
lean_closure_set(v___f_4829_, 2, v_inst_4827_);
v___x_4830_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3);
v___x_4831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4831_, 0, v___f_4829_);
v___x_4832_ = lean_box(0);
v___x_4833_ = l_Lean_registerEnvExtension___redArg(v___x_4830_, v___x_4831_, v___x_4832_);
if (lean_obj_tag(v___x_4833_) == 0)
{
lean_object* v_a_4834_; lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_4841_; 
v_a_4834_ = lean_ctor_get(v___x_4833_, 0);
v_isSharedCheck_4841_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4836_ = v___x_4833_;
v_isShared_4837_ = v_isSharedCheck_4841_;
goto v_resetjp_4835_;
}
else
{
lean_inc(v_a_4834_);
lean_dec(v___x_4833_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_4841_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
lean_object* v___x_4839_; 
if (v_isShared_4837_ == 0)
{
v___x_4839_ = v___x_4836_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v_a_4834_);
v___x_4839_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
return v___x_4839_;
}
}
}
else
{
lean_object* v_a_4842_; lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4849_; 
v_a_4842_ = lean_ctor_get(v___x_4833_, 0);
v_isSharedCheck_4849_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_4849_ == 0)
{
v___x_4844_ = v___x_4833_;
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
else
{
lean_inc(v_a_4842_);
lean_dec(v___x_4833_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v___x_4847_; 
if (v_isShared_4845_ == 0)
{
v___x_4847_ = v___x_4844_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v_a_4842_);
v___x_4847_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
return v___x_4847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object* v_inst_4850_, lean_object* v_inst_4851_, lean_object* v_inst_4852_, lean_object* v_a_4853_){
_start:
{
lean_object* v_res_4854_; 
v_res_4854_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4850_, v_inst_4851_, v_inst_4852_);
return v_res_4854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object* v_00_u03b1_4855_, lean_object* v_00_u03b2_4856_, lean_object* v_inst_4857_, lean_object* v_inst_4858_, lean_object* v_inst_4859_){
_start:
{
lean_object* v___x_4861_; 
v___x_4861_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4857_, v_inst_4858_, v_inst_4859_);
return v___x_4861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object* v_00_u03b1_4862_, lean_object* v_00_u03b2_4863_, lean_object* v_inst_4864_, lean_object* v_inst_4865_, lean_object* v_inst_4866_, lean_object* v_a_4867_){
_start:
{
lean_object* v_res_4868_; 
v_res_4868_ = l_Lean_Compiler_LCNF_CacheExtension_register(v_00_u03b1_4862_, v_00_u03b2_4863_, v_inst_4864_, v_inst_4865_, v_inst_4866_);
return v_res_4868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object* v_a_4869_, lean_object* v_inst_4870_, lean_object* v_inst_4871_, lean_object* v_b_4872_, lean_object* v_x_4873_){
_start:
{
lean_object* v_fst_4874_; lean_object* v_snd_4875_; lean_object* v___x_4877_; uint8_t v_isShared_4878_; uint8_t v_isSharedCheck_4884_; 
v_fst_4874_ = lean_ctor_get(v_x_4873_, 0);
v_snd_4875_ = lean_ctor_get(v_x_4873_, 1);
v_isSharedCheck_4884_ = !lean_is_exclusive(v_x_4873_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4877_ = v_x_4873_;
v_isShared_4878_ = v_isSharedCheck_4884_;
goto v_resetjp_4876_;
}
else
{
lean_inc(v_snd_4875_);
lean_inc(v_fst_4874_);
lean_dec(v_x_4873_);
v___x_4877_ = lean_box(0);
v_isShared_4878_ = v_isSharedCheck_4884_;
goto v_resetjp_4876_;
}
v_resetjp_4876_:
{
lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4882_; 
lean_inc(v_a_4869_);
v___x_4879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4879_, 0, v_a_4869_);
lean_ctor_set(v___x_4879_, 1, v_fst_4874_);
v___x_4880_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4870_, v_inst_4871_, v_snd_4875_, v_a_4869_, v_b_4872_);
if (v_isShared_4878_ == 0)
{
lean_ctor_set(v___x_4877_, 1, v___x_4880_);
lean_ctor_set(v___x_4877_, 0, v___x_4879_);
v___x_4882_ = v___x_4877_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v___x_4879_);
lean_ctor_set(v_reuseFailAlloc_4883_, 1, v___x_4880_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_4885_; 
v___x_4885_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4885_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_4886_; lean_object* v___x_4887_; 
v___x_4886_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0);
v___x_4887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4886_);
return v___x_4887_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2(void){
_start:
{
lean_object* v___x_4888_; lean_object* v___x_4889_; 
v___x_4888_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1);
v___x_4889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4889_, 0, v___x_4888_);
lean_ctor_set(v___x_4889_, 1, v___x_4888_);
return v___x_4889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object* v_inst_4890_, lean_object* v_inst_4891_, lean_object* v_ext_4892_, lean_object* v_a_4893_, lean_object* v_b_4894_, lean_object* v_a_4895_){
_start:
{
lean_object* v___x_4897_; lean_object* v_env_4898_; lean_object* v_nextMacroScope_4899_; lean_object* v_ngen_4900_; lean_object* v_auxDeclNGen_4901_; lean_object* v_traceState_4902_; lean_object* v_messages_4903_; lean_object* v_infoState_4904_; lean_object* v_snapshotTasks_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4920_; 
v___x_4897_ = lean_st_ref_take(v_a_4895_);
v_env_4898_ = lean_ctor_get(v___x_4897_, 0);
v_nextMacroScope_4899_ = lean_ctor_get(v___x_4897_, 1);
v_ngen_4900_ = lean_ctor_get(v___x_4897_, 2);
v_auxDeclNGen_4901_ = lean_ctor_get(v___x_4897_, 3);
v_traceState_4902_ = lean_ctor_get(v___x_4897_, 4);
v_messages_4903_ = lean_ctor_get(v___x_4897_, 6);
v_infoState_4904_ = lean_ctor_get(v___x_4897_, 7);
v_snapshotTasks_4905_ = lean_ctor_get(v___x_4897_, 8);
v_isSharedCheck_4920_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4920_ == 0)
{
lean_object* v_unused_4921_; 
v_unused_4921_ = lean_ctor_get(v___x_4897_, 5);
lean_dec(v_unused_4921_);
v___x_4907_ = v___x_4897_;
v_isShared_4908_ = v_isSharedCheck_4920_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_snapshotTasks_4905_);
lean_inc(v_infoState_4904_);
lean_inc(v_messages_4903_);
lean_inc(v_traceState_4902_);
lean_inc(v_auxDeclNGen_4901_);
lean_inc(v_ngen_4900_);
lean_inc(v_nextMacroScope_4899_);
lean_inc(v_env_4898_);
lean_dec(v___x_4897_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4920_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v_asyncMode_4909_; lean_object* v___f_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4915_; 
v_asyncMode_4909_ = lean_ctor_get(v_ext_4892_, 2);
lean_inc(v_asyncMode_4909_);
v___f_4910_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4910_, 0, v_a_4893_);
lean_closure_set(v___f_4910_, 1, v_inst_4890_);
lean_closure_set(v___f_4910_, 2, v_inst_4891_);
lean_closure_set(v___f_4910_, 3, v_b_4894_);
v___x_4911_ = lean_box(0);
v___x_4912_ = l_Lean_EnvExtension_modifyState___redArg(v_ext_4892_, v_env_4898_, v___f_4910_, v_asyncMode_4909_, v___x_4911_);
lean_dec(v_asyncMode_4909_);
v___x_4913_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2);
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 5, v___x_4913_);
lean_ctor_set(v___x_4907_, 0, v___x_4912_);
v___x_4915_ = v___x_4907_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v___x_4912_);
lean_ctor_set(v_reuseFailAlloc_4919_, 1, v_nextMacroScope_4899_);
lean_ctor_set(v_reuseFailAlloc_4919_, 2, v_ngen_4900_);
lean_ctor_set(v_reuseFailAlloc_4919_, 3, v_auxDeclNGen_4901_);
lean_ctor_set(v_reuseFailAlloc_4919_, 4, v_traceState_4902_);
lean_ctor_set(v_reuseFailAlloc_4919_, 5, v___x_4913_);
lean_ctor_set(v_reuseFailAlloc_4919_, 6, v_messages_4903_);
lean_ctor_set(v_reuseFailAlloc_4919_, 7, v_infoState_4904_);
lean_ctor_set(v_reuseFailAlloc_4919_, 8, v_snapshotTasks_4905_);
v___x_4915_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
v___x_4916_ = lean_st_ref_put(v_a_4895_, v___x_4915_);
v___x_4917_ = lean_box(0);
v___x_4918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4918_, 0, v___x_4917_);
return v___x_4918_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object* v_inst_4922_, lean_object* v_inst_4923_, lean_object* v_ext_4924_, lean_object* v_a_4925_, lean_object* v_b_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_){
_start:
{
lean_object* v_res_4929_; 
v_res_4929_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4922_, v_inst_4923_, v_ext_4924_, v_a_4925_, v_b_4926_, v_a_4927_);
lean_dec(v_a_4927_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object* v_00_u03b1_4930_, lean_object* v_00_u03b2_4931_, lean_object* v_inst_4932_, lean_object* v_inst_4933_, lean_object* v_inst_4934_, lean_object* v_ext_4935_, lean_object* v_a_4936_, lean_object* v_b_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_){
_start:
{
lean_object* v___x_4941_; 
v___x_4941_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4932_, v_inst_4933_, v_ext_4935_, v_a_4936_, v_b_4937_, v_a_4939_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object* v_00_u03b1_4942_, lean_object* v_00_u03b2_4943_, lean_object* v_inst_4944_, lean_object* v_inst_4945_, lean_object* v_inst_4946_, lean_object* v_ext_4947_, lean_object* v_a_4948_, lean_object* v_b_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_){
_start:
{
lean_object* v_res_4953_; 
v_res_4953_ = l_Lean_Compiler_LCNF_CacheExtension_insert(v_00_u03b1_4942_, v_00_u03b2_4943_, v_inst_4944_, v_inst_4945_, v_inst_4946_, v_ext_4947_, v_a_4948_, v_b_4949_, v_a_4950_, v_a_4951_);
lean_dec(v_a_4951_);
lean_dec_ref(v_a_4950_);
lean_dec(v_inst_4946_);
return v_res_4953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(lean_object* v_inst_4954_, lean_object* v_inst_4955_, lean_object* v_ext_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_){
_start:
{
lean_object* v___x_4960_; lean_object* v_env_4961_; lean_object* v_asyncMode_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v_snd_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
v___x_4960_ = lean_st_ref_get(v_a_4958_);
v_env_4961_ = lean_ctor_get(v___x_4960_, 0);
lean_inc_ref(v_env_4961_);
lean_dec(v___x_4960_);
v_asyncMode_4962_ = lean_ctor_get(v_ext_4956_, 2);
v___x_4963_ = lean_box(0);
v___x_4964_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v_inst_4954_, v_inst_4955_);
v___x_4965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4965_, 0, v___x_4963_);
lean_ctor_set(v___x_4965_, 1, v___x_4964_);
v___x_4966_ = lean_box(0);
v___x_4967_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4965_, v_ext_4956_, v_env_4961_, v_asyncMode_4962_, v___x_4966_);
lean_dec_ref_known(v___x_4965_, 2);
v_snd_4968_ = lean_ctor_get(v___x_4967_, 1);
lean_inc(v_snd_4968_);
lean_dec(v___x_4967_);
v___x_4969_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4954_, v_inst_4955_, v_snd_4968_, v_a_4957_);
lean_dec(v_snd_4968_);
v___x_4970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4970_, 0, v___x_4969_);
return v___x_4970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(lean_object* v_inst_4971_, lean_object* v_inst_4972_, lean_object* v_ext_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_){
_start:
{
lean_object* v_res_4977_; 
v_res_4977_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4971_, v_inst_4972_, v_ext_4973_, v_a_4974_, v_a_4975_);
lean_dec(v_a_4975_);
lean_dec_ref(v_ext_4973_);
return v_res_4977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_object* v_00_u03b1_4978_, lean_object* v_00_u03b2_4979_, lean_object* v_inst_4980_, lean_object* v_inst_4981_, lean_object* v_inst_4982_, lean_object* v_ext_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_){
_start:
{
lean_object* v___x_4988_; 
v___x_4988_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4980_, v_inst_4981_, v_ext_4983_, v_a_4984_, v_a_4986_);
return v___x_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(lean_object* v_00_u03b1_4989_, lean_object* v_00_u03b2_4990_, lean_object* v_inst_4991_, lean_object* v_inst_4992_, lean_object* v_inst_4993_, lean_object* v_ext_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_){
_start:
{
lean_object* v_res_4999_; 
v_res_4999_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f(v_00_u03b1_4989_, v_00_u03b2_4990_, v_inst_4991_, v_inst_4992_, v_inst_4993_, v_ext_4994_, v_a_4995_, v_a_4996_, v_a_4997_);
lean_dec(v_a_4997_);
lean_dec_ref(v_a_4996_);
lean_dec_ref(v_ext_4994_);
lean_dec(v_inst_4993_);
return v_res_4999_;
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
