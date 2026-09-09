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
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_370_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_370_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_370_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_370_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v_env_352_; lean_object* v_lctx_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_368_; 
v_env_352_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref(v_env_352_);
lean_dec(v___x_345_);
v_lctx_353_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; 
v_unused_369_ = lean_ctor_get(v___x_346_, 1);
lean_dec(v_unused_369_);
v___x_355_ = v___x_346_;
v_isShared_356_ = v_isSharedCheck_368_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_lctx_353_);
lean_dec(v___x_346_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_368_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v_options_357_; uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v_options_357_ = lean_ctor_get(v___y_342_, 1);
v___x_358_ = lean_unbox(v_a_348_);
lean_dec(v_a_348_);
v___x_359_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_353_, v___x_358_);
lean_dec_ref(v_lctx_353_);
v___x_360_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_357_);
v___x_361_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_361_, 0, v_env_352_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
lean_ctor_set(v___x_361_, 2, v___x_359_);
lean_ctor_set(v___x_361_, 3, v_options_357_);
if (v_isShared_356_ == 0)
{
lean_ctor_set_tag(v___x_355_, 3);
lean_ctor_set(v___x_355_, 1, v_msgData_339_);
lean_ctor_set(v___x_355_, 0, v___x_361_);
v___x_363_ = v___x_355_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_msgData_339_);
v___x_363_ = v_reuseFailAlloc_367_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_365_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_363_);
v___x_365_ = v___x_350_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec(v___x_346_);
lean_dec(v___x_345_);
lean_dec_ref(v_msgData_339_);
v_a_371_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_347_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_347_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed(lean_object* v_msgData_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(v_msgData_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(lean_object* v_msg_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_options_394_; lean_object* v_ref_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_options_394_ = lean_ctor_get(v___y_391_, 1);
v_ref_395_ = lean_ctor_get(v___y_391_, 4);
v___x_396_ = lean_st_ref_get(v___y_392_);
v___x_397_ = lean_st_ref_get(v___y_390_);
v___x_398_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_389_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_421_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_421_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_421_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_421_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v_env_403_; lean_object* v_lctx_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_419_; 
v_env_403_ = lean_ctor_get(v___x_396_, 0);
lean_inc_ref(v_env_403_);
lean_dec(v___x_396_);
v_lctx_404_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v___x_397_, 1);
lean_dec(v_unused_420_);
v___x_406_ = v___x_397_;
v_isShared_407_ = v_isSharedCheck_419_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_lctx_404_);
lean_dec(v___x_397_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_419_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_408_ = lean_unbox(v_a_399_);
lean_dec(v_a_399_);
v___x_409_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_404_, v___x_408_);
lean_dec_ref(v_lctx_404_);
v___x_410_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_394_);
v___x_411_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_411_, 0, v_env_403_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
lean_ctor_set(v___x_411_, 2, v___x_409_);
lean_ctor_set(v___x_411_, 3, v_options_394_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 3);
lean_ctor_set(v___x_406_, 1, v_msg_388_);
lean_ctor_set(v___x_406_, 0, v___x_411_);
v___x_413_ = v___x_406_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_411_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_msg_388_);
v___x_413_ = v_reuseFailAlloc_418_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
lean_inc(v_ref_395_);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v_ref_395_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
if (v_isShared_402_ == 0)
{
lean_ctor_set_tag(v___x_401_, 1);
lean_ctor_set(v___x_401_, 0, v___x_414_);
v___x_416_ = v___x_401_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec(v___x_397_);
lean_dec(v___x_396_);
lean_dec_ref(v_msg_388_);
v_a_422_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_398_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_398_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg___boxed(lean_object* v_msg_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(lean_object* v_00_u03b1_437_, lean_object* v_msg_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___boxed(lean_object* v_00_u03b1_445_, lean_object* v_msg_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(v_00_u03b1_445_, v_msg_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(lean_object* v_a_453_, lean_object* v_x_454_){
_start:
{
if (lean_obj_tag(v_x_454_) == 0)
{
lean_object* v___x_455_; 
v___x_455_ = lean_box(0);
return v___x_455_;
}
else
{
lean_object* v_key_456_; lean_object* v_value_457_; lean_object* v_tail_458_; uint8_t v___x_459_; 
v_key_456_ = lean_ctor_get(v_x_454_, 0);
v_value_457_ = lean_ctor_get(v_x_454_, 1);
v_tail_458_ = lean_ctor_get(v_x_454_, 2);
v___x_459_ = l_Lean_instBEqFVarId_beq(v_key_456_, v_a_453_);
if (v___x_459_ == 0)
{
v_x_454_ = v_tail_458_;
goto _start;
}
else
{
lean_object* v___x_461_; 
lean_inc(v_value_457_);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v_value_457_);
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg___boxed(lean_object* v_a_462_, lean_object* v_x_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_462_, v_x_463_);
lean_dec(v_x_463_);
lean_dec(v_a_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object* v_m_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_buckets_467_; lean_object* v___x_468_; uint64_t v___x_469_; uint64_t v___x_470_; uint64_t v___x_471_; uint64_t v_fold_472_; uint64_t v___x_473_; uint64_t v___x_474_; uint64_t v___x_475_; size_t v___x_476_; size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; size_t v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v_buckets_467_ = lean_ctor_get(v_m_465_, 1);
v___x_468_ = lean_array_get_size(v_buckets_467_);
v___x_469_ = l_Lean_instHashableFVarId_hash(v_a_466_);
v___x_470_ = 32ULL;
v___x_471_ = lean_uint64_shift_right(v___x_469_, v___x_470_);
v_fold_472_ = lean_uint64_xor(v___x_469_, v___x_471_);
v___x_473_ = 16ULL;
v___x_474_ = lean_uint64_shift_right(v_fold_472_, v___x_473_);
v___x_475_ = lean_uint64_xor(v_fold_472_, v___x_474_);
v___x_476_ = lean_uint64_to_usize(v___x_475_);
v___x_477_ = lean_usize_of_nat(v___x_468_);
v___x_478_ = ((size_t)1ULL);
v___x_479_ = lean_usize_sub(v___x_477_, v___x_478_);
v___x_480_ = lean_usize_land(v___x_476_, v___x_479_);
v___x_481_ = lean_array_uget_borrowed(v_buckets_467_, v___x_480_);
v___x_482_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_466_, v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg___boxed(lean_object* v_m_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_483_, v_a_484_);
lean_dec(v_a_484_);
lean_dec_ref(v_m_483_);
return v_res_485_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getType___closed__1(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l_Lean_Compiler_LCNF_getType___closed__0));
v___x_488_ = l_Lean_stringToMessageData(v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType(lean_object* v_fvarId_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_st_ref_get(v_a_491_);
v___x_496_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_490_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_547_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_547_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_547_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_547_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___y_502_; lean_object* v_lctx_513_; lean_object* v___y_515_; lean_object* v___y_530_; uint8_t v___x_544_; 
v_lctx_513_ = lean_ctor_get(v___x_495_, 0);
lean_inc_ref(v_lctx_513_);
lean_dec(v___x_495_);
v___x_544_ = lean_unbox(v_a_497_);
if (v___x_544_ == 0)
{
lean_object* v_letDeclsPure_545_; 
v_letDeclsPure_545_ = lean_ctor_get(v_lctx_513_, 2);
lean_inc_ref(v_letDeclsPure_545_);
v___y_530_ = v_letDeclsPure_545_;
goto v___jp_529_;
}
else
{
lean_object* v_letDeclsImpure_546_; 
v_letDeclsImpure_546_ = lean_ctor_get(v_lctx_513_, 3);
lean_inc_ref(v_letDeclsImpure_546_);
v___y_530_ = v_letDeclsImpure_546_;
goto v___jp_529_;
}
v___jp_501_:
{
lean_object* v___x_503_; 
v___x_503_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_502_, v_fvarId_489_);
lean_dec_ref(v___y_502_);
if (lean_obj_tag(v___x_503_) == 1)
{
lean_object* v_val_504_; lean_object* v_type_505_; lean_object* v___x_507_; 
lean_dec(v_fvarId_489_);
v_val_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_val_504_);
lean_dec_ref_known(v___x_503_, 1);
v_type_505_ = lean_ctor_get(v_val_504_, 3);
lean_inc_ref(v_type_505_);
lean_dec(v_val_504_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v_type_505_);
v___x_507_ = v___x_499_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_type_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v___x_503_);
lean_del_object(v___x_499_);
v___x_509_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_510_ = l_Lean_MessageData_ofName(v_fvarId_489_);
v___x_511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_509_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_511_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
return v___x_512_;
}
}
v___jp_514_:
{
lean_object* v___x_516_; 
v___x_516_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_515_, v_fvarId_489_);
lean_dec_ref(v___y_515_);
if (lean_obj_tag(v___x_516_) == 1)
{
lean_object* v_val_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v_lctx_513_);
lean_del_object(v___x_499_);
lean_dec(v_a_497_);
lean_dec(v_fvarId_489_);
v_val_517_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_525_ == 0)
{
v___x_519_ = v___x_516_;
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_val_517_);
lean_dec(v___x_516_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v_type_521_; lean_object* v___x_523_; 
v_type_521_ = lean_ctor_get(v_val_517_, 2);
lean_inc_ref(v_type_521_);
lean_dec(v_val_517_);
if (v_isShared_520_ == 0)
{
lean_ctor_set_tag(v___x_519_, 0);
lean_ctor_set(v___x_519_, 0, v_type_521_);
v___x_523_ = v___x_519_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_type_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
else
{
uint8_t v___x_526_; 
lean_dec(v___x_516_);
v___x_526_ = lean_unbox(v_a_497_);
lean_dec(v_a_497_);
if (v___x_526_ == 0)
{
lean_object* v_funDeclsPure_527_; 
v_funDeclsPure_527_ = lean_ctor_get(v_lctx_513_, 4);
lean_inc_ref(v_funDeclsPure_527_);
lean_dec_ref(v_lctx_513_);
v___y_502_ = v_funDeclsPure_527_;
goto v___jp_501_;
}
else
{
lean_object* v_funDeclsImpure_528_; 
v_funDeclsImpure_528_ = lean_ctor_get(v_lctx_513_, 5);
lean_inc_ref(v_funDeclsImpure_528_);
lean_dec_ref(v_lctx_513_);
v___y_502_ = v_funDeclsImpure_528_;
goto v___jp_501_;
}
}
}
v___jp_529_:
{
lean_object* v___x_531_; 
v___x_531_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_530_, v_fvarId_489_);
lean_dec_ref(v___y_530_);
if (lean_obj_tag(v___x_531_) == 1)
{
lean_object* v_val_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_540_; 
lean_dec_ref(v_lctx_513_);
lean_del_object(v___x_499_);
lean_dec(v_a_497_);
lean_dec(v_fvarId_489_);
v_val_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_540_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_540_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_val_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_540_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v_type_536_; lean_object* v___x_538_; 
v_type_536_ = lean_ctor_get(v_val_532_, 2);
lean_inc_ref(v_type_536_);
lean_dec(v_val_532_);
if (v_isShared_535_ == 0)
{
lean_ctor_set_tag(v___x_534_, 0);
lean_ctor_set(v___x_534_, 0, v_type_536_);
v___x_538_ = v___x_534_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_type_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
else
{
uint8_t v___x_541_; 
lean_dec(v___x_531_);
v___x_541_ = lean_unbox(v_a_497_);
if (v___x_541_ == 0)
{
lean_object* v_paramsPure_542_; 
v_paramsPure_542_ = lean_ctor_get(v_lctx_513_, 0);
lean_inc_ref(v_paramsPure_542_);
v___y_515_ = v_paramsPure_542_;
goto v___jp_514_;
}
else
{
lean_object* v_paramsImpure_543_; 
v_paramsImpure_543_ = lean_ctor_get(v_lctx_513_, 1);
lean_inc_ref(v_paramsImpure_543_);
v___y_515_ = v_paramsImpure_543_;
goto v___jp_514_;
}
}
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec(v___x_495_);
lean_dec(v_fvarId_489_);
v_a_548_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_496_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_496_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType___boxed(lean_object* v_fvarId_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Compiler_LCNF_getType(v_fvarId_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(lean_object* v_00_u03b2_563_, lean_object* v_m_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_564_, v_a_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___boxed(lean_object* v_00_u03b2_567_, lean_object* v_m_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(v_00_u03b2_567_, v_m_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_m_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(lean_object* v_00_u03b2_571_, lean_object* v_a_572_, lean_object* v_x_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_572_, v_x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_575_, lean_object* v_a_576_, lean_object* v_x_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(v_00_u03b2_575_, v_a_576_, v_x_577_);
lean_dec(v_x_577_);
lean_dec(v_a_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object* v_fvarId_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = lean_st_ref_get(v_a_581_);
v___x_586_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_580_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_637_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_637_ == 0)
{
v___x_589_ = v___x_586_;
v_isShared_590_ = v_isSharedCheck_637_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_586_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_637_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___y_592_; lean_object* v_lctx_603_; lean_object* v___y_605_; lean_object* v___y_620_; uint8_t v___x_634_; 
v_lctx_603_ = lean_ctor_get(v___x_585_, 0);
lean_inc_ref(v_lctx_603_);
lean_dec(v___x_585_);
v___x_634_ = lean_unbox(v_a_587_);
if (v___x_634_ == 0)
{
lean_object* v_letDeclsPure_635_; 
v_letDeclsPure_635_ = lean_ctor_get(v_lctx_603_, 2);
lean_inc_ref(v_letDeclsPure_635_);
v___y_620_ = v_letDeclsPure_635_;
goto v___jp_619_;
}
else
{
lean_object* v_letDeclsImpure_636_; 
v_letDeclsImpure_636_ = lean_ctor_get(v_lctx_603_, 3);
lean_inc_ref(v_letDeclsImpure_636_);
v___y_620_ = v_letDeclsImpure_636_;
goto v___jp_619_;
}
v___jp_591_:
{
lean_object* v___x_593_; 
v___x_593_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_592_, v_fvarId_579_);
lean_dec_ref(v___y_592_);
if (lean_obj_tag(v___x_593_) == 1)
{
lean_object* v_val_594_; lean_object* v_binderName_595_; lean_object* v___x_597_; 
lean_dec(v_fvarId_579_);
v_val_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_val_594_);
lean_dec_ref_known(v___x_593_, 1);
v_binderName_595_ = lean_ctor_get(v_val_594_, 1);
lean_inc(v_binderName_595_);
lean_dec(v_val_594_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v_binderName_595_);
v___x_597_ = v___x_589_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_binderName_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v___x_593_);
lean_del_object(v___x_589_);
v___x_599_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_600_ = l_Lean_MessageData_ofName(v_fvarId_579_);
v___x_601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_601_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
return v___x_602_;
}
}
v___jp_604_:
{
lean_object* v___x_606_; 
v___x_606_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_605_, v_fvarId_579_);
lean_dec_ref(v___y_605_);
if (lean_obj_tag(v___x_606_) == 1)
{
lean_object* v_val_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v_lctx_603_);
lean_del_object(v___x_589_);
lean_dec(v_a_587_);
lean_dec(v_fvarId_579_);
v_val_607_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_615_ == 0)
{
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_val_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v_binderName_611_; lean_object* v___x_613_; 
v_binderName_611_ = lean_ctor_get(v_val_607_, 1);
lean_inc(v_binderName_611_);
lean_dec(v_val_607_);
if (v_isShared_610_ == 0)
{
lean_ctor_set_tag(v___x_609_, 0);
lean_ctor_set(v___x_609_, 0, v_binderName_611_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_binderName_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
else
{
uint8_t v___x_616_; 
lean_dec(v___x_606_);
v___x_616_ = lean_unbox(v_a_587_);
lean_dec(v_a_587_);
if (v___x_616_ == 0)
{
lean_object* v_funDeclsPure_617_; 
v_funDeclsPure_617_ = lean_ctor_get(v_lctx_603_, 4);
lean_inc_ref(v_funDeclsPure_617_);
lean_dec_ref(v_lctx_603_);
v___y_592_ = v_funDeclsPure_617_;
goto v___jp_591_;
}
else
{
lean_object* v_funDeclsImpure_618_; 
v_funDeclsImpure_618_ = lean_ctor_get(v_lctx_603_, 5);
lean_inc_ref(v_funDeclsImpure_618_);
lean_dec_ref(v_lctx_603_);
v___y_592_ = v_funDeclsImpure_618_;
goto v___jp_591_;
}
}
}
v___jp_619_:
{
lean_object* v___x_621_; 
v___x_621_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_620_, v_fvarId_579_);
lean_dec_ref(v___y_620_);
if (lean_obj_tag(v___x_621_) == 1)
{
lean_object* v_val_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v_lctx_603_);
lean_del_object(v___x_589_);
lean_dec(v_a_587_);
lean_dec(v_fvarId_579_);
v_val_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_630_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_630_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_val_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_630_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v_binderName_626_; lean_object* v___x_628_; 
v_binderName_626_ = lean_ctor_get(v_val_622_, 1);
lean_inc(v_binderName_626_);
lean_dec(v_val_622_);
if (v_isShared_625_ == 0)
{
lean_ctor_set_tag(v___x_624_, 0);
lean_ctor_set(v___x_624_, 0, v_binderName_626_);
v___x_628_ = v___x_624_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_binderName_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
else
{
uint8_t v___x_631_; 
lean_dec(v___x_621_);
v___x_631_ = lean_unbox(v_a_587_);
if (v___x_631_ == 0)
{
lean_object* v_paramsPure_632_; 
v_paramsPure_632_ = lean_ctor_get(v_lctx_603_, 0);
lean_inc_ref(v_paramsPure_632_);
v___y_605_ = v_paramsPure_632_;
goto v___jp_604_;
}
else
{
lean_object* v_paramsImpure_633_; 
v_paramsImpure_633_ = lean_ctor_get(v_lctx_603_, 1);
lean_inc_ref(v_paramsImpure_633_);
v___y_605_ = v_paramsImpure_633_;
goto v___jp_604_;
}
}
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec(v___x_585_);
lean_dec(v_fvarId_579_);
v_a_638_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_586_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_586_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName___boxed(lean_object* v_fvarId_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t v_pu_653_, lean_object* v_fvarId_654_, lean_object* v_a_655_){
_start:
{
lean_object* v___x_657_; lean_object* v___y_659_; 
v___x_657_ = lean_st_ref_get(v_a_655_);
if (v_pu_653_ == 0)
{
lean_object* v_lctx_662_; lean_object* v_paramsPure_663_; 
v_lctx_662_ = lean_ctor_get(v___x_657_, 0);
lean_inc_ref(v_lctx_662_);
lean_dec(v___x_657_);
v_paramsPure_663_ = lean_ctor_get(v_lctx_662_, 0);
lean_inc_ref(v_paramsPure_663_);
lean_dec_ref(v_lctx_662_);
v___y_659_ = v_paramsPure_663_;
goto v___jp_658_;
}
else
{
lean_object* v_lctx_664_; lean_object* v_paramsImpure_665_; 
v_lctx_664_ = lean_ctor_get(v___x_657_, 0);
lean_inc_ref(v_lctx_664_);
lean_dec(v___x_657_);
v_paramsImpure_665_ = lean_ctor_get(v_lctx_664_, 1);
lean_inc_ref(v_paramsImpure_665_);
lean_dec_ref(v_lctx_664_);
v___y_659_ = v_paramsImpure_665_;
goto v___jp_658_;
}
v___jp_658_:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_659_, v_fvarId_654_);
lean_dec_ref(v___y_659_);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg___boxed(lean_object* v_pu_666_, lean_object* v_fvarId_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
uint8_t v_pu_boxed_670_; lean_object* v_res_671_; 
v_pu_boxed_670_ = lean_unbox(v_pu_666_);
v_res_671_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_boxed_670_, v_fvarId_667_, v_a_668_);
lean_dec(v_a_668_);
lean_dec(v_fvarId_667_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f(uint8_t v_pu_672_, lean_object* v_fvarId_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_672_, v_fvarId_673_, v_a_675_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___boxed(lean_object* v_pu_680_, lean_object* v_fvarId_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
uint8_t v_pu_boxed_687_; lean_object* v_res_688_; 
v_pu_boxed_687_ = lean_unbox(v_pu_680_);
v_res_688_ = l_Lean_Compiler_LCNF_findParam_x3f(v_pu_boxed_687_, v_fvarId_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_fvarId_681_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t v_pu_689_, lean_object* v_fvarId_690_, lean_object* v_a_691_){
_start:
{
lean_object* v___x_693_; lean_object* v___y_695_; 
v___x_693_ = lean_st_ref_get(v_a_691_);
if (v_pu_689_ == 0)
{
lean_object* v_lctx_698_; lean_object* v_letDeclsPure_699_; 
v_lctx_698_ = lean_ctor_get(v___x_693_, 0);
lean_inc_ref(v_lctx_698_);
lean_dec(v___x_693_);
v_letDeclsPure_699_ = lean_ctor_get(v_lctx_698_, 2);
lean_inc_ref(v_letDeclsPure_699_);
lean_dec_ref(v_lctx_698_);
v___y_695_ = v_letDeclsPure_699_;
goto v___jp_694_;
}
else
{
lean_object* v_lctx_700_; lean_object* v_letDeclsImpure_701_; 
v_lctx_700_ = lean_ctor_get(v___x_693_, 0);
lean_inc_ref(v_lctx_700_);
lean_dec(v___x_693_);
v_letDeclsImpure_701_ = lean_ctor_get(v_lctx_700_, 3);
lean_inc_ref(v_letDeclsImpure_701_);
lean_dec_ref(v_lctx_700_);
v___y_695_ = v_letDeclsImpure_701_;
goto v___jp_694_;
}
v___jp_694_:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_695_, v_fvarId_690_);
lean_dec_ref(v___y_695_);
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg___boxed(lean_object* v_pu_702_, lean_object* v_fvarId_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
uint8_t v_pu_boxed_706_; lean_object* v_res_707_; 
v_pu_boxed_706_ = lean_unbox(v_pu_702_);
v_res_707_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_boxed_706_, v_fvarId_703_, v_a_704_);
lean_dec(v_a_704_);
lean_dec(v_fvarId_703_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(uint8_t v_pu_708_, lean_object* v_fvarId_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_708_, v_fvarId_709_, v_a_711_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___boxed(lean_object* v_pu_716_, lean_object* v_fvarId_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
uint8_t v_pu_boxed_723_; lean_object* v_res_724_; 
v_pu_boxed_723_ = lean_unbox(v_pu_716_);
v_res_724_ = l_Lean_Compiler_LCNF_findLetDecl_x3f(v_pu_boxed_723_, v_fvarId_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_fvarId_717_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t v_pu_725_, lean_object* v_fvarId_726_, lean_object* v_a_727_){
_start:
{
lean_object* v___x_729_; lean_object* v___y_731_; 
v___x_729_ = lean_st_ref_get(v_a_727_);
if (v_pu_725_ == 0)
{
lean_object* v_lctx_734_; lean_object* v_funDeclsPure_735_; 
v_lctx_734_ = lean_ctor_get(v___x_729_, 0);
lean_inc_ref(v_lctx_734_);
lean_dec(v___x_729_);
v_funDeclsPure_735_ = lean_ctor_get(v_lctx_734_, 4);
lean_inc_ref(v_funDeclsPure_735_);
lean_dec_ref(v_lctx_734_);
v___y_731_ = v_funDeclsPure_735_;
goto v___jp_730_;
}
else
{
lean_object* v_lctx_736_; lean_object* v_funDeclsImpure_737_; 
v_lctx_736_ = lean_ctor_get(v___x_729_, 0);
lean_inc_ref(v_lctx_736_);
lean_dec(v___x_729_);
v_funDeclsImpure_737_ = lean_ctor_get(v_lctx_736_, 5);
lean_inc_ref(v_funDeclsImpure_737_);
lean_dec_ref(v_lctx_736_);
v___y_731_ = v_funDeclsImpure_737_;
goto v___jp_730_;
}
v___jp_730_:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_731_, v_fvarId_726_);
lean_dec_ref(v___y_731_);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg___boxed(lean_object* v_pu_738_, lean_object* v_fvarId_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
uint8_t v_pu_boxed_742_; lean_object* v_res_743_; 
v_pu_boxed_742_ = lean_unbox(v_pu_738_);
v_res_743_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_boxed_742_, v_fvarId_739_, v_a_740_);
lean_dec(v_a_740_);
lean_dec(v_fvarId_739_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(uint8_t v_pu_744_, lean_object* v_fvarId_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_744_, v_fvarId_745_, v_a_747_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___boxed(lean_object* v_pu_752_, lean_object* v_fvarId_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
uint8_t v_pu_boxed_759_; lean_object* v_res_760_; 
v_pu_boxed_759_ = lean_unbox(v_pu_752_);
v_res_760_ = l_Lean_Compiler_LCNF_findFunDecl_x3f(v_pu_boxed_759_, v_fvarId_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_fvarId_753_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t v_pu_761_, lean_object* v_fvarId_762_, lean_object* v_a_763_){
_start:
{
lean_object* v___x_765_; lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_786_; 
v___x_765_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_761_, v_fvarId_762_, v_a_763_);
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_786_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_786_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_786_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
if (lean_obj_tag(v_a_766_) == 1)
{
lean_object* v_val_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_781_; 
v_val_770_ = lean_ctor_get(v_a_766_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v_a_766_);
if (v_isSharedCheck_781_ == 0)
{
v___x_772_ = v_a_766_;
v_isShared_773_ = v_isSharedCheck_781_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_val_770_);
lean_dec(v_a_766_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_781_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_value_774_; lean_object* v___x_776_; 
v_value_774_ = lean_ctor_get(v_val_770_, 3);
lean_inc(v_value_774_);
lean_dec(v_val_770_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v_value_774_);
v___x_776_ = v___x_772_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_value_774_);
v___x_776_ = v_reuseFailAlloc_780_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_778_; 
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_776_);
v___x_778_ = v___x_768_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
else
{
lean_object* v___x_782_; lean_object* v___x_784_; 
lean_dec(v_a_766_);
v___x_782_ = lean_box(0);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_782_);
v___x_784_ = v___x_768_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg___boxed(lean_object* v_pu_787_, lean_object* v_fvarId_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
uint8_t v_pu_boxed_791_; lean_object* v_res_792_; 
v_pu_boxed_791_ = lean_unbox(v_pu_787_);
v_res_792_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_boxed_791_, v_fvarId_788_, v_a_789_);
lean_dec(v_a_789_);
lean_dec(v_fvarId_788_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f(uint8_t v_pu_793_, lean_object* v_fvarId_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_793_, v_fvarId_794_, v_a_796_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___boxed(lean_object* v_pu_801_, lean_object* v_fvarId_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
uint8_t v_pu_boxed_808_; lean_object* v_res_809_; 
v_pu_boxed_808_ = lean_unbox(v_pu_801_);
v_res_809_ = l_Lean_Compiler_LCNF_findLetValue_x3f(v_pu_boxed_808_, v_fvarId_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_fvarId_802_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg(lean_object* v_fvarId_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
uint8_t v___x_814_; lean_object* v___x_815_; 
v___x_814_ = 0;
v___x_815_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_814_, v_fvarId_810_, v_a_811_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_853_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_853_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_853_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_853_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
if (lean_obj_tag(v_a_816_) == 1)
{
lean_object* v_val_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_852_; 
v_val_826_ = lean_ctor_get(v_a_816_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v_a_816_);
if (v_isSharedCheck_852_ == 0)
{
v___x_828_ = v_a_816_;
v_isShared_829_ = v_isSharedCheck_852_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_val_826_);
lean_dec(v_a_816_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_852_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
if (lean_obj_tag(v_val_826_) == 3)
{
lean_object* v_declName_830_; lean_object* v___x_831_; lean_object* v_env_838_; uint8_t v___x_839_; lean_object* v___x_840_; 
lean_del_object(v___x_818_);
v_declName_830_ = lean_ctor_get(v_val_826_, 0);
lean_inc(v_declName_830_);
lean_dec_ref_known(v_val_826_, 3);
v___x_831_ = lean_st_ref_get(v_a_812_);
v_env_838_ = lean_ctor_get(v___x_831_, 0);
lean_inc_ref(v_env_838_);
lean_dec(v___x_831_);
v___x_839_ = 0;
v___x_840_ = l_Lean_Environment_find_x3f(v_env_838_, v_declName_830_, v___x_839_);
if (lean_obj_tag(v___x_840_) == 1)
{
lean_object* v_val_841_; 
v_val_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_val_841_);
lean_dec_ref_known(v___x_840_, 1);
if (lean_obj_tag(v_val_841_) == 6)
{
lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_850_; 
lean_del_object(v___x_828_);
v_isSharedCheck_850_ = !lean_is_exclusive(v_val_841_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; 
v_unused_851_ = lean_ctor_get(v_val_841_, 0);
lean_dec(v_unused_851_);
v___x_843_ = v_val_841_;
v_isShared_844_ = v_isSharedCheck_850_;
goto v_resetjp_842_;
}
else
{
lean_dec(v_val_841_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_850_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_845_ = 1;
v___x_846_ = lean_box(v___x_845_);
if (v_isShared_844_ == 0)
{
lean_ctor_set_tag(v___x_843_, 0);
lean_ctor_set(v___x_843_, 0, v___x_846_);
v___x_848_ = v___x_843_;
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
else
{
lean_dec(v_val_841_);
goto v___jp_832_;
}
}
else
{
lean_dec(v___x_840_);
goto v___jp_832_;
}
v___jp_832_:
{
uint8_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_833_ = 0;
v___x_834_ = lean_box(v___x_833_);
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 0);
lean_ctor_set(v___x_828_, 0, v___x_834_);
v___x_836_ = v___x_828_;
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
}
else
{
lean_del_object(v___x_828_);
lean_dec(v_val_826_);
goto v___jp_820_;
}
}
}
else
{
lean_dec(v_a_816_);
goto v___jp_820_;
}
v___jp_820_:
{
uint8_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_821_ = 0;
v___x_822_ = lean_box(v___x_821_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_822_);
v___x_824_ = v___x_818_;
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
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
v_a_854_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_815_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_815_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg___boxed(lean_object* v_fvarId_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_862_, v_a_863_, v_a_864_);
lean_dec(v_a_864_);
lean_dec(v_a_863_);
lean_dec(v_fvarId_862_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp(lean_object* v_fvarId_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_867_, v_a_869_, v_a_871_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___boxed(lean_object* v_fvarId_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_Compiler_LCNF_isConstructorApp(v_fvarId_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_fvarId_874_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(lean_object* v_arg_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
if (lean_obj_tag(v_arg_881_) == 1)
{
lean_object* v_fvarId_885_; lean_object* v___x_886_; 
v_fvarId_885_ = lean_ctor_get(v_arg_881_, 0);
v___x_886_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_885_, v_a_882_, v_a_883_);
return v___x_886_;
}
else
{
uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_887_ = 0;
v___x_888_ = lean_box(v___x_887_);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg___boxed(lean_object* v_arg_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_890_, v_a_891_, v_a_892_);
lean_dec(v_a_892_);
lean_dec(v_a_891_);
lean_dec(v_arg_890_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp(uint8_t v_pu_895_, lean_object* v_arg_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_896_, v_a_898_, v_a_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___boxed(lean_object* v_pu_903_, lean_object* v_arg_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
uint8_t v_pu_boxed_910_; lean_object* v_res_911_; 
v_pu_boxed_910_ = lean_unbox(v_pu_903_);
v_res_911_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp(v_pu_boxed_910_, v_arg_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_arg_904_);
return v_res_911_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getParam___closed__1(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParam___closed__0));
v___x_914_ = l_Lean_stringToMessageData(v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam(uint8_t v_pu_915_, lean_object* v_fvarId_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v___x_922_; lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_935_; 
v___x_922_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_915_, v_fvarId_916_, v_a_918_);
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_935_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_935_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_935_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
if (lean_obj_tag(v_a_923_) == 1)
{
lean_object* v_val_927_; lean_object* v___x_929_; 
lean_dec(v_fvarId_916_);
v_val_927_ = lean_ctor_get(v_a_923_, 0);
lean_inc(v_val_927_);
lean_dec_ref_known(v_a_923_, 1);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v_val_927_);
v___x_929_ = v___x_925_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_val_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
lean_del_object(v___x_925_);
lean_dec(v_a_923_);
v___x_931_ = lean_obj_once(&l_Lean_Compiler_LCNF_getParam___closed__1, &l_Lean_Compiler_LCNF_getParam___closed__1_once, _init_l_Lean_Compiler_LCNF_getParam___closed__1);
v___x_932_ = l_Lean_MessageData_ofName(v_fvarId_916_);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_933_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
return v___x_934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam___boxed(lean_object* v_pu_936_, lean_object* v_fvarId_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
uint8_t v_pu_boxed_943_; lean_object* v_res_944_; 
v_pu_boxed_943_ = lean_unbox(v_pu_936_);
v_res_944_ = l_Lean_Compiler_LCNF_getParam(v_pu_boxed_943_, v_fvarId_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
return v_res_944_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = ((lean_object*)(l_Lean_Compiler_LCNF_getLetDecl___closed__0));
v___x_947_ = l_Lean_stringToMessageData(v___x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl(uint8_t v_pu_948_, lean_object* v_fvarId_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v___x_955_; lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_968_; 
v___x_955_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_948_, v_fvarId_949_, v_a_951_);
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_968_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_968_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_968_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
if (lean_obj_tag(v_a_956_) == 1)
{
lean_object* v_val_960_; lean_object* v___x_962_; 
lean_dec(v_fvarId_949_);
v_val_960_ = lean_ctor_get(v_a_956_, 0);
lean_inc(v_val_960_);
lean_dec_ref_known(v_a_956_, 1);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v_val_960_);
v___x_962_ = v___x_958_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_val_960_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
lean_del_object(v___x_958_);
lean_dec(v_a_956_);
v___x_964_ = lean_obj_once(&l_Lean_Compiler_LCNF_getLetDecl___closed__1, &l_Lean_Compiler_LCNF_getLetDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1);
v___x_965_ = l_Lean_MessageData_ofName(v_fvarId_949_);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_966_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
return v___x_967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl___boxed(lean_object* v_pu_969_, lean_object* v_fvarId_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
uint8_t v_pu_boxed_976_; lean_object* v_res_977_; 
v_pu_boxed_976_ = lean_unbox(v_pu_969_);
v_res_977_ = l_Lean_Compiler_LCNF_getLetDecl(v_pu_boxed_976_, v_fvarId_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
return v_res_977_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = ((lean_object*)(l_Lean_Compiler_LCNF_getFunDecl___closed__0));
v___x_980_ = l_Lean_stringToMessageData(v___x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t v_pu_981_, lean_object* v_fvarId_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v___x_988_; lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1001_; 
v___x_988_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_981_, v_fvarId_982_, v_a_984_);
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_1001_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1001_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
if (lean_obj_tag(v_a_989_) == 1)
{
lean_object* v_val_993_; lean_object* v___x_995_; 
lean_dec(v_fvarId_982_);
v_val_993_ = lean_ctor_get(v_a_989_, 0);
lean_inc(v_val_993_);
lean_dec_ref_known(v_a_989_, 1);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v_val_993_);
v___x_995_ = v___x_991_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_val_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
else
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_del_object(v___x_991_);
lean_dec(v_a_989_);
v___x_997_ = lean_obj_once(&l_Lean_Compiler_LCNF_getFunDecl___closed__1, &l_Lean_Compiler_LCNF_getFunDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1);
v___x_998_ = l_Lean_MessageData_ofName(v_fvarId_982_);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_999_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
return v___x_1000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl___boxed(lean_object* v_pu_1002_, lean_object* v_fvarId_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
uint8_t v_pu_boxed_1009_; lean_object* v_res_1010_; 
v_pu_boxed_1009_ = lean_unbox(v_pu_1002_);
v_res_1010_ = l_Lean_Compiler_LCNF_getFunDecl(v_pu_boxed_1009_, v_fvarId_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg(lean_object* v_f_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v___x_1014_; lean_object* v_lctx_1015_; lean_object* v_nextIdx_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1027_; 
v___x_1014_ = lean_st_ref_take(v_a_1012_);
v_lctx_1015_ = lean_ctor_get(v___x_1014_, 0);
v_nextIdx_1016_ = lean_ctor_get(v___x_1014_, 1);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1018_ = v___x_1014_;
v_isShared_1019_ = v_isSharedCheck_1027_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_nextIdx_1016_);
lean_inc(v_lctx_1015_);
lean_dec(v___x_1014_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1027_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1020_ = lean_apply_1(v_f_1011_, v_lctx_1015_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1020_);
v___x_1022_ = v___x_1018_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_nextIdx_1016_);
v___x_1022_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = lean_st_ref_put(v_a_1012_, v___x_1022_);
v___x_1024_ = lean_box(0);
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg___boxed(lean_object* v_f_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_Compiler_LCNF_modifyLCtx___redArg(v_f_1028_, v_a_1029_);
lean_dec(v_a_1029_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx(lean_object* v_f_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v___x_1038_; lean_object* v_lctx_1039_; lean_object* v_nextIdx_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1051_; 
v___x_1038_ = lean_st_ref_take(v_a_1034_);
v_lctx_1039_ = lean_ctor_get(v___x_1038_, 0);
v_nextIdx_1040_ = lean_ctor_get(v___x_1038_, 1);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1042_ = v___x_1038_;
v_isShared_1043_ = v_isSharedCheck_1051_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_nextIdx_1040_);
lean_inc(v_lctx_1039_);
lean_dec(v___x_1038_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1051_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1044_ = lean_apply_1(v_f_1032_, v_lctx_1039_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1044_);
v___x_1046_ = v___x_1042_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_nextIdx_1040_);
v___x_1046_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1047_ = lean_st_ref_put(v_a_1034_, v___x_1046_);
v___x_1048_ = lean_box(0);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___boxed(lean_object* v_f_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Compiler_LCNF_modifyLCtx(v_f_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t v_pu_1059_, lean_object* v_decl_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v___x_1063_; lean_object* v_lctx_1064_; lean_object* v_nextIdx_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1076_; 
v___x_1063_ = lean_st_ref_take(v_a_1061_);
v_lctx_1064_ = lean_ctor_get(v___x_1063_, 0);
v_nextIdx_1065_ = lean_ctor_get(v___x_1063_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1067_ = v___x_1063_;
v_isShared_1068_ = v_isSharedCheck_1076_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_nextIdx_1065_);
lean_inc(v_lctx_1064_);
lean_dec(v___x_1063_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1076_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1069_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_1059_, v_lctx_1064_, v_decl_1060_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1069_);
v___x_1071_ = v___x_1067_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_nextIdx_1065_);
v___x_1071_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1072_ = lean_st_ref_put(v_a_1061_, v___x_1071_);
v___x_1073_ = lean_box(0);
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
return v___x_1074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg___boxed(lean_object* v_pu_1077_, lean_object* v_decl_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
uint8_t v_pu_boxed_1081_; lean_object* v_res_1082_; 
v_pu_boxed_1081_ = lean_unbox(v_pu_1077_);
v_res_1082_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_boxed_1081_, v_decl_1078_, v_a_1079_);
lean_dec(v_a_1079_);
lean_dec_ref(v_decl_1078_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(uint8_t v_pu_1083_, lean_object* v_decl_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1083_, v_decl_1084_, v_a_1086_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___boxed(lean_object* v_pu_1091_, lean_object* v_decl_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
uint8_t v_pu_boxed_1098_; lean_object* v_res_1099_; 
v_pu_boxed_1098_ = lean_unbox(v_pu_1091_);
v_res_1099_ = l_Lean_Compiler_LCNF_eraseLetDecl(v_pu_boxed_1098_, v_decl_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
lean_dec_ref(v_decl_1092_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t v_pu_1100_, lean_object* v_decl_1101_, uint8_t v_recursive_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v___x_1105_; lean_object* v_lctx_1106_; lean_object* v_nextIdx_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1118_; 
v___x_1105_ = lean_st_ref_take(v_a_1103_);
v_lctx_1106_ = lean_ctor_get(v___x_1105_, 0);
v_nextIdx_1107_ = lean_ctor_get(v___x_1105_, 1);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1109_ = v___x_1105_;
v_isShared_1110_ = v_isSharedCheck_1118_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_nextIdx_1107_);
lean_inc(v_lctx_1106_);
lean_dec(v___x_1105_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1118_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1111_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_1100_, v_lctx_1106_, v_decl_1101_, v_recursive_1102_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1111_);
v___x_1113_ = v___x_1109_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_nextIdx_1107_);
v___x_1113_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = lean_st_ref_put(v_a_1103_, v___x_1113_);
v___x_1115_ = lean_box(0);
v___x_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
return v___x_1116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg___boxed(lean_object* v_pu_1119_, lean_object* v_decl_1120_, lean_object* v_recursive_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
uint8_t v_pu_boxed_1124_; uint8_t v_recursive_boxed_1125_; lean_object* v_res_1126_; 
v_pu_boxed_1124_ = lean_unbox(v_pu_1119_);
v_recursive_boxed_1125_ = lean_unbox(v_recursive_1121_);
v_res_1126_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_boxed_1124_, v_decl_1120_, v_recursive_boxed_1125_, v_a_1122_);
lean_dec(v_a_1122_);
lean_dec_ref(v_decl_1120_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(uint8_t v_pu_1127_, lean_object* v_decl_1128_, uint8_t v_recursive_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1127_, v_decl_1128_, v_recursive_1129_, v_a_1131_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___boxed(lean_object* v_pu_1136_, lean_object* v_decl_1137_, lean_object* v_recursive_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
uint8_t v_pu_boxed_1144_; uint8_t v_recursive_boxed_1145_; lean_object* v_res_1146_; 
v_pu_boxed_1144_ = lean_unbox(v_pu_1136_);
v_recursive_boxed_1145_ = lean_unbox(v_recursive_1138_);
v_res_1146_ = l_Lean_Compiler_LCNF_eraseFunDecl(v_pu_boxed_1144_, v_decl_1137_, v_recursive_boxed_1145_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec_ref(v_decl_1137_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t v_pu_1147_, lean_object* v_code_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v___x_1151_; lean_object* v_lctx_1152_; lean_object* v_nextIdx_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1164_; 
v___x_1151_ = lean_st_ref_take(v_a_1149_);
v_lctx_1152_ = lean_ctor_get(v___x_1151_, 0);
v_nextIdx_1153_ = lean_ctor_get(v___x_1151_, 1);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1155_ = v___x_1151_;
v_isShared_1156_ = v_isSharedCheck_1164_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_nextIdx_1153_);
lean_inc(v_lctx_1152_);
lean_dec(v___x_1151_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1164_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1157_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_1147_, v_code_1148_, v_lctx_1152_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v___x_1157_);
v___x_1159_ = v___x_1155_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_nextIdx_1153_);
v___x_1159_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1160_ = lean_st_ref_put(v_a_1149_, v___x_1159_);
v___x_1161_ = lean_box(0);
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
return v___x_1162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg___boxed(lean_object* v_pu_1165_, lean_object* v_code_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
uint8_t v_pu_boxed_1169_; lean_object* v_res_1170_; 
v_pu_boxed_1169_ = lean_unbox(v_pu_1165_);
v_res_1170_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_boxed_1169_, v_code_1166_, v_a_1167_);
lean_dec(v_a_1167_);
lean_dec_ref(v_code_1166_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode(uint8_t v_pu_1171_, lean_object* v_code_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_1171_, v_code_1172_, v_a_1174_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___boxed(lean_object* v_pu_1179_, lean_object* v_code_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
uint8_t v_pu_boxed_1186_; lean_object* v_res_1187_; 
v_pu_boxed_1186_ = lean_unbox(v_pu_1179_);
v_res_1187_ = l_Lean_Compiler_LCNF_eraseCode(v_pu_boxed_1186_, v_code_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec_ref(v_code_1180_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t v_pu_1188_, lean_object* v_param_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v___x_1192_; lean_object* v_lctx_1193_; lean_object* v_nextIdx_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1205_; 
v___x_1192_ = lean_st_ref_take(v_a_1190_);
v_lctx_1193_ = lean_ctor_get(v___x_1192_, 0);
v_nextIdx_1194_ = lean_ctor_get(v___x_1192_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1196_ = v___x_1192_;
v_isShared_1197_ = v_isSharedCheck_1205_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_nextIdx_1194_);
lean_inc(v_lctx_1193_);
lean_dec(v___x_1192_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1205_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1198_ = l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_1188_, v_lctx_1193_, v_param_1189_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1198_);
v___x_1200_ = v___x_1196_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_nextIdx_1194_);
v___x_1200_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1201_ = lean_st_ref_put(v_a_1190_, v___x_1200_);
v___x_1202_ = lean_box(0);
v___x_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
return v___x_1203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg___boxed(lean_object* v_pu_1206_, lean_object* v_param_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
uint8_t v_pu_boxed_1210_; lean_object* v_res_1211_; 
v_pu_boxed_1210_ = lean_unbox(v_pu_1206_);
v_res_1211_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_boxed_1210_, v_param_1207_, v_a_1208_);
lean_dec(v_a_1208_);
lean_dec_ref(v_param_1207_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam(uint8_t v_pu_1212_, lean_object* v_param_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_1212_, v_param_1213_, v_a_1215_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___boxed(lean_object* v_pu_1220_, lean_object* v_param_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
uint8_t v_pu_boxed_1227_; lean_object* v_res_1228_; 
v_pu_boxed_1227_ = lean_unbox(v_pu_1220_);
v_res_1228_ = l_Lean_Compiler_LCNF_eraseParam(v_pu_boxed_1227_, v_param_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec_ref(v_param_1221_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t v_pu_1229_, lean_object* v_params_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v___x_1233_; lean_object* v_lctx_1234_; lean_object* v_nextIdx_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1246_; 
v___x_1233_ = lean_st_ref_take(v_a_1231_);
v_lctx_1234_ = lean_ctor_get(v___x_1233_, 0);
v_nextIdx_1235_ = lean_ctor_get(v___x_1233_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1237_ = v___x_1233_;
v_isShared_1238_ = v_isSharedCheck_1246_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_nextIdx_1235_);
lean_inc(v_lctx_1234_);
lean_dec(v___x_1233_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1246_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1239_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_1229_, v_lctx_1234_, v_params_1230_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v___x_1239_);
v___x_1241_ = v___x_1237_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_nextIdx_1235_);
v___x_1241_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = lean_st_ref_put(v_a_1231_, v___x_1241_);
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg___boxed(lean_object* v_pu_1247_, lean_object* v_params_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
uint8_t v_pu_boxed_1251_; lean_object* v_res_1252_; 
v_pu_boxed_1251_ = lean_unbox(v_pu_1247_);
v_res_1252_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_boxed_1251_, v_params_1248_, v_a_1249_);
lean_dec(v_a_1249_);
lean_dec_ref(v_params_1248_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams(uint8_t v_pu_1253_, lean_object* v_params_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1253_, v_params_1254_, v_a_1256_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___boxed(lean_object* v_pu_1261_, lean_object* v_params_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
uint8_t v_pu_boxed_1268_; lean_object* v_res_1269_; 
v_pu_boxed_1268_ = lean_unbox(v_pu_1261_);
v_res_1269_ = l_Lean_Compiler_LCNF_eraseParams(v_pu_boxed_1268_, v_params_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
lean_dec_ref(v_params_1262_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t v_pu_1270_, lean_object* v_decl_1271_, lean_object* v_a_1272_){
_start:
{
switch(lean_obj_tag(v_decl_1271_))
{
case 0:
{
lean_object* v_decl_1274_; lean_object* v___x_1275_; 
v_decl_1274_ = lean_ctor_get(v_decl_1271_, 0);
v___x_1275_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1270_, v_decl_1274_, v_a_1272_);
return v___x_1275_;
}
case 1:
{
lean_object* v_decl_1276_; uint8_t v___x_1277_; lean_object* v___x_1278_; 
v_decl_1276_ = lean_ctor_get(v_decl_1271_, 0);
v___x_1277_ = 1;
v___x_1278_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1270_, v_decl_1276_, v___x_1277_, v_a_1272_);
return v___x_1278_;
}
case 2:
{
lean_object* v_decl_1279_; uint8_t v___x_1280_; lean_object* v___x_1281_; 
v_decl_1279_ = lean_ctor_get(v_decl_1271_, 0);
v___x_1280_ = 1;
v___x_1281_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1270_, v_decl_1279_, v___x_1280_, v_a_1272_);
return v___x_1281_;
}
default: 
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_box(0);
v___x_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
return v___x_1283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg___boxed(lean_object* v_pu_1284_, lean_object* v_decl_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
uint8_t v_pu_boxed_1288_; lean_object* v_res_1289_; 
v_pu_boxed_1288_ = lean_unbox(v_pu_1284_);
v_res_1289_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_boxed_1288_, v_decl_1285_, v_a_1286_);
lean_dec(v_a_1286_);
lean_dec_ref(v_decl_1285_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl(uint8_t v_pu_1290_, lean_object* v_decl_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1290_, v_decl_1291_, v_a_1293_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___boxed(lean_object* v_pu_1298_, lean_object* v_decl_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
uint8_t v_pu_boxed_1305_; lean_object* v_res_1306_; 
v_pu_boxed_1305_ = lean_unbox(v_pu_1298_);
v_res_1306_ = l_Lean_Compiler_LCNF_eraseCodeDecl(v_pu_boxed_1305_, v_decl_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec_ref(v_decl_1299_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(uint8_t v_pu_1307_, lean_object* v_as_1308_, size_t v_i_1309_, size_t v_stop_1310_, lean_object* v_b_1311_, lean_object* v___y_1312_){
_start:
{
uint8_t v___x_1314_; 
v___x_1314_ = lean_usize_dec_eq(v_i_1309_, v_stop_1310_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = lean_array_uget_borrowed(v_as_1308_, v_i_1309_);
v___x_1316_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1307_, v___x_1315_, v___y_1312_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; size_t v___x_1318_; size_t v___x_1319_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_a_1317_);
lean_dec_ref_known(v___x_1316_, 1);
v___x_1318_ = ((size_t)1ULL);
v___x_1319_ = lean_usize_add(v_i_1309_, v___x_1318_);
v_i_1309_ = v___x_1319_;
v_b_1311_ = v_a_1317_;
goto _start;
}
else
{
return v___x_1316_;
}
}
else
{
lean_object* v___x_1321_; 
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v_b_1311_);
return v___x_1321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg___boxed(lean_object* v_pu_1322_, lean_object* v_as_1323_, lean_object* v_i_1324_, lean_object* v_stop_1325_, lean_object* v_b_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
uint8_t v_pu_boxed_1329_; size_t v_i_boxed_1330_; size_t v_stop_boxed_1331_; lean_object* v_res_1332_; 
v_pu_boxed_1329_ = lean_unbox(v_pu_1322_);
v_i_boxed_1330_ = lean_unbox_usize(v_i_1324_);
lean_dec(v_i_1324_);
v_stop_boxed_1331_ = lean_unbox_usize(v_stop_1325_);
lean_dec(v_stop_1325_);
v_res_1332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_boxed_1329_, v_as_1323_, v_i_boxed_1330_, v_stop_boxed_1331_, v_b_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v_as_1323_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls(uint8_t v_pu_1333_, lean_object* v_decls_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v___x_1340_ = lean_unsigned_to_nat(0u);
v___x_1341_ = lean_array_get_size(v_decls_1334_);
v___x_1342_ = lean_box(0);
v___x_1343_ = lean_nat_dec_lt(v___x_1340_, v___x_1341_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1342_);
return v___x_1344_;
}
else
{
uint8_t v___x_1345_; 
v___x_1345_ = lean_nat_dec_le(v___x_1341_, v___x_1341_);
if (v___x_1345_ == 0)
{
if (v___x_1343_ == 0)
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1342_);
return v___x_1346_;
}
else
{
size_t v___x_1347_; size_t v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = ((size_t)0ULL);
v___x_1348_ = lean_usize_of_nat(v___x_1341_);
v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1333_, v_decls_1334_, v___x_1347_, v___x_1348_, v___x_1342_, v_a_1336_);
return v___x_1349_;
}
}
else
{
size_t v___x_1350_; size_t v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = ((size_t)0ULL);
v___x_1351_ = lean_usize_of_nat(v___x_1341_);
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1333_, v_decls_1334_, v___x_1350_, v___x_1351_, v___x_1342_, v_a_1336_);
return v___x_1352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls___boxed(lean_object* v_pu_1353_, lean_object* v_decls_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
uint8_t v_pu_boxed_1360_; lean_object* v_res_1361_; 
v_pu_boxed_1360_ = lean_unbox(v_pu_1353_);
v_res_1361_ = l_Lean_Compiler_LCNF_eraseCodeDecls(v_pu_boxed_1360_, v_decls_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
lean_dec_ref(v_decls_1354_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(uint8_t v_pu_1362_, lean_object* v_as_1363_, size_t v_i_1364_, size_t v_stop_1365_, lean_object* v_b_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1362_, v_as_1363_, v_i_1364_, v_stop_1365_, v_b_1366_, v___y_1368_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___boxed(lean_object* v_pu_1373_, lean_object* v_as_1374_, lean_object* v_i_1375_, lean_object* v_stop_1376_, lean_object* v_b_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
uint8_t v_pu_boxed_1383_; size_t v_i_boxed_1384_; size_t v_stop_boxed_1385_; lean_object* v_res_1386_; 
v_pu_boxed_1383_ = lean_unbox(v_pu_1373_);
v_i_boxed_1384_ = lean_unbox_usize(v_i_1375_);
lean_dec(v_i_1375_);
v_stop_boxed_1385_ = lean_unbox_usize(v_stop_1376_);
lean_dec(v_stop_1376_);
v_res_1386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(v_pu_boxed_1383_, v_as_1374_, v_i_boxed_1384_, v_stop_boxed_1385_, v_b_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec_ref(v_as_1374_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(lean_object* v_f_1387_, lean_object* v_v_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
if (lean_obj_tag(v_v_1388_) == 0)
{
lean_object* v_code_1394_; lean_object* v___x_1395_; 
v_code_1394_ = lean_ctor_get(v_v_1388_, 0);
lean_inc_ref(v_code_1394_);
lean_dec_ref_known(v_v_1388_, 1);
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
lean_inc(v___y_1390_);
lean_inc_ref(v___y_1389_);
v___x_1395_ = lean_apply_6(v_f_1387_, v_code_1394_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, lean_box(0));
return v___x_1395_;
}
else
{
lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1403_; 
lean_dec_ref(v_f_1387_);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_v_1388_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; 
v_unused_1404_ = lean_ctor_get(v_v_1388_, 0);
lean_dec(v_unused_1404_);
v___x_1397_ = v_v_1388_;
v_isShared_1398_ = v_isSharedCheck_1403_;
goto v_resetjp_1396_;
}
else
{
lean_dec(v_v_1388_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1403_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1399_ = lean_box(0);
if (v_isShared_1398_ == 0)
{
lean_ctor_set_tag(v___x_1397_, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1399_);
v___x_1401_ = v___x_1397_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg___boxed(lean_object* v_f_1405_, lean_object* v_v_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1405_, v_v_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(uint8_t v_pu_1413_, lean_object* v_f_1414_, lean_object* v_v_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1414_, v_v_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___boxed(lean_object* v_pu_1422_, lean_object* v_f_1423_, lean_object* v_v_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
uint8_t v_pu_boxed_1430_; lean_object* v_res_1431_; 
v_pu_boxed_1430_ = lean_unbox(v_pu_1422_);
v_res_1431_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(v_pu_boxed_1430_, v_f_1423_, v_v_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t v_pu_1432_, lean_object* v_decl_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v_toSignature_1439_; lean_object* v_value_1440_; lean_object* v_params_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v_toSignature_1439_ = lean_ctor_get(v_decl_1433_, 0);
lean_inc_ref(v_toSignature_1439_);
v_value_1440_ = lean_ctor_get(v_decl_1433_, 1);
lean_inc_ref(v_value_1440_);
lean_dec_ref(v_decl_1433_);
v_params_1441_ = lean_ctor_get(v_toSignature_1439_, 3);
lean_inc_ref(v_params_1441_);
lean_dec_ref(v_toSignature_1439_);
v___x_1442_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1432_, v_params_1441_, v_a_1435_);
lean_dec_ref(v_params_1441_);
lean_dec_ref(v___x_1442_);
v___x_1443_ = lean_box(v_pu_1432_);
v___x_1444_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_eraseCode___boxed), 7, 1);
lean_closure_set(v___x_1444_, 0, v___x_1443_);
v___x_1445_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v___x_1444_, v_value_1440_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl___boxed(lean_object* v_pu_1446_, lean_object* v_decl_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_){
_start:
{
uint8_t v_pu_boxed_1453_; lean_object* v_res_1454_; 
v_pu_boxed_1453_ = lean_unbox(v_pu_1446_);
v_res_1454_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_boxed_1453_, v_decl_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_);
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase(uint8_t v_pu_1455_, lean_object* v_decl_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_1455_, v_decl_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase___boxed(lean_object* v_pu_1463_, lean_object* v_decl_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
uint8_t v_pu_boxed_1470_; lean_object* v_res_1471_; 
v_pu_boxed_1470_ = lean_unbox(v_pu_1463_);
v_res_1471_ = l_Lean_Compiler_LCNF_Decl_erase(v_pu_boxed_1470_, v_decl_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(lean_object* v_msg_1472_){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = l_Lean_instInhabitedExpr;
v___x_1474_ = lean_panic_fn_borrowed(v___x_1473_, v_msg_1472_);
return v___x_1474_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3(void){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1478_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2));
v___x_1479_ = lean_unsigned_to_nat(20u);
v___x_1480_ = lean_unsigned_to_nat(215u);
v___x_1481_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1));
v___x_1482_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0));
v___x_1483_ = l_mkPanicMessageWithDecl(v___x_1482_, v___x_1481_, v___x_1480_, v___x_1479_, v___x_1478_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t v_pu_1484_, lean_object* v_s_1485_, uint8_t v_translator_1486_, lean_object* v_e_1487_){
_start:
{
uint8_t v___x_1488_; 
v___x_1488_ = l_Lean_Expr_hasFVar(v_e_1487_);
if (v___x_1488_ == 0)
{
return v_e_1487_;
}
else
{
switch(lean_obj_tag(v_e_1487_))
{
case 1:
{
lean_object* v_fvarId_1489_; lean_object* v___x_1490_; 
v_fvarId_1489_ = lean_ctor_get(v_e_1487_, 0);
v___x_1490_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1485_, v_fvarId_1489_);
if (lean_obj_tag(v___x_1490_) == 0)
{
return v_e_1487_;
}
else
{
lean_object* v_val_1491_; 
lean_dec_ref_known(v_e_1487_, 1);
v_val_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_val_1491_);
lean_dec_ref_known(v___x_1490_, 1);
switch(lean_obj_tag(v_val_1491_))
{
case 0:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_Compiler_LCNF_erasedExpr;
return v___x_1492_;
}
case 1:
{
if (v_translator_1486_ == 0)
{
lean_object* v_fvarId_1493_; lean_object* v___x_1494_; 
v_fvarId_1493_ = lean_ctor_get(v_val_1491_, 0);
lean_inc(v_fvarId_1493_);
lean_dec_ref_known(v_val_1491_, 1);
v___x_1494_ = l_Lean_Expr_fvar___override(v_fvarId_1493_);
v_e_1487_ = v___x_1494_;
goto _start;
}
else
{
lean_object* v_fvarId_1496_; lean_object* v___x_1497_; 
v_fvarId_1496_ = lean_ctor_get(v_val_1491_, 0);
lean_inc(v_fvarId_1496_);
lean_dec_ref_known(v_val_1491_, 1);
v___x_1497_ = l_Lean_Expr_fvar___override(v_fvarId_1496_);
return v___x_1497_;
}
}
default: 
{
if (v_translator_1486_ == 0)
{
lean_object* v_expr_1498_; 
v_expr_1498_ = lean_ctor_get(v_val_1491_, 0);
lean_inc_ref(v_expr_1498_);
lean_dec_ref_known(v_val_1491_, 1);
v_e_1487_ = v_expr_1498_;
goto _start;
}
else
{
lean_object* v_expr_1500_; 
v_expr_1500_ = lean_ctor_get(v_val_1491_, 0);
lean_inc_ref(v_expr_1500_);
lean_dec_ref_known(v_val_1491_, 1);
return v_expr_1500_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_1501_; lean_object* v_arg_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; size_t v___x_1505_; size_t v___x_1506_; uint8_t v___x_1507_; 
v_fn_1501_ = lean_ctor_get(v_e_1487_, 0);
v_arg_1502_ = lean_ctor_get(v_e_1487_, 1);
lean_inc_ref(v_fn_1501_);
v___x_1503_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1484_, v_s_1485_, v_translator_1486_, v_fn_1501_);
lean_inc_ref(v_arg_1502_);
v___x_1504_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1484_, v_s_1485_, v_translator_1486_, v_arg_1502_);
v___x_1505_ = lean_ptr_addr(v_fn_1501_);
v___x_1506_ = lean_ptr_addr(v___x_1503_);
v___x_1507_ = lean_usize_dec_eq(v___x_1505_, v___x_1506_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_dec_ref_known(v_e_1487_, 2);
v___x_1508_ = l_Lean_Expr_app___override(v___x_1503_, v___x_1504_);
v___x_1509_ = l_Lean_Expr_headBeta(v___x_1508_);
return v___x_1509_;
}
else
{
size_t v___x_1510_; size_t v___x_1511_; uint8_t v___x_1512_; 
v___x_1510_ = lean_ptr_addr(v_arg_1502_);
v___x_1511_ = lean_ptr_addr(v___x_1504_);
v___x_1512_ = lean_usize_dec_eq(v___x_1510_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec_ref_known(v_e_1487_, 2);
v___x_1513_ = l_Lean_Expr_app___override(v___x_1503_, v___x_1504_);
v___x_1514_ = l_Lean_Expr_headBeta(v___x_1513_);
return v___x_1514_;
}
else
{
lean_object* v___x_1515_; 
lean_dec_ref(v___x_1504_);
lean_dec_ref(v___x_1503_);
v___x_1515_ = l_Lean_Expr_headBeta(v_e_1487_);
return v___x_1515_;
}
}
}
case 6:
{
lean_object* v_binderName_1516_; lean_object* v_binderType_1517_; lean_object* v_body_1518_; uint8_t v_binderInfo_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; size_t v___x_1522_; size_t v___x_1523_; uint8_t v___x_1524_; 
v_binderName_1516_ = lean_ctor_get(v_e_1487_, 0);
v_binderType_1517_ = lean_ctor_get(v_e_1487_, 1);
v_body_1518_ = lean_ctor_get(v_e_1487_, 2);
v_binderInfo_1519_ = lean_ctor_get_uint8(v_e_1487_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1517_);
v___x_1520_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1484_, v_s_1485_, v_translator_1486_, v_binderType_1517_);
lean_inc_ref(v_body_1518_);
v___x_1521_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1484_, v_s_1485_, v_translator_1486_, v_body_1518_);
v___x_1522_ = lean_ptr_addr(v_binderType_1517_);
v___x_1523_ = lean_ptr_addr(v___x_1520_);
v___x_1524_ = lean_usize_dec_eq(v___x_1522_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; 
lean_inc(v_binderName_1516_);
lean_dec_ref_known(v_e_1487_, 3);
v___x_1525_ = l_Lean_Expr_lam___override(v_binderName_1516_, v___x_1520_, v___x_1521_, v_binderInfo_1519_);
return v___x_1525_;
}
else
{
size_t v___x_1526_; size_t v___x_1527_; uint8_t v___x_1528_; 
v___x_1526_ = lean_ptr_addr(v_body_1518_);
v___x_1527_ = lean_ptr_addr(v___x_1521_);
v___x_1528_ = lean_usize_dec_eq(v___x_1526_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
lean_inc(v_binderName_1516_);
lean_dec_ref_known(v_e_1487_, 3);
v___x_1529_ = l_Lean_Expr_lam___override(v_binderName_1516_, v___x_1520_, v___x_1521_, v_binderInfo_1519_);
return v___x_1529_;
}
else
{
uint8_t v___x_1530_; 
v___x_1530_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1519_, v_binderInfo_1519_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; 
lean_inc(v_binderName_1516_);
lean_dec_ref_known(v_e_1487_, 3);
v___x_1531_ = l_Lean_Expr_lam___override(v_binderName_1516_, v___x_1520_, v___x_1521_, v_binderInfo_1519_);
return v___x_1531_;
}
else
{
lean_dec_ref(v___x_1521_);
lean_dec_ref(v___x_1520_);
return v_e_1487_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1532_; lean_object* v_binderType_1533_; lean_object* v_body_1534_; uint8_t v_binderInfo_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; size_t v___x_1538_; size_t v___x_1539_; uint8_t v___x_1540_; 
v_binderName_1532_ = lean_ctor_get(v_e_1487_, 0);
v_binderType_1533_ = lean_ctor_get(v_e_1487_, 1);
v_body_1534_ = lean_ctor_get(v_e_1487_, 2);
v_binderInfo_1535_ = lean_ctor_get_uint8(v_e_1487_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1533_);
v___x_1536_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1484_, v_s_1485_, v_translator_1486_, v_binderType_1533_);
lean_inc_ref(v_body_1534_);
v___x_1537_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1484_, v_s_1485_, v_translator_1486_, v_body_1534_);
v___x_1538_ = lean_ptr_addr(v_binderType_1533_);
v___x_1539_ = lean_ptr_addr(v___x_1536_);
v___x_1540_ = lean_usize_dec_eq(v___x_1538_, v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; 
lean_inc(v_binderName_1532_);
lean_dec_ref_known(v_e_1487_, 3);
v___x_1541_ = l_Lean_Expr_forallE___override(v_binderName_1532_, v___x_1536_, v___x_1537_, v_binderInfo_1535_);
return v___x_1541_;
}
else
{
size_t v___x_1542_; size_t v___x_1543_; uint8_t v___x_1544_; 
v___x_1542_ = lean_ptr_addr(v_body_1534_);
v___x_1543_ = lean_ptr_addr(v___x_1537_);
v___x_1544_ = lean_usize_dec_eq(v___x_1542_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; 
lean_inc(v_binderName_1532_);
lean_dec_ref_known(v_e_1487_, 3);
v___x_1545_ = l_Lean_Expr_forallE___override(v_binderName_1532_, v___x_1536_, v___x_1537_, v_binderInfo_1535_);
return v___x_1545_;
}
else
{
uint8_t v___x_1546_; 
v___x_1546_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1535_, v_binderInfo_1535_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; 
lean_inc(v_binderName_1532_);
lean_dec_ref_known(v_e_1487_, 3);
v___x_1547_ = l_Lean_Expr_forallE___override(v_binderName_1532_, v___x_1536_, v___x_1537_, v_binderInfo_1535_);
return v___x_1547_;
}
else
{
lean_dec_ref(v___x_1537_);
lean_dec_ref(v___x_1536_);
return v_e_1487_;
}
}
}
}
case 8:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_dec_ref_known(v_e_1487_, 4);
v___x_1548_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3, &l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3);
v___x_1549_ = l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(v___x_1548_);
return v___x_1549_;
}
case 10:
{
lean_object* v_data_1550_; lean_object* v_expr_1551_; lean_object* v___x_1552_; size_t v___x_1553_; size_t v___x_1554_; uint8_t v___x_1555_; 
v_data_1550_ = lean_ctor_get(v_e_1487_, 0);
v_expr_1551_ = lean_ctor_get(v_e_1487_, 1);
lean_inc_ref(v_expr_1551_);
v___x_1552_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1484_, v_s_1485_, v_translator_1486_, v_expr_1551_);
v___x_1553_ = lean_ptr_addr(v_expr_1551_);
v___x_1554_ = lean_ptr_addr(v___x_1552_);
v___x_1555_ = lean_usize_dec_eq(v___x_1553_, v___x_1554_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; 
lean_inc(v_data_1550_);
lean_dec_ref_known(v_e_1487_, 2);
v___x_1556_ = l_Lean_Expr_mdata___override(v_data_1550_, v___x_1552_);
return v___x_1556_;
}
else
{
lean_dec_ref(v___x_1552_);
return v_e_1487_;
}
}
case 11:
{
lean_object* v_typeName_1557_; lean_object* v_idx_1558_; lean_object* v_struct_1559_; lean_object* v___x_1560_; size_t v___x_1561_; size_t v___x_1562_; uint8_t v___x_1563_; 
v_typeName_1557_ = lean_ctor_get(v_e_1487_, 0);
v_idx_1558_ = lean_ctor_get(v_e_1487_, 1);
v_struct_1559_ = lean_ctor_get(v_e_1487_, 2);
lean_inc_ref(v_struct_1559_);
v___x_1560_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1484_, v_s_1485_, v_translator_1486_, v_struct_1559_);
v___x_1561_ = lean_ptr_addr(v_struct_1559_);
v___x_1562_ = lean_ptr_addr(v___x_1560_);
v___x_1563_ = lean_usize_dec_eq(v___x_1561_, v___x_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; 
lean_inc(v_idx_1558_);
lean_inc(v_typeName_1557_);
lean_dec_ref_known(v_e_1487_, 3);
v___x_1564_ = l_Lean_Expr_proj___override(v_typeName_1557_, v_idx_1558_, v___x_1560_);
return v___x_1564_;
}
else
{
lean_dec_ref(v___x_1560_);
return v_e_1487_;
}
}
default: 
{
return v_e_1487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(uint8_t v_pu_1565_, lean_object* v_s_1566_, uint8_t v_translator_1567_, lean_object* v_e_1568_){
_start:
{
if (lean_obj_tag(v_e_1568_) == 5)
{
lean_object* v_fn_1569_; lean_object* v_arg_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; size_t v___x_1573_; size_t v___x_1574_; uint8_t v___x_1575_; 
v_fn_1569_ = lean_ctor_get(v_e_1568_, 0);
v_arg_1570_ = lean_ctor_get(v_e_1568_, 1);
lean_inc_ref(v_fn_1569_);
v___x_1571_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1565_, v_s_1566_, v_translator_1567_, v_fn_1569_);
lean_inc_ref(v_arg_1570_);
v___x_1572_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1565_, v_s_1566_, v_translator_1567_, v_arg_1570_);
v___x_1573_ = lean_ptr_addr(v_fn_1569_);
v___x_1574_ = lean_ptr_addr(v___x_1571_);
v___x_1575_ = lean_usize_dec_eq(v___x_1573_, v___x_1574_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; 
lean_dec_ref_known(v_e_1568_, 2);
v___x_1576_ = l_Lean_Expr_app___override(v___x_1571_, v___x_1572_);
return v___x_1576_;
}
else
{
size_t v___x_1577_; size_t v___x_1578_; uint8_t v___x_1579_; 
v___x_1577_ = lean_ptr_addr(v_arg_1570_);
v___x_1578_ = lean_ptr_addr(v___x_1572_);
v___x_1579_ = lean_usize_dec_eq(v___x_1577_, v___x_1578_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; 
lean_dec_ref_known(v_e_1568_, 2);
v___x_1580_ = l_Lean_Expr_app___override(v___x_1571_, v___x_1572_);
return v___x_1580_;
}
else
{
lean_dec_ref(v___x_1572_);
lean_dec_ref(v___x_1571_);
return v_e_1568_;
}
}
}
else
{
lean_object* v___x_1581_; 
v___x_1581_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1565_, v_s_1566_, v_translator_1567_, v_e_1568_);
return v___x_1581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(lean_object* v_pu_1582_, lean_object* v_s_1583_, lean_object* v_translator_1584_, lean_object* v_e_1585_){
_start:
{
uint8_t v_pu_boxed_1586_; uint8_t v_translator_boxed_1587_; lean_object* v_res_1588_; 
v_pu_boxed_1586_ = lean_unbox(v_pu_1582_);
v_translator_boxed_1587_ = lean_unbox(v_translator_1584_);
v_res_1588_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_boxed_1586_, v_s_1583_, v_translator_boxed_1587_, v_e_1585_);
lean_dec_ref(v_s_1583_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(lean_object* v_pu_1589_, lean_object* v_s_1590_, lean_object* v_translator_1591_, lean_object* v_e_1592_){
_start:
{
uint8_t v_pu_boxed_1593_; uint8_t v_translator_boxed_1594_; lean_object* v_res_1595_; 
v_pu_boxed_1593_ = lean_unbox(v_pu_1589_);
v_translator_boxed_1594_ = lean_unbox(v_translator_1591_);
v_res_1595_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_boxed_1593_, v_s_1590_, v_translator_boxed_1594_, v_e_1592_);
lean_dec_ref(v_s_1590_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(uint8_t v_pu_1596_, lean_object* v_s_1597_, lean_object* v_e_1598_, uint8_t v_translator_1599_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1596_, v_s_1597_, v_translator_1599_, v_e_1598_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(lean_object* v_pu_1601_, lean_object* v_s_1602_, lean_object* v_e_1603_, lean_object* v_translator_1604_){
_start:
{
uint8_t v_pu_boxed_1605_; uint8_t v_translator_boxed_1606_; lean_object* v_res_1607_; 
v_pu_boxed_1605_ = lean_unbox(v_pu_1601_);
v_translator_boxed_1606_ = lean_unbox(v_translator_1604_);
v_res_1607_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(v_pu_boxed_1605_, v_s_1602_, v_e_1603_, v_translator_boxed_1606_);
lean_dec_ref(v_s_1602_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(lean_object* v_x_1608_){
_start:
{
if (lean_obj_tag(v_x_1608_) == 0)
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_unsigned_to_nat(0u);
return v___x_1609_;
}
else
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_unsigned_to_nat(1u);
return v___x_1610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___boxed(lean_object* v_x_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(v_x_1611_);
lean_dec(v_x_1611_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(lean_object* v_t_1613_, lean_object* v_k_1614_){
_start:
{
if (lean_obj_tag(v_t_1613_) == 0)
{
lean_object* v_fvarId_1615_; lean_object* v___x_1616_; 
v_fvarId_1615_ = lean_ctor_get(v_t_1613_, 0);
lean_inc(v_fvarId_1615_);
lean_dec_ref_known(v_t_1613_, 1);
v___x_1616_ = lean_apply_1(v_k_1614_, v_fvarId_1615_);
return v___x_1616_;
}
else
{
return v_k_1614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(lean_object* v_motive_1617_, lean_object* v_ctorIdx_1618_, lean_object* v_t_1619_, lean_object* v_h_1620_, lean_object* v_k_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1619_, v_k_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___boxed(lean_object* v_motive_1623_, lean_object* v_ctorIdx_1624_, lean_object* v_t_1625_, lean_object* v_h_1626_, lean_object* v_k_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(v_motive_1623_, v_ctorIdx_1624_, v_t_1625_, v_h_1626_, v_k_1627_);
lean_dec(v_ctorIdx_1624_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim___redArg(lean_object* v_t_1629_, lean_object* v_fvar_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1629_, v_fvar_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim(lean_object* v_motive_1632_, lean_object* v_t_1633_, lean_object* v_h_1634_, lean_object* v_fvar_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1633_, v_fvar_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim___redArg(lean_object* v_t_1637_, lean_object* v_erased_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1637_, v_erased_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim(lean_object* v_motive_1640_, lean_object* v_t_1641_, lean_object* v_h_1642_, lean_object* v_erased_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1641_, v_erased_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object* v_s_1649_, lean_object* v_fvarId_1650_, uint8_t v_translator_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1649_, v_fvarId_1650_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v_fvarId_1650_);
return v___x_1653_;
}
else
{
lean_object* v_val_1654_; 
lean_dec(v_fvarId_1650_);
v_val_1654_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_val_1654_);
lean_dec_ref_known(v___x_1652_, 1);
if (lean_obj_tag(v_val_1654_) == 1)
{
if (v_translator_1651_ == 0)
{
lean_object* v_fvarId_1655_; 
v_fvarId_1655_ = lean_ctor_get(v_val_1654_, 0);
lean_inc(v_fvarId_1655_);
lean_dec_ref_known(v_val_1654_, 1);
v_fvarId_1650_ = v_fvarId_1655_;
goto _start;
}
else
{
lean_object* v_fvarId_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
v_fvarId_1657_ = lean_ctor_get(v_val_1654_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_val_1654_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v_val_1654_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_fvarId_1657_);
lean_dec(v_val_1654_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set_tag(v___x_1659_, 0);
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_fvarId_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_object* v___x_1665_; 
lean_dec(v_val_1654_);
v___x_1665_ = lean_box(1);
return v___x_1665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg___boxed(lean_object* v_s_1666_, lean_object* v_fvarId_1667_, lean_object* v_translator_1668_){
_start:
{
uint8_t v_translator_boxed_1669_; lean_object* v_res_1670_; 
v_translator_boxed_1669_ = lean_unbox(v_translator_1668_);
v_res_1670_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1666_, v_fvarId_1667_, v_translator_boxed_1669_);
lean_dec_ref(v_s_1666_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp(uint8_t v_pu_1671_, lean_object* v_s_1672_, lean_object* v_fvarId_1673_, uint8_t v_translator_1674_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1672_, v_fvarId_1673_, v_translator_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___boxed(lean_object* v_pu_1676_, lean_object* v_s_1677_, lean_object* v_fvarId_1678_, lean_object* v_translator_1679_){
_start:
{
uint8_t v_pu_boxed_1680_; uint8_t v_translator_boxed_1681_; lean_object* v_res_1682_; 
v_pu_boxed_1680_ = lean_unbox(v_pu_1676_);
v_translator_boxed_1681_ = lean_unbox(v_translator_1679_);
v_res_1682_ = l_Lean_Compiler_LCNF_normFVarImp(v_pu_boxed_1680_, v_s_1677_, v_fvarId_1678_, v_translator_boxed_1681_);
lean_dec_ref(v_s_1677_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t v_pu_1683_, lean_object* v_s_1684_, lean_object* v_arg_1685_, uint8_t v_translator_1686_){
_start:
{
switch(lean_obj_tag(v_arg_1685_))
{
case 0:
{
return v_arg_1685_;
}
case 1:
{
lean_object* v_fvarId_1687_; lean_object* v___x_1688_; 
v_fvarId_1687_ = lean_ctor_get(v_arg_1685_, 0);
v___x_1688_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1684_, v_fvarId_1687_);
if (lean_obj_tag(v___x_1688_) == 0)
{
return v_arg_1685_;
}
else
{
lean_object* v_val_1689_; 
lean_dec_ref_known(v_arg_1685_, 1);
v_val_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_val_1689_);
lean_dec_ref_known(v___x_1688_, 1);
switch(lean_obj_tag(v_val_1689_))
{
case 0:
{
lean_object* v___x_1690_; 
v___x_1690_ = lean_box(0);
return v___x_1690_;
}
case 1:
{
lean_object* v_fvarId_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1699_; 
v_fvarId_1691_ = lean_ctor_get(v_val_1689_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_val_1689_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1693_ = v_val_1689_;
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_fvarId_1691_);
lean_dec(v_val_1689_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_fvarId_1691_);
v___x_1696_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
if (v_translator_1686_ == 0)
{
v_arg_1685_ = v___x_1696_;
goto _start;
}
else
{
return v___x_1696_;
}
}
}
}
default: 
{
lean_object* v_expr_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
v_expr_1700_ = lean_ctor_get(v_val_1689_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_val_1689_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v_val_1689_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_expr_1700_);
lean_dec(v_val_1689_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_expr_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
}
default: 
{
lean_object* v_expr_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v_expr_1708_ = lean_ctor_get(v_arg_1685_, 0);
lean_inc_ref(v_expr_1708_);
v___x_1709_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1683_, v_s_1684_, v_translator_1686_, v_expr_1708_);
v___x_1710_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1683_, v_arg_1685_, v___x_1709_);
return v___x_1710_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp___boxed(lean_object* v_pu_1711_, lean_object* v_s_1712_, lean_object* v_arg_1713_, lean_object* v_translator_1714_){
_start:
{
uint8_t v_pu_boxed_1715_; uint8_t v_translator_boxed_1716_; lean_object* v_res_1717_; 
v_pu_boxed_1715_ = lean_unbox(v_pu_1711_);
v_translator_boxed_1716_ = lean_unbox(v_translator_1714_);
v_res_1717_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_boxed_1715_, v_s_1712_, v_arg_1713_, v_translator_boxed_1716_);
lean_dec_ref(v_s_1712_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(uint8_t v_pu_1718_, lean_object* v_s_1719_, uint8_t v_translator_1720_, lean_object* v_i_1721_, lean_object* v_as_1722_){
_start:
{
lean_object* v___x_1723_; uint8_t v___x_1724_; 
v___x_1723_ = lean_array_get_size(v_as_1722_);
v___x_1724_ = lean_nat_dec_lt(v_i_1721_, v___x_1723_);
if (v___x_1724_ == 0)
{
lean_dec(v_i_1721_);
return v_as_1722_;
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1726_; size_t v___x_1727_; size_t v___x_1728_; uint8_t v___x_1729_; 
v_a_1725_ = lean_array_fget_borrowed(v_as_1722_, v_i_1721_);
lean_inc(v_a_1725_);
v___x_1726_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1718_, v_s_1719_, v_a_1725_, v_translator_1720_);
v___x_1727_ = lean_ptr_addr(v_a_1725_);
v___x_1728_ = lean_ptr_addr(v___x_1726_);
v___x_1729_ = lean_usize_dec_eq(v___x_1727_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1730_ = lean_unsigned_to_nat(1u);
v___x_1731_ = lean_nat_add(v_i_1721_, v___x_1730_);
v___x_1732_ = lean_array_fset(v_as_1722_, v_i_1721_, v___x_1726_);
lean_dec(v_i_1721_);
v_i_1721_ = v___x_1731_;
v_as_1722_ = v___x_1732_;
goto _start;
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
lean_dec(v___x_1726_);
v___x_1734_ = lean_unsigned_to_nat(1u);
v___x_1735_ = lean_nat_add(v_i_1721_, v___x_1734_);
lean_dec(v_i_1721_);
v_i_1721_ = v___x_1735_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0___boxed(lean_object* v_pu_1737_, lean_object* v_s_1738_, lean_object* v_translator_1739_, lean_object* v_i_1740_, lean_object* v_as_1741_){
_start:
{
uint8_t v_pu_boxed_1742_; uint8_t v_translator_boxed_1743_; lean_object* v_res_1744_; 
v_pu_boxed_1742_ = lean_unbox(v_pu_1737_);
v_translator_boxed_1743_ = lean_unbox(v_translator_1739_);
v_res_1744_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_boxed_1742_, v_s_1738_, v_translator_boxed_1743_, v_i_1740_, v_as_1741_);
lean_dec_ref(v_s_1738_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t v_pu_1745_, lean_object* v_s_1746_, lean_object* v_args_1747_, uint8_t v_translator_1748_){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = lean_unsigned_to_nat(0u);
v___x_1750_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_1745_, v_s_1746_, v_translator_1748_, v___x_1749_, v_args_1747_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp___boxed(lean_object* v_pu_1751_, lean_object* v_s_1752_, lean_object* v_args_1753_, lean_object* v_translator_1754_){
_start:
{
uint8_t v_pu_boxed_1755_; uint8_t v_translator_boxed_1756_; lean_object* v_res_1757_; 
v_pu_boxed_1755_ = lean_unbox(v_pu_1751_);
v_translator_boxed_1756_ = lean_unbox(v_translator_1754_);
v_res_1757_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_boxed_1755_, v_s_1752_, v_args_1753_, v_translator_boxed_1756_);
lean_dec_ref(v_s_1752_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t v_pu_1758_, lean_object* v_s_1759_, lean_object* v_e_1760_, uint8_t v_translator_1761_){
_start:
{
lean_object* v_fvarId_1763_; lean_object* v_args_1769_; 
switch(lean_obj_tag(v_e_1760_))
{
case 2:
{
lean_object* v_struct_1772_; lean_object* v___x_1773_; 
v_struct_1772_ = lean_ctor_get(v_e_1760_, 2);
lean_inc(v_struct_1772_);
v___x_1773_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1759_, v_struct_1772_, v_translator_1761_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_fvarId_1774_; lean_object* v___x_1775_; 
v_fvarId_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_fvarId_1774_);
lean_dec_ref_known(v___x_1773_, 1);
v___x_1775_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1758_, v_e_1760_, v_fvarId_1774_);
return v___x_1775_;
}
else
{
lean_object* v___x_1776_; 
lean_dec_ref_known(v_e_1760_, 3);
v___x_1776_ = lean_box(1);
return v___x_1776_;
}
}
case 3:
{
lean_object* v_args_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v_args_1777_ = lean_ctor_get(v_e_1760_, 2);
lean_inc_ref(v_args_1777_);
v___x_1778_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1758_, v_s_1759_, v_args_1777_, v_translator_1761_);
v___x_1779_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1758_, v_e_1760_, v___x_1778_);
return v___x_1779_;
}
case 4:
{
lean_object* v_fvarId_1780_; lean_object* v_args_1781_; lean_object* v___x_1782_; 
v_fvarId_1780_ = lean_ctor_get(v_e_1760_, 0);
v_args_1781_ = lean_ctor_get(v_e_1760_, 1);
lean_inc(v_fvarId_1780_);
v___x_1782_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1759_, v_fvarId_1780_, v_translator_1761_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_fvarId_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v_fvarId_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_fvarId_1783_);
lean_dec_ref_known(v___x_1782_, 1);
lean_inc_ref(v_args_1781_);
v___x_1784_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1758_, v_s_1759_, v_args_1781_, v_translator_1761_);
v___x_1785_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_1758_, v_e_1760_, v_fvarId_1783_, v___x_1784_);
lean_dec_ref_known(v_e_1760_, 2);
return v___x_1785_;
}
else
{
lean_object* v___x_1786_; 
lean_dec_ref_known(v_e_1760_, 2);
v___x_1786_ = lean_box(1);
return v___x_1786_;
}
}
case 5:
{
lean_object* v_args_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v_args_1787_ = lean_ctor_get(v_e_1760_, 1);
lean_inc_ref(v_args_1787_);
v___x_1788_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1758_, v_s_1759_, v_args_1787_, v_translator_1761_);
v___x_1789_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1758_, v_e_1760_, v___x_1788_);
return v___x_1789_;
}
case 6:
{
lean_object* v_var_1790_; 
v_var_1790_ = lean_ctor_get(v_e_1760_, 1);
lean_inc(v_var_1790_);
v_fvarId_1763_ = v_var_1790_;
goto v___jp_1762_;
}
case 7:
{
lean_object* v_var_1791_; 
v_var_1791_ = lean_ctor_get(v_e_1760_, 1);
lean_inc(v_var_1791_);
v_fvarId_1763_ = v_var_1791_;
goto v___jp_1762_;
}
case 8:
{
lean_object* v_var_1792_; lean_object* v___x_1793_; 
v_var_1792_ = lean_ctor_get(v_e_1760_, 2);
lean_inc(v_var_1792_);
v___x_1793_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1759_, v_var_1792_, v_translator_1761_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_fvarId_1794_; lean_object* v___x_1795_; 
v_fvarId_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_fvarId_1794_);
lean_dec_ref_known(v___x_1793_, 1);
v___x_1795_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1758_, v_e_1760_, v_fvarId_1794_);
return v___x_1795_;
}
else
{
lean_object* v___x_1796_; 
lean_dec_ref_known(v_e_1760_, 3);
v___x_1796_ = lean_box(1);
return v___x_1796_;
}
}
case 9:
{
lean_object* v_args_1797_; 
v_args_1797_ = lean_ctor_get(v_e_1760_, 1);
lean_inc_ref(v_args_1797_);
v_args_1769_ = v_args_1797_;
goto v___jp_1768_;
}
case 10:
{
lean_object* v_args_1798_; 
v_args_1798_ = lean_ctor_get(v_e_1760_, 1);
lean_inc_ref(v_args_1798_);
v_args_1769_ = v_args_1798_;
goto v___jp_1768_;
}
case 11:
{
lean_object* v_n_1799_; lean_object* v_var_1800_; lean_object* v___x_1801_; 
v_n_1799_ = lean_ctor_get(v_e_1760_, 0);
lean_inc(v_n_1799_);
v_var_1800_ = lean_ctor_get(v_e_1760_, 1);
lean_inc(v_var_1800_);
v___x_1801_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1759_, v_var_1800_, v_translator_1761_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_fvarId_1802_; lean_object* v___x_1803_; 
v_fvarId_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_fvarId_1802_);
lean_dec_ref_known(v___x_1801_, 1);
v___x_1803_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_1758_, v_e_1760_, v_n_1799_, v_fvarId_1802_);
return v___x_1803_;
}
else
{
lean_object* v___x_1804_; 
lean_dec(v_n_1799_);
lean_dec_ref_known(v_e_1760_, 2);
v___x_1804_ = lean_box(1);
return v___x_1804_;
}
}
case 12:
{
lean_object* v_var_1805_; lean_object* v_i_1806_; uint8_t v_updateHeader_1807_; lean_object* v_args_1808_; lean_object* v___x_1809_; 
v_var_1805_ = lean_ctor_get(v_e_1760_, 0);
v_i_1806_ = lean_ctor_get(v_e_1760_, 1);
lean_inc_ref(v_i_1806_);
v_updateHeader_1807_ = lean_ctor_get_uint8(v_e_1760_, sizeof(void*)*3);
v_args_1808_ = lean_ctor_get(v_e_1760_, 2);
lean_inc(v_var_1805_);
v___x_1809_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1759_, v_var_1805_, v_translator_1761_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_fvarId_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v_fvarId_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_fvarId_1810_);
lean_dec_ref_known(v___x_1809_, 1);
lean_inc_ref(v_args_1808_);
v___x_1811_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1758_, v_s_1759_, v_args_1808_, v_translator_1761_);
v___x_1812_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_1758_, v_e_1760_, v_fvarId_1810_, v_i_1806_, v_updateHeader_1807_, v___x_1811_);
return v___x_1812_;
}
else
{
lean_object* v___x_1813_; 
lean_dec_ref(v_i_1806_);
lean_dec_ref_known(v_e_1760_, 3);
v___x_1813_ = lean_box(1);
return v___x_1813_;
}
}
case 13:
{
lean_object* v_ty_1814_; lean_object* v_fvarId_1815_; lean_object* v___x_1816_; 
v_ty_1814_ = lean_ctor_get(v_e_1760_, 0);
lean_inc_ref(v_ty_1814_);
v_fvarId_1815_ = lean_ctor_get(v_e_1760_, 1);
lean_inc(v_fvarId_1815_);
v___x_1816_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1759_, v_fvarId_1815_, v_translator_1761_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_fvarId_1817_; lean_object* v___x_1818_; 
v_fvarId_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_fvarId_1817_);
lean_dec_ref_known(v___x_1816_, 1);
v___x_1818_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_1758_, v_e_1760_, v_ty_1814_, v_fvarId_1817_);
return v___x_1818_;
}
else
{
lean_object* v___x_1819_; 
lean_dec_ref(v_ty_1814_);
lean_dec_ref_known(v_e_1760_, 2);
v___x_1819_ = lean_box(1);
return v___x_1819_;
}
}
case 14:
{
lean_object* v_fvarId_1820_; lean_object* v___x_1821_; 
v_fvarId_1820_ = lean_ctor_get(v_e_1760_, 0);
lean_inc(v_fvarId_1820_);
v___x_1821_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1759_, v_fvarId_1820_, v_translator_1761_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_fvarId_1822_; lean_object* v___x_1823_; 
v_fvarId_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_fvarId_1822_);
lean_dec_ref_known(v___x_1821_, 1);
v___x_1823_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_1758_, v_e_1760_, v_fvarId_1822_);
return v___x_1823_;
}
else
{
lean_object* v___x_1824_; 
lean_dec_ref_known(v_e_1760_, 1);
v___x_1824_ = lean_box(1);
return v___x_1824_;
}
}
case 15:
{
lean_object* v_fvarId_1825_; lean_object* v___x_1826_; 
v_fvarId_1825_ = lean_ctor_get(v_e_1760_, 0);
lean_inc(v_fvarId_1825_);
v___x_1826_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1759_, v_fvarId_1825_, v_translator_1761_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_fvarId_1827_; lean_object* v___x_1828_; 
v_fvarId_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_fvarId_1827_);
lean_dec_ref_known(v___x_1826_, 1);
v___x_1828_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_1758_, v_e_1760_, v_fvarId_1827_);
return v___x_1828_;
}
else
{
lean_object* v___x_1829_; 
lean_dec_ref_known(v_e_1760_, 1);
v___x_1829_ = lean_box(1);
return v___x_1829_;
}
}
default: 
{
return v_e_1760_;
}
}
v___jp_1762_:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1759_, v_fvarId_1763_, v_translator_1761_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_fvarId_1765_; lean_object* v___x_1766_; 
v_fvarId_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_fvarId_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v___x_1766_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1758_, v_e_1760_, v_fvarId_1765_);
return v___x_1766_;
}
else
{
lean_object* v___x_1767_; 
lean_dec(v_e_1760_);
v___x_1767_ = lean_box(1);
return v___x_1767_;
}
}
v___jp_1768_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1758_, v_s_1759_, v_args_1769_, v_translator_1761_);
v___x_1771_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1758_, v_e_1760_, v___x_1770_);
return v___x_1771_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp___boxed(lean_object* v_pu_1830_, lean_object* v_s_1831_, lean_object* v_e_1832_, lean_object* v_translator_1833_){
_start:
{
uint8_t v_pu_boxed_1834_; uint8_t v_translator_boxed_1835_; lean_object* v_res_1836_; 
v_pu_boxed_1834_ = lean_unbox(v_pu_1830_);
v_translator_boxed_1835_ = lean_unbox(v_translator_1833_);
v_res_1836_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_boxed_1834_, v_s_1831_, v_e_1832_, v_translator_boxed_1835_);
lean_dec_ref(v_s_1831_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___redArg(lean_object* v_inst_1837_, lean_object* v_inst_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = lean_apply_2(v_inst_1837_, lean_box(0), v_inst_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(uint8_t v_pu_1840_, uint8_t v_t_1841_, lean_object* v_m_1842_, lean_object* v_n_1843_, lean_object* v_inst_1844_, lean_object* v_inst_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = lean_apply_2(v_inst_1844_, lean_box(0), v_inst_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___boxed(lean_object* v_pu_1847_, lean_object* v_t_1848_, lean_object* v_m_1849_, lean_object* v_n_1850_, lean_object* v_inst_1851_, lean_object* v_inst_1852_){
_start:
{
uint8_t v_pu_boxed_1853_; uint8_t v_t_boxed_1854_; lean_object* v_res_1855_; 
v_pu_boxed_1853_ = lean_unbox(v_pu_1847_);
v_t_boxed_1854_ = lean_unbox(v_t_1848_);
v_res_1855_ = l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(v_pu_boxed_1853_, v_t_boxed_1854_, v_m_1849_, v_n_1850_, v_inst_1851_, v_inst_1852_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0(lean_object* v_inst_1856_, lean_object* v_inst_1857_, lean_object* v_f_1858_){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = lean_apply_1(v_inst_1856_, v_f_1858_);
v___x_1860_ = lean_apply_2(v_inst_1857_, lean_box(0), v___x_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg(lean_object* v_inst_1861_, lean_object* v_inst_1862_){
_start:
{
lean_object* v___f_1863_; 
v___f_1863_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1863_, 0, v_inst_1862_);
lean_closure_set(v___f_1863_, 1, v_inst_1861_);
return v___f_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(uint8_t v_pu_1864_, lean_object* v_m_1865_, lean_object* v_n_1866_, lean_object* v_inst_1867_, lean_object* v_inst_1868_){
_start:
{
lean_object* v___f_1869_; 
v___f_1869_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1869_, 0, v_inst_1868_);
lean_closure_set(v___f_1869_, 1, v_inst_1867_);
return v___f_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___boxed(lean_object* v_pu_1870_, lean_object* v_m_1871_, lean_object* v_n_1872_, lean_object* v_inst_1873_, lean_object* v_inst_1874_){
_start:
{
uint8_t v_pu_boxed_1875_; lean_object* v_res_1876_; 
v_pu_boxed_1875_ = lean_unbox(v_pu_1870_);
v_res_1876_ = l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(v_pu_boxed_1875_, v_m_1871_, v_n_1872_, v_inst_1873_, v_inst_1874_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___lam__0(lean_object* v___x_1877_, lean_object* v___x_1878_, lean_object* v_fvarId_1879_, lean_object* v_arg_1880_, lean_object* v_s_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1877_, v___x_1878_, v_s_1881_, v_fvarId_1879_, v_arg_1880_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg(lean_object* v_inst_1885_, lean_object* v_fvarId_1886_, lean_object* v_arg_1887_){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___f_1890_; lean_object* v___x_1891_; 
v___x_1888_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1889_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1890_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1890_, 0, v___x_1888_);
lean_closure_set(v___f_1890_, 1, v___x_1889_);
lean_closure_set(v___f_1890_, 2, v_fvarId_1886_);
lean_closure_set(v___f_1890_, 3, v_arg_1887_);
v___x_1891_ = lean_apply_1(v_inst_1885_, v___f_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst(lean_object* v_m_1892_, uint8_t v_pu_1893_, lean_object* v_inst_1894_, lean_object* v_fvarId_1895_, lean_object* v_arg_1896_){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___f_1899_; lean_object* v___x_1900_; 
v___x_1897_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1898_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1899_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1899_, 0, v___x_1897_);
lean_closure_set(v___f_1899_, 1, v___x_1898_);
lean_closure_set(v___f_1899_, 2, v_fvarId_1895_);
lean_closure_set(v___f_1899_, 3, v_arg_1896_);
v___x_1900_ = lean_apply_1(v_inst_1894_, v___f_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___boxed(lean_object* v_m_1901_, lean_object* v_pu_1902_, lean_object* v_inst_1903_, lean_object* v_fvarId_1904_, lean_object* v_arg_1905_){
_start:
{
uint8_t v_pu_boxed_1906_; lean_object* v_res_1907_; 
v_pu_boxed_1906_ = lean_unbox(v_pu_1902_);
v_res_1907_ = l_Lean_Compiler_LCNF_addSubst(v_m_1901_, v_pu_boxed_1906_, v_inst_1903_, v_fvarId_1904_, v_arg_1905_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0(lean_object* v_fvarId_x27_1908_, lean_object* v___x_1909_, lean_object* v___x_1910_, lean_object* v_fvarId_1911_, lean_object* v_s_1912_){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1913_, 0, v_fvarId_x27_1908_);
v___x_1914_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1909_, v___x_1910_, v_s_1912_, v_fvarId_1911_, v___x_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg(lean_object* v_inst_1915_, lean_object* v_fvarId_1916_, lean_object* v_fvarId_x27_1917_){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___f_1920_; lean_object* v___x_1921_; 
v___x_1918_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1919_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1920_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1920_, 0, v_fvarId_x27_1917_);
lean_closure_set(v___f_1920_, 1, v___x_1918_);
lean_closure_set(v___f_1920_, 2, v___x_1919_);
lean_closure_set(v___f_1920_, 3, v_fvarId_1916_);
v___x_1921_ = lean_apply_1(v_inst_1915_, v___f_1920_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst(lean_object* v_m_1922_, uint8_t v_ph_1923_, lean_object* v_inst_1924_, lean_object* v_fvarId_1925_, lean_object* v_fvarId_x27_1926_){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___f_1929_; lean_object* v___x_1930_; 
v___x_1927_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1928_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1929_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1929_, 0, v_fvarId_x27_1926_);
lean_closure_set(v___f_1929_, 1, v___x_1927_);
lean_closure_set(v___f_1929_, 2, v___x_1928_);
lean_closure_set(v___f_1929_, 3, v_fvarId_1925_);
v___x_1930_ = lean_apply_1(v_inst_1924_, v___f_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___boxed(lean_object* v_m_1931_, lean_object* v_ph_1932_, lean_object* v_inst_1933_, lean_object* v_fvarId_1934_, lean_object* v_fvarId_x27_1935_){
_start:
{
uint8_t v_ph_boxed_1936_; lean_object* v_res_1937_; 
v_ph_boxed_1936_ = lean_unbox(v_ph_1932_);
v_res_1937_ = l_Lean_Compiler_LCNF_addFVarSubst(v_m_1931_, v_ph_boxed_1936_, v_inst_1933_, v_fvarId_1934_, v_fvarId_x27_1935_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(lean_object* v_fvarId_1938_, uint8_t v_t_1939_, lean_object* v_toPure_1940_, lean_object* v_____do__lift_1941_){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_____do__lift_1941_, v_fvarId_1938_, v_t_1939_);
v___x_1943_ = lean_apply_2(v_toPure_1940_, lean_box(0), v___x_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed(lean_object* v_fvarId_1944_, lean_object* v_t_1945_, lean_object* v_toPure_1946_, lean_object* v_____do__lift_1947_){
_start:
{
uint8_t v_t_boxed_1948_; lean_object* v_res_1949_; 
v_t_boxed_1948_ = lean_unbox(v_t_1945_);
v_res_1949_ = l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(v_fvarId_1944_, v_t_boxed_1948_, v_toPure_1946_, v_____do__lift_1947_);
lean_dec_ref(v_____do__lift_1947_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg(uint8_t v_t_1950_, lean_object* v_inst_1951_, lean_object* v_inst_1952_, lean_object* v_fvarId_1953_){
_start:
{
lean_object* v_toApplicative_1954_; lean_object* v_toBind_1955_; lean_object* v_toPure_1956_; lean_object* v___x_1957_; lean_object* v___f_1958_; lean_object* v___x_1959_; 
v_toApplicative_1954_ = lean_ctor_get(v_inst_1952_, 0);
lean_inc_ref(v_toApplicative_1954_);
v_toBind_1955_ = lean_ctor_get(v_inst_1952_, 1);
lean_inc(v_toBind_1955_);
lean_dec_ref(v_inst_1952_);
v_toPure_1956_ = lean_ctor_get(v_toApplicative_1954_, 1);
lean_inc(v_toPure_1956_);
lean_dec_ref(v_toApplicative_1954_);
v___x_1957_ = lean_box(v_t_1950_);
v___f_1958_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1958_, 0, v_fvarId_1953_);
lean_closure_set(v___f_1958_, 1, v___x_1957_);
lean_closure_set(v___f_1958_, 2, v_toPure_1956_);
v___x_1959_ = lean_apply_4(v_toBind_1955_, lean_box(0), lean_box(0), v_inst_1951_, v___f_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___boxed(lean_object* v_t_1960_, lean_object* v_inst_1961_, lean_object* v_inst_1962_, lean_object* v_fvarId_1963_){
_start:
{
uint8_t v_t_boxed_1964_; lean_object* v_res_1965_; 
v_t_boxed_1964_ = lean_unbox(v_t_1960_);
v_res_1965_ = l_Lean_Compiler_LCNF_normFVar___redArg(v_t_boxed_1964_, v_inst_1961_, v_inst_1962_, v_fvarId_1963_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar(lean_object* v_m_1966_, uint8_t v_pu_1967_, uint8_t v_t_1968_, lean_object* v_inst_1969_, lean_object* v_inst_1970_, lean_object* v_fvarId_1971_){
_start:
{
lean_object* v_toApplicative_1972_; lean_object* v_toBind_1973_; lean_object* v_toPure_1974_; lean_object* v___x_1975_; lean_object* v___f_1976_; lean_object* v___x_1977_; 
v_toApplicative_1972_ = lean_ctor_get(v_inst_1970_, 0);
lean_inc_ref(v_toApplicative_1972_);
v_toBind_1973_ = lean_ctor_get(v_inst_1970_, 1);
lean_inc(v_toBind_1973_);
lean_dec_ref(v_inst_1970_);
v_toPure_1974_ = lean_ctor_get(v_toApplicative_1972_, 1);
lean_inc(v_toPure_1974_);
lean_dec_ref(v_toApplicative_1972_);
v___x_1975_ = lean_box(v_t_1968_);
v___f_1976_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1976_, 0, v_fvarId_1971_);
lean_closure_set(v___f_1976_, 1, v___x_1975_);
lean_closure_set(v___f_1976_, 2, v_toPure_1974_);
v___x_1977_ = lean_apply_4(v_toBind_1973_, lean_box(0), lean_box(0), v_inst_1969_, v___f_1976_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___boxed(lean_object* v_m_1978_, lean_object* v_pu_1979_, lean_object* v_t_1980_, lean_object* v_inst_1981_, lean_object* v_inst_1982_, lean_object* v_fvarId_1983_){
_start:
{
uint8_t v_pu_boxed_1984_; uint8_t v_t_boxed_1985_; lean_object* v_res_1986_; 
v_pu_boxed_1984_ = lean_unbox(v_pu_1979_);
v_t_boxed_1985_ = lean_unbox(v_t_1980_);
v_res_1986_ = l_Lean_Compiler_LCNF_normFVar(v_m_1978_, v_pu_boxed_1984_, v_t_boxed_1985_, v_inst_1981_, v_inst_1982_, v_fvarId_1983_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(uint8_t v_pu_1987_, uint8_t v_t_1988_, lean_object* v_e_1989_, lean_object* v_toPure_1990_, lean_object* v_____do__lift_1991_){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1987_, v_____do__lift_1991_, v_t_1988_, v_e_1989_);
v___x_1993_ = lean_apply_2(v_toPure_1990_, lean_box(0), v___x_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed(lean_object* v_pu_1994_, lean_object* v_t_1995_, lean_object* v_e_1996_, lean_object* v_toPure_1997_, lean_object* v_____do__lift_1998_){
_start:
{
uint8_t v_pu_boxed_1999_; uint8_t v_t_boxed_2000_; lean_object* v_res_2001_; 
v_pu_boxed_1999_ = lean_unbox(v_pu_1994_);
v_t_boxed_2000_ = lean_unbox(v_t_1995_);
v_res_2001_ = l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(v_pu_boxed_1999_, v_t_boxed_2000_, v_e_1996_, v_toPure_1997_, v_____do__lift_1998_);
lean_dec_ref(v_____do__lift_1998_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg(uint8_t v_pu_2002_, uint8_t v_t_2003_, lean_object* v_inst_2004_, lean_object* v_inst_2005_, lean_object* v_e_2006_){
_start:
{
lean_object* v_toApplicative_2007_; lean_object* v_toBind_2008_; lean_object* v_toPure_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___f_2012_; lean_object* v___x_2013_; 
v_toApplicative_2007_ = lean_ctor_get(v_inst_2005_, 0);
lean_inc_ref(v_toApplicative_2007_);
v_toBind_2008_ = lean_ctor_get(v_inst_2005_, 1);
lean_inc(v_toBind_2008_);
lean_dec_ref(v_inst_2005_);
v_toPure_2009_ = lean_ctor_get(v_toApplicative_2007_, 1);
lean_inc(v_toPure_2009_);
lean_dec_ref(v_toApplicative_2007_);
v___x_2010_ = lean_box(v_pu_2002_);
v___x_2011_ = lean_box(v_t_2003_);
v___f_2012_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2012_, 0, v___x_2010_);
lean_closure_set(v___f_2012_, 1, v___x_2011_);
lean_closure_set(v___f_2012_, 2, v_e_2006_);
lean_closure_set(v___f_2012_, 3, v_toPure_2009_);
v___x_2013_ = lean_apply_4(v_toBind_2008_, lean_box(0), lean_box(0), v_inst_2004_, v___f_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___boxed(lean_object* v_pu_2014_, lean_object* v_t_2015_, lean_object* v_inst_2016_, lean_object* v_inst_2017_, lean_object* v_e_2018_){
_start:
{
uint8_t v_pu_boxed_2019_; uint8_t v_t_boxed_2020_; lean_object* v_res_2021_; 
v_pu_boxed_2019_ = lean_unbox(v_pu_2014_);
v_t_boxed_2020_ = lean_unbox(v_t_2015_);
v_res_2021_ = l_Lean_Compiler_LCNF_normExpr___redArg(v_pu_boxed_2019_, v_t_boxed_2020_, v_inst_2016_, v_inst_2017_, v_e_2018_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr(lean_object* v_m_2022_, uint8_t v_pu_2023_, uint8_t v_t_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_e_2027_){
_start:
{
lean_object* v_toApplicative_2028_; lean_object* v_toBind_2029_; lean_object* v_toPure_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___f_2033_; lean_object* v___x_2034_; 
v_toApplicative_2028_ = lean_ctor_get(v_inst_2026_, 0);
lean_inc_ref(v_toApplicative_2028_);
v_toBind_2029_ = lean_ctor_get(v_inst_2026_, 1);
lean_inc(v_toBind_2029_);
lean_dec_ref(v_inst_2026_);
v_toPure_2030_ = lean_ctor_get(v_toApplicative_2028_, 1);
lean_inc(v_toPure_2030_);
lean_dec_ref(v_toApplicative_2028_);
v___x_2031_ = lean_box(v_pu_2023_);
v___x_2032_ = lean_box(v_t_2024_);
v___f_2033_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2033_, 0, v___x_2031_);
lean_closure_set(v___f_2033_, 1, v___x_2032_);
lean_closure_set(v___f_2033_, 2, v_e_2027_);
lean_closure_set(v___f_2033_, 3, v_toPure_2030_);
v___x_2034_ = lean_apply_4(v_toBind_2029_, lean_box(0), lean_box(0), v_inst_2025_, v___f_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___boxed(lean_object* v_m_2035_, lean_object* v_pu_2036_, lean_object* v_t_2037_, lean_object* v_inst_2038_, lean_object* v_inst_2039_, lean_object* v_e_2040_){
_start:
{
uint8_t v_pu_boxed_2041_; uint8_t v_t_boxed_2042_; lean_object* v_res_2043_; 
v_pu_boxed_2041_ = lean_unbox(v_pu_2036_);
v_t_boxed_2042_ = lean_unbox(v_t_2037_);
v_res_2043_ = l_Lean_Compiler_LCNF_normExpr(v_m_2035_, v_pu_boxed_2041_, v_t_boxed_2042_, v_inst_2038_, v_inst_2039_, v_e_2040_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0(uint8_t v_pu_2044_, lean_object* v_arg_2045_, uint8_t v_t_2046_, lean_object* v_toPure_2047_, lean_object* v_____do__lift_2048_){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2044_, v_____do__lift_2048_, v_arg_2045_, v_t_2046_);
v___x_2050_ = lean_apply_2(v_toPure_2047_, lean_box(0), v___x_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed(lean_object* v_pu_2051_, lean_object* v_arg_2052_, lean_object* v_t_2053_, lean_object* v_toPure_2054_, lean_object* v_____do__lift_2055_){
_start:
{
uint8_t v_pu_boxed_2056_; uint8_t v_t_boxed_2057_; lean_object* v_res_2058_; 
v_pu_boxed_2056_ = lean_unbox(v_pu_2051_);
v_t_boxed_2057_ = lean_unbox(v_t_2053_);
v_res_2058_ = l_Lean_Compiler_LCNF_normArg___redArg___lam__0(v_pu_boxed_2056_, v_arg_2052_, v_t_boxed_2057_, v_toPure_2054_, v_____do__lift_2055_);
lean_dec_ref(v_____do__lift_2055_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg(uint8_t v_pu_2059_, uint8_t v_t_2060_, lean_object* v_inst_2061_, lean_object* v_inst_2062_, lean_object* v_arg_2063_){
_start:
{
lean_object* v_toApplicative_2064_; lean_object* v_toBind_2065_; lean_object* v_toPure_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___f_2069_; lean_object* v___x_2070_; 
v_toApplicative_2064_ = lean_ctor_get(v_inst_2062_, 0);
lean_inc_ref(v_toApplicative_2064_);
v_toBind_2065_ = lean_ctor_get(v_inst_2062_, 1);
lean_inc(v_toBind_2065_);
lean_dec_ref(v_inst_2062_);
v_toPure_2066_ = lean_ctor_get(v_toApplicative_2064_, 1);
lean_inc(v_toPure_2066_);
lean_dec_ref(v_toApplicative_2064_);
v___x_2067_ = lean_box(v_pu_2059_);
v___x_2068_ = lean_box(v_t_2060_);
v___f_2069_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2069_, 0, v___x_2067_);
lean_closure_set(v___f_2069_, 1, v_arg_2063_);
lean_closure_set(v___f_2069_, 2, v___x_2068_);
lean_closure_set(v___f_2069_, 3, v_toPure_2066_);
v___x_2070_ = lean_apply_4(v_toBind_2065_, lean_box(0), lean_box(0), v_inst_2061_, v___f_2069_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___boxed(lean_object* v_pu_2071_, lean_object* v_t_2072_, lean_object* v_inst_2073_, lean_object* v_inst_2074_, lean_object* v_arg_2075_){
_start:
{
uint8_t v_pu_boxed_2076_; uint8_t v_t_boxed_2077_; lean_object* v_res_2078_; 
v_pu_boxed_2076_ = lean_unbox(v_pu_2071_);
v_t_boxed_2077_ = lean_unbox(v_t_2072_);
v_res_2078_ = l_Lean_Compiler_LCNF_normArg___redArg(v_pu_boxed_2076_, v_t_boxed_2077_, v_inst_2073_, v_inst_2074_, v_arg_2075_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg(lean_object* v_m_2079_, uint8_t v_pu_2080_, uint8_t v_t_2081_, lean_object* v_inst_2082_, lean_object* v_inst_2083_, lean_object* v_arg_2084_){
_start:
{
lean_object* v_toApplicative_2085_; lean_object* v_toBind_2086_; lean_object* v_toPure_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___f_2090_; lean_object* v___x_2091_; 
v_toApplicative_2085_ = lean_ctor_get(v_inst_2083_, 0);
lean_inc_ref(v_toApplicative_2085_);
v_toBind_2086_ = lean_ctor_get(v_inst_2083_, 1);
lean_inc(v_toBind_2086_);
lean_dec_ref(v_inst_2083_);
v_toPure_2087_ = lean_ctor_get(v_toApplicative_2085_, 1);
lean_inc(v_toPure_2087_);
lean_dec_ref(v_toApplicative_2085_);
v___x_2088_ = lean_box(v_pu_2080_);
v___x_2089_ = lean_box(v_t_2081_);
v___f_2090_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2090_, 0, v___x_2088_);
lean_closure_set(v___f_2090_, 1, v_arg_2084_);
lean_closure_set(v___f_2090_, 2, v___x_2089_);
lean_closure_set(v___f_2090_, 3, v_toPure_2087_);
v___x_2091_ = lean_apply_4(v_toBind_2086_, lean_box(0), lean_box(0), v_inst_2082_, v___f_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___boxed(lean_object* v_m_2092_, lean_object* v_pu_2093_, lean_object* v_t_2094_, lean_object* v_inst_2095_, lean_object* v_inst_2096_, lean_object* v_arg_2097_){
_start:
{
uint8_t v_pu_boxed_2098_; uint8_t v_t_boxed_2099_; lean_object* v_res_2100_; 
v_pu_boxed_2098_ = lean_unbox(v_pu_2093_);
v_t_boxed_2099_ = lean_unbox(v_t_2094_);
v_res_2100_ = l_Lean_Compiler_LCNF_normArg(v_m_2092_, v_pu_boxed_2098_, v_t_boxed_2099_, v_inst_2095_, v_inst_2096_, v_arg_2097_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(uint8_t v_pu_2101_, lean_object* v_e_2102_, uint8_t v_t_2103_, lean_object* v_toPure_2104_, lean_object* v_____do__lift_2105_){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_2101_, v_____do__lift_2105_, v_e_2102_, v_t_2103_);
v___x_2107_ = lean_apply_2(v_toPure_2104_, lean_box(0), v___x_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed(lean_object* v_pu_2108_, lean_object* v_e_2109_, lean_object* v_t_2110_, lean_object* v_toPure_2111_, lean_object* v_____do__lift_2112_){
_start:
{
uint8_t v_pu_boxed_2113_; uint8_t v_t_boxed_2114_; lean_object* v_res_2115_; 
v_pu_boxed_2113_ = lean_unbox(v_pu_2108_);
v_t_boxed_2114_ = lean_unbox(v_t_2110_);
v_res_2115_ = l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(v_pu_boxed_2113_, v_e_2109_, v_t_boxed_2114_, v_toPure_2111_, v_____do__lift_2112_);
lean_dec_ref(v_____do__lift_2112_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg(uint8_t v_pu_2116_, uint8_t v_t_2117_, lean_object* v_inst_2118_, lean_object* v_inst_2119_, lean_object* v_e_2120_){
_start:
{
lean_object* v_toApplicative_2121_; lean_object* v_toBind_2122_; lean_object* v_toPure_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___f_2126_; lean_object* v___x_2127_; 
v_toApplicative_2121_ = lean_ctor_get(v_inst_2119_, 0);
lean_inc_ref(v_toApplicative_2121_);
v_toBind_2122_ = lean_ctor_get(v_inst_2119_, 1);
lean_inc(v_toBind_2122_);
lean_dec_ref(v_inst_2119_);
v_toPure_2123_ = lean_ctor_get(v_toApplicative_2121_, 1);
lean_inc(v_toPure_2123_);
lean_dec_ref(v_toApplicative_2121_);
v___x_2124_ = lean_box(v_pu_2116_);
v___x_2125_ = lean_box(v_t_2117_);
v___f_2126_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2126_, 0, v___x_2124_);
lean_closure_set(v___f_2126_, 1, v_e_2120_);
lean_closure_set(v___f_2126_, 2, v___x_2125_);
lean_closure_set(v___f_2126_, 3, v_toPure_2123_);
v___x_2127_ = lean_apply_4(v_toBind_2122_, lean_box(0), lean_box(0), v_inst_2118_, v___f_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___boxed(lean_object* v_pu_2128_, lean_object* v_t_2129_, lean_object* v_inst_2130_, lean_object* v_inst_2131_, lean_object* v_e_2132_){
_start:
{
uint8_t v_pu_boxed_2133_; uint8_t v_t_boxed_2134_; lean_object* v_res_2135_; 
v_pu_boxed_2133_ = lean_unbox(v_pu_2128_);
v_t_boxed_2134_ = lean_unbox(v_t_2129_);
v_res_2135_ = l_Lean_Compiler_LCNF_normLetValue___redArg(v_pu_boxed_2133_, v_t_boxed_2134_, v_inst_2130_, v_inst_2131_, v_e_2132_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue(lean_object* v_m_2136_, uint8_t v_pu_2137_, uint8_t v_t_2138_, lean_object* v_inst_2139_, lean_object* v_inst_2140_, lean_object* v_e_2141_){
_start:
{
lean_object* v_toApplicative_2142_; lean_object* v_toBind_2143_; lean_object* v_toPure_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___f_2147_; lean_object* v___x_2148_; 
v_toApplicative_2142_ = lean_ctor_get(v_inst_2140_, 0);
lean_inc_ref(v_toApplicative_2142_);
v_toBind_2143_ = lean_ctor_get(v_inst_2140_, 1);
lean_inc(v_toBind_2143_);
lean_dec_ref(v_inst_2140_);
v_toPure_2144_ = lean_ctor_get(v_toApplicative_2142_, 1);
lean_inc(v_toPure_2144_);
lean_dec_ref(v_toApplicative_2142_);
v___x_2145_ = lean_box(v_pu_2137_);
v___x_2146_ = lean_box(v_t_2138_);
v___f_2147_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2147_, 0, v___x_2145_);
lean_closure_set(v___f_2147_, 1, v_e_2141_);
lean_closure_set(v___f_2147_, 2, v___x_2146_);
lean_closure_set(v___f_2147_, 3, v_toPure_2144_);
v___x_2148_ = lean_apply_4(v_toBind_2143_, lean_box(0), lean_box(0), v_inst_2139_, v___f_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___boxed(lean_object* v_m_2149_, lean_object* v_pu_2150_, lean_object* v_t_2151_, lean_object* v_inst_2152_, lean_object* v_inst_2153_, lean_object* v_e_2154_){
_start:
{
uint8_t v_pu_boxed_2155_; uint8_t v_t_boxed_2156_; lean_object* v_res_2157_; 
v_pu_boxed_2155_ = lean_unbox(v_pu_2150_);
v_t_boxed_2156_ = lean_unbox(v_t_2151_);
v_res_2157_ = l_Lean_Compiler_LCNF_normLetValue(v_m_2149_, v_pu_boxed_2155_, v_t_boxed_2156_, v_inst_2152_, v_inst_2153_, v_e_2154_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore(uint8_t v_pu_2158_, lean_object* v_s_2159_, lean_object* v_e_2160_, uint8_t v_translator_2161_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2158_, v_s_2159_, v_translator_2161_, v_e_2160_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore___boxed(lean_object* v_pu_2163_, lean_object* v_s_2164_, lean_object* v_e_2165_, lean_object* v_translator_2166_){
_start:
{
uint8_t v_pu_boxed_2167_; uint8_t v_translator_boxed_2168_; lean_object* v_res_2169_; 
v_pu_boxed_2167_ = lean_unbox(v_pu_2163_);
v_translator_boxed_2168_ = lean_unbox(v_translator_2166_);
v_res_2169_ = l_Lean_Compiler_LCNF_normExprCore(v_pu_boxed_2167_, v_s_2164_, v_e_2165_, v_translator_boxed_2168_);
lean_dec_ref(v_s_2164_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(uint8_t v_pu_2170_, lean_object* v_args_2171_, uint8_t v_t_2172_, lean_object* v_toPure_2173_, lean_object* v_____do__lift_2174_){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_2170_, v_____do__lift_2174_, v_args_2171_, v_t_2172_);
v___x_2176_ = lean_apply_2(v_toPure_2173_, lean_box(0), v___x_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed(lean_object* v_pu_2177_, lean_object* v_args_2178_, lean_object* v_t_2179_, lean_object* v_toPure_2180_, lean_object* v_____do__lift_2181_){
_start:
{
uint8_t v_pu_boxed_2182_; uint8_t v_t_boxed_2183_; lean_object* v_res_2184_; 
v_pu_boxed_2182_ = lean_unbox(v_pu_2177_);
v_t_boxed_2183_ = lean_unbox(v_t_2179_);
v_res_2184_ = l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(v_pu_boxed_2182_, v_args_2178_, v_t_boxed_2183_, v_toPure_2180_, v_____do__lift_2181_);
lean_dec_ref(v_____do__lift_2181_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg(uint8_t v_pu_2185_, uint8_t v_t_2186_, lean_object* v_inst_2187_, lean_object* v_inst_2188_, lean_object* v_args_2189_){
_start:
{
lean_object* v_toApplicative_2190_; lean_object* v_toBind_2191_; lean_object* v_toPure_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___f_2195_; lean_object* v___x_2196_; 
v_toApplicative_2190_ = lean_ctor_get(v_inst_2188_, 0);
lean_inc_ref(v_toApplicative_2190_);
v_toBind_2191_ = lean_ctor_get(v_inst_2188_, 1);
lean_inc(v_toBind_2191_);
lean_dec_ref(v_inst_2188_);
v_toPure_2192_ = lean_ctor_get(v_toApplicative_2190_, 1);
lean_inc(v_toPure_2192_);
lean_dec_ref(v_toApplicative_2190_);
v___x_2193_ = lean_box(v_pu_2185_);
v___x_2194_ = lean_box(v_t_2186_);
v___f_2195_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2195_, 0, v___x_2193_);
lean_closure_set(v___f_2195_, 1, v_args_2189_);
lean_closure_set(v___f_2195_, 2, v___x_2194_);
lean_closure_set(v___f_2195_, 3, v_toPure_2192_);
v___x_2196_ = lean_apply_4(v_toBind_2191_, lean_box(0), lean_box(0), v_inst_2187_, v___f_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___boxed(lean_object* v_pu_2197_, lean_object* v_t_2198_, lean_object* v_inst_2199_, lean_object* v_inst_2200_, lean_object* v_args_2201_){
_start:
{
uint8_t v_pu_boxed_2202_; uint8_t v_t_boxed_2203_; lean_object* v_res_2204_; 
v_pu_boxed_2202_ = lean_unbox(v_pu_2197_);
v_t_boxed_2203_ = lean_unbox(v_t_2198_);
v_res_2204_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_boxed_2202_, v_t_boxed_2203_, v_inst_2199_, v_inst_2200_, v_args_2201_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs(lean_object* v_m_2205_, uint8_t v_pu_2206_, uint8_t v_t_2207_, lean_object* v_inst_2208_, lean_object* v_inst_2209_, lean_object* v_args_2210_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_2206_, v_t_2207_, v_inst_2208_, v_inst_2209_, v_args_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___boxed(lean_object* v_m_2212_, lean_object* v_pu_2213_, lean_object* v_t_2214_, lean_object* v_inst_2215_, lean_object* v_inst_2216_, lean_object* v_args_2217_){
_start:
{
uint8_t v_pu_boxed_2218_; uint8_t v_t_boxed_2219_; lean_object* v_res_2220_; 
v_pu_boxed_2218_ = lean_unbox(v_pu_2213_);
v_t_boxed_2219_ = lean_unbox(v_t_2214_);
v_res_2220_ = l_Lean_Compiler_LCNF_normArgs(v_m_2212_, v_pu_boxed_2218_, v_t_boxed_2219_, v_inst_2215_, v_inst_2216_, v_args_2217_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object* v_binderName_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v_lctx_2226_; lean_object* v_nextIdx_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2240_; 
v___x_2224_ = lean_st_ref_get(v_a_2222_);
v___x_2225_ = lean_st_ref_take(v_a_2222_);
v_lctx_2226_ = lean_ctor_get(v___x_2225_, 0);
v_nextIdx_2227_ = lean_ctor_get(v___x_2225_, 1);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2229_ = v___x_2225_;
v_isShared_2230_ = v_isSharedCheck_2240_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_nextIdx_2227_);
lean_inc(v_lctx_2226_);
lean_dec(v___x_2225_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2240_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2231_ = lean_unsigned_to_nat(1u);
v___x_2232_ = lean_nat_add(v_nextIdx_2227_, v___x_2231_);
lean_dec(v_nextIdx_2227_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 1, v___x_2232_);
v___x_2234_ = v___x_2229_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_lctx_2226_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
lean_object* v___x_2235_; lean_object* v_nextIdx_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2235_ = lean_st_ref_put(v_a_2222_, v___x_2234_);
v_nextIdx_2236_ = lean_ctor_get(v___x_2224_, 1);
lean_inc(v_nextIdx_2236_);
lean_dec(v___x_2224_);
v___x_2237_ = l_Lean_Name_num___override(v_binderName_2221_, v_nextIdx_2236_);
v___x_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
return v___x_2238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg___boxed(lean_object* v_binderName_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2241_, v_a_2242_);
lean_dec(v_a_2242_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object* v_binderName_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2245_, v_a_2247_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___boxed(lean_object* v_binderName_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_Compiler_LCNF_mkFreshBinderName(v_binderName_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
lean_dec(v_a_2256_);
lean_dec_ref(v_a_2255_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(lean_object* v_binderName_2259_, lean_object* v_baseName_2260_, lean_object* v_a_2261_){
_start:
{
uint8_t v___x_2263_; 
v___x_2263_ = l_Lean_Name_isAnonymous(v_binderName_2259_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; 
lean_dec(v_baseName_2260_);
v___x_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2264_, 0, v_binderName_2259_);
return v___x_2264_;
}
else
{
lean_object* v___x_2265_; 
lean_dec(v_binderName_2259_);
v___x_2265_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_baseName_2260_, v_a_2261_);
return v___x_2265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg___boxed(lean_object* v_binderName_2266_, lean_object* v_baseName_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2266_, v_baseName_2267_, v_a_2268_);
lean_dec(v_a_2268_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous(lean_object* v_binderName_2271_, lean_object* v_baseName_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2271_, v_baseName_2272_, v_a_2274_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___boxed(lean_object* v_binderName_2279_, lean_object* v_baseName_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_Compiler_LCNF_ensureNotAnonymous(v_binderName_2279_, v_baseName_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
lean_dec(v_a_2282_);
lean_dec_ref(v_a_2281_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(lean_object* v___y_2287_){
_start:
{
lean_object* v___x_2289_; lean_object* v_ngen_2290_; lean_object* v_namePrefix_2291_; lean_object* v_idx_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2321_; 
v___x_2289_ = lean_st_ref_get(v___y_2287_);
v_ngen_2290_ = lean_ctor_get(v___x_2289_, 2);
lean_inc_ref(v_ngen_2290_);
lean_dec(v___x_2289_);
v_namePrefix_2291_ = lean_ctor_get(v_ngen_2290_, 0);
v_idx_2292_ = lean_ctor_get(v_ngen_2290_, 1);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_ngen_2290_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2294_ = v_ngen_2290_;
v_isShared_2295_ = v_isSharedCheck_2321_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_idx_2292_);
lean_inc(v_namePrefix_2291_);
lean_dec(v_ngen_2290_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2321_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2296_; lean_object* v_env_2297_; lean_object* v_nextMacroScope_2298_; lean_object* v_auxDeclNGen_2299_; lean_object* v_traceState_2300_; lean_object* v_cache_2301_; lean_object* v_messages_2302_; lean_object* v_infoState_2303_; lean_object* v_snapshotTasks_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2319_; 
v___x_2296_ = lean_st_ref_take(v___y_2287_);
v_env_2297_ = lean_ctor_get(v___x_2296_, 0);
v_nextMacroScope_2298_ = lean_ctor_get(v___x_2296_, 1);
v_auxDeclNGen_2299_ = lean_ctor_get(v___x_2296_, 3);
v_traceState_2300_ = lean_ctor_get(v___x_2296_, 4);
v_cache_2301_ = lean_ctor_get(v___x_2296_, 5);
v_messages_2302_ = lean_ctor_get(v___x_2296_, 6);
v_infoState_2303_ = lean_ctor_get(v___x_2296_, 7);
v_snapshotTasks_2304_ = lean_ctor_get(v___x_2296_, 8);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; 
v_unused_2320_ = lean_ctor_get(v___x_2296_, 2);
lean_dec(v_unused_2320_);
v___x_2306_ = v___x_2296_;
v_isShared_2307_ = v_isSharedCheck_2319_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_snapshotTasks_2304_);
lean_inc(v_infoState_2303_);
lean_inc(v_messages_2302_);
lean_inc(v_cache_2301_);
lean_inc(v_traceState_2300_);
lean_inc(v_auxDeclNGen_2299_);
lean_inc(v_nextMacroScope_2298_);
lean_inc(v_env_2297_);
lean_dec(v___x_2296_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2319_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v_r_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
lean_inc(v_idx_2292_);
lean_inc(v_namePrefix_2291_);
v_r_2308_ = l_Lean_Name_num___override(v_namePrefix_2291_, v_idx_2292_);
v___x_2309_ = lean_unsigned_to_nat(1u);
v___x_2310_ = lean_nat_add(v_idx_2292_, v___x_2309_);
lean_dec(v_idx_2292_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 1, v___x_2310_);
v___x_2312_ = v___x_2294_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_namePrefix_2291_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2314_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 2, v___x_2312_);
v___x_2314_ = v___x_2306_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_env_2297_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v_nextMacroScope_2298_);
lean_ctor_set(v_reuseFailAlloc_2317_, 2, v___x_2312_);
lean_ctor_set(v_reuseFailAlloc_2317_, 3, v_auxDeclNGen_2299_);
lean_ctor_set(v_reuseFailAlloc_2317_, 4, v_traceState_2300_);
lean_ctor_set(v_reuseFailAlloc_2317_, 5, v_cache_2301_);
lean_ctor_set(v_reuseFailAlloc_2317_, 6, v_messages_2302_);
lean_ctor_set(v_reuseFailAlloc_2317_, 7, v_infoState_2303_);
lean_ctor_set(v_reuseFailAlloc_2317_, 8, v_snapshotTasks_2304_);
v___x_2314_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = lean_st_ref_put(v___y_2287_, v___x_2314_);
v___x_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2316_, 0, v_r_2308_);
return v___x_2316_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg___boxed(lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2322_);
lean_dec(v___y_2322_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v___x_2330_; lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
v___x_2330_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2328_);
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2330_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2330_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0___boxed(lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t v_pu_2348_, lean_object* v_binderName_2349_, lean_object* v_type_2350_, uint8_t v_borrow_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
lean_object* v___x_2357_; 
v___x_2357_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2381_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref_known(v___x_2357_, 1);
v___x_2359_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_2360_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2349_, v___x_2359_, v_a_2353_);
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2363_ = v___x_2360_;
v_isShared_2364_ = v_isSharedCheck_2381_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2381_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2365_; lean_object* v_lctx_2366_; lean_object* v_nextIdx_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2380_; 
v___x_2365_ = lean_st_ref_take(v_a_2353_);
v_lctx_2366_ = lean_ctor_get(v___x_2365_, 0);
v_nextIdx_2367_ = lean_ctor_get(v___x_2365_, 1);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2369_ = v___x_2365_;
v_isShared_2370_ = v_isSharedCheck_2380_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_nextIdx_2367_);
lean_inc(v_lctx_2366_);
lean_dec(v___x_2365_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2380_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2374_; 
v___x_2371_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2371_, 0, v_a_2358_);
lean_ctor_set(v___x_2371_, 1, v_a_2361_);
lean_ctor_set(v___x_2371_, 2, v_type_2350_);
lean_ctor_set_uint8(v___x_2371_, sizeof(void*)*3, v_borrow_2351_);
lean_inc_ref(v___x_2371_);
v___x_2372_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2348_, v_lctx_2366_, v___x_2371_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v___x_2372_);
v___x_2374_ = v___x_2369_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2372_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_nextIdx_2367_);
v___x_2374_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2375_; lean_object* v___x_2377_; 
v___x_2375_ = lean_st_ref_put(v_a_2353_, v___x_2374_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2371_);
v___x_2377_ = v___x_2363_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2371_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec_ref(v_type_2350_);
lean_dec(v_binderName_2349_);
v_a_2382_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2357_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2357_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam___boxed(lean_object* v_pu_2390_, lean_object* v_binderName_2391_, lean_object* v_type_2392_, lean_object* v_borrow_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
uint8_t v_pu_boxed_2399_; uint8_t v_borrow_boxed_2400_; lean_object* v_res_2401_; 
v_pu_boxed_2399_ = lean_unbox(v_pu_2390_);
v_borrow_boxed_2400_ = lean_unbox(v_borrow_2393_);
v_res_2401_ = l_Lean_Compiler_LCNF_mkParam(v_pu_boxed_2399_, v_binderName_2391_, v_type_2392_, v_borrow_boxed_2400_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_);
lean_dec(v_a_2397_);
lean_dec_ref(v_a_2396_);
lean_dec(v_a_2395_);
lean_dec_ref(v_a_2394_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2405_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___boxed(lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t v_pu_2417_, lean_object* v_binderName_2418_, lean_object* v_type_2419_, lean_object* v_value_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2450_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_a_2427_);
lean_dec_ref_known(v___x_2426_, 1);
v___x_2428_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2429_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2418_, v___x_2428_, v_a_2422_);
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2450_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2450_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; lean_object* v_lctx_2435_; lean_object* v_nextIdx_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2449_; 
v___x_2434_ = lean_st_ref_take(v_a_2422_);
v_lctx_2435_ = lean_ctor_get(v___x_2434_, 0);
v_nextIdx_2436_ = lean_ctor_get(v___x_2434_, 1);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2438_ = v___x_2434_;
v_isShared_2439_ = v_isSharedCheck_2449_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_nextIdx_2436_);
lean_inc(v_lctx_2435_);
lean_dec(v___x_2434_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2449_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2443_; 
v___x_2440_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2440_, 0, v_a_2427_);
lean_ctor_set(v___x_2440_, 1, v_a_2430_);
lean_ctor_set(v___x_2440_, 2, v_type_2419_);
lean_ctor_set(v___x_2440_, 3, v_value_2420_);
lean_inc_ref(v___x_2440_);
v___x_2441_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2417_, v_lctx_2435_, v___x_2440_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 0, v___x_2441_);
v___x_2443_ = v___x_2438_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2441_);
lean_ctor_set(v_reuseFailAlloc_2448_, 1, v_nextIdx_2436_);
v___x_2443_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
lean_object* v___x_2444_; lean_object* v___x_2446_; 
v___x_2444_ = lean_st_ref_put(v_a_2422_, v___x_2443_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v___x_2440_);
v___x_2446_ = v___x_2432_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2440_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec(v_value_2420_);
lean_dec_ref(v_type_2419_);
lean_dec(v_binderName_2418_);
v_a_2451_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2426_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2426_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl___boxed(lean_object* v_pu_2459_, lean_object* v_binderName_2460_, lean_object* v_type_2461_, lean_object* v_value_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_){
_start:
{
uint8_t v_pu_boxed_2468_; lean_object* v_res_2469_; 
v_pu_boxed_2468_ = lean_unbox(v_pu_2459_);
v_res_2469_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_boxed_2468_, v_binderName_2460_, v_type_2461_, v_value_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_);
lean_dec(v_a_2466_);
lean_dec_ref(v_a_2465_);
lean_dec(v_a_2464_);
lean_dec_ref(v_a_2463_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t v_pu_2473_, lean_object* v_binderName_2474_, lean_object* v_type_2475_, lean_object* v_params_2476_, lean_object* v_value_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2507_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref_known(v___x_2483_, 1);
v___x_2485_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFunDecl___closed__1));
v___x_2486_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2474_, v___x_2485_, v_a_2479_);
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2489_ = v___x_2486_;
v_isShared_2490_ = v_isSharedCheck_2507_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2486_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2507_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2491_; lean_object* v_lctx_2492_; lean_object* v_nextIdx_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2506_; 
v___x_2491_ = lean_st_ref_take(v_a_2479_);
v_lctx_2492_ = lean_ctor_get(v___x_2491_, 0);
v_nextIdx_2493_ = lean_ctor_get(v___x_2491_, 1);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2495_ = v___x_2491_;
v_isShared_2496_ = v_isSharedCheck_2506_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_nextIdx_2493_);
lean_inc(v_lctx_2492_);
lean_dec(v___x_2491_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2506_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2500_; 
v___x_2497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2497_, 0, v_a_2484_);
lean_ctor_set(v___x_2497_, 1, v_a_2487_);
lean_ctor_set(v___x_2497_, 2, v_params_2476_);
lean_ctor_set(v___x_2497_, 3, v_type_2475_);
lean_ctor_set(v___x_2497_, 4, v_value_2477_);
lean_inc_ref(v___x_2497_);
v___x_2498_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2473_, v_lctx_2492_, v___x_2497_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v___x_2498_);
v___x_2500_ = v___x_2495_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2498_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_nextIdx_2493_);
v___x_2500_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
lean_object* v___x_2501_; lean_object* v___x_2503_; 
v___x_2501_ = lean_st_ref_put(v_a_2479_, v___x_2500_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 0, v___x_2497_);
v___x_2503_ = v___x_2489_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2497_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec_ref(v_value_2477_);
lean_dec_ref(v_params_2476_);
lean_dec_ref(v_type_2475_);
lean_dec(v_binderName_2474_);
v_a_2508_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2483_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2483_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl___boxed(lean_object* v_pu_2516_, lean_object* v_binderName_2517_, lean_object* v_type_2518_, lean_object* v_params_2519_, lean_object* v_value_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_){
_start:
{
uint8_t v_pu_boxed_2526_; lean_object* v_res_2527_; 
v_pu_boxed_2526_ = lean_unbox(v_pu_2516_);
v_res_2527_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_boxed_2526_, v_binderName_2517_, v_type_2518_, v_params_2519_, v_value_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2523_);
lean_dec(v_a_2522_);
lean_dec_ref(v_a_2521_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(uint8_t v_pu_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v_a_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2534_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2535_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2534_, v_a_2530_);
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2536_);
lean_dec_ref(v___x_2535_);
v___x_2537_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2538_ = lean_box(1);
v___x_2539_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2528_, v_a_2536_, v___x_2537_, v___x_2538_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased___boxed(lean_object* v_pu_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_){
_start:
{
uint8_t v_pu_boxed_2546_; lean_object* v_res_2547_; 
v_pu_boxed_2546_ = lean_unbox(v_pu_2540_);
v_res_2547_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_boxed_2546_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t v_pu_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2565_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2565_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2565_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v_fvarId_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2563_; 
v_fvarId_2559_ = lean_ctor_get(v_a_2555_, 0);
lean_inc(v_fvarId_2559_);
v___x_2560_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2560_, 0, v_fvarId_2559_);
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v_a_2555_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v___x_2561_);
v___x_2563_ = v___x_2557_;
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
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
v_a_2566_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2554_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2554_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased___boxed(lean_object* v_pu_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_){
_start:
{
uint8_t v_pu_boxed_2580_; lean_object* v_res_2581_; 
v_pu_boxed_2580_ = lean_unbox(v_pu_2574_);
v_res_2581_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_boxed_2580_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
lean_dec(v_a_2576_);
lean_dec_ref(v_a_2575_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t v_pu_2582_, lean_object* v_p_2583_, lean_object* v_type_2584_, lean_object* v_a_2585_){
_start:
{
lean_object* v_fvarId_2587_; lean_object* v_binderName_2588_; lean_object* v_type_2589_; uint8_t v_borrow_2590_; size_t v___x_2591_; size_t v___x_2592_; uint8_t v___x_2593_; 
v_fvarId_2587_ = lean_ctor_get(v_p_2583_, 0);
v_binderName_2588_ = lean_ctor_get(v_p_2583_, 1);
v_type_2589_ = lean_ctor_get(v_p_2583_, 2);
v_borrow_2590_ = lean_ctor_get_uint8(v_p_2583_, sizeof(void*)*3);
v___x_2591_ = lean_ptr_addr(v_type_2584_);
v___x_2592_ = lean_ptr_addr(v_type_2589_);
v___x_2593_ = lean_usize_dec_eq(v___x_2591_, v___x_2592_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2613_; 
lean_inc(v_binderName_2588_);
lean_inc(v_fvarId_2587_);
v_isSharedCheck_2613_ = !lean_is_exclusive(v_p_2583_);
if (v_isSharedCheck_2613_ == 0)
{
lean_object* v_unused_2614_; lean_object* v_unused_2615_; lean_object* v_unused_2616_; 
v_unused_2614_ = lean_ctor_get(v_p_2583_, 2);
lean_dec(v_unused_2614_);
v_unused_2615_ = lean_ctor_get(v_p_2583_, 1);
lean_dec(v_unused_2615_);
v_unused_2616_ = lean_ctor_get(v_p_2583_, 0);
lean_dec(v_unused_2616_);
v___x_2595_ = v_p_2583_;
v_isShared_2596_ = v_isSharedCheck_2613_;
goto v_resetjp_2594_;
}
else
{
lean_dec(v_p_2583_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2613_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v_lctx_2598_; lean_object* v_nextIdx_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2612_; 
v___x_2597_ = lean_st_ref_take(v_a_2585_);
v_lctx_2598_ = lean_ctor_get(v___x_2597_, 0);
v_nextIdx_2599_ = lean_ctor_get(v___x_2597_, 1);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2601_ = v___x_2597_;
v_isShared_2602_ = v_isSharedCheck_2612_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_nextIdx_2599_);
lean_inc(v_lctx_2598_);
lean_dec(v___x_2597_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2612_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v_p_2604_; 
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 2, v_type_2584_);
v_p_2604_ = v___x_2595_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_fvarId_2587_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_binderName_2588_);
lean_ctor_set(v_reuseFailAlloc_2611_, 2, v_type_2584_);
lean_ctor_set_uint8(v_reuseFailAlloc_2611_, sizeof(void*)*3, v_borrow_2590_);
v_p_2604_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
lean_object* v___x_2605_; lean_object* v___x_2607_; 
lean_inc_ref(v_p_2604_);
v___x_2605_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2582_, v_lctx_2598_, v_p_2604_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 0, v___x_2605_);
v___x_2607_ = v___x_2601_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2605_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_nextIdx_2599_);
v___x_2607_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = lean_st_ref_put(v_a_2585_, v___x_2607_);
v___x_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2609_, 0, v_p_2604_);
return v___x_2609_;
}
}
}
}
}
else
{
lean_object* v___x_2617_; 
lean_dec_ref(v_type_2584_);
v___x_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2617_, 0, v_p_2583_);
return v___x_2617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg___boxed(lean_object* v_pu_2618_, lean_object* v_p_2619_, lean_object* v_type_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_){
_start:
{
uint8_t v_pu_boxed_2623_; lean_object* v_res_2624_; 
v_pu_boxed_2623_ = lean_unbox(v_pu_2618_);
v_res_2624_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_boxed_2623_, v_p_2619_, v_type_2620_, v_a_2621_);
lean_dec(v_a_2621_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(uint8_t v_pu_2625_, lean_object* v_p_2626_, lean_object* v_type_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_2625_, v_p_2626_, v_type_2627_, v_a_2629_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(lean_object* v_pu_2634_, lean_object* v_p_2635_, lean_object* v_type_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_){
_start:
{
uint8_t v_pu_boxed_2642_; lean_object* v_res_2643_; 
v_pu_boxed_2642_ = lean_unbox(v_pu_2634_);
v_res_2643_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(v_pu_boxed_2642_, v_p_2635_, v_type_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
lean_dec(v_a_2640_);
lean_dec_ref(v_a_2639_);
lean_dec(v_a_2638_);
lean_dec_ref(v_a_2637_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t v_pu_2644_, lean_object* v_p_2645_, uint8_t v_borrow_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v_fvarId_2649_; lean_object* v_binderName_2650_; lean_object* v_type_2651_; uint8_t v_borrow_2652_; 
v_fvarId_2649_ = lean_ctor_get(v_p_2645_, 0);
v_binderName_2650_ = lean_ctor_get(v_p_2645_, 1);
v_type_2651_ = lean_ctor_get(v_p_2645_, 2);
v_borrow_2652_ = lean_ctor_get_uint8(v_p_2645_, sizeof(void*)*3);
if (v_borrow_2652_ == 0)
{
if (v_borrow_2646_ == 0)
{
lean_object* v___x_2668_; 
v___x_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2668_, 0, v_p_2645_);
return v___x_2668_;
}
else
{
lean_inc_ref(v_type_2651_);
lean_inc(v_binderName_2650_);
lean_inc(v_fvarId_2649_);
lean_dec_ref(v_p_2645_);
goto v___jp_2653_;
}
}
else
{
if (v_borrow_2646_ == 0)
{
lean_inc_ref(v_type_2651_);
lean_inc(v_binderName_2650_);
lean_inc(v_fvarId_2649_);
lean_dec_ref(v_p_2645_);
goto v___jp_2653_;
}
else
{
lean_object* v___x_2669_; 
v___x_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2669_, 0, v_p_2645_);
return v___x_2669_;
}
}
v___jp_2653_:
{
lean_object* v___x_2654_; lean_object* v_lctx_2655_; lean_object* v_nextIdx_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2667_; 
v___x_2654_ = lean_st_ref_take(v_a_2647_);
v_lctx_2655_ = lean_ctor_get(v___x_2654_, 0);
v_nextIdx_2656_ = lean_ctor_get(v___x_2654_, 1);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2658_ = v___x_2654_;
v_isShared_2659_ = v_isSharedCheck_2667_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_nextIdx_2656_);
lean_inc(v_lctx_2655_);
lean_dec(v___x_2654_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2667_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v_p_2660_; lean_object* v___x_2661_; lean_object* v___x_2663_; 
v_p_2660_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_p_2660_, 0, v_fvarId_2649_);
lean_ctor_set(v_p_2660_, 1, v_binderName_2650_);
lean_ctor_set(v_p_2660_, 2, v_type_2651_);
lean_ctor_set_uint8(v_p_2660_, sizeof(void*)*3, v_borrow_2646_);
lean_inc_ref(v_p_2660_);
v___x_2661_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2644_, v_lctx_2655_, v_p_2660_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v___x_2661_);
v___x_2663_ = v___x_2658_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v_nextIdx_2656_);
v___x_2663_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = lean_st_ref_put(v_a_2647_, v___x_2663_);
v___x_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2665_, 0, v_p_2660_);
return v___x_2665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg___boxed(lean_object* v_pu_2670_, lean_object* v_p_2671_, lean_object* v_borrow_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_){
_start:
{
uint8_t v_pu_boxed_2675_; uint8_t v_borrow_boxed_2676_; lean_object* v_res_2677_; 
v_pu_boxed_2675_ = lean_unbox(v_pu_2670_);
v_borrow_boxed_2676_ = lean_unbox(v_borrow_2672_);
v_res_2677_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_boxed_2675_, v_p_2671_, v_borrow_boxed_2676_, v_a_2673_);
lean_dec(v_a_2673_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(uint8_t v_pu_2678_, lean_object* v_p_2679_, uint8_t v_borrow_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_2678_, v_p_2679_, v_borrow_2680_, v_a_2682_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___boxed(lean_object* v_pu_2687_, lean_object* v_p_2688_, lean_object* v_borrow_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_){
_start:
{
uint8_t v_pu_boxed_2695_; uint8_t v_borrow_boxed_2696_; lean_object* v_res_2697_; 
v_pu_boxed_2695_ = lean_unbox(v_pu_2687_);
v_borrow_boxed_2696_ = lean_unbox(v_borrow_2689_);
v_res_2697_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(v_pu_boxed_2695_, v_p_2688_, v_borrow_boxed_2696_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t v_pu_2698_, lean_object* v_decl_2699_, lean_object* v_type_2700_, lean_object* v_value_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v_fvarId_2704_; lean_object* v_binderName_2705_; lean_object* v_type_2706_; lean_object* v_value_2707_; size_t v___x_2723_; size_t v___x_2724_; uint8_t v___x_2725_; 
v_fvarId_2704_ = lean_ctor_get(v_decl_2699_, 0);
v_binderName_2705_ = lean_ctor_get(v_decl_2699_, 1);
v_type_2706_ = lean_ctor_get(v_decl_2699_, 2);
v_value_2707_ = lean_ctor_get(v_decl_2699_, 3);
v___x_2723_ = lean_ptr_addr(v_type_2700_);
v___x_2724_ = lean_ptr_addr(v_type_2706_);
v___x_2725_ = lean_usize_dec_eq(v___x_2723_, v___x_2724_);
if (v___x_2725_ == 0)
{
lean_inc(v_binderName_2705_);
lean_inc(v_fvarId_2704_);
lean_dec_ref(v_decl_2699_);
goto v___jp_2708_;
}
else
{
size_t v___x_2726_; size_t v___x_2727_; uint8_t v___x_2728_; 
v___x_2726_ = lean_ptr_addr(v_value_2701_);
v___x_2727_ = lean_ptr_addr(v_value_2707_);
v___x_2728_ = lean_usize_dec_eq(v___x_2726_, v___x_2727_);
if (v___x_2728_ == 0)
{
lean_inc(v_binderName_2705_);
lean_inc(v_fvarId_2704_);
lean_dec_ref(v_decl_2699_);
goto v___jp_2708_;
}
else
{
lean_object* v___x_2729_; 
lean_dec(v_value_2701_);
lean_dec_ref(v_type_2700_);
v___x_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2729_, 0, v_decl_2699_);
return v___x_2729_;
}
}
v___jp_2708_:
{
lean_object* v___x_2709_; lean_object* v_lctx_2710_; lean_object* v_nextIdx_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2722_; 
v___x_2709_ = lean_st_ref_take(v_a_2702_);
v_lctx_2710_ = lean_ctor_get(v___x_2709_, 0);
v_nextIdx_2711_ = lean_ctor_get(v___x_2709_, 1);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2713_ = v___x_2709_;
v_isShared_2714_ = v_isSharedCheck_2722_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_nextIdx_2711_);
lean_inc(v_lctx_2710_);
lean_dec(v___x_2709_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2722_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v_decl_2715_; lean_object* v___x_2716_; lean_object* v___x_2718_; 
v_decl_2715_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_decl_2715_, 0, v_fvarId_2704_);
lean_ctor_set(v_decl_2715_, 1, v_binderName_2705_);
lean_ctor_set(v_decl_2715_, 2, v_type_2700_);
lean_ctor_set(v_decl_2715_, 3, v_value_2701_);
lean_inc_ref(v_decl_2715_);
v___x_2716_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2698_, v_lctx_2710_, v_decl_2715_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v___x_2716_);
v___x_2718_ = v___x_2713_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2716_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v_nextIdx_2711_);
v___x_2718_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2719_ = lean_st_ref_put(v_a_2702_, v___x_2718_);
v___x_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2720_, 0, v_decl_2715_);
return v___x_2720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg___boxed(lean_object* v_pu_2730_, lean_object* v_decl_2731_, lean_object* v_type_2732_, lean_object* v_value_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_){
_start:
{
uint8_t v_pu_boxed_2736_; lean_object* v_res_2737_; 
v_pu_boxed_2736_ = lean_unbox(v_pu_2730_);
v_res_2737_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_boxed_2736_, v_decl_2731_, v_type_2732_, v_value_2733_, v_a_2734_);
lean_dec(v_a_2734_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(uint8_t v_pu_2738_, lean_object* v_decl_2739_, lean_object* v_type_2740_, lean_object* v_value_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2738_, v_decl_2739_, v_type_2740_, v_value_2741_, v_a_2743_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(lean_object* v_pu_2748_, lean_object* v_decl_2749_, lean_object* v_type_2750_, lean_object* v_value_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_){
_start:
{
uint8_t v_pu_boxed_2757_; lean_object* v_res_2758_; 
v_pu_boxed_2757_ = lean_unbox(v_pu_2748_);
v_res_2758_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(v_pu_boxed_2757_, v_decl_2749_, v_type_2750_, v_value_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t v_pu_2759_, lean_object* v_decl_2760_, lean_object* v_value_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v_type_2764_; lean_object* v___x_2765_; 
v_type_2764_ = lean_ctor_get(v_decl_2760_, 2);
lean_inc_ref(v_type_2764_);
v___x_2765_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2759_, v_decl_2760_, v_type_2764_, v_value_2761_, v_a_2762_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg___boxed(lean_object* v_pu_2766_, lean_object* v_decl_2767_, lean_object* v_value_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
uint8_t v_pu_boxed_2771_; lean_object* v_res_2772_; 
v_pu_boxed_2771_ = lean_unbox(v_pu_2766_);
v_res_2772_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_boxed_2771_, v_decl_2767_, v_value_2768_, v_a_2769_);
lean_dec(v_a_2769_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(uint8_t v_pu_2773_, lean_object* v_decl_2774_, lean_object* v_value_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_2773_, v_decl_2774_, v_value_2775_, v_a_2777_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___boxed(lean_object* v_pu_2782_, lean_object* v_decl_2783_, lean_object* v_value_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
uint8_t v_pu_boxed_2790_; lean_object* v_res_2791_; 
v_pu_boxed_2790_ = lean_unbox(v_pu_2782_);
v_res_2791_ = l_Lean_Compiler_LCNF_LetDecl_updateValue(v_pu_boxed_2790_, v_decl_2783_, v_value_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_);
lean_dec(v_a_2788_);
lean_dec_ref(v_a_2787_);
lean_dec(v_a_2786_);
lean_dec_ref(v_a_2785_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t v_pu_2792_, lean_object* v_decl_2793_, lean_object* v_type_2794_, lean_object* v_params_2795_, lean_object* v_value_2796_, lean_object* v_a_2797_){
_start:
{
lean_object* v_fvarId_2799_; lean_object* v_binderName_2800_; lean_object* v_params_2801_; lean_object* v_type_2802_; lean_object* v_value_2803_; size_t v___x_2819_; size_t v___x_2820_; uint8_t v___x_2821_; 
v_fvarId_2799_ = lean_ctor_get(v_decl_2793_, 0);
v_binderName_2800_ = lean_ctor_get(v_decl_2793_, 1);
v_params_2801_ = lean_ctor_get(v_decl_2793_, 2);
v_type_2802_ = lean_ctor_get(v_decl_2793_, 3);
v_value_2803_ = lean_ctor_get(v_decl_2793_, 4);
v___x_2819_ = lean_ptr_addr(v_type_2794_);
v___x_2820_ = lean_ptr_addr(v_type_2802_);
v___x_2821_ = lean_usize_dec_eq(v___x_2819_, v___x_2820_);
if (v___x_2821_ == 0)
{
lean_inc(v_binderName_2800_);
lean_inc(v_fvarId_2799_);
lean_dec_ref(v_decl_2793_);
goto v___jp_2804_;
}
else
{
size_t v___x_2822_; size_t v___x_2823_; uint8_t v___x_2824_; 
v___x_2822_ = lean_ptr_addr(v_params_2795_);
v___x_2823_ = lean_ptr_addr(v_params_2801_);
v___x_2824_ = lean_usize_dec_eq(v___x_2822_, v___x_2823_);
if (v___x_2824_ == 0)
{
lean_inc(v_binderName_2800_);
lean_inc(v_fvarId_2799_);
lean_dec_ref(v_decl_2793_);
goto v___jp_2804_;
}
else
{
size_t v___x_2825_; size_t v___x_2826_; uint8_t v___x_2827_; 
v___x_2825_ = lean_ptr_addr(v_value_2796_);
v___x_2826_ = lean_ptr_addr(v_value_2803_);
v___x_2827_ = lean_usize_dec_eq(v___x_2825_, v___x_2826_);
if (v___x_2827_ == 0)
{
lean_inc(v_binderName_2800_);
lean_inc(v_fvarId_2799_);
lean_dec_ref(v_decl_2793_);
goto v___jp_2804_;
}
else
{
lean_object* v___x_2828_; 
lean_dec_ref(v_value_2796_);
lean_dec_ref(v_params_2795_);
lean_dec_ref(v_type_2794_);
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v_decl_2793_);
return v___x_2828_;
}
}
}
v___jp_2804_:
{
lean_object* v___x_2805_; lean_object* v_lctx_2806_; lean_object* v_nextIdx_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2818_; 
v___x_2805_ = lean_st_ref_take(v_a_2797_);
v_lctx_2806_ = lean_ctor_get(v___x_2805_, 0);
v_nextIdx_2807_ = lean_ctor_get(v___x_2805_, 1);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2809_ = v___x_2805_;
v_isShared_2810_ = v_isSharedCheck_2818_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_nextIdx_2807_);
lean_inc(v_lctx_2806_);
lean_dec(v___x_2805_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2818_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v_decl_2811_; lean_object* v___x_2812_; lean_object* v___x_2814_; 
v_decl_2811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_decl_2811_, 0, v_fvarId_2799_);
lean_ctor_set(v_decl_2811_, 1, v_binderName_2800_);
lean_ctor_set(v_decl_2811_, 2, v_params_2795_);
lean_ctor_set(v_decl_2811_, 3, v_type_2794_);
lean_ctor_set(v_decl_2811_, 4, v_value_2796_);
lean_inc_ref(v_decl_2811_);
v___x_2812_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2792_, v_lctx_2806_, v_decl_2811_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 0, v___x_2812_);
v___x_2814_ = v___x_2809_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2812_);
lean_ctor_set(v_reuseFailAlloc_2817_, 1, v_nextIdx_2807_);
v___x_2814_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = lean_st_ref_put(v_a_2797_, v___x_2814_);
v___x_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2816_, 0, v_decl_2811_);
return v___x_2816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg___boxed(lean_object* v_pu_2829_, lean_object* v_decl_2830_, lean_object* v_type_2831_, lean_object* v_params_2832_, lean_object* v_value_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_){
_start:
{
uint8_t v_pu_boxed_2836_; lean_object* v_res_2837_; 
v_pu_boxed_2836_ = lean_unbox(v_pu_2829_);
v_res_2837_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_boxed_2836_, v_decl_2830_, v_type_2831_, v_params_2832_, v_value_2833_, v_a_2834_);
lean_dec(v_a_2834_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(uint8_t v_pu_2838_, lean_object* v_decl_2839_, lean_object* v_type_2840_, lean_object* v_params_2841_, lean_object* v_value_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2838_, v_decl_2839_, v_type_2840_, v_params_2841_, v_value_2842_, v_a_2844_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(lean_object* v_pu_2849_, lean_object* v_decl_2850_, lean_object* v_type_2851_, lean_object* v_params_2852_, lean_object* v_value_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
uint8_t v_pu_boxed_2859_; lean_object* v_res_2860_; 
v_pu_boxed_2859_ = lean_unbox(v_pu_2849_);
v_res_2860_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(v_pu_boxed_2859_, v_decl_2850_, v_type_2851_, v_params_2852_, v_value_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(uint8_t v_pu_2861_, lean_object* v_decl_2862_, lean_object* v_type_2863_, lean_object* v_value_2864_, lean_object* v_a_2865_){
_start:
{
lean_object* v_params_2867_; lean_object* v___x_2868_; 
v_params_2867_ = lean_ctor_get(v_decl_2862_, 2);
lean_inc_ref(v_params_2867_);
v___x_2868_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2861_, v_decl_2862_, v_type_2863_, v_params_2867_, v_value_2864_, v_a_2865_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg___boxed(lean_object* v_pu_2869_, lean_object* v_decl_2870_, lean_object* v_type_2871_, lean_object* v_value_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
uint8_t v_pu_boxed_2875_; lean_object* v_res_2876_; 
v_pu_boxed_2875_ = lean_unbox(v_pu_2869_);
v_res_2876_ = l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(v_pu_boxed_2875_, v_decl_2870_, v_type_2871_, v_value_2872_, v_a_2873_);
lean_dec(v_a_2873_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27(uint8_t v_pu_2877_, lean_object* v_decl_2878_, lean_object* v_type_2879_, lean_object* v_value_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_){
_start:
{
lean_object* v_params_2886_; lean_object* v___x_2887_; 
v_params_2886_ = lean_ctor_get(v_decl_2878_, 2);
lean_inc_ref(v_params_2886_);
v___x_2887_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2877_, v_decl_2878_, v_type_2879_, v_params_2886_, v_value_2880_, v_a_2882_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___boxed(lean_object* v_pu_2888_, lean_object* v_decl_2889_, lean_object* v_type_2890_, lean_object* v_value_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
uint8_t v_pu_boxed_2897_; lean_object* v_res_2898_; 
v_pu_boxed_2897_ = lean_unbox(v_pu_2888_);
v_res_2898_ = l_Lean_Compiler_LCNF_FunDecl_update_x27(v_pu_boxed_2897_, v_decl_2889_, v_type_2890_, v_value_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
lean_dec(v_a_2893_);
lean_dec_ref(v_a_2892_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(uint8_t v_pu_2899_, lean_object* v_decl_2900_, lean_object* v_value_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v_params_2904_; lean_object* v_type_2905_; lean_object* v___x_2906_; 
v_params_2904_ = lean_ctor_get(v_decl_2900_, 2);
lean_inc_ref(v_params_2904_);
v_type_2905_ = lean_ctor_get(v_decl_2900_, 3);
lean_inc_ref(v_type_2905_);
v___x_2906_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2899_, v_decl_2900_, v_type_2905_, v_params_2904_, v_value_2901_, v_a_2902_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg___boxed(lean_object* v_pu_2907_, lean_object* v_decl_2908_, lean_object* v_value_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_){
_start:
{
uint8_t v_pu_boxed_2912_; lean_object* v_res_2913_; 
v_pu_boxed_2912_ = lean_unbox(v_pu_2907_);
v_res_2913_ = l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(v_pu_boxed_2912_, v_decl_2908_, v_value_2909_, v_a_2910_);
lean_dec(v_a_2910_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue(uint8_t v_pu_2914_, lean_object* v_decl_2915_, lean_object* v_value_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v_params_2922_; lean_object* v_type_2923_; lean_object* v___x_2924_; 
v_params_2922_ = lean_ctor_get(v_decl_2915_, 2);
lean_inc_ref(v_params_2922_);
v_type_2923_ = lean_ctor_get(v_decl_2915_, 3);
lean_inc_ref(v_type_2923_);
v___x_2924_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2914_, v_decl_2915_, v_type_2923_, v_params_2922_, v_value_2916_, v_a_2918_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___boxed(lean_object* v_pu_2925_, lean_object* v_decl_2926_, lean_object* v_value_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_){
_start:
{
uint8_t v_pu_boxed_2933_; lean_object* v_res_2934_; 
v_pu_boxed_2933_ = lean_unbox(v_pu_2925_);
v_res_2934_ = l_Lean_Compiler_LCNF_FunDecl_updateValue(v_pu_boxed_2933_, v_decl_2926_, v_value_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_);
lean_dec(v_a_2931_);
lean_dec_ref(v_a_2930_);
lean_dec(v_a_2929_);
lean_dec_ref(v_a_2928_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0(uint8_t v_pu_2935_, lean_object* v_p_2936_, lean_object* v_inst_2937_, lean_object* v_____do__lift_2938_){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2939_ = lean_box(v_pu_2935_);
v___x_2940_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_2940_, 0, v___x_2939_);
lean_closure_set(v___x_2940_, 1, v_p_2936_);
lean_closure_set(v___x_2940_, 2, v_____do__lift_2938_);
v___x_2941_ = lean_apply_2(v_inst_2937_, lean_box(0), v___x_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed(lean_object* v_pu_2942_, lean_object* v_p_2943_, lean_object* v_inst_2944_, lean_object* v_____do__lift_2945_){
_start:
{
uint8_t v_pu_boxed_2946_; lean_object* v_res_2947_; 
v_pu_boxed_2946_ = lean_unbox(v_pu_2942_);
v_res_2947_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__0(v_pu_boxed_2946_, v_p_2943_, v_inst_2944_, v_____do__lift_2945_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1(uint8_t v_pu_2948_, uint8_t v_t_2949_, lean_object* v_type_2950_, lean_object* v_toPure_2951_, lean_object* v_____do__lift_2952_){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2948_, v_____do__lift_2952_, v_t_2949_, v_type_2950_);
v___x_2954_ = lean_apply_2(v_toPure_2951_, lean_box(0), v___x_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed(lean_object* v_pu_2955_, lean_object* v_t_2956_, lean_object* v_type_2957_, lean_object* v_toPure_2958_, lean_object* v_____do__lift_2959_){
_start:
{
uint8_t v_pu_boxed_2960_; uint8_t v_t_boxed_2961_; lean_object* v_res_2962_; 
v_pu_boxed_2960_ = lean_unbox(v_pu_2955_);
v_t_boxed_2961_ = lean_unbox(v_t_2956_);
v_res_2962_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__1(v_pu_boxed_2960_, v_t_boxed_2961_, v_type_2957_, v_toPure_2958_, v_____do__lift_2959_);
lean_dec_ref(v_____do__lift_2959_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg(uint8_t v_pu_2963_, uint8_t v_t_2964_, lean_object* v_inst_2965_, lean_object* v_inst_2966_, lean_object* v_inst_2967_, lean_object* v_p_2968_){
_start:
{
lean_object* v_toApplicative_2969_; lean_object* v_toBind_2970_; lean_object* v_type_2971_; lean_object* v_toPure_2972_; lean_object* v___x_2973_; lean_object* v___f_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___f_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v_toApplicative_2969_ = lean_ctor_get(v_inst_2966_, 0);
lean_inc_ref(v_toApplicative_2969_);
v_toBind_2970_ = lean_ctor_get(v_inst_2966_, 1);
lean_inc_n(v_toBind_2970_, 2);
lean_dec_ref(v_inst_2966_);
v_type_2971_ = lean_ctor_get(v_p_2968_, 2);
lean_inc_ref(v_type_2971_);
v_toPure_2972_ = lean_ctor_get(v_toApplicative_2969_, 1);
lean_inc(v_toPure_2972_);
lean_dec_ref(v_toApplicative_2969_);
v___x_2973_ = lean_box(v_pu_2963_);
v___f_2974_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2974_, 0, v___x_2973_);
lean_closure_set(v___f_2974_, 1, v_p_2968_);
lean_closure_set(v___f_2974_, 2, v_inst_2965_);
v___x_2975_ = lean_box(v_pu_2963_);
v___x_2976_ = lean_box(v_t_2964_);
v___f_2977_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2977_, 0, v___x_2975_);
lean_closure_set(v___f_2977_, 1, v___x_2976_);
lean_closure_set(v___f_2977_, 2, v_type_2971_);
lean_closure_set(v___f_2977_, 3, v_toPure_2972_);
v___x_2978_ = lean_apply_4(v_toBind_2970_, lean_box(0), lean_box(0), v_inst_2967_, v___f_2977_);
v___x_2979_ = lean_apply_4(v_toBind_2970_, lean_box(0), lean_box(0), v___x_2978_, v___f_2974_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___boxed(lean_object* v_pu_2980_, lean_object* v_t_2981_, lean_object* v_inst_2982_, lean_object* v_inst_2983_, lean_object* v_inst_2984_, lean_object* v_p_2985_){
_start:
{
uint8_t v_pu_boxed_2986_; uint8_t v_t_boxed_2987_; lean_object* v_res_2988_; 
v_pu_boxed_2986_ = lean_unbox(v_pu_2980_);
v_t_boxed_2987_ = lean_unbox(v_t_2981_);
v_res_2988_ = l_Lean_Compiler_LCNF_normParam___redArg(v_pu_boxed_2986_, v_t_boxed_2987_, v_inst_2982_, v_inst_2983_, v_inst_2984_, v_p_2985_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam(lean_object* v_m_2989_, uint8_t v_pu_2990_, uint8_t v_t_2991_, lean_object* v_inst_2992_, lean_object* v_inst_2993_, lean_object* v_inst_2994_, lean_object* v_p_2995_){
_start:
{
lean_object* v_toApplicative_2996_; lean_object* v_toBind_2997_; lean_object* v_type_2998_; lean_object* v_toPure_2999_; lean_object* v___x_3000_; lean_object* v___f_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___f_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_toApplicative_2996_ = lean_ctor_get(v_inst_2993_, 0);
lean_inc_ref(v_toApplicative_2996_);
v_toBind_2997_ = lean_ctor_get(v_inst_2993_, 1);
lean_inc_n(v_toBind_2997_, 2);
lean_dec_ref(v_inst_2993_);
v_type_2998_ = lean_ctor_get(v_p_2995_, 2);
lean_inc_ref(v_type_2998_);
v_toPure_2999_ = lean_ctor_get(v_toApplicative_2996_, 1);
lean_inc(v_toPure_2999_);
lean_dec_ref(v_toApplicative_2996_);
v___x_3000_ = lean_box(v_pu_2990_);
v___f_3001_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3001_, 0, v___x_3000_);
lean_closure_set(v___f_3001_, 1, v_p_2995_);
lean_closure_set(v___f_3001_, 2, v_inst_2992_);
v___x_3002_ = lean_box(v_pu_2990_);
v___x_3003_ = lean_box(v_t_2991_);
v___f_3004_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3004_, 0, v___x_3002_);
lean_closure_set(v___f_3004_, 1, v___x_3003_);
lean_closure_set(v___f_3004_, 2, v_type_2998_);
lean_closure_set(v___f_3004_, 3, v_toPure_2999_);
v___x_3005_ = lean_apply_4(v_toBind_2997_, lean_box(0), lean_box(0), v_inst_2994_, v___f_3004_);
v___x_3006_ = lean_apply_4(v_toBind_2997_, lean_box(0), lean_box(0), v___x_3005_, v___f_3001_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___boxed(lean_object* v_m_3007_, lean_object* v_pu_3008_, lean_object* v_t_3009_, lean_object* v_inst_3010_, lean_object* v_inst_3011_, lean_object* v_inst_3012_, lean_object* v_p_3013_){
_start:
{
uint8_t v_pu_boxed_3014_; uint8_t v_t_boxed_3015_; lean_object* v_res_3016_; 
v_pu_boxed_3014_ = lean_unbox(v_pu_3008_);
v_t_boxed_3015_ = lean_unbox(v_t_3009_);
v_res_3016_ = l_Lean_Compiler_LCNF_normParam(v_m_3007_, v_pu_boxed_3014_, v_t_boxed_3015_, v_inst_3010_, v_inst_3011_, v_inst_3012_, v_p_3013_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg(uint8_t v_pu_3017_, uint8_t v_t_3018_, lean_object* v_inst_3019_, lean_object* v_inst_3020_, lean_object* v_inst_3021_, lean_object* v_ps_3022_){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3023_ = lean_box(v_pu_3017_);
v___x_3024_ = lean_box(v_t_3018_);
lean_inc_ref(v_inst_3020_);
v___x_3025_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___boxed), 7, 6);
lean_closure_set(v___x_3025_, 0, lean_box(0));
lean_closure_set(v___x_3025_, 1, v___x_3023_);
lean_closure_set(v___x_3025_, 2, v___x_3024_);
lean_closure_set(v___x_3025_, 3, v_inst_3019_);
lean_closure_set(v___x_3025_, 4, v_inst_3020_);
lean_closure_set(v___x_3025_, 5, v_inst_3021_);
v___x_3026_ = lean_unsigned_to_nat(0u);
v___x_3027_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_3020_, v___x_3025_, v___x_3026_, v_ps_3022_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg___boxed(lean_object* v_pu_3028_, lean_object* v_t_3029_, lean_object* v_inst_3030_, lean_object* v_inst_3031_, lean_object* v_inst_3032_, lean_object* v_ps_3033_){
_start:
{
uint8_t v_pu_boxed_3034_; uint8_t v_t_boxed_3035_; lean_object* v_res_3036_; 
v_pu_boxed_3034_ = lean_unbox(v_pu_3028_);
v_t_boxed_3035_ = lean_unbox(v_t_3029_);
v_res_3036_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_boxed_3034_, v_t_boxed_3035_, v_inst_3030_, v_inst_3031_, v_inst_3032_, v_ps_3033_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams(lean_object* v_m_3037_, uint8_t v_pu_3038_, uint8_t v_t_3039_, lean_object* v_inst_3040_, lean_object* v_inst_3041_, lean_object* v_inst_3042_, lean_object* v_ps_3043_){
_start:
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_3038_, v_t_3039_, v_inst_3040_, v_inst_3041_, v_inst_3042_, v_ps_3043_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___boxed(lean_object* v_m_3045_, lean_object* v_pu_3046_, lean_object* v_t_3047_, lean_object* v_inst_3048_, lean_object* v_inst_3049_, lean_object* v_inst_3050_, lean_object* v_ps_3051_){
_start:
{
uint8_t v_pu_boxed_3052_; uint8_t v_t_boxed_3053_; lean_object* v_res_3054_; 
v_pu_boxed_3052_ = lean_unbox(v_pu_3046_);
v_t_boxed_3053_ = lean_unbox(v_t_3047_);
v_res_3054_ = l_Lean_Compiler_LCNF_normParams(v_m_3045_, v_pu_boxed_3052_, v_t_boxed_3053_, v_inst_3048_, v_inst_3049_, v_inst_3050_, v_ps_3051_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(uint8_t v_pu_3055_, lean_object* v_decl_3056_, lean_object* v_____do__lift_3057_, lean_object* v_inst_3058_, lean_object* v_____do__lift_3059_){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3060_ = lean_box(v_pu_3055_);
v___x_3061_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_3061_, 0, v___x_3060_);
lean_closure_set(v___x_3061_, 1, v_decl_3056_);
lean_closure_set(v___x_3061_, 2, v_____do__lift_3057_);
lean_closure_set(v___x_3061_, 3, v_____do__lift_3059_);
v___x_3062_ = lean_apply_2(v_inst_3058_, lean_box(0), v___x_3061_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed(lean_object* v_pu_3063_, lean_object* v_decl_3064_, lean_object* v_____do__lift_3065_, lean_object* v_inst_3066_, lean_object* v_____do__lift_3067_){
_start:
{
uint8_t v_pu_boxed_3068_; lean_object* v_res_3069_; 
v_pu_boxed_3068_ = lean_unbox(v_pu_3063_);
v_res_3069_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(v_pu_boxed_3068_, v_decl_3064_, v_____do__lift_3065_, v_inst_3066_, v_____do__lift_3067_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(uint8_t v_pu_3070_, lean_object* v_value_3071_, uint8_t v_t_3072_, lean_object* v_toPure_3073_, lean_object* v_____do__lift_3074_){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3070_, v_____do__lift_3074_, v_value_3071_, v_t_3072_);
v___x_3076_ = lean_apply_2(v_toPure_3073_, lean_box(0), v___x_3075_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed(lean_object* v_pu_3077_, lean_object* v_value_3078_, lean_object* v_t_3079_, lean_object* v_toPure_3080_, lean_object* v_____do__lift_3081_){
_start:
{
uint8_t v_pu_boxed_3082_; uint8_t v_t_boxed_3083_; lean_object* v_res_3084_; 
v_pu_boxed_3082_ = lean_unbox(v_pu_3077_);
v_t_boxed_3083_ = lean_unbox(v_t_3079_);
v_res_3084_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(v_pu_boxed_3082_, v_value_3078_, v_t_boxed_3083_, v_toPure_3080_, v_____do__lift_3081_);
lean_dec_ref(v_____do__lift_3081_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(uint8_t v_pu_3085_, lean_object* v_decl_3086_, lean_object* v_inst_3087_, lean_object* v_value_3088_, uint8_t v_t_3089_, lean_object* v_toPure_3090_, lean_object* v_toBind_3091_, lean_object* v_inst_3092_, lean_object* v_____do__lift_3093_){
_start:
{
lean_object* v___x_3094_; lean_object* v___f_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___f_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3094_ = lean_box(v_pu_3085_);
v___f_3095_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3095_, 0, v___x_3094_);
lean_closure_set(v___f_3095_, 1, v_decl_3086_);
lean_closure_set(v___f_3095_, 2, v_____do__lift_3093_);
lean_closure_set(v___f_3095_, 3, v_inst_3087_);
v___x_3096_ = lean_box(v_pu_3085_);
v___x_3097_ = lean_box(v_t_3089_);
v___f_3098_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3098_, 0, v___x_3096_);
lean_closure_set(v___f_3098_, 1, v_value_3088_);
lean_closure_set(v___f_3098_, 2, v___x_3097_);
lean_closure_set(v___f_3098_, 3, v_toPure_3090_);
lean_inc(v_toBind_3091_);
v___x_3099_ = lean_apply_4(v_toBind_3091_, lean_box(0), lean_box(0), v_inst_3092_, v___f_3098_);
v___x_3100_ = lean_apply_4(v_toBind_3091_, lean_box(0), lean_box(0), v___x_3099_, v___f_3095_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed(lean_object* v_pu_3101_, lean_object* v_decl_3102_, lean_object* v_inst_3103_, lean_object* v_value_3104_, lean_object* v_t_3105_, lean_object* v_toPure_3106_, lean_object* v_toBind_3107_, lean_object* v_inst_3108_, lean_object* v_____do__lift_3109_){
_start:
{
uint8_t v_pu_boxed_3110_; uint8_t v_t_boxed_3111_; lean_object* v_res_3112_; 
v_pu_boxed_3110_ = lean_unbox(v_pu_3101_);
v_t_boxed_3111_ = lean_unbox(v_t_3105_);
v_res_3112_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(v_pu_boxed_3110_, v_decl_3102_, v_inst_3103_, v_value_3104_, v_t_boxed_3111_, v_toPure_3106_, v_toBind_3107_, v_inst_3108_, v_____do__lift_3109_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg(uint8_t v_pu_3113_, uint8_t v_t_3114_, lean_object* v_inst_3115_, lean_object* v_inst_3116_, lean_object* v_inst_3117_, lean_object* v_decl_3118_){
_start:
{
lean_object* v_toApplicative_3119_; lean_object* v_toBind_3120_; lean_object* v_type_3121_; lean_object* v_value_3122_; lean_object* v_toPure_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___f_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___f_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v_toApplicative_3119_ = lean_ctor_get(v_inst_3116_, 0);
lean_inc_ref(v_toApplicative_3119_);
v_toBind_3120_ = lean_ctor_get(v_inst_3116_, 1);
lean_inc_n(v_toBind_3120_, 3);
lean_dec_ref(v_inst_3116_);
v_type_3121_ = lean_ctor_get(v_decl_3118_, 2);
lean_inc_ref(v_type_3121_);
v_value_3122_ = lean_ctor_get(v_decl_3118_, 3);
lean_inc(v_value_3122_);
v_toPure_3123_ = lean_ctor_get(v_toApplicative_3119_, 1);
lean_inc_n(v_toPure_3123_, 2);
lean_dec_ref(v_toApplicative_3119_);
v___x_3124_ = lean_box(v_pu_3113_);
v___x_3125_ = lean_box(v_t_3114_);
lean_inc(v_inst_3117_);
v___f_3126_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_3126_, 0, v___x_3124_);
lean_closure_set(v___f_3126_, 1, v_decl_3118_);
lean_closure_set(v___f_3126_, 2, v_inst_3115_);
lean_closure_set(v___f_3126_, 3, v_value_3122_);
lean_closure_set(v___f_3126_, 4, v___x_3125_);
lean_closure_set(v___f_3126_, 5, v_toPure_3123_);
lean_closure_set(v___f_3126_, 6, v_toBind_3120_);
lean_closure_set(v___f_3126_, 7, v_inst_3117_);
v___x_3127_ = lean_box(v_pu_3113_);
v___x_3128_ = lean_box(v_t_3114_);
v___f_3129_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3129_, 0, v___x_3127_);
lean_closure_set(v___f_3129_, 1, v___x_3128_);
lean_closure_set(v___f_3129_, 2, v_type_3121_);
lean_closure_set(v___f_3129_, 3, v_toPure_3123_);
v___x_3130_ = lean_apply_4(v_toBind_3120_, lean_box(0), lean_box(0), v_inst_3117_, v___f_3129_);
v___x_3131_ = lean_apply_4(v_toBind_3120_, lean_box(0), lean_box(0), v___x_3130_, v___f_3126_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___boxed(lean_object* v_pu_3132_, lean_object* v_t_3133_, lean_object* v_inst_3134_, lean_object* v_inst_3135_, lean_object* v_inst_3136_, lean_object* v_decl_3137_){
_start:
{
uint8_t v_pu_boxed_3138_; uint8_t v_t_boxed_3139_; lean_object* v_res_3140_; 
v_pu_boxed_3138_ = lean_unbox(v_pu_3132_);
v_t_boxed_3139_ = lean_unbox(v_t_3133_);
v_res_3140_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_boxed_3138_, v_t_boxed_3139_, v_inst_3134_, v_inst_3135_, v_inst_3136_, v_decl_3137_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl(lean_object* v_m_3141_, uint8_t v_pu_3142_, uint8_t v_t_3143_, lean_object* v_inst_3144_, lean_object* v_inst_3145_, lean_object* v_inst_3146_, lean_object* v_decl_3147_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_3142_, v_t_3143_, v_inst_3144_, v_inst_3145_, v_inst_3146_, v_decl_3147_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___boxed(lean_object* v_m_3149_, lean_object* v_pu_3150_, lean_object* v_t_3151_, lean_object* v_inst_3152_, lean_object* v_inst_3153_, lean_object* v_inst_3154_, lean_object* v_decl_3155_){
_start:
{
uint8_t v_pu_boxed_3156_; uint8_t v_t_boxed_3157_; lean_object* v_res_3158_; 
v_pu_boxed_3156_ = lean_unbox(v_pu_3150_);
v_t_boxed_3157_ = lean_unbox(v_t_3151_);
v_res_3158_ = l_Lean_Compiler_LCNF_normLetDecl(v_m_3149_, v_pu_boxed_3156_, v_t_boxed_3157_, v_inst_3152_, v_inst_3153_, v_inst_3154_, v_decl_3155_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(uint8_t v_pu_3159_, uint8_t v_t_3160_){
_start:
{
lean_object* v___x_3161_; lean_object* v_toApplicative_3162_; lean_object* v_toFunctor_3163_; lean_object* v_toSeq_3164_; lean_object* v_toSeqLeft_3165_; lean_object* v_toSeqRight_3166_; lean_object* v___f_3167_; lean_object* v___f_3168_; lean_object* v___f_3169_; lean_object* v___f_3170_; lean_object* v___x_3171_; lean_object* v___f_3172_; lean_object* v___f_3173_; lean_object* v___f_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v_toApplicative_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3206_; 
v___x_3161_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_3162_ = lean_ctor_get(v___x_3161_, 0);
v_toFunctor_3163_ = lean_ctor_get(v_toApplicative_3162_, 0);
v_toSeq_3164_ = lean_ctor_get(v_toApplicative_3162_, 2);
v_toSeqLeft_3165_ = lean_ctor_get(v_toApplicative_3162_, 3);
v_toSeqRight_3166_ = lean_ctor_get(v_toApplicative_3162_, 4);
v___f_3167_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_3168_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_3163_, 2);
v___f_3169_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3169_, 0, v_toFunctor_3163_);
v___f_3170_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3170_, 0, v_toFunctor_3163_);
v___x_3171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___f_3169_);
lean_ctor_set(v___x_3171_, 1, v___f_3170_);
lean_inc(v_toSeqRight_3166_);
v___f_3172_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3172_, 0, v_toSeqRight_3166_);
lean_inc(v_toSeqLeft_3165_);
v___f_3173_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3173_, 0, v_toSeqLeft_3165_);
lean_inc(v_toSeq_3164_);
v___f_3174_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3174_, 0, v_toSeq_3164_);
v___x_3175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3171_);
lean_ctor_set(v___x_3175_, 1, v___f_3167_);
lean_ctor_set(v___x_3175_, 2, v___f_3174_);
lean_ctor_set(v___x_3175_, 3, v___f_3173_);
lean_ctor_set(v___x_3175_, 4, v___f_3172_);
v___x_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3175_);
lean_ctor_set(v___x_3176_, 1, v___f_3168_);
v___x_3177_ = l_StateRefT_x27_instMonad___redArg(v___x_3176_);
v_toApplicative_3178_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3206_ == 0)
{
lean_object* v_unused_3207_; 
v_unused_3207_ = lean_ctor_get(v___x_3177_, 1);
lean_dec(v_unused_3207_);
v___x_3180_ = v___x_3177_;
v_isShared_3181_ = v_isSharedCheck_3206_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_toApplicative_3178_);
lean_dec(v___x_3177_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3206_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v_toFunctor_3182_; lean_object* v_toSeq_3183_; lean_object* v_toSeqLeft_3184_; lean_object* v_toSeqRight_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3204_; 
v_toFunctor_3182_ = lean_ctor_get(v_toApplicative_3178_, 0);
v_toSeq_3183_ = lean_ctor_get(v_toApplicative_3178_, 2);
v_toSeqLeft_3184_ = lean_ctor_get(v_toApplicative_3178_, 3);
v_toSeqRight_3185_ = lean_ctor_get(v_toApplicative_3178_, 4);
v_isSharedCheck_3204_ = !lean_is_exclusive(v_toApplicative_3178_);
if (v_isSharedCheck_3204_ == 0)
{
lean_object* v_unused_3205_; 
v_unused_3205_ = lean_ctor_get(v_toApplicative_3178_, 1);
lean_dec(v_unused_3205_);
v___x_3187_ = v_toApplicative_3178_;
v_isShared_3188_ = v_isSharedCheck_3204_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_toSeqRight_3185_);
lean_inc(v_toSeqLeft_3184_);
lean_inc(v_toSeq_3183_);
lean_inc(v_toFunctor_3182_);
lean_dec(v_toApplicative_3178_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3204_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___f_3189_; lean_object* v___f_3190_; lean_object* v___f_3191_; lean_object* v___f_3192_; lean_object* v___x_3193_; lean_object* v___f_3194_; lean_object* v___f_3195_; lean_object* v___f_3196_; lean_object* v___x_3198_; 
v___f_3189_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_3190_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_3182_);
v___f_3191_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3191_, 0, v_toFunctor_3182_);
v___f_3192_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3192_, 0, v_toFunctor_3182_);
v___x_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3193_, 0, v___f_3191_);
lean_ctor_set(v___x_3193_, 1, v___f_3192_);
v___f_3194_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3194_, 0, v_toSeqRight_3185_);
v___f_3195_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3195_, 0, v_toSeqLeft_3184_);
v___f_3196_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3196_, 0, v_toSeq_3183_);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 4, v___f_3194_);
lean_ctor_set(v___x_3187_, 3, v___f_3195_);
lean_ctor_set(v___x_3187_, 2, v___f_3196_);
lean_ctor_set(v___x_3187_, 1, v___f_3189_);
lean_ctor_set(v___x_3187_, 0, v___x_3193_);
v___x_3198_ = v___x_3187_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3193_);
lean_ctor_set(v_reuseFailAlloc_3203_, 1, v___f_3189_);
lean_ctor_set(v_reuseFailAlloc_3203_, 2, v___f_3196_);
lean_ctor_set(v_reuseFailAlloc_3203_, 3, v___f_3195_);
lean_ctor_set(v_reuseFailAlloc_3203_, 4, v___f_3194_);
v___x_3198_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
lean_object* v___x_3200_; 
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 1, v___f_3190_);
lean_ctor_set(v___x_3180_, 0, v___x_3198_);
v___x_3200_ = v___x_3180_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3198_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v___f_3190_);
v___x_3200_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
lean_object* v___x_3201_; 
v___x_3201_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_3201_, 0, lean_box(0));
lean_closure_set(v___x_3201_, 1, lean_box(0));
lean_closure_set(v___x_3201_, 2, v___x_3200_);
return v___x_3201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___boxed(lean_object* v_pu_3208_, lean_object* v_t_3209_){
_start:
{
uint8_t v_pu_boxed_3210_; uint8_t v_t_boxed_3211_; lean_object* v_res_3212_; 
v_pu_boxed_3210_ = lean_unbox(v_pu_3208_);
v_t_boxed_3211_ = lean_unbox(v_t_3209_);
v_res_3212_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(v_pu_boxed_3210_, v_t_boxed_3211_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg(uint8_t v_pu_3213_, lean_object* v_inst_3214_, lean_object* v_result_3215_, lean_object* v_x_3216_){
_start:
{
if (lean_obj_tag(v_result_3215_) == 0)
{
lean_object* v_fvarId_3217_; lean_object* v___x_3218_; 
lean_dec(v_inst_3214_);
v_fvarId_3217_ = lean_ctor_get(v_result_3215_, 0);
lean_inc(v_fvarId_3217_);
lean_dec_ref_known(v_result_3215_, 1);
v___x_3218_ = lean_apply_1(v_x_3216_, v_fvarId_3217_);
return v___x_3218_;
}
else
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
lean_dec(v_x_3216_);
v___x_3219_ = lean_box(v_pu_3213_);
v___x_3220_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3220_, 0, v___x_3219_);
v___x_3221_ = lean_apply_2(v_inst_3214_, lean_box(0), v___x_3220_);
return v___x_3221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg___boxed(lean_object* v_pu_3222_, lean_object* v_inst_3223_, lean_object* v_result_3224_, lean_object* v_x_3225_){
_start:
{
uint8_t v_pu_boxed_3226_; lean_object* v_res_3227_; 
v_pu_boxed_3226_ = lean_unbox(v_pu_3222_);
v_res_3227_ = l_Lean_Compiler_LCNF_withNormFVarResult___redArg(v_pu_boxed_3226_, v_inst_3223_, v_result_3224_, v_x_3225_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult(lean_object* v_m_3228_, uint8_t v_pu_3229_, lean_object* v_inst_3230_, lean_object* v_inst_3231_, lean_object* v_result_3232_, lean_object* v_x_3233_){
_start:
{
if (lean_obj_tag(v_result_3232_) == 0)
{
lean_object* v_fvarId_3234_; lean_object* v___x_3235_; 
lean_dec(v_inst_3230_);
v_fvarId_3234_ = lean_ctor_get(v_result_3232_, 0);
lean_inc(v_fvarId_3234_);
lean_dec_ref_known(v_result_3232_, 1);
v___x_3235_ = lean_apply_1(v_x_3233_, v_fvarId_3234_);
return v___x_3235_;
}
else
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
lean_dec(v_x_3233_);
v___x_3236_ = lean_box(v_pu_3229_);
v___x_3237_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3237_, 0, v___x_3236_);
v___x_3238_ = lean_apply_2(v_inst_3230_, lean_box(0), v___x_3237_);
return v___x_3238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___boxed(lean_object* v_m_3239_, lean_object* v_pu_3240_, lean_object* v_inst_3241_, lean_object* v_inst_3242_, lean_object* v_result_3243_, lean_object* v_x_3244_){
_start:
{
uint8_t v_pu_boxed_3245_; lean_object* v_res_3246_; 
v_pu_boxed_3245_ = lean_unbox(v_pu_3240_);
v_res_3246_ = l_Lean_Compiler_LCNF_withNormFVarResult(v_m_3239_, v_pu_boxed_3245_, v_inst_3241_, v_inst_3242_, v_result_3243_, v_x_3244_);
lean_dec_ref(v_inst_3242_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(uint8_t v_pu_3247_, uint8_t v_t_3248_, lean_object* v_args_3249_, lean_object* v___y_3250_){
_start:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3252_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_3247_, v___y_3250_, v_args_3249_, v_t_3248_);
v___x_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3252_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg___boxed(lean_object* v_pu_3254_, lean_object* v_t_3255_, lean_object* v_args_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
uint8_t v_pu_boxed_3259_; uint8_t v_t_boxed_3260_; lean_object* v_res_3261_; 
v_pu_boxed_3259_ = lean_unbox(v_pu_3254_);
v_t_boxed_3260_ = lean_unbox(v_t_3255_);
v_res_3261_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_boxed_3259_, v_t_boxed_3260_, v_args_3256_, v___y_3257_);
lean_dec_ref(v___y_3257_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(uint8_t v_pu_3262_, uint8_t v_t_3263_, lean_object* v_i_3264_, lean_object* v_as_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
lean_object* v___x_3269_; uint8_t v___x_3270_; 
v___x_3269_ = lean_array_get_size(v_as_3265_);
v___x_3270_ = lean_nat_dec_lt(v_i_3264_, v___x_3269_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3271_; 
lean_dec(v_i_3264_);
v___x_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3271_, 0, v_as_3265_);
return v___x_3271_;
}
else
{
lean_object* v_a_3272_; lean_object* v_type_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v_a_3272_ = lean_array_fget_borrowed(v_as_3265_, v_i_3264_);
v_type_3273_ = lean_ctor_get(v_a_3272_, 2);
lean_inc_ref(v_type_3273_);
v___x_3274_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3262_, v___y_3266_, v_t_3263_, v_type_3273_);
lean_inc(v_a_3272_);
v___x_3275_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_3262_, v_a_3272_, v___x_3274_, v___y_3267_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_a_3276_; size_t v___x_3277_; size_t v___x_3278_; uint8_t v___x_3279_; 
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_a_3276_);
lean_dec_ref_known(v___x_3275_, 1);
v___x_3277_ = lean_ptr_addr(v_a_3272_);
v___x_3278_ = lean_ptr_addr(v_a_3276_);
v___x_3279_ = lean_usize_dec_eq(v___x_3277_, v___x_3278_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3280_ = lean_unsigned_to_nat(1u);
v___x_3281_ = lean_nat_add(v_i_3264_, v___x_3280_);
v___x_3282_ = lean_array_fset(v_as_3265_, v_i_3264_, v_a_3276_);
lean_dec(v_i_3264_);
v_i_3264_ = v___x_3281_;
v_as_3265_ = v___x_3282_;
goto _start;
}
else
{
lean_object* v___x_3284_; lean_object* v___x_3285_; 
lean_dec(v_a_3276_);
v___x_3284_ = lean_unsigned_to_nat(1u);
v___x_3285_ = lean_nat_add(v_i_3264_, v___x_3284_);
lean_dec(v_i_3264_);
v_i_3264_ = v___x_3285_;
goto _start;
}
}
else
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3294_; 
lean_dec_ref(v_as_3265_);
lean_dec(v_i_3264_);
v_a_3287_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3289_ = v___x_3275_;
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3275_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3292_; 
if (v_isShared_3290_ == 0)
{
v___x_3292_ = v___x_3289_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3287_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg___boxed(lean_object* v_pu_3295_, lean_object* v_t_3296_, lean_object* v_i_3297_, lean_object* v_as_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
uint8_t v_pu_boxed_3302_; uint8_t v_t_boxed_3303_; lean_object* v_res_3304_; 
v_pu_boxed_3302_ = lean_unbox(v_pu_3295_);
v_t_boxed_3303_ = lean_unbox(v_t_3296_);
v_res_3304_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_boxed_3302_, v_t_boxed_3303_, v_i_3297_, v_as_3298_, v___y_3299_, v___y_3300_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(uint8_t v_pu_3305_, uint8_t v_t_3306_, lean_object* v_ps_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3314_ = lean_unsigned_to_nat(0u);
v___x_3315_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_3305_, v_t_3306_, v___x_3314_, v_ps_3307_, v___y_3308_, v___y_3310_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg___boxed(lean_object* v_pu_3316_, lean_object* v_t_3317_, lean_object* v_ps_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
uint8_t v_pu_boxed_3325_; uint8_t v_t_boxed_3326_; lean_object* v_res_3327_; 
v_pu_boxed_3325_ = lean_unbox(v_pu_3316_);
v_t_boxed_3326_ = lean_unbox(v_t_3317_);
v_res_3327_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_boxed_3325_, v_t_boxed_3326_, v_ps_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec_ref(v___y_3319_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(uint8_t v_pu_3328_, uint8_t v_t_3329_, lean_object* v_decl_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v_type_3334_; lean_object* v_value_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v_type_3334_ = lean_ctor_get(v_decl_3330_, 2);
v_value_3335_ = lean_ctor_get(v_decl_3330_, 3);
lean_inc_ref(v_type_3334_);
v___x_3336_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3328_, v___y_3331_, v_t_3329_, v_type_3334_);
lean_inc(v_value_3335_);
v___x_3337_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3328_, v___y_3331_, v_value_3335_, v_t_3329_);
v___x_3338_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_3328_, v_decl_3330_, v___x_3336_, v___x_3337_, v___y_3332_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg___boxed(lean_object* v_pu_3339_, lean_object* v_t_3340_, lean_object* v_decl_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
uint8_t v_pu_boxed_3345_; uint8_t v_t_boxed_3346_; lean_object* v_res_3347_; 
v_pu_boxed_3345_ = lean_unbox(v_pu_3339_);
v_t_boxed_3346_ = lean_unbox(v_t_3340_);
v_res_3347_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_boxed_3345_, v_t_boxed_3346_, v_decl_3341_, v___y_3342_, v___y_3343_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(uint8_t v_pu_3348_, uint8_t v_t_3349_, lean_object* v_i_3350_, lean_object* v_as_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v___x_3358_; uint8_t v___x_3359_; 
v___x_3358_ = lean_array_get_size(v_as_3351_);
v___x_3359_ = lean_nat_dec_lt(v_i_3350_, v___x_3358_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; 
lean_dec(v_i_3350_);
v___x_3360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3360_, 0, v_as_3351_);
return v___x_3360_;
}
else
{
lean_object* v_a_3361_; lean_object* v_a_3363_; 
v_a_3361_ = lean_array_fget_borrowed(v_as_3351_, v_i_3350_);
switch(lean_obj_tag(v_a_3361_))
{
case 0:
{
lean_object* v_params_3374_; lean_object* v_code_3375_; lean_object* v___x_3376_; 
v_params_3374_ = lean_ctor_get(v_a_3361_, 1);
v_code_3375_ = lean_ctor_get(v_a_3361_, 2);
lean_inc_ref(v_params_3374_);
v___x_3376_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_3348_, v_t_3349_, v_params_3374_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v___x_3378_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3377_);
lean_dec_ref_known(v___x_3376_, 1);
lean_inc_ref(v_code_3375_);
v___x_3378_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3348_, v_t_3349_, v_code_3375_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3380_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3379_);
lean_dec_ref_known(v___x_3378_, 1);
lean_inc_ref(v_a_3361_);
v___x_3380_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_3348_, v_a_3361_, v_a_3377_, v_a_3379_);
v_a_3363_ = v___x_3380_;
goto v___jp_3362_;
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
lean_dec(v_a_3377_);
lean_dec_ref(v_as_3351_);
lean_dec(v_i_3350_);
v_a_3381_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3378_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3378_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec_ref(v_as_3351_);
lean_dec(v_i_3350_);
v_a_3389_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3376_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3376_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
case 1:
{
lean_object* v_code_3397_; lean_object* v___x_3398_; 
v_code_3397_ = lean_ctor_get(v_a_3361_, 1);
lean_inc_ref(v_code_3397_);
v___x_3398_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3348_, v_t_3349_, v_code_3397_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3400_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___x_3398_, 1);
lean_inc_ref(v_a_3361_);
v___x_3400_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3361_, v_a_3399_);
v_a_3363_ = v___x_3400_;
goto v___jp_3362_;
}
else
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
lean_dec_ref(v_as_3351_);
lean_dec(v_i_3350_);
v_a_3401_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3398_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3398_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3401_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
default: 
{
lean_object* v_code_3409_; lean_object* v___x_3410_; 
v_code_3409_ = lean_ctor_get(v_a_3361_, 0);
lean_inc_ref(v_code_3409_);
v___x_3410_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3348_, v_t_3349_, v_code_3409_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; lean_object* v___x_3412_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3411_);
lean_dec_ref_known(v___x_3410_, 1);
lean_inc_ref(v_a_3361_);
v___x_3412_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3361_, v_a_3411_);
v_a_3363_ = v___x_3412_;
goto v___jp_3362_;
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec_ref(v_as_3351_);
lean_dec(v_i_3350_);
v_a_3413_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3410_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3410_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
}
v___jp_3362_:
{
size_t v___x_3364_; size_t v___x_3365_; uint8_t v___x_3366_; 
v___x_3364_ = lean_ptr_addr(v_a_3361_);
v___x_3365_ = lean_ptr_addr(v_a_3363_);
v___x_3366_ = lean_usize_dec_eq(v___x_3364_, v___x_3365_);
if (v___x_3366_ == 0)
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3367_ = lean_unsigned_to_nat(1u);
v___x_3368_ = lean_nat_add(v_i_3350_, v___x_3367_);
v___x_3369_ = lean_array_fset(v_as_3351_, v_i_3350_, v_a_3363_);
lean_dec(v_i_3350_);
v_i_3350_ = v___x_3368_;
v_as_3351_ = v___x_3369_;
goto _start;
}
else
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
lean_dec_ref(v_a_3363_);
v___x_3371_ = lean_unsigned_to_nat(1u);
v___x_3372_ = lean_nat_add(v_i_3350_, v___x_3371_);
lean_dec(v_i_3350_);
v_i_3350_ = v___x_3372_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp(uint8_t v_pu_3421_, uint8_t v_t_3422_, lean_object* v_code_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_){
_start:
{
switch(lean_obj_tag(v_code_3423_))
{
case 0:
{
lean_object* v_decl_3430_; lean_object* v_k_3431_; lean_object* v___x_3432_; 
v_decl_3430_ = lean_ctor_get(v_code_3423_, 0);
v_k_3431_ = lean_ctor_get(v_code_3423_, 1);
lean_inc_ref(v_decl_3430_);
v___x_3432_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_3421_, v_t_3422_, v_decl_3430_, v_a_3424_, v_a_3426_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3434_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_a_3433_);
lean_dec_ref_known(v___x_3432_, 1);
lean_inc_ref(v_k_3431_);
v___x_3434_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3421_, v_t_3422_, v_k_3431_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3472_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3437_ = v___x_3434_;
v_isShared_3438_ = v_isSharedCheck_3472_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3434_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3472_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
size_t v___x_3439_; size_t v___x_3440_; uint8_t v___x_3441_; 
v___x_3439_ = lean_ptr_addr(v_k_3431_);
v___x_3440_ = lean_ptr_addr(v_a_3435_);
v___x_3441_ = lean_usize_dec_eq(v___x_3439_, v___x_3440_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3451_; 
v_isSharedCheck_3451_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3451_ == 0)
{
lean_object* v_unused_3452_; lean_object* v_unused_3453_; 
v_unused_3452_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3452_);
v_unused_3453_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3453_);
v___x_3443_ = v_code_3423_;
v_isShared_3444_ = v_isSharedCheck_3451_;
goto v_resetjp_3442_;
}
else
{
lean_dec(v_code_3423_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3451_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3446_; 
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 1, v_a_3435_);
lean_ctor_set(v___x_3443_, 0, v_a_3433_);
v___x_3446_ = v___x_3443_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3433_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v_a_3435_);
v___x_3446_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3448_; 
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3446_);
v___x_3448_ = v___x_3437_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
else
{
size_t v___x_3454_; size_t v___x_3455_; uint8_t v___x_3456_; 
v___x_3454_ = lean_ptr_addr(v_decl_3430_);
v___x_3455_ = lean_ptr_addr(v_a_3433_);
v___x_3456_ = lean_usize_dec_eq(v___x_3454_, v___x_3455_);
if (v___x_3456_ == 0)
{
lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3466_; 
v_isSharedCheck_3466_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3466_ == 0)
{
lean_object* v_unused_3467_; lean_object* v_unused_3468_; 
v_unused_3467_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3467_);
v_unused_3468_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3468_);
v___x_3458_ = v_code_3423_;
v_isShared_3459_ = v_isSharedCheck_3466_;
goto v_resetjp_3457_;
}
else
{
lean_dec(v_code_3423_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3466_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 1, v_a_3435_);
lean_ctor_set(v___x_3458_, 0, v_a_3433_);
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3433_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_a_3435_);
v___x_3461_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
lean_object* v___x_3463_; 
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3461_);
v___x_3463_ = v___x_3437_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3461_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
else
{
lean_object* v___x_3470_; 
lean_dec(v_a_3435_);
lean_dec(v_a_3433_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v_code_3423_);
v___x_3470_ = v___x_3437_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_code_3423_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
}
else
{
lean_dec(v_a_3433_);
lean_dec_ref_known(v_code_3423_, 2);
return v___x_3434_;
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_dec_ref_known(v_code_3423_, 2);
v_a_3473_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3432_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3432_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
case 1:
{
lean_object* v_decl_3481_; lean_object* v_k_3482_; lean_object* v___x_3483_; 
v_decl_3481_ = lean_ctor_get(v_code_3423_, 0);
v_k_3482_ = lean_ctor_get(v_code_3423_, 1);
lean_inc_ref(v_decl_3481_);
v___x_3483_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3421_, v_t_3422_, v_decl_3481_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; lean_object* v___x_3485_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
lean_inc(v_a_3484_);
lean_dec_ref_known(v___x_3483_, 1);
lean_inc_ref(v_k_3482_);
v___x_3485_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3421_, v_t_3422_, v_k_3482_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3523_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3488_ = v___x_3485_;
v_isShared_3489_ = v_isSharedCheck_3523_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3485_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3523_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
size_t v___x_3490_; size_t v___x_3491_; uint8_t v___x_3492_; 
v___x_3490_ = lean_ptr_addr(v_k_3482_);
v___x_3491_ = lean_ptr_addr(v_a_3486_);
v___x_3492_ = lean_usize_dec_eq(v___x_3490_, v___x_3491_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3502_; 
v_isSharedCheck_3502_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3502_ == 0)
{
lean_object* v_unused_3503_; lean_object* v_unused_3504_; 
v_unused_3503_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3503_);
v_unused_3504_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3504_);
v___x_3494_ = v_code_3423_;
v_isShared_3495_ = v_isSharedCheck_3502_;
goto v_resetjp_3493_;
}
else
{
lean_dec(v_code_3423_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3502_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 1, v_a_3486_);
lean_ctor_set(v___x_3494_, 0, v_a_3484_);
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3484_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v_a_3486_);
v___x_3497_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
lean_object* v___x_3499_; 
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 0, v___x_3497_);
v___x_3499_ = v___x_3488_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3497_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
else
{
size_t v___x_3505_; size_t v___x_3506_; uint8_t v___x_3507_; 
v___x_3505_ = lean_ptr_addr(v_decl_3481_);
v___x_3506_ = lean_ptr_addr(v_a_3484_);
v___x_3507_ = lean_usize_dec_eq(v___x_3505_, v___x_3506_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3517_; 
v_isSharedCheck_3517_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3517_ == 0)
{
lean_object* v_unused_3518_; lean_object* v_unused_3519_; 
v_unused_3518_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3518_);
v_unused_3519_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3519_);
v___x_3509_ = v_code_3423_;
v_isShared_3510_ = v_isSharedCheck_3517_;
goto v_resetjp_3508_;
}
else
{
lean_dec(v_code_3423_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3517_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 1, v_a_3486_);
lean_ctor_set(v___x_3509_, 0, v_a_3484_);
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3484_);
lean_ctor_set(v_reuseFailAlloc_3516_, 1, v_a_3486_);
v___x_3512_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
lean_object* v___x_3514_; 
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 0, v___x_3512_);
v___x_3514_ = v___x_3488_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3512_);
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
else
{
lean_object* v___x_3521_; 
lean_dec(v_a_3486_);
lean_dec(v_a_3484_);
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 0, v_code_3423_);
v___x_3521_ = v___x_3488_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_code_3423_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
}
else
{
lean_dec(v_a_3484_);
lean_dec_ref_known(v_code_3423_, 2);
return v___x_3485_;
}
}
else
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
lean_dec_ref_known(v_code_3423_, 2);
v_a_3524_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___x_3483_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3483_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
if (v_isShared_3527_ == 0)
{
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3524_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
case 2:
{
lean_object* v_decl_3532_; lean_object* v_k_3533_; lean_object* v___x_3534_; 
v_decl_3532_ = lean_ctor_get(v_code_3423_, 0);
v_k_3533_ = lean_ctor_get(v_code_3423_, 1);
lean_inc_ref(v_decl_3532_);
v___x_3534_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3421_, v_t_3422_, v_decl_3532_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3536_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3535_);
lean_dec_ref_known(v___x_3534_, 1);
lean_inc_ref(v_k_3533_);
v___x_3536_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3421_, v_t_3422_, v_k_3533_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3574_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3539_ = v___x_3536_;
v_isShared_3540_ = v_isSharedCheck_3574_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3536_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3574_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
size_t v___x_3541_; size_t v___x_3542_; uint8_t v___x_3543_; 
v___x_3541_ = lean_ptr_addr(v_k_3533_);
v___x_3542_ = lean_ptr_addr(v_a_3537_);
v___x_3543_ = lean_usize_dec_eq(v___x_3541_, v___x_3542_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3553_; 
v_isSharedCheck_3553_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3553_ == 0)
{
lean_object* v_unused_3554_; lean_object* v_unused_3555_; 
v_unused_3554_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3554_);
v_unused_3555_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3555_);
v___x_3545_ = v_code_3423_;
v_isShared_3546_ = v_isSharedCheck_3553_;
goto v_resetjp_3544_;
}
else
{
lean_dec(v_code_3423_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3553_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 1, v_a_3537_);
lean_ctor_set(v___x_3545_, 0, v_a_3535_);
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3535_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_a_3537_);
v___x_3548_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
lean_object* v___x_3550_; 
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 0, v___x_3548_);
v___x_3550_ = v___x_3539_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3548_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
else
{
size_t v___x_3556_; size_t v___x_3557_; uint8_t v___x_3558_; 
v___x_3556_ = lean_ptr_addr(v_decl_3532_);
v___x_3557_ = lean_ptr_addr(v_a_3535_);
v___x_3558_ = lean_usize_dec_eq(v___x_3556_, v___x_3557_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3568_; 
v_isSharedCheck_3568_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3568_ == 0)
{
lean_object* v_unused_3569_; lean_object* v_unused_3570_; 
v_unused_3569_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3569_);
v_unused_3570_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3570_);
v___x_3560_ = v_code_3423_;
v_isShared_3561_ = v_isSharedCheck_3568_;
goto v_resetjp_3559_;
}
else
{
lean_dec(v_code_3423_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3568_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 1, v_a_3537_);
lean_ctor_set(v___x_3560_, 0, v_a_3535_);
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3535_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v_a_3537_);
v___x_3563_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
lean_object* v___x_3565_; 
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 0, v___x_3563_);
v___x_3565_ = v___x_3539_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v___x_3563_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
}
else
{
lean_object* v___x_3572_; 
lean_dec(v_a_3537_);
lean_dec(v_a_3535_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 0, v_code_3423_);
v___x_3572_ = v___x_3539_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_code_3423_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
}
else
{
lean_dec(v_a_3535_);
lean_dec_ref_known(v_code_3423_, 2);
return v___x_3536_;
}
}
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_dec_ref_known(v_code_3423_, 2);
v_a_3575_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3534_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3534_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3583_; lean_object* v_args_3584_; lean_object* v___x_3585_; 
v_fvarId_3583_ = lean_ctor_get(v_code_3423_, 0);
v_args_3584_ = lean_ctor_get(v_code_3423_, 1);
lean_inc(v_fvarId_3583_);
v___x_3585_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3424_, v_fvarId_3583_, v_t_3422_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_fvarId_3586_; lean_object* v___x_3587_; 
v_fvarId_3586_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_fvarId_3586_);
lean_dec_ref_known(v___x_3585_, 1);
lean_inc_ref(v_args_3584_);
v___x_3587_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_3421_, v_t_3422_, v_args_3584_, v_a_3424_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3613_; 
v_a_3588_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3590_ = v___x_3587_;
v_isShared_3591_ = v_isSharedCheck_3613_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3587_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3613_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
uint8_t v___y_3593_; uint8_t v___x_3609_; 
v___x_3609_ = l_Lean_instBEqFVarId_beq(v_fvarId_3583_, v_fvarId_3586_);
if (v___x_3609_ == 0)
{
v___y_3593_ = v___x_3609_;
goto v___jp_3592_;
}
else
{
size_t v___x_3610_; size_t v___x_3611_; uint8_t v___x_3612_; 
v___x_3610_ = lean_ptr_addr(v_args_3584_);
v___x_3611_ = lean_ptr_addr(v_a_3588_);
v___x_3612_ = lean_usize_dec_eq(v___x_3610_, v___x_3611_);
v___y_3593_ = v___x_3612_;
goto v___jp_3592_;
}
v___jp_3592_:
{
if (v___y_3593_ == 0)
{
lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3603_; 
v_isSharedCheck_3603_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3603_ == 0)
{
lean_object* v_unused_3604_; lean_object* v_unused_3605_; 
v_unused_3604_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3604_);
v_unused_3605_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3605_);
v___x_3595_ = v_code_3423_;
v_isShared_3596_ = v_isSharedCheck_3603_;
goto v_resetjp_3594_;
}
else
{
lean_dec(v_code_3423_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3603_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
if (v_isShared_3596_ == 0)
{
lean_ctor_set(v___x_3595_, 1, v_a_3588_);
lean_ctor_set(v___x_3595_, 0, v_fvarId_3586_);
v___x_3598_ = v___x_3595_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_fvarId_3586_);
lean_ctor_set(v_reuseFailAlloc_3602_, 1, v_a_3588_);
v___x_3598_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
lean_object* v___x_3600_; 
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 0, v___x_3598_);
v___x_3600_ = v___x_3590_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3598_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
else
{
lean_object* v___x_3607_; 
lean_dec(v_a_3588_);
lean_dec(v_fvarId_3586_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 0, v_code_3423_);
v___x_3607_ = v___x_3590_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_code_3423_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
lean_dec(v_fvarId_3586_);
lean_dec_ref_known(v_code_3423_, 2);
v_a_3614_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3616_ = v___x_3587_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3587_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
else
{
lean_object* v___x_3622_; 
lean_dec_ref_known(v_code_3423_, 2);
v___x_3622_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3421_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
return v___x_3622_;
}
}
case 4:
{
lean_object* v_cases_3623_; lean_object* v_typeName_3624_; lean_object* v_resultType_3625_; lean_object* v_discr_3626_; lean_object* v_alts_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3672_; 
v_cases_3623_ = lean_ctor_get(v_code_3423_, 0);
lean_inc_ref(v_cases_3623_);
v_typeName_3624_ = lean_ctor_get(v_cases_3623_, 0);
v_resultType_3625_ = lean_ctor_get(v_cases_3623_, 1);
v_discr_3626_ = lean_ctor_get(v_cases_3623_, 2);
v_alts_3627_ = lean_ctor_get(v_cases_3623_, 3);
v_isSharedCheck_3672_ = !lean_is_exclusive(v_cases_3623_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3629_ = v_cases_3623_;
v_isShared_3630_ = v_isSharedCheck_3672_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_alts_3627_);
lean_inc(v_discr_3626_);
lean_inc(v_resultType_3625_);
lean_inc(v_typeName_3624_);
lean_dec(v_cases_3623_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3672_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
lean_inc_ref(v_resultType_3625_);
v___x_3631_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3421_, v_a_3424_, v_t_3422_, v_resultType_3625_);
lean_inc(v_discr_3626_);
v___x_3632_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3424_, v_discr_3626_, v_t_3422_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_fvarId_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3670_; 
v_fvarId_3633_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3635_ = v___x_3632_;
v_isShared_3636_ = v_isSharedCheck_3670_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_fvarId_3633_);
lean_dec(v___x_3632_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3670_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3637_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3627_);
v___x_3638_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_3421_, v_t_3422_, v___x_3637_, v_alts_3627_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3661_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3641_ = v___x_3638_;
v_isShared_3642_ = v_isSharedCheck_3661_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3638_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3661_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
size_t v___x_3653_; size_t v___x_3654_; uint8_t v___x_3655_; 
v___x_3653_ = lean_ptr_addr(v_alts_3627_);
lean_dec_ref(v_alts_3627_);
v___x_3654_ = lean_ptr_addr(v_a_3639_);
v___x_3655_ = lean_usize_dec_eq(v___x_3653_, v___x_3654_);
if (v___x_3655_ == 0)
{
lean_dec(v_discr_3626_);
lean_dec_ref(v_resultType_3625_);
lean_dec_ref_known(v_code_3423_, 1);
goto v___jp_3643_;
}
else
{
size_t v___x_3656_; size_t v___x_3657_; uint8_t v___x_3658_; 
v___x_3656_ = lean_ptr_addr(v_resultType_3625_);
lean_dec_ref(v_resultType_3625_);
v___x_3657_ = lean_ptr_addr(v___x_3631_);
v___x_3658_ = lean_usize_dec_eq(v___x_3656_, v___x_3657_);
if (v___x_3658_ == 0)
{
lean_dec(v_discr_3626_);
lean_dec_ref_known(v_code_3423_, 1);
goto v___jp_3643_;
}
else
{
uint8_t v___x_3659_; 
v___x_3659_ = l_Lean_instBEqFVarId_beq(v_discr_3626_, v_fvarId_3633_);
lean_dec(v_discr_3626_);
if (v___x_3659_ == 0)
{
lean_dec_ref_known(v_code_3423_, 1);
goto v___jp_3643_;
}
else
{
lean_object* v___x_3660_; 
lean_del_object(v___x_3641_);
lean_dec(v_a_3639_);
lean_del_object(v___x_3635_);
lean_dec(v_fvarId_3633_);
lean_dec_ref(v___x_3631_);
lean_del_object(v___x_3629_);
lean_dec(v_typeName_3624_);
v___x_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3660_, 0, v_code_3423_);
return v___x_3660_;
}
}
}
v___jp_3643_:
{
lean_object* v___x_3645_; 
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 3, v_a_3639_);
lean_ctor_set(v___x_3629_, 2, v_fvarId_3633_);
lean_ctor_set(v___x_3629_, 1, v___x_3631_);
v___x_3645_ = v___x_3629_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_typeName_3624_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v___x_3631_);
lean_ctor_set(v_reuseFailAlloc_3652_, 2, v_fvarId_3633_);
lean_ctor_set(v_reuseFailAlloc_3652_, 3, v_a_3639_);
v___x_3645_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
lean_object* v___x_3647_; 
if (v_isShared_3636_ == 0)
{
lean_ctor_set_tag(v___x_3635_, 4);
lean_ctor_set(v___x_3635_, 0, v___x_3645_);
v___x_3647_ = v___x_3635_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3645_);
v___x_3647_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3649_; 
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 0, v___x_3647_);
v___x_3649_ = v___x_3641_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3647_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
}
}
else
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3669_; 
lean_del_object(v___x_3635_);
lean_dec(v_fvarId_3633_);
lean_dec_ref(v___x_3631_);
lean_del_object(v___x_3629_);
lean_dec_ref(v_alts_3627_);
lean_dec(v_discr_3626_);
lean_dec_ref(v_resultType_3625_);
lean_dec(v_typeName_3624_);
lean_dec_ref_known(v_code_3423_, 1);
v_a_3662_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3664_ = v___x_3638_;
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3638_);
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
lean_dec_ref(v___x_3631_);
lean_del_object(v___x_3629_);
lean_dec_ref(v_alts_3627_);
lean_dec(v_discr_3626_);
lean_dec_ref(v_resultType_3625_);
lean_dec(v_typeName_3624_);
lean_dec_ref_known(v_code_3423_, 1);
v___x_3671_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3421_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
return v___x_3671_;
}
}
}
case 5:
{
lean_object* v_fvarId_3673_; lean_object* v___x_3674_; 
v_fvarId_3673_ = lean_ctor_get(v_code_3423_, 0);
lean_inc(v_fvarId_3673_);
v___x_3674_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3424_, v_fvarId_3673_, v_t_3422_);
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
v_isSharedCheck_3689_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; 
v_unused_3690_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3690_);
v___x_3681_ = v_code_3423_;
v_isShared_3682_ = v_isSharedCheck_3689_;
goto v_resetjp_3680_;
}
else
{
lean_dec(v_code_3423_);
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
lean_ctor_set(v___x_3677_, 0, v_code_3423_);
v___x_3692_ = v___x_3677_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_code_3423_);
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
lean_dec_ref_known(v_code_3423_, 1);
v___x_3695_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3421_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
return v___x_3695_;
}
}
case 6:
{
lean_object* v_type_3696_; lean_object* v___x_3697_; size_t v___x_3698_; size_t v___x_3699_; uint8_t v___x_3700_; 
v_type_3696_ = lean_ctor_get(v_code_3423_, 0);
lean_inc_ref(v_type_3696_);
v___x_3697_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3421_, v_a_3424_, v_t_3422_, v_type_3696_);
v___x_3698_ = lean_ptr_addr(v_type_3696_);
v___x_3699_ = lean_ptr_addr(v___x_3697_);
v___x_3700_ = lean_usize_dec_eq(v___x_3698_, v___x_3699_);
if (v___x_3700_ == 0)
{
lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3708_; 
v_isSharedCheck_3708_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3708_ == 0)
{
lean_object* v_unused_3709_; 
v_unused_3709_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3709_);
v___x_3702_ = v_code_3423_;
v_isShared_3703_ = v_isSharedCheck_3708_;
goto v_resetjp_3701_;
}
else
{
lean_dec(v_code_3423_);
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
lean_ctor_set(v___x_3710_, 0, v_code_3423_);
return v___x_3710_;
}
}
case 7:
{
lean_object* v_fvarId_3711_; lean_object* v_i_3712_; lean_object* v_y_3713_; lean_object* v_k_3714_; lean_object* v___x_3715_; 
v_fvarId_3711_ = lean_ctor_get(v_code_3423_, 0);
v_i_3712_ = lean_ctor_get(v_code_3423_, 1);
v_y_3713_ = lean_ctor_get(v_code_3423_, 2);
v_k_3714_ = lean_ctor_get(v_code_3423_, 3);
lean_inc(v_fvarId_3711_);
v___x_3715_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3424_, v_fvarId_3711_, v_t_3422_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_fvarId_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v_fvarId_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_fvarId_3716_);
lean_dec_ref_known(v___x_3715_, 1);
lean_inc(v_y_3713_);
v___x_3717_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_3421_, v_a_3424_, v_y_3713_, v_t_3422_);
lean_inc_ref(v_k_3714_);
v___x_3718_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3421_, v_t_3422_, v_k_3714_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3792_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3721_ = v___x_3718_;
v_isShared_3722_ = v_isSharedCheck_3792_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3718_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3792_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
size_t v___x_3723_; size_t v___x_3724_; uint8_t v___x_3725_; 
v___x_3723_ = lean_ptr_addr(v_fvarId_3711_);
v___x_3724_ = lean_ptr_addr(v_fvarId_3716_);
v___x_3725_ = lean_usize_dec_eq(v___x_3723_, v___x_3724_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3735_; 
lean_inc(v_i_3712_);
v_isSharedCheck_3735_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3735_ == 0)
{
lean_object* v_unused_3736_; lean_object* v_unused_3737_; lean_object* v_unused_3738_; lean_object* v_unused_3739_; 
v_unused_3736_ = lean_ctor_get(v_code_3423_, 3);
lean_dec(v_unused_3736_);
v_unused_3737_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_3737_);
v_unused_3738_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3738_);
v_unused_3739_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3739_);
v___x_3727_ = v_code_3423_;
v_isShared_3728_ = v_isSharedCheck_3735_;
goto v_resetjp_3726_;
}
else
{
lean_dec(v_code_3423_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3735_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 3, v_a_3719_);
lean_ctor_set(v___x_3727_, 2, v___x_3717_);
lean_ctor_set(v___x_3727_, 0, v_fvarId_3716_);
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_fvarId_3716_);
lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_i_3712_);
lean_ctor_set(v_reuseFailAlloc_3734_, 2, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3734_, 3, v_a_3719_);
v___x_3730_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
lean_object* v___x_3732_; 
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v___x_3730_);
v___x_3732_ = v___x_3721_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3730_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
else
{
uint8_t v___x_3740_; 
v___x_3740_ = lean_nat_dec_eq(v_i_3712_, v_i_3712_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3750_; 
lean_inc(v_i_3712_);
v_isSharedCheck_3750_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3750_ == 0)
{
lean_object* v_unused_3751_; lean_object* v_unused_3752_; lean_object* v_unused_3753_; lean_object* v_unused_3754_; 
v_unused_3751_ = lean_ctor_get(v_code_3423_, 3);
lean_dec(v_unused_3751_);
v_unused_3752_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_3752_);
v_unused_3753_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3753_);
v_unused_3754_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3754_);
v___x_3742_ = v_code_3423_;
v_isShared_3743_ = v_isSharedCheck_3750_;
goto v_resetjp_3741_;
}
else
{
lean_dec(v_code_3423_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3750_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3745_; 
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 3, v_a_3719_);
lean_ctor_set(v___x_3742_, 2, v___x_3717_);
lean_ctor_set(v___x_3742_, 0, v_fvarId_3716_);
v___x_3745_ = v___x_3742_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_fvarId_3716_);
lean_ctor_set(v_reuseFailAlloc_3749_, 1, v_i_3712_);
lean_ctor_set(v_reuseFailAlloc_3749_, 2, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3749_, 3, v_a_3719_);
v___x_3745_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
lean_object* v___x_3747_; 
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v___x_3745_);
v___x_3747_ = v___x_3721_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
else
{
size_t v___x_3755_; size_t v___x_3756_; uint8_t v___x_3757_; 
v___x_3755_ = lean_ptr_addr(v_y_3713_);
v___x_3756_ = lean_ptr_addr(v___x_3717_);
v___x_3757_ = lean_usize_dec_eq(v___x_3755_, v___x_3756_);
if (v___x_3757_ == 0)
{
lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3767_; 
lean_inc(v_i_3712_);
v_isSharedCheck_3767_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3767_ == 0)
{
lean_object* v_unused_3768_; lean_object* v_unused_3769_; lean_object* v_unused_3770_; lean_object* v_unused_3771_; 
v_unused_3768_ = lean_ctor_get(v_code_3423_, 3);
lean_dec(v_unused_3768_);
v_unused_3769_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_3769_);
v_unused_3770_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3770_);
v_unused_3771_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3771_);
v___x_3759_ = v_code_3423_;
v_isShared_3760_ = v_isSharedCheck_3767_;
goto v_resetjp_3758_;
}
else
{
lean_dec(v_code_3423_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3767_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 3, v_a_3719_);
lean_ctor_set(v___x_3759_, 2, v___x_3717_);
lean_ctor_set(v___x_3759_, 0, v_fvarId_3716_);
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_fvarId_3716_);
lean_ctor_set(v_reuseFailAlloc_3766_, 1, v_i_3712_);
lean_ctor_set(v_reuseFailAlloc_3766_, 2, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3766_, 3, v_a_3719_);
v___x_3762_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
lean_object* v___x_3764_; 
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v___x_3762_);
v___x_3764_ = v___x_3721_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3762_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
else
{
size_t v___x_3772_; size_t v___x_3773_; uint8_t v___x_3774_; 
v___x_3772_ = lean_ptr_addr(v_k_3714_);
v___x_3773_ = lean_ptr_addr(v_a_3719_);
v___x_3774_ = lean_usize_dec_eq(v___x_3772_, v___x_3773_);
if (v___x_3774_ == 0)
{
lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3784_; 
lean_inc(v_i_3712_);
v_isSharedCheck_3784_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3784_ == 0)
{
lean_object* v_unused_3785_; lean_object* v_unused_3786_; lean_object* v_unused_3787_; lean_object* v_unused_3788_; 
v_unused_3785_ = lean_ctor_get(v_code_3423_, 3);
lean_dec(v_unused_3785_);
v_unused_3786_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_3786_);
v_unused_3787_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3787_);
v_unused_3788_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3788_);
v___x_3776_ = v_code_3423_;
v_isShared_3777_ = v_isSharedCheck_3784_;
goto v_resetjp_3775_;
}
else
{
lean_dec(v_code_3423_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3784_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3779_; 
if (v_isShared_3777_ == 0)
{
lean_ctor_set(v___x_3776_, 3, v_a_3719_);
lean_ctor_set(v___x_3776_, 2, v___x_3717_);
lean_ctor_set(v___x_3776_, 0, v_fvarId_3716_);
v___x_3779_ = v___x_3776_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_fvarId_3716_);
lean_ctor_set(v_reuseFailAlloc_3783_, 1, v_i_3712_);
lean_ctor_set(v_reuseFailAlloc_3783_, 2, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3783_, 3, v_a_3719_);
v___x_3779_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
lean_object* v___x_3781_; 
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v___x_3779_);
v___x_3781_ = v___x_3721_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3779_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
else
{
lean_object* v___x_3790_; 
lean_dec(v_a_3719_);
lean_dec(v___x_3717_);
lean_dec(v_fvarId_3716_);
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v_code_3423_);
v___x_3790_ = v___x_3721_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_code_3423_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
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
lean_dec_ref_known(v_code_3423_, 4);
return v___x_3718_;
}
}
else
{
lean_object* v___x_3793_; 
lean_dec_ref_known(v_code_3423_, 4);
v___x_3793_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3421_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
return v___x_3793_;
}
}
case 8:
{
lean_object* v_fvarId_3794_; lean_object* v_i_3795_; lean_object* v_y_3796_; lean_object* v_k_3797_; lean_object* v___x_3798_; 
v_fvarId_3794_ = lean_ctor_get(v_code_3423_, 0);
v_i_3795_ = lean_ctor_get(v_code_3423_, 1);
v_y_3796_ = lean_ctor_get(v_code_3423_, 2);
v_k_3797_ = lean_ctor_get(v_code_3423_, 3);
lean_inc(v_fvarId_3794_);
v___x_3798_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3424_, v_fvarId_3794_, v_t_3422_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v_fvarId_3799_; lean_object* v___x_3800_; 
v_fvarId_3799_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_fvarId_3799_);
lean_dec_ref_known(v___x_3798_, 1);
lean_inc(v_y_3796_);
v___x_3800_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3424_, v_y_3796_, v_t_3422_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v_fvarId_3801_; lean_object* v___x_3802_; 
v_fvarId_3801_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_fvarId_3801_);
lean_dec_ref_known(v___x_3800_, 1);
lean_inc_ref(v_k_3797_);
v___x_3802_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3421_, v_t_3422_, v_k_3797_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3876_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3805_ = v___x_3802_;
v_isShared_3806_ = v_isSharedCheck_3876_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3802_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3876_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
size_t v___x_3807_; size_t v___x_3808_; uint8_t v___x_3809_; 
v___x_3807_ = lean_ptr_addr(v_fvarId_3794_);
v___x_3808_ = lean_ptr_addr(v_fvarId_3799_);
v___x_3809_ = lean_usize_dec_eq(v___x_3807_, v___x_3808_);
if (v___x_3809_ == 0)
{
lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3819_; 
lean_inc(v_i_3795_);
v_isSharedCheck_3819_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3819_ == 0)
{
lean_object* v_unused_3820_; lean_object* v_unused_3821_; lean_object* v_unused_3822_; lean_object* v_unused_3823_; 
v_unused_3820_ = lean_ctor_get(v_code_3423_, 3);
lean_dec(v_unused_3820_);
v_unused_3821_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_3821_);
v_unused_3822_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3822_);
v_unused_3823_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3823_);
v___x_3811_ = v_code_3423_;
v_isShared_3812_ = v_isSharedCheck_3819_;
goto v_resetjp_3810_;
}
else
{
lean_dec(v_code_3423_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3819_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 3, v_a_3803_);
lean_ctor_set(v___x_3811_, 2, v_fvarId_3801_);
lean_ctor_set(v___x_3811_, 0, v_fvarId_3799_);
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_fvarId_3799_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v_i_3795_);
lean_ctor_set(v_reuseFailAlloc_3818_, 2, v_fvarId_3801_);
lean_ctor_set(v_reuseFailAlloc_3818_, 3, v_a_3803_);
v___x_3814_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
lean_object* v___x_3816_; 
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 0, v___x_3814_);
v___x_3816_ = v___x_3805_;
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
uint8_t v___x_3824_; 
v___x_3824_ = lean_nat_dec_eq(v_i_3795_, v_i_3795_);
if (v___x_3824_ == 0)
{
lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3834_; 
lean_inc(v_i_3795_);
v_isSharedCheck_3834_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3834_ == 0)
{
lean_object* v_unused_3835_; lean_object* v_unused_3836_; lean_object* v_unused_3837_; lean_object* v_unused_3838_; 
v_unused_3835_ = lean_ctor_get(v_code_3423_, 3);
lean_dec(v_unused_3835_);
v_unused_3836_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_3836_);
v_unused_3837_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3837_);
v_unused_3838_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3838_);
v___x_3826_ = v_code_3423_;
v_isShared_3827_ = v_isSharedCheck_3834_;
goto v_resetjp_3825_;
}
else
{
lean_dec(v_code_3423_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3834_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 3, v_a_3803_);
lean_ctor_set(v___x_3826_, 2, v_fvarId_3801_);
lean_ctor_set(v___x_3826_, 0, v_fvarId_3799_);
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_fvarId_3799_);
lean_ctor_set(v_reuseFailAlloc_3833_, 1, v_i_3795_);
lean_ctor_set(v_reuseFailAlloc_3833_, 2, v_fvarId_3801_);
lean_ctor_set(v_reuseFailAlloc_3833_, 3, v_a_3803_);
v___x_3829_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
lean_object* v___x_3831_; 
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 0, v___x_3829_);
v___x_3831_ = v___x_3805_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3829_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
else
{
size_t v___x_3839_; size_t v___x_3840_; uint8_t v___x_3841_; 
v___x_3839_ = lean_ptr_addr(v_y_3796_);
v___x_3840_ = lean_ptr_addr(v_fvarId_3801_);
v___x_3841_ = lean_usize_dec_eq(v___x_3839_, v___x_3840_);
if (v___x_3841_ == 0)
{
lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3851_; 
lean_inc(v_i_3795_);
v_isSharedCheck_3851_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3851_ == 0)
{
lean_object* v_unused_3852_; lean_object* v_unused_3853_; lean_object* v_unused_3854_; lean_object* v_unused_3855_; 
v_unused_3852_ = lean_ctor_get(v_code_3423_, 3);
lean_dec(v_unused_3852_);
v_unused_3853_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_3853_);
v_unused_3854_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3854_);
v_unused_3855_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3855_);
v___x_3843_ = v_code_3423_;
v_isShared_3844_ = v_isSharedCheck_3851_;
goto v_resetjp_3842_;
}
else
{
lean_dec(v_code_3423_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3851_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 3, v_a_3803_);
lean_ctor_set(v___x_3843_, 2, v_fvarId_3801_);
lean_ctor_set(v___x_3843_, 0, v_fvarId_3799_);
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_fvarId_3799_);
lean_ctor_set(v_reuseFailAlloc_3850_, 1, v_i_3795_);
lean_ctor_set(v_reuseFailAlloc_3850_, 2, v_fvarId_3801_);
lean_ctor_set(v_reuseFailAlloc_3850_, 3, v_a_3803_);
v___x_3846_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
lean_object* v___x_3848_; 
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 0, v___x_3846_);
v___x_3848_ = v___x_3805_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3846_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
}
else
{
size_t v___x_3856_; size_t v___x_3857_; uint8_t v___x_3858_; 
v___x_3856_ = lean_ptr_addr(v_k_3797_);
v___x_3857_ = lean_ptr_addr(v_a_3803_);
v___x_3858_ = lean_usize_dec_eq(v___x_3856_, v___x_3857_);
if (v___x_3858_ == 0)
{
lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3868_; 
lean_inc(v_i_3795_);
v_isSharedCheck_3868_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3868_ == 0)
{
lean_object* v_unused_3869_; lean_object* v_unused_3870_; lean_object* v_unused_3871_; lean_object* v_unused_3872_; 
v_unused_3869_ = lean_ctor_get(v_code_3423_, 3);
lean_dec(v_unused_3869_);
v_unused_3870_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_3870_);
v_unused_3871_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3871_);
v_unused_3872_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3872_);
v___x_3860_ = v_code_3423_;
v_isShared_3861_ = v_isSharedCheck_3868_;
goto v_resetjp_3859_;
}
else
{
lean_dec(v_code_3423_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3868_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 3, v_a_3803_);
lean_ctor_set(v___x_3860_, 2, v_fvarId_3801_);
lean_ctor_set(v___x_3860_, 0, v_fvarId_3799_);
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_fvarId_3799_);
lean_ctor_set(v_reuseFailAlloc_3867_, 1, v_i_3795_);
lean_ctor_set(v_reuseFailAlloc_3867_, 2, v_fvarId_3801_);
lean_ctor_set(v_reuseFailAlloc_3867_, 3, v_a_3803_);
v___x_3863_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3865_; 
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 0, v___x_3863_);
v___x_3865_ = v___x_3805_;
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
else
{
lean_object* v___x_3874_; 
lean_dec(v_a_3803_);
lean_dec(v_fvarId_3801_);
lean_dec(v_fvarId_3799_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 0, v_code_3423_);
v___x_3874_ = v___x_3805_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_code_3423_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_3801_);
lean_dec(v_fvarId_3799_);
lean_dec_ref_known(v_code_3423_, 4);
return v___x_3802_;
}
}
else
{
lean_object* v___x_3877_; 
lean_dec(v_fvarId_3799_);
lean_dec_ref_known(v_code_3423_, 4);
v___x_3877_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3421_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
return v___x_3877_;
}
}
else
{
lean_object* v___x_3878_; 
lean_dec_ref_known(v_code_3423_, 4);
v___x_3878_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3421_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
return v___x_3878_;
}
}
case 9:
{
lean_object* v_fvarId_3879_; lean_object* v_i_3880_; lean_object* v_offset_3881_; lean_object* v_y_3882_; lean_object* v_ty_3883_; lean_object* v_k_3884_; lean_object* v___x_3885_; 
v_fvarId_3879_ = lean_ctor_get(v_code_3423_, 0);
v_i_3880_ = lean_ctor_get(v_code_3423_, 1);
v_offset_3881_ = lean_ctor_get(v_code_3423_, 2);
v_y_3882_ = lean_ctor_get(v_code_3423_, 3);
v_ty_3883_ = lean_ctor_get(v_code_3423_, 4);
v_k_3884_ = lean_ctor_get(v_code_3423_, 5);
lean_inc(v_fvarId_3879_);
v___x_3885_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3424_, v_fvarId_3879_, v_t_3422_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_fvarId_3886_; lean_object* v___x_3887_; 
v_fvarId_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_fvarId_3886_);
lean_dec_ref_known(v___x_3885_, 1);
lean_inc(v_y_3882_);
v___x_3887_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3424_, v_y_3882_, v_t_3422_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_fvarId_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
v_fvarId_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_fvarId_3888_);
lean_dec_ref_known(v___x_3887_, 1);
lean_inc_ref(v_ty_3883_);
v___x_3889_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3421_, v_a_3424_, v_t_3422_, v_ty_3883_);
lean_inc_ref(v_k_3884_);
v___x_3890_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3421_, v_t_3422_, v_k_3884_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_4008_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_3893_ = v___x_3890_;
v_isShared_3894_ = v_isSharedCheck_4008_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3890_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_4008_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
size_t v___x_3895_; size_t v___x_3896_; uint8_t v___x_3897_; 
v___x_3895_ = lean_ptr_addr(v_fvarId_3879_);
v___x_3896_ = lean_ptr_addr(v_fvarId_3886_);
v___x_3897_ = lean_usize_dec_eq(v___x_3895_, v___x_3896_);
if (v___x_3897_ == 0)
{
lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3907_; 
lean_inc(v_offset_3881_);
lean_inc(v_i_3880_);
v_isSharedCheck_3907_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3907_ == 0)
{
lean_object* v_unused_3908_; lean_object* v_unused_3909_; lean_object* v_unused_3910_; lean_object* v_unused_3911_; lean_object* v_unused_3912_; lean_object* v_unused_3913_; 
v_unused_3908_ = lean_ctor_get(v_code_3423_, 5);
lean_dec(v_unused_3908_);
v_unused_3909_ = lean_ctor_get(v_code_3423_, 4);
lean_dec(v_unused_3909_);
v_unused_3910_ = lean_ctor_get(v_code_3423_, 3);
lean_dec(v_unused_3910_);
v_unused_3911_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_3911_);
v_unused_3912_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3912_);
v_unused_3913_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3913_);
v___x_3899_ = v_code_3423_;
v_isShared_3900_ = v_isSharedCheck_3907_;
goto v_resetjp_3898_;
}
else
{
lean_dec(v_code_3423_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3907_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 5, v_a_3891_);
lean_ctor_set(v___x_3899_, 4, v___x_3889_);
lean_ctor_set(v___x_3899_, 3, v_fvarId_3888_);
lean_ctor_set(v___x_3899_, 0, v_fvarId_3886_);
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_fvarId_3886_);
lean_ctor_set(v_reuseFailAlloc_3906_, 1, v_i_3880_);
lean_ctor_set(v_reuseFailAlloc_3906_, 2, v_offset_3881_);
lean_ctor_set(v_reuseFailAlloc_3906_, 3, v_fvarId_3888_);
lean_ctor_set(v_reuseFailAlloc_3906_, 4, v___x_3889_);
lean_ctor_set(v_reuseFailAlloc_3906_, 5, v_a_3891_);
v___x_3902_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
lean_object* v___x_3904_; 
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 0, v___x_3902_);
v___x_3904_ = v___x_3893_;
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
uint8_t v___x_3914_; 
v___x_3914_ = lean_nat_dec_eq(v_i_3880_, v_i_3880_);
if (v___x_3914_ == 0)
{
lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3924_; 
lean_inc(v_offset_3881_);
lean_inc(v_i_3880_);
v_isSharedCheck_3924_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3924_ == 0)
{
lean_object* v_unused_3925_; lean_object* v_unused_3926_; lean_object* v_unused_3927_; lean_object* v_unused_3928_; lean_object* v_unused_3929_; lean_object* v_unused_3930_; 
v_unused_3925_ = lean_ctor_get(v_code_3423_, 5);
lean_dec(v_unused_3925_);
v_unused_3926_ = lean_ctor_get(v_code_3423_, 4);
lean_dec(v_unused_3926_);
v_unused_3927_ = lean_ctor_get(v_code_3423_, 3);
lean_dec(v_unused_3927_);
v_unused_3928_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_3928_);
v_unused_3929_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3929_);
v_unused_3930_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3930_);
v___x_3916_ = v_code_3423_;
v_isShared_3917_ = v_isSharedCheck_3924_;
goto v_resetjp_3915_;
}
else
{
lean_dec(v_code_3423_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3924_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 5, v_a_3891_);
lean_ctor_set(v___x_3916_, 4, v___x_3889_);
lean_ctor_set(v___x_3916_, 3, v_fvarId_3888_);
lean_ctor_set(v___x_3916_, 0, v_fvarId_3886_);
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_fvarId_3886_);
lean_ctor_set(v_reuseFailAlloc_3923_, 1, v_i_3880_);
lean_ctor_set(v_reuseFailAlloc_3923_, 2, v_offset_3881_);
lean_ctor_set(v_reuseFailAlloc_3923_, 3, v_fvarId_3888_);
lean_ctor_set(v_reuseFailAlloc_3923_, 4, v___x_3889_);
lean_ctor_set(v_reuseFailAlloc_3923_, 5, v_a_3891_);
v___x_3919_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
lean_object* v___x_3921_; 
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 0, v___x_3919_);
v___x_3921_ = v___x_3893_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3919_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
else
{
uint8_t v___x_3931_; 
v___x_3931_ = lean_nat_dec_eq(v_offset_3881_, v_offset_3881_);
if (v___x_3931_ == 0)
{
lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3941_; 
lean_inc(v_offset_3881_);
lean_inc(v_i_3880_);
v_isSharedCheck_3941_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3941_ == 0)
{
lean_object* v_unused_3942_; lean_object* v_unused_3943_; lean_object* v_unused_3944_; lean_object* v_unused_3945_; lean_object* v_unused_3946_; lean_object* v_unused_3947_; 
v_unused_3942_ = lean_ctor_get(v_code_3423_, 5);
lean_dec(v_unused_3942_);
v_unused_3943_ = lean_ctor_get(v_code_3423_, 4);
lean_dec(v_unused_3943_);
v_unused_3944_ = lean_ctor_get(v_code_3423_, 3);
lean_dec(v_unused_3944_);
v_unused_3945_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_3945_);
v_unused_3946_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3946_);
v_unused_3947_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3947_);
v___x_3933_ = v_code_3423_;
v_isShared_3934_ = v_isSharedCheck_3941_;
goto v_resetjp_3932_;
}
else
{
lean_dec(v_code_3423_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3941_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3936_; 
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 5, v_a_3891_);
lean_ctor_set(v___x_3933_, 4, v___x_3889_);
lean_ctor_set(v___x_3933_, 3, v_fvarId_3888_);
lean_ctor_set(v___x_3933_, 0, v_fvarId_3886_);
v___x_3936_ = v___x_3933_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_fvarId_3886_);
lean_ctor_set(v_reuseFailAlloc_3940_, 1, v_i_3880_);
lean_ctor_set(v_reuseFailAlloc_3940_, 2, v_offset_3881_);
lean_ctor_set(v_reuseFailAlloc_3940_, 3, v_fvarId_3888_);
lean_ctor_set(v_reuseFailAlloc_3940_, 4, v___x_3889_);
lean_ctor_set(v_reuseFailAlloc_3940_, 5, v_a_3891_);
v___x_3936_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
lean_object* v___x_3938_; 
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 0, v___x_3936_);
v___x_3938_ = v___x_3893_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v___x_3936_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
else
{
size_t v___x_3948_; size_t v___x_3949_; uint8_t v___x_3950_; 
v___x_3948_ = lean_ptr_addr(v_y_3882_);
v___x_3949_ = lean_ptr_addr(v_fvarId_3888_);
v___x_3950_ = lean_usize_dec_eq(v___x_3948_, v___x_3949_);
if (v___x_3950_ == 0)
{
lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3960_; 
lean_inc(v_offset_3881_);
lean_inc(v_i_3880_);
v_isSharedCheck_3960_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3960_ == 0)
{
lean_object* v_unused_3961_; lean_object* v_unused_3962_; lean_object* v_unused_3963_; lean_object* v_unused_3964_; lean_object* v_unused_3965_; lean_object* v_unused_3966_; 
v_unused_3961_ = lean_ctor_get(v_code_3423_, 5);
lean_dec(v_unused_3961_);
v_unused_3962_ = lean_ctor_get(v_code_3423_, 4);
lean_dec(v_unused_3962_);
v_unused_3963_ = lean_ctor_get(v_code_3423_, 3);
lean_dec(v_unused_3963_);
v_unused_3964_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_3964_);
v_unused_3965_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3965_);
v_unused_3966_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3966_);
v___x_3952_ = v_code_3423_;
v_isShared_3953_ = v_isSharedCheck_3960_;
goto v_resetjp_3951_;
}
else
{
lean_dec(v_code_3423_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3960_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3955_; 
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 5, v_a_3891_);
lean_ctor_set(v___x_3952_, 4, v___x_3889_);
lean_ctor_set(v___x_3952_, 3, v_fvarId_3888_);
lean_ctor_set(v___x_3952_, 0, v_fvarId_3886_);
v___x_3955_ = v___x_3952_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_fvarId_3886_);
lean_ctor_set(v_reuseFailAlloc_3959_, 1, v_i_3880_);
lean_ctor_set(v_reuseFailAlloc_3959_, 2, v_offset_3881_);
lean_ctor_set(v_reuseFailAlloc_3959_, 3, v_fvarId_3888_);
lean_ctor_set(v_reuseFailAlloc_3959_, 4, v___x_3889_);
lean_ctor_set(v_reuseFailAlloc_3959_, 5, v_a_3891_);
v___x_3955_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
lean_object* v___x_3957_; 
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 0, v___x_3955_);
v___x_3957_ = v___x_3893_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3955_);
v___x_3957_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
return v___x_3957_;
}
}
}
}
else
{
size_t v___x_3967_; size_t v___x_3968_; uint8_t v___x_3969_; 
v___x_3967_ = lean_ptr_addr(v_ty_3883_);
v___x_3968_ = lean_ptr_addr(v___x_3889_);
v___x_3969_ = lean_usize_dec_eq(v___x_3967_, v___x_3968_);
if (v___x_3969_ == 0)
{
lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3979_; 
lean_inc(v_offset_3881_);
lean_inc(v_i_3880_);
v_isSharedCheck_3979_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3979_ == 0)
{
lean_object* v_unused_3980_; lean_object* v_unused_3981_; lean_object* v_unused_3982_; lean_object* v_unused_3983_; lean_object* v_unused_3984_; lean_object* v_unused_3985_; 
v_unused_3980_ = lean_ctor_get(v_code_3423_, 5);
lean_dec(v_unused_3980_);
v_unused_3981_ = lean_ctor_get(v_code_3423_, 4);
lean_dec(v_unused_3981_);
v_unused_3982_ = lean_ctor_get(v_code_3423_, 3);
lean_dec(v_unused_3982_);
v_unused_3983_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_3983_);
v_unused_3984_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_3984_);
v_unused_3985_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_3985_);
v___x_3971_ = v_code_3423_;
v_isShared_3972_ = v_isSharedCheck_3979_;
goto v_resetjp_3970_;
}
else
{
lean_dec(v_code_3423_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3979_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3974_; 
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 5, v_a_3891_);
lean_ctor_set(v___x_3971_, 4, v___x_3889_);
lean_ctor_set(v___x_3971_, 3, v_fvarId_3888_);
lean_ctor_set(v___x_3971_, 0, v_fvarId_3886_);
v___x_3974_ = v___x_3971_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_fvarId_3886_);
lean_ctor_set(v_reuseFailAlloc_3978_, 1, v_i_3880_);
lean_ctor_set(v_reuseFailAlloc_3978_, 2, v_offset_3881_);
lean_ctor_set(v_reuseFailAlloc_3978_, 3, v_fvarId_3888_);
lean_ctor_set(v_reuseFailAlloc_3978_, 4, v___x_3889_);
lean_ctor_set(v_reuseFailAlloc_3978_, 5, v_a_3891_);
v___x_3974_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
lean_object* v___x_3976_; 
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 0, v___x_3974_);
v___x_3976_ = v___x_3893_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3974_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
else
{
size_t v___x_3986_; size_t v___x_3987_; uint8_t v___x_3988_; 
v___x_3986_ = lean_ptr_addr(v_k_3884_);
v___x_3987_ = lean_ptr_addr(v_a_3891_);
v___x_3988_ = lean_usize_dec_eq(v___x_3986_, v___x_3987_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3998_; 
lean_inc(v_offset_3881_);
lean_inc(v_i_3880_);
v_isSharedCheck_3998_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_3998_ == 0)
{
lean_object* v_unused_3999_; lean_object* v_unused_4000_; lean_object* v_unused_4001_; lean_object* v_unused_4002_; lean_object* v_unused_4003_; lean_object* v_unused_4004_; 
v_unused_3999_ = lean_ctor_get(v_code_3423_, 5);
lean_dec(v_unused_3999_);
v_unused_4000_ = lean_ctor_get(v_code_3423_, 4);
lean_dec(v_unused_4000_);
v_unused_4001_ = lean_ctor_get(v_code_3423_, 3);
lean_dec(v_unused_4001_);
v_unused_4002_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_4002_);
v_unused_4003_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_4003_);
v_unused_4004_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_4004_);
v___x_3990_ = v_code_3423_;
v_isShared_3991_ = v_isSharedCheck_3998_;
goto v_resetjp_3989_;
}
else
{
lean_dec(v_code_3423_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3998_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 5, v_a_3891_);
lean_ctor_set(v___x_3990_, 4, v___x_3889_);
lean_ctor_set(v___x_3990_, 3, v_fvarId_3888_);
lean_ctor_set(v___x_3990_, 0, v_fvarId_3886_);
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_fvarId_3886_);
lean_ctor_set(v_reuseFailAlloc_3997_, 1, v_i_3880_);
lean_ctor_set(v_reuseFailAlloc_3997_, 2, v_offset_3881_);
lean_ctor_set(v_reuseFailAlloc_3997_, 3, v_fvarId_3888_);
lean_ctor_set(v_reuseFailAlloc_3997_, 4, v___x_3889_);
lean_ctor_set(v_reuseFailAlloc_3997_, 5, v_a_3891_);
v___x_3993_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
lean_object* v___x_3995_; 
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 0, v___x_3993_);
v___x_3995_ = v___x_3893_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v___x_3993_);
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
else
{
lean_object* v___x_4006_; 
lean_dec(v_a_3891_);
lean_dec_ref(v___x_3889_);
lean_dec(v_fvarId_3888_);
lean_dec(v_fvarId_3886_);
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 0, v_code_3423_);
v___x_4006_ = v___x_3893_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_code_3423_);
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
}
}
}
else
{
lean_dec_ref(v___x_3889_);
lean_dec(v_fvarId_3888_);
lean_dec(v_fvarId_3886_);
lean_dec_ref_known(v_code_3423_, 6);
return v___x_3890_;
}
}
else
{
lean_object* v___x_4009_; 
lean_dec(v_fvarId_3886_);
lean_dec_ref_known(v_code_3423_, 6);
v___x_4009_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3421_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
return v___x_4009_;
}
}
else
{
lean_object* v___x_4010_; 
lean_dec_ref_known(v_code_3423_, 6);
v___x_4010_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3421_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
return v___x_4010_;
}
}
case 10:
{
lean_object* v_fvarId_4011_; lean_object* v_cidx_4012_; lean_object* v_k_4013_; lean_object* v___x_4014_; 
v_fvarId_4011_ = lean_ctor_get(v_code_3423_, 0);
v_cidx_4012_ = lean_ctor_get(v_code_3423_, 1);
v_k_4013_ = lean_ctor_get(v_code_3423_, 2);
lean_inc(v_fvarId_4011_);
v___x_4014_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3424_, v_fvarId_4011_, v_t_3422_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v_fvarId_4015_; lean_object* v___x_4016_; 
v_fvarId_4015_ = lean_ctor_get(v___x_4014_, 0);
lean_inc(v_fvarId_4015_);
lean_dec_ref_known(v___x_4014_, 1);
lean_inc_ref(v_k_4013_);
v___x_4016_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3421_, v_t_3422_, v_k_4013_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4070_; 
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4019_ = v___x_4016_;
v_isShared_4020_ = v_isSharedCheck_4070_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_4016_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4070_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
size_t v___x_4021_; size_t v___x_4022_; uint8_t v___x_4023_; 
v___x_4021_ = lean_ptr_addr(v_fvarId_4011_);
v___x_4022_ = lean_ptr_addr(v_fvarId_4015_);
v___x_4023_ = lean_usize_dec_eq(v___x_4021_, v___x_4022_);
if (v___x_4023_ == 0)
{
lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4033_; 
lean_inc(v_cidx_4012_);
v_isSharedCheck_4033_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_4033_ == 0)
{
lean_object* v_unused_4034_; lean_object* v_unused_4035_; lean_object* v_unused_4036_; 
v_unused_4034_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_4034_);
v_unused_4035_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_4035_);
v_unused_4036_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_4036_);
v___x_4025_ = v_code_3423_;
v_isShared_4026_ = v_isSharedCheck_4033_;
goto v_resetjp_4024_;
}
else
{
lean_dec(v_code_3423_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4033_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4028_; 
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 2, v_a_4017_);
lean_ctor_set(v___x_4025_, 0, v_fvarId_4015_);
v___x_4028_ = v___x_4025_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v_fvarId_4015_);
lean_ctor_set(v_reuseFailAlloc_4032_, 1, v_cidx_4012_);
lean_ctor_set(v_reuseFailAlloc_4032_, 2, v_a_4017_);
v___x_4028_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
lean_object* v___x_4030_; 
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 0, v___x_4028_);
v___x_4030_ = v___x_4019_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4028_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
else
{
uint8_t v___x_4037_; 
v___x_4037_ = lean_nat_dec_eq(v_cidx_4012_, v_cidx_4012_);
if (v___x_4037_ == 0)
{
lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4047_; 
lean_inc(v_cidx_4012_);
v_isSharedCheck_4047_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_4047_ == 0)
{
lean_object* v_unused_4048_; lean_object* v_unused_4049_; lean_object* v_unused_4050_; 
v_unused_4048_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_4048_);
v_unused_4049_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_4049_);
v_unused_4050_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_4050_);
v___x_4039_ = v_code_3423_;
v_isShared_4040_ = v_isSharedCheck_4047_;
goto v_resetjp_4038_;
}
else
{
lean_dec(v_code_3423_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4047_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 2, v_a_4017_);
lean_ctor_set(v___x_4039_, 0, v_fvarId_4015_);
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_fvarId_4015_);
lean_ctor_set(v_reuseFailAlloc_4046_, 1, v_cidx_4012_);
lean_ctor_set(v_reuseFailAlloc_4046_, 2, v_a_4017_);
v___x_4042_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
lean_object* v___x_4044_; 
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 0, v___x_4042_);
v___x_4044_ = v___x_4019_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4042_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
}
else
{
size_t v___x_4051_; size_t v___x_4052_; uint8_t v___x_4053_; 
v___x_4051_ = lean_ptr_addr(v_k_4013_);
v___x_4052_ = lean_ptr_addr(v_a_4017_);
v___x_4053_ = lean_usize_dec_eq(v___x_4051_, v___x_4052_);
if (v___x_4053_ == 0)
{
lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4063_; 
lean_inc(v_cidx_4012_);
v_isSharedCheck_4063_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_4063_ == 0)
{
lean_object* v_unused_4064_; lean_object* v_unused_4065_; lean_object* v_unused_4066_; 
v_unused_4064_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_4064_);
v_unused_4065_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_4065_);
v_unused_4066_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_4066_);
v___x_4055_ = v_code_3423_;
v_isShared_4056_ = v_isSharedCheck_4063_;
goto v_resetjp_4054_;
}
else
{
lean_dec(v_code_3423_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4063_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4058_; 
if (v_isShared_4056_ == 0)
{
lean_ctor_set(v___x_4055_, 2, v_a_4017_);
lean_ctor_set(v___x_4055_, 0, v_fvarId_4015_);
v___x_4058_ = v___x_4055_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_fvarId_4015_);
lean_ctor_set(v_reuseFailAlloc_4062_, 1, v_cidx_4012_);
lean_ctor_set(v_reuseFailAlloc_4062_, 2, v_a_4017_);
v___x_4058_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
lean_object* v___x_4060_; 
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 0, v___x_4058_);
v___x_4060_ = v___x_4019_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v___x_4058_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
else
{
lean_object* v___x_4068_; 
lean_dec(v_a_4017_);
lean_dec(v_fvarId_4015_);
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 0, v_code_3423_);
v___x_4068_ = v___x_4019_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_code_3423_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4015_);
lean_dec_ref_known(v_code_3423_, 3);
return v___x_4016_;
}
}
else
{
lean_object* v___x_4071_; 
lean_dec_ref_known(v_code_3423_, 3);
v___x_4071_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3421_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
return v___x_4071_;
}
}
case 11:
{
lean_object* v_fvarId_4072_; lean_object* v_n_4073_; uint8_t v_check_4074_; uint8_t v_persistent_4075_; lean_object* v_k_4076_; lean_object* v___x_4077_; 
v_fvarId_4072_ = lean_ctor_get(v_code_3423_, 0);
v_n_4073_ = lean_ctor_get(v_code_3423_, 1);
v_check_4074_ = lean_ctor_get_uint8(v_code_3423_, sizeof(void*)*3);
v_persistent_4075_ = lean_ctor_get_uint8(v_code_3423_, sizeof(void*)*3 + 1);
v_k_4076_ = lean_ctor_get(v_code_3423_, 2);
lean_inc(v_fvarId_4072_);
v___x_4077_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3424_, v_fvarId_4072_, v_t_3422_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_fvarId_4078_; lean_object* v___x_4079_; 
v_fvarId_4078_ = lean_ctor_get(v___x_4077_, 0);
lean_inc(v_fvarId_4078_);
lean_dec_ref_known(v___x_4077_, 1);
lean_inc_ref(v_k_4076_);
v___x_4079_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3421_, v_t_3422_, v_k_4076_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4133_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4082_ = v___x_4079_;
v_isShared_4083_ = v_isSharedCheck_4133_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_a_4080_);
lean_dec(v___x_4079_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4133_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
size_t v___x_4084_; size_t v___x_4085_; uint8_t v___x_4086_; 
v___x_4084_ = lean_ptr_addr(v_fvarId_4072_);
v___x_4085_ = lean_ptr_addr(v_fvarId_4078_);
v___x_4086_ = lean_usize_dec_eq(v___x_4084_, v___x_4085_);
if (v___x_4086_ == 0)
{
lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4096_; 
lean_inc(v_n_4073_);
v_isSharedCheck_4096_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_4096_ == 0)
{
lean_object* v_unused_4097_; lean_object* v_unused_4098_; lean_object* v_unused_4099_; 
v_unused_4097_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_4097_);
v_unused_4098_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_4098_);
v_unused_4099_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_4099_);
v___x_4088_ = v_code_3423_;
v_isShared_4089_ = v_isSharedCheck_4096_;
goto v_resetjp_4087_;
}
else
{
lean_dec(v_code_3423_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4096_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4091_; 
if (v_isShared_4089_ == 0)
{
lean_ctor_set(v___x_4088_, 2, v_a_4080_);
lean_ctor_set(v___x_4088_, 0, v_fvarId_4078_);
v___x_4091_ = v___x_4088_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_fvarId_4078_);
lean_ctor_set(v_reuseFailAlloc_4095_, 1, v_n_4073_);
lean_ctor_set(v_reuseFailAlloc_4095_, 2, v_a_4080_);
lean_ctor_set_uint8(v_reuseFailAlloc_4095_, sizeof(void*)*3, v_check_4074_);
lean_ctor_set_uint8(v_reuseFailAlloc_4095_, sizeof(void*)*3 + 1, v_persistent_4075_);
v___x_4091_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
lean_object* v___x_4093_; 
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 0, v___x_4091_);
v___x_4093_ = v___x_4082_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v___x_4091_);
v___x_4093_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
return v___x_4093_;
}
}
}
}
else
{
uint8_t v___x_4100_; 
v___x_4100_ = lean_nat_dec_eq(v_n_4073_, v_n_4073_);
if (v___x_4100_ == 0)
{
lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4110_; 
lean_inc(v_n_4073_);
v_isSharedCheck_4110_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_4110_ == 0)
{
lean_object* v_unused_4111_; lean_object* v_unused_4112_; lean_object* v_unused_4113_; 
v_unused_4111_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_4111_);
v_unused_4112_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_4112_);
v_unused_4113_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_4113_);
v___x_4102_ = v_code_3423_;
v_isShared_4103_ = v_isSharedCheck_4110_;
goto v_resetjp_4101_;
}
else
{
lean_dec(v_code_3423_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4110_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
lean_ctor_set(v___x_4102_, 2, v_a_4080_);
lean_ctor_set(v___x_4102_, 0, v_fvarId_4078_);
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_fvarId_4078_);
lean_ctor_set(v_reuseFailAlloc_4109_, 1, v_n_4073_);
lean_ctor_set(v_reuseFailAlloc_4109_, 2, v_a_4080_);
lean_ctor_set_uint8(v_reuseFailAlloc_4109_, sizeof(void*)*3, v_check_4074_);
lean_ctor_set_uint8(v_reuseFailAlloc_4109_, sizeof(void*)*3 + 1, v_persistent_4075_);
v___x_4105_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
lean_object* v___x_4107_; 
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 0, v___x_4105_);
v___x_4107_ = v___x_4082_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v___x_4105_);
v___x_4107_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
return v___x_4107_;
}
}
}
}
else
{
size_t v___x_4114_; size_t v___x_4115_; uint8_t v___x_4116_; 
v___x_4114_ = lean_ptr_addr(v_k_4076_);
v___x_4115_ = lean_ptr_addr(v_a_4080_);
v___x_4116_ = lean_usize_dec_eq(v___x_4114_, v___x_4115_);
if (v___x_4116_ == 0)
{
lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4126_; 
lean_inc(v_n_4073_);
v_isSharedCheck_4126_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_4126_ == 0)
{
lean_object* v_unused_4127_; lean_object* v_unused_4128_; lean_object* v_unused_4129_; 
v_unused_4127_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_4127_);
v_unused_4128_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_4128_);
v_unused_4129_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_4129_);
v___x_4118_ = v_code_3423_;
v_isShared_4119_ = v_isSharedCheck_4126_;
goto v_resetjp_4117_;
}
else
{
lean_dec(v_code_3423_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4126_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4121_; 
if (v_isShared_4119_ == 0)
{
lean_ctor_set(v___x_4118_, 2, v_a_4080_);
lean_ctor_set(v___x_4118_, 0, v_fvarId_4078_);
v___x_4121_ = v___x_4118_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_fvarId_4078_);
lean_ctor_set(v_reuseFailAlloc_4125_, 1, v_n_4073_);
lean_ctor_set(v_reuseFailAlloc_4125_, 2, v_a_4080_);
lean_ctor_set_uint8(v_reuseFailAlloc_4125_, sizeof(void*)*3, v_check_4074_);
lean_ctor_set_uint8(v_reuseFailAlloc_4125_, sizeof(void*)*3 + 1, v_persistent_4075_);
v___x_4121_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
lean_object* v___x_4123_; 
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 0, v___x_4121_);
v___x_4123_ = v___x_4082_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v___x_4121_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
else
{
lean_object* v___x_4131_; 
lean_dec(v_a_4080_);
lean_dec(v_fvarId_4078_);
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 0, v_code_3423_);
v___x_4131_ = v___x_4082_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_code_3423_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4078_);
lean_dec_ref_known(v_code_3423_, 3);
return v___x_4079_;
}
}
else
{
lean_object* v___x_4134_; 
lean_dec_ref_known(v_code_3423_, 3);
v___x_4134_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3421_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
return v___x_4134_;
}
}
case 12:
{
lean_object* v_fvarId_4135_; lean_object* v_n_4136_; uint8_t v_check_4137_; uint8_t v_persistent_4138_; lean_object* v_objs_x3f_4139_; lean_object* v_k_4140_; lean_object* v___x_4141_; 
v_fvarId_4135_ = lean_ctor_get(v_code_3423_, 0);
v_n_4136_ = lean_ctor_get(v_code_3423_, 1);
v_check_4137_ = lean_ctor_get_uint8(v_code_3423_, sizeof(void*)*4);
v_persistent_4138_ = lean_ctor_get_uint8(v_code_3423_, sizeof(void*)*4 + 1);
v_objs_x3f_4139_ = lean_ctor_get(v_code_3423_, 2);
v_k_4140_ = lean_ctor_get(v_code_3423_, 3);
lean_inc(v_fvarId_4135_);
v___x_4141_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3424_, v_fvarId_4135_, v_t_3422_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_fvarId_4142_; lean_object* v___x_4143_; 
v_fvarId_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_fvarId_4142_);
lean_dec_ref_known(v___x_4141_, 1);
lean_inc_ref(v_k_4140_);
v___x_4143_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3421_, v_t_3422_, v_k_4140_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4216_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4146_ = v___x_4143_;
v_isShared_4147_ = v_isSharedCheck_4216_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4143_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4216_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
size_t v___x_4148_; size_t v___x_4149_; uint8_t v___x_4150_; 
v___x_4148_ = lean_ptr_addr(v_fvarId_4135_);
v___x_4149_ = lean_ptr_addr(v_fvarId_4142_);
v___x_4150_ = lean_usize_dec_eq(v___x_4148_, v___x_4149_);
if (v___x_4150_ == 0)
{
lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4160_; 
lean_inc(v_objs_x3f_4139_);
lean_inc(v_n_4136_);
v_isSharedCheck_4160_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_4160_ == 0)
{
lean_object* v_unused_4161_; lean_object* v_unused_4162_; lean_object* v_unused_4163_; lean_object* v_unused_4164_; 
v_unused_4161_ = lean_ctor_get(v_code_3423_, 3);
lean_dec(v_unused_4161_);
v_unused_4162_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_4162_);
v_unused_4163_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_4163_);
v_unused_4164_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_4164_);
v___x_4152_ = v_code_3423_;
v_isShared_4153_ = v_isSharedCheck_4160_;
goto v_resetjp_4151_;
}
else
{
lean_dec(v_code_3423_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4160_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
lean_ctor_set(v___x_4152_, 3, v_a_4144_);
lean_ctor_set(v___x_4152_, 0, v_fvarId_4142_);
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_fvarId_4142_);
lean_ctor_set(v_reuseFailAlloc_4159_, 1, v_n_4136_);
lean_ctor_set(v_reuseFailAlloc_4159_, 2, v_objs_x3f_4139_);
lean_ctor_set(v_reuseFailAlloc_4159_, 3, v_a_4144_);
lean_ctor_set_uint8(v_reuseFailAlloc_4159_, sizeof(void*)*4, v_check_4137_);
lean_ctor_set_uint8(v_reuseFailAlloc_4159_, sizeof(void*)*4 + 1, v_persistent_4138_);
v___x_4155_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
lean_object* v___x_4157_; 
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 0, v___x_4155_);
v___x_4157_ = v___x_4146_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v___x_4155_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
else
{
uint8_t v___x_4165_; 
v___x_4165_ = lean_nat_dec_eq(v_n_4136_, v_n_4136_);
if (v___x_4165_ == 0)
{
lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4175_; 
lean_inc(v_objs_x3f_4139_);
lean_inc(v_n_4136_);
v_isSharedCheck_4175_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_4175_ == 0)
{
lean_object* v_unused_4176_; lean_object* v_unused_4177_; lean_object* v_unused_4178_; lean_object* v_unused_4179_; 
v_unused_4176_ = lean_ctor_get(v_code_3423_, 3);
lean_dec(v_unused_4176_);
v_unused_4177_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_4177_);
v_unused_4178_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_4178_);
v_unused_4179_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_4179_);
v___x_4167_ = v_code_3423_;
v_isShared_4168_ = v_isSharedCheck_4175_;
goto v_resetjp_4166_;
}
else
{
lean_dec(v_code_3423_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4175_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4170_; 
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 3, v_a_4144_);
lean_ctor_set(v___x_4167_, 0, v_fvarId_4142_);
v___x_4170_ = v___x_4167_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_fvarId_4142_);
lean_ctor_set(v_reuseFailAlloc_4174_, 1, v_n_4136_);
lean_ctor_set(v_reuseFailAlloc_4174_, 2, v_objs_x3f_4139_);
lean_ctor_set(v_reuseFailAlloc_4174_, 3, v_a_4144_);
lean_ctor_set_uint8(v_reuseFailAlloc_4174_, sizeof(void*)*4, v_check_4137_);
lean_ctor_set_uint8(v_reuseFailAlloc_4174_, sizeof(void*)*4 + 1, v_persistent_4138_);
v___x_4170_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
lean_object* v___x_4172_; 
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 0, v___x_4170_);
v___x_4172_ = v___x_4146_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4170_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
}
else
{
size_t v___x_4180_; uint8_t v___x_4181_; 
v___x_4180_ = lean_ptr_addr(v_objs_x3f_4139_);
v___x_4181_ = lean_usize_dec_eq(v___x_4180_, v___x_4180_);
if (v___x_4181_ == 0)
{
lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4191_; 
lean_inc(v_objs_x3f_4139_);
lean_inc(v_n_4136_);
v_isSharedCheck_4191_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_4191_ == 0)
{
lean_object* v_unused_4192_; lean_object* v_unused_4193_; lean_object* v_unused_4194_; lean_object* v_unused_4195_; 
v_unused_4192_ = lean_ctor_get(v_code_3423_, 3);
lean_dec(v_unused_4192_);
v_unused_4193_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_4193_);
v_unused_4194_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_4194_);
v_unused_4195_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_4195_);
v___x_4183_ = v_code_3423_;
v_isShared_4184_ = v_isSharedCheck_4191_;
goto v_resetjp_4182_;
}
else
{
lean_dec(v_code_3423_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4191_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4186_; 
if (v_isShared_4184_ == 0)
{
lean_ctor_set(v___x_4183_, 3, v_a_4144_);
lean_ctor_set(v___x_4183_, 0, v_fvarId_4142_);
v___x_4186_ = v___x_4183_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_fvarId_4142_);
lean_ctor_set(v_reuseFailAlloc_4190_, 1, v_n_4136_);
lean_ctor_set(v_reuseFailAlloc_4190_, 2, v_objs_x3f_4139_);
lean_ctor_set(v_reuseFailAlloc_4190_, 3, v_a_4144_);
lean_ctor_set_uint8(v_reuseFailAlloc_4190_, sizeof(void*)*4, v_check_4137_);
lean_ctor_set_uint8(v_reuseFailAlloc_4190_, sizeof(void*)*4 + 1, v_persistent_4138_);
v___x_4186_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
lean_object* v___x_4188_; 
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 0, v___x_4186_);
v___x_4188_ = v___x_4146_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v___x_4186_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
else
{
size_t v___x_4196_; size_t v___x_4197_; uint8_t v___x_4198_; 
v___x_4196_ = lean_ptr_addr(v_k_4140_);
v___x_4197_ = lean_ptr_addr(v_a_4144_);
v___x_4198_ = lean_usize_dec_eq(v___x_4196_, v___x_4197_);
if (v___x_4198_ == 0)
{
lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4208_; 
lean_inc(v_objs_x3f_4139_);
lean_inc(v_n_4136_);
v_isSharedCheck_4208_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_4208_ == 0)
{
lean_object* v_unused_4209_; lean_object* v_unused_4210_; lean_object* v_unused_4211_; lean_object* v_unused_4212_; 
v_unused_4209_ = lean_ctor_get(v_code_3423_, 3);
lean_dec(v_unused_4209_);
v_unused_4210_ = lean_ctor_get(v_code_3423_, 2);
lean_dec(v_unused_4210_);
v_unused_4211_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_4211_);
v_unused_4212_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_4212_);
v___x_4200_ = v_code_3423_;
v_isShared_4201_ = v_isSharedCheck_4208_;
goto v_resetjp_4199_;
}
else
{
lean_dec(v_code_3423_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4208_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 3, v_a_4144_);
lean_ctor_set(v___x_4200_, 0, v_fvarId_4142_);
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_fvarId_4142_);
lean_ctor_set(v_reuseFailAlloc_4207_, 1, v_n_4136_);
lean_ctor_set(v_reuseFailAlloc_4207_, 2, v_objs_x3f_4139_);
lean_ctor_set(v_reuseFailAlloc_4207_, 3, v_a_4144_);
lean_ctor_set_uint8(v_reuseFailAlloc_4207_, sizeof(void*)*4, v_check_4137_);
lean_ctor_set_uint8(v_reuseFailAlloc_4207_, sizeof(void*)*4 + 1, v_persistent_4138_);
v___x_4203_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
lean_object* v___x_4205_; 
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 0, v___x_4203_);
v___x_4205_ = v___x_4146_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v___x_4203_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
}
}
else
{
lean_object* v___x_4214_; 
lean_dec(v_a_4144_);
lean_dec(v_fvarId_4142_);
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 0, v_code_3423_);
v___x_4214_ = v___x_4146_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_code_3423_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4142_);
lean_dec_ref_known(v_code_3423_, 4);
return v___x_4143_;
}
}
else
{
lean_object* v___x_4217_; 
lean_dec_ref_known(v_code_3423_, 4);
v___x_4217_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3421_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
return v___x_4217_;
}
}
default: 
{
lean_object* v_fvarId_4218_; lean_object* v_k_4219_; lean_object* v___x_4220_; 
v_fvarId_4218_ = lean_ctor_get(v_code_3423_, 0);
v_k_4219_ = lean_ctor_get(v_code_3423_, 1);
lean_inc(v_fvarId_4218_);
v___x_4220_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3424_, v_fvarId_4218_, v_t_3422_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_fvarId_4221_; lean_object* v___x_4222_; 
v_fvarId_4221_ = lean_ctor_get(v___x_4220_, 0);
lean_inc(v_fvarId_4221_);
lean_dec_ref_known(v___x_4220_, 1);
lean_inc_ref(v_k_4219_);
v___x_4222_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3421_, v_t_3422_, v_k_4219_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4260_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4225_ = v___x_4222_;
v_isShared_4226_ = v_isSharedCheck_4260_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4222_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4260_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
size_t v___x_4227_; size_t v___x_4228_; uint8_t v___x_4229_; 
v___x_4227_ = lean_ptr_addr(v_fvarId_4218_);
v___x_4228_ = lean_ptr_addr(v_fvarId_4221_);
v___x_4229_ = lean_usize_dec_eq(v___x_4227_, v___x_4228_);
if (v___x_4229_ == 0)
{
lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4239_; 
v_isSharedCheck_4239_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_4239_ == 0)
{
lean_object* v_unused_4240_; lean_object* v_unused_4241_; 
v_unused_4240_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_4240_);
v_unused_4241_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_4241_);
v___x_4231_ = v_code_3423_;
v_isShared_4232_ = v_isSharedCheck_4239_;
goto v_resetjp_4230_;
}
else
{
lean_dec(v_code_3423_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4239_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
lean_ctor_set(v___x_4231_, 1, v_a_4223_);
lean_ctor_set(v___x_4231_, 0, v_fvarId_4221_);
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_fvarId_4221_);
lean_ctor_set(v_reuseFailAlloc_4238_, 1, v_a_4223_);
v___x_4234_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
lean_object* v___x_4236_; 
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 0, v___x_4234_);
v___x_4236_ = v___x_4225_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4234_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
else
{
size_t v___x_4242_; size_t v___x_4243_; uint8_t v___x_4244_; 
v___x_4242_ = lean_ptr_addr(v_k_4219_);
v___x_4243_ = lean_ptr_addr(v_a_4223_);
v___x_4244_ = lean_usize_dec_eq(v___x_4242_, v___x_4243_);
if (v___x_4244_ == 0)
{
lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4254_; 
v_isSharedCheck_4254_ = !lean_is_exclusive(v_code_3423_);
if (v_isSharedCheck_4254_ == 0)
{
lean_object* v_unused_4255_; lean_object* v_unused_4256_; 
v_unused_4255_ = lean_ctor_get(v_code_3423_, 1);
lean_dec(v_unused_4255_);
v_unused_4256_ = lean_ctor_get(v_code_3423_, 0);
lean_dec(v_unused_4256_);
v___x_4246_ = v_code_3423_;
v_isShared_4247_ = v_isSharedCheck_4254_;
goto v_resetjp_4245_;
}
else
{
lean_dec(v_code_3423_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4254_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4249_; 
if (v_isShared_4247_ == 0)
{
lean_ctor_set(v___x_4246_, 1, v_a_4223_);
lean_ctor_set(v___x_4246_, 0, v_fvarId_4221_);
v___x_4249_ = v___x_4246_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_fvarId_4221_);
lean_ctor_set(v_reuseFailAlloc_4253_, 1, v_a_4223_);
v___x_4249_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
lean_object* v___x_4251_; 
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 0, v___x_4249_);
v___x_4251_ = v___x_4225_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4249_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
else
{
lean_object* v___x_4258_; 
lean_dec(v_a_4223_);
lean_dec(v_fvarId_4221_);
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 0, v_code_3423_);
v___x_4258_ = v___x_4225_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_code_3423_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_4221_);
lean_dec_ref_known(v_code_3423_, 2);
return v___x_4222_;
}
}
else
{
lean_object* v___x_4261_; 
lean_dec_ref_known(v_code_3423_, 2);
v___x_4261_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3421_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
return v___x_4261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t v_pu_4262_, uint8_t v_t_4263_, lean_object* v_decl_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_){
_start:
{
lean_object* v_params_4271_; lean_object* v_type_4272_; lean_object* v_value_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v_params_4271_ = lean_ctor_get(v_decl_4264_, 2);
v_type_4272_ = lean_ctor_get(v_decl_4264_, 3);
v_value_4273_ = lean_ctor_get(v_decl_4264_, 4);
lean_inc_ref(v_type_4272_);
v___x_4274_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4262_, v_a_4265_, v_t_4263_, v_type_4272_);
lean_inc_ref(v_params_4271_);
v___x_4275_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4262_, v_t_4263_, v_params_4271_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; lean_object* v___x_4277_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_a_4276_);
lean_dec_ref_known(v___x_4275_, 1);
lean_inc_ref(v_value_4273_);
v___x_4277_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4262_, v_t_4263_, v_value_4273_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; lean_object* v___x_4279_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4278_);
lean_dec_ref_known(v___x_4277_, 1);
v___x_4279_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_4262_, v_decl_4264_, v___x_4274_, v_a_4276_, v_a_4278_, v_a_4267_);
return v___x_4279_;
}
else
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4287_; 
lean_dec(v_a_4276_);
lean_dec_ref(v___x_4274_);
lean_dec_ref(v_decl_4264_);
v_a_4280_ = lean_ctor_get(v___x_4277_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4282_ = v___x_4277_;
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___x_4277_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4285_; 
if (v_isShared_4283_ == 0)
{
v___x_4285_ = v___x_4282_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_a_4280_);
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
else
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4295_; 
lean_dec_ref(v___x_4274_);
lean_dec_ref(v_decl_4264_);
v_a_4288_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4290_ = v___x_4275_;
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4275_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4293_; 
if (v_isShared_4291_ == 0)
{
v___x_4293_ = v___x_4290_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_a_4288_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
return v___x_4293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp___boxed(lean_object* v_pu_4296_, lean_object* v_t_4297_, lean_object* v_decl_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_){
_start:
{
uint8_t v_pu_boxed_4305_; uint8_t v_t_boxed_4306_; lean_object* v_res_4307_; 
v_pu_boxed_4305_ = lean_unbox(v_pu_4296_);
v_t_boxed_4306_ = lean_unbox(v_t_4297_);
v_res_4307_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_boxed_4305_, v_t_boxed_4306_, v_decl_4298_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_);
lean_dec(v_a_4303_);
lean_dec_ref(v_a_4302_);
lean_dec(v_a_4301_);
lean_dec_ref(v_a_4300_);
lean_dec_ref(v_a_4299_);
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4___boxed(lean_object* v_pu_4308_, lean_object* v_t_4309_, lean_object* v_i_4310_, lean_object* v_as_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_){
_start:
{
uint8_t v_pu_boxed_4318_; uint8_t v_t_boxed_4319_; lean_object* v_res_4320_; 
v_pu_boxed_4318_ = lean_unbox(v_pu_4308_);
v_t_boxed_4319_ = lean_unbox(v_t_4309_);
v_res_4320_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_boxed_4318_, v_t_boxed_4319_, v_i_4310_, v_as_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
lean_dec_ref(v___y_4312_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp___boxed(lean_object* v_pu_4321_, lean_object* v_t_4322_, lean_object* v_code_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_){
_start:
{
uint8_t v_pu_boxed_4330_; uint8_t v_t_boxed_4331_; lean_object* v_res_4332_; 
v_pu_boxed_4330_ = lean_unbox(v_pu_4321_);
v_t_boxed_4331_ = lean_unbox(v_t_4322_);
v_res_4332_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_boxed_4330_, v_t_boxed_4331_, v_code_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_);
lean_dec(v_a_4328_);
lean_dec_ref(v_a_4327_);
lean_dec(v_a_4326_);
lean_dec_ref(v_a_4325_);
lean_dec_ref(v_a_4324_);
return v_res_4332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(uint8_t v_pu_4333_, uint8_t v_t_4334_, uint8_t v_pu_4335_, uint8_t v_t_4336_, lean_object* v_decl_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_){
_start:
{
lean_object* v___x_4344_; 
v___x_4344_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_4335_, v_t_4336_, v_decl_4337_, v___y_4338_, v___y_4340_);
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___boxed(lean_object* v_pu_4345_, lean_object* v_t_4346_, lean_object* v_pu_4347_, lean_object* v_t_4348_, lean_object* v_decl_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
uint8_t v_pu_boxed_4356_; uint8_t v_t_boxed_4357_; uint8_t v_pu_boxed_4358_; uint8_t v_t_boxed_4359_; lean_object* v_res_4360_; 
v_pu_boxed_4356_ = lean_unbox(v_pu_4345_);
v_t_boxed_4357_ = lean_unbox(v_t_4346_);
v_pu_boxed_4358_ = lean_unbox(v_pu_4347_);
v_t_boxed_4359_ = lean_unbox(v_t_4348_);
v_res_4360_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(v_pu_boxed_4356_, v_t_boxed_4357_, v_pu_boxed_4358_, v_t_boxed_4359_, v_decl_4349_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
lean_dec_ref(v___y_4350_);
return v_res_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(uint8_t v_pu_4361_, uint8_t v_t_4362_, uint8_t v_pu_4363_, uint8_t v_t_4364_, lean_object* v_args_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v___x_4372_; 
v___x_4372_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_4363_, v_t_4364_, v_args_4365_, v___y_4366_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___boxed(lean_object* v_pu_4373_, lean_object* v_t_4374_, lean_object* v_pu_4375_, lean_object* v_t_4376_, lean_object* v_args_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
uint8_t v_pu_boxed_4384_; uint8_t v_t_boxed_4385_; uint8_t v_pu_boxed_4386_; uint8_t v_t_boxed_4387_; lean_object* v_res_4388_; 
v_pu_boxed_4384_ = lean_unbox(v_pu_4373_);
v_t_boxed_4385_ = lean_unbox(v_t_4374_);
v_pu_boxed_4386_ = lean_unbox(v_pu_4375_);
v_t_boxed_4387_ = lean_unbox(v_t_4376_);
v_res_4388_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(v_pu_boxed_4384_, v_t_boxed_4385_, v_pu_boxed_4386_, v_t_boxed_4387_, v_args_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec_ref(v___y_4378_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(uint8_t v_pu_4389_, uint8_t v_t_4390_, uint8_t v_pu_4391_, uint8_t v_t_4392_, lean_object* v_ps_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
lean_object* v___x_4400_; 
v___x_4400_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4391_, v_t_4392_, v_ps_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___boxed(lean_object* v_pu_4401_, lean_object* v_t_4402_, lean_object* v_pu_4403_, lean_object* v_t_4404_, lean_object* v_ps_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_){
_start:
{
uint8_t v_pu_boxed_4412_; uint8_t v_t_boxed_4413_; uint8_t v_pu_boxed_4414_; uint8_t v_t_boxed_4415_; lean_object* v_res_4416_; 
v_pu_boxed_4412_ = lean_unbox(v_pu_4401_);
v_t_boxed_4413_ = lean_unbox(v_t_4402_);
v_pu_boxed_4414_ = lean_unbox(v_pu_4403_);
v_t_boxed_4415_ = lean_unbox(v_t_4404_);
v_res_4416_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(v_pu_boxed_4412_, v_t_boxed_4413_, v_pu_boxed_4414_, v_t_boxed_4415_, v_ps_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
lean_dec_ref(v___y_4406_);
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(uint8_t v_pu_4417_, uint8_t v_t_4418_, lean_object* v_i_4419_, lean_object* v_as_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_){
_start:
{
lean_object* v___x_4427_; 
v___x_4427_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_4417_, v_t_4418_, v_i_4419_, v_as_4420_, v___y_4421_, v___y_4423_);
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___boxed(lean_object* v_pu_4428_, lean_object* v_t_4429_, lean_object* v_i_4430_, lean_object* v_as_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
uint8_t v_pu_boxed_4438_; uint8_t v_t_boxed_4439_; lean_object* v_res_4440_; 
v_pu_boxed_4438_ = lean_unbox(v_pu_4428_);
v_t_boxed_4439_ = lean_unbox(v_t_4429_);
v_res_4440_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(v_pu_boxed_4438_, v_t_boxed_4439_, v_i_4430_, v_as_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
lean_dec_ref(v___y_4432_);
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(uint8_t v_pu_4441_, uint8_t v_t_4442_, lean_object* v_decl_4443_, lean_object* v_inst_4444_, lean_object* v_____do__lift_4445_){
_start:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4446_ = lean_box(v_pu_4441_);
v___x_4447_ = lean_box(v_t_4442_);
v___x_4448_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDeclImp___boxed), 9, 4);
lean_closure_set(v___x_4448_, 0, v___x_4446_);
lean_closure_set(v___x_4448_, 1, v___x_4447_);
lean_closure_set(v___x_4448_, 2, v_decl_4443_);
lean_closure_set(v___x_4448_, 3, v_____do__lift_4445_);
v___x_4449_ = lean_apply_2(v_inst_4444_, lean_box(0), v___x_4448_);
return v___x_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed(lean_object* v_pu_4450_, lean_object* v_t_4451_, lean_object* v_decl_4452_, lean_object* v_inst_4453_, lean_object* v_____do__lift_4454_){
_start:
{
uint8_t v_pu_boxed_4455_; uint8_t v_t_boxed_4456_; lean_object* v_res_4457_; 
v_pu_boxed_4455_ = lean_unbox(v_pu_4450_);
v_t_boxed_4456_ = lean_unbox(v_t_4451_);
v_res_4457_ = l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(v_pu_boxed_4455_, v_t_boxed_4456_, v_decl_4452_, v_inst_4453_, v_____do__lift_4454_);
return v_res_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg(uint8_t v_pu_4458_, uint8_t v_t_4459_, lean_object* v_inst_4460_, lean_object* v_inst_4461_, lean_object* v_inst_4462_, lean_object* v_decl_4463_){
_start:
{
lean_object* v_toBind_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___f_4467_; lean_object* v___x_4468_; 
v_toBind_4464_ = lean_ctor_get(v_inst_4461_, 1);
lean_inc(v_toBind_4464_);
lean_dec_ref(v_inst_4461_);
v___x_4465_ = lean_box(v_pu_4458_);
v___x_4466_ = lean_box(v_t_4459_);
v___f_4467_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4467_, 0, v___x_4465_);
lean_closure_set(v___f_4467_, 1, v___x_4466_);
lean_closure_set(v___f_4467_, 2, v_decl_4463_);
lean_closure_set(v___f_4467_, 3, v_inst_4460_);
v___x_4468_ = lean_apply_4(v_toBind_4464_, lean_box(0), lean_box(0), v_inst_4462_, v___f_4467_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___boxed(lean_object* v_pu_4469_, lean_object* v_t_4470_, lean_object* v_inst_4471_, lean_object* v_inst_4472_, lean_object* v_inst_4473_, lean_object* v_decl_4474_){
_start:
{
uint8_t v_pu_boxed_4475_; uint8_t v_t_boxed_4476_; lean_object* v_res_4477_; 
v_pu_boxed_4475_ = lean_unbox(v_pu_4469_);
v_t_boxed_4476_ = lean_unbox(v_t_4470_);
v_res_4477_ = l_Lean_Compiler_LCNF_normFunDecl___redArg(v_pu_boxed_4475_, v_t_boxed_4476_, v_inst_4471_, v_inst_4472_, v_inst_4473_, v_decl_4474_);
return v_res_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl(lean_object* v_m_4478_, uint8_t v_pu_4479_, uint8_t v_t_4480_, lean_object* v_inst_4481_, lean_object* v_inst_4482_, lean_object* v_inst_4483_, lean_object* v_decl_4484_){
_start:
{
lean_object* v_toBind_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___f_4488_; lean_object* v___x_4489_; 
v_toBind_4485_ = lean_ctor_get(v_inst_4482_, 1);
lean_inc(v_toBind_4485_);
lean_dec_ref(v_inst_4482_);
v___x_4486_ = lean_box(v_pu_4479_);
v___x_4487_ = lean_box(v_t_4480_);
v___f_4488_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4488_, 0, v___x_4486_);
lean_closure_set(v___f_4488_, 1, v___x_4487_);
lean_closure_set(v___f_4488_, 2, v_decl_4484_);
lean_closure_set(v___f_4488_, 3, v_inst_4481_);
v___x_4489_ = lean_apply_4(v_toBind_4485_, lean_box(0), lean_box(0), v_inst_4483_, v___f_4488_);
return v___x_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___boxed(lean_object* v_m_4490_, lean_object* v_pu_4491_, lean_object* v_t_4492_, lean_object* v_inst_4493_, lean_object* v_inst_4494_, lean_object* v_inst_4495_, lean_object* v_decl_4496_){
_start:
{
uint8_t v_pu_boxed_4497_; uint8_t v_t_boxed_4498_; lean_object* v_res_4499_; 
v_pu_boxed_4497_ = lean_unbox(v_pu_4491_);
v_t_boxed_4498_ = lean_unbox(v_t_4492_);
v_res_4499_ = l_Lean_Compiler_LCNF_normFunDecl(v_m_4490_, v_pu_boxed_4497_, v_t_boxed_4498_, v_inst_4493_, v_inst_4494_, v_inst_4495_, v_decl_4496_);
return v_res_4499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0(uint8_t v_pu_4500_, uint8_t v_t_4501_, lean_object* v_code_4502_, lean_object* v_inst_4503_, lean_object* v_____do__lift_4504_){
_start:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; 
v___x_4505_ = lean_box(v_pu_4500_);
v___x_4506_ = lean_box(v_t_4501_);
v___x_4507_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCodeImp___boxed), 9, 4);
lean_closure_set(v___x_4507_, 0, v___x_4505_);
lean_closure_set(v___x_4507_, 1, v___x_4506_);
lean_closure_set(v___x_4507_, 2, v_code_4502_);
lean_closure_set(v___x_4507_, 3, v_____do__lift_4504_);
v___x_4508_ = lean_apply_2(v_inst_4503_, lean_box(0), v___x_4507_);
return v___x_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed(lean_object* v_pu_4509_, lean_object* v_t_4510_, lean_object* v_code_4511_, lean_object* v_inst_4512_, lean_object* v_____do__lift_4513_){
_start:
{
uint8_t v_pu_boxed_4514_; uint8_t v_t_boxed_4515_; lean_object* v_res_4516_; 
v_pu_boxed_4514_ = lean_unbox(v_pu_4509_);
v_t_boxed_4515_ = lean_unbox(v_t_4510_);
v_res_4516_ = l_Lean_Compiler_LCNF_normCode___redArg___lam__0(v_pu_boxed_4514_, v_t_boxed_4515_, v_code_4511_, v_inst_4512_, v_____do__lift_4513_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg(uint8_t v_pu_4517_, uint8_t v_t_4518_, lean_object* v_inst_4519_, lean_object* v_inst_4520_, lean_object* v_inst_4521_, lean_object* v_code_4522_){
_start:
{
lean_object* v_toBind_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___f_4526_; lean_object* v___x_4527_; 
v_toBind_4523_ = lean_ctor_get(v_inst_4520_, 1);
lean_inc(v_toBind_4523_);
lean_dec_ref(v_inst_4520_);
v___x_4524_ = lean_box(v_pu_4517_);
v___x_4525_ = lean_box(v_t_4518_);
v___f_4526_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4526_, 0, v___x_4524_);
lean_closure_set(v___f_4526_, 1, v___x_4525_);
lean_closure_set(v___f_4526_, 2, v_code_4522_);
lean_closure_set(v___f_4526_, 3, v_inst_4519_);
v___x_4527_ = lean_apply_4(v_toBind_4523_, lean_box(0), lean_box(0), v_inst_4521_, v___f_4526_);
return v___x_4527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___boxed(lean_object* v_pu_4528_, lean_object* v_t_4529_, lean_object* v_inst_4530_, lean_object* v_inst_4531_, lean_object* v_inst_4532_, lean_object* v_code_4533_){
_start:
{
uint8_t v_pu_boxed_4534_; uint8_t v_t_boxed_4535_; lean_object* v_res_4536_; 
v_pu_boxed_4534_ = lean_unbox(v_pu_4528_);
v_t_boxed_4535_ = lean_unbox(v_t_4529_);
v_res_4536_ = l_Lean_Compiler_LCNF_normCode___redArg(v_pu_boxed_4534_, v_t_boxed_4535_, v_inst_4530_, v_inst_4531_, v_inst_4532_, v_code_4533_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode(lean_object* v_m_4537_, uint8_t v_pu_4538_, uint8_t v_t_4539_, lean_object* v_inst_4540_, lean_object* v_inst_4541_, lean_object* v_inst_4542_, lean_object* v_code_4543_){
_start:
{
lean_object* v_toBind_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___f_4547_; lean_object* v___x_4548_; 
v_toBind_4544_ = lean_ctor_get(v_inst_4541_, 1);
lean_inc(v_toBind_4544_);
lean_dec_ref(v_inst_4541_);
v___x_4545_ = lean_box(v_pu_4538_);
v___x_4546_ = lean_box(v_t_4539_);
v___f_4547_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4547_, 0, v___x_4545_);
lean_closure_set(v___f_4547_, 1, v___x_4546_);
lean_closure_set(v___f_4547_, 2, v_code_4543_);
lean_closure_set(v___f_4547_, 3, v_inst_4540_);
v___x_4548_ = lean_apply_4(v_toBind_4544_, lean_box(0), lean_box(0), v_inst_4542_, v___f_4547_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___boxed(lean_object* v_m_4549_, lean_object* v_pu_4550_, lean_object* v_t_4551_, lean_object* v_inst_4552_, lean_object* v_inst_4553_, lean_object* v_inst_4554_, lean_object* v_code_4555_){
_start:
{
uint8_t v_pu_boxed_4556_; uint8_t v_t_boxed_4557_; lean_object* v_res_4558_; 
v_pu_boxed_4556_ = lean_unbox(v_pu_4550_);
v_t_boxed_4557_ = lean_unbox(v_t_4551_);
v_res_4558_ = l_Lean_Compiler_LCNF_normCode(v_m_4549_, v_pu_boxed_4556_, v_t_boxed_4557_, v_inst_4552_, v_inst_4553_, v_inst_4554_, v_code_4555_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t v_pu_4559_, lean_object* v_e_4560_, lean_object* v_s_4561_, uint8_t v_translator_4562_){
_start:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; 
v___x_4564_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4559_, v_s_4561_, v_translator_4562_, v_e_4560_);
v___x_4565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4565_, 0, v___x_4564_);
return v___x_4565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg___boxed(lean_object* v_pu_4566_, lean_object* v_e_4567_, lean_object* v_s_4568_, lean_object* v_translator_4569_, lean_object* v_a_4570_){
_start:
{
uint8_t v_pu_boxed_4571_; uint8_t v_translator_boxed_4572_; lean_object* v_res_4573_; 
v_pu_boxed_4571_ = lean_unbox(v_pu_4566_);
v_translator_boxed_4572_ = lean_unbox(v_translator_4569_);
v_res_4573_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_boxed_4571_, v_e_4567_, v_s_4568_, v_translator_boxed_4572_);
lean_dec_ref(v_s_4568_);
return v_res_4573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(uint8_t v_pu_4574_, lean_object* v_e_4575_, lean_object* v_s_4576_, uint8_t v_translator_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_){
_start:
{
lean_object* v___x_4583_; 
v___x_4583_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_4574_, v_e_4575_, v_s_4576_, v_translator_4577_);
return v___x_4583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___boxed(lean_object* v_pu_4584_, lean_object* v_e_4585_, lean_object* v_s_4586_, lean_object* v_translator_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_){
_start:
{
uint8_t v_pu_boxed_4593_; uint8_t v_translator_boxed_4594_; lean_object* v_res_4595_; 
v_pu_boxed_4593_ = lean_unbox(v_pu_4584_);
v_translator_boxed_4594_ = lean_unbox(v_translator_4587_);
v_res_4595_ = l_Lean_Compiler_LCNF_replaceExprFVars(v_pu_boxed_4593_, v_e_4585_, v_s_4586_, v_translator_boxed_4594_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_);
lean_dec(v_a_4591_);
lean_dec_ref(v_a_4590_);
lean_dec(v_a_4589_);
lean_dec_ref(v_a_4588_);
lean_dec_ref(v_s_4586_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t v_pu_4596_, lean_object* v_code_4597_, lean_object* v_s_4598_, uint8_t v_translator_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_){
_start:
{
lean_object* v___x_4605_; 
v___x_4605_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4596_, v_translator_4599_, v_code_4597_, v_s_4598_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_);
return v___x_4605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars___boxed(lean_object* v_pu_4606_, lean_object* v_code_4607_, lean_object* v_s_4608_, lean_object* v_translator_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_){
_start:
{
uint8_t v_pu_boxed_4615_; uint8_t v_translator_boxed_4616_; lean_object* v_res_4617_; 
v_pu_boxed_4615_ = lean_unbox(v_pu_4606_);
v_translator_boxed_4616_ = lean_unbox(v_translator_4609_);
v_res_4617_ = l_Lean_Compiler_LCNF_replaceFVars(v_pu_boxed_4615_, v_code_4607_, v_s_4608_, v_translator_boxed_4616_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_);
lean_dec(v_a_4613_);
lean_dec_ref(v_a_4612_);
lean_dec(v_a_4611_);
lean_dec_ref(v_a_4610_);
lean_dec_ref(v_s_4608_);
return v_res_4617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg(lean_object* v_a_4621_){
_start:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4623_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1));
v___x_4624_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4623_, v_a_4621_);
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___boxed(lean_object* v_a_4625_, lean_object* v_a_4626_){
_start:
{
lean_object* v_res_4627_; 
v_res_4627_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4625_);
lean_dec(v_a_4625_);
return v_res_4627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName(lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_){
_start:
{
lean_object* v___x_4633_; 
v___x_4633_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4629_);
return v___x_4633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___boxed(lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_){
_start:
{
lean_object* v_res_4639_; 
v_res_4639_ = l_Lean_Compiler_LCNF_mkFreshJpName(v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_);
lean_dec(v_a_4637_);
lean_dec_ref(v_a_4636_);
lean_dec(v_a_4635_);
lean_dec_ref(v_a_4634_);
return v_res_4639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t v_pu_4640_, lean_object* v_type_4641_, uint8_t v_borrow_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_){
_start:
{
lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v_a_4650_; lean_object* v___x_4651_; 
v___x_4648_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_4649_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4648_, v_a_4644_);
v_a_4650_ = lean_ctor_get(v___x_4649_, 0);
lean_inc(v_a_4650_);
lean_dec_ref(v___x_4649_);
v___x_4651_ = l_Lean_Compiler_LCNF_mkParam(v_pu_4640_, v_a_4650_, v_type_4641_, v_borrow_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_);
return v___x_4651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam___boxed(lean_object* v_pu_4652_, lean_object* v_type_4653_, lean_object* v_borrow_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_){
_start:
{
uint8_t v_pu_boxed_4660_; uint8_t v_borrow_boxed_4661_; lean_object* v_res_4662_; 
v_pu_boxed_4660_ = lean_unbox(v_pu_4652_);
v_borrow_boxed_4661_ = lean_unbox(v_borrow_4654_);
v_res_4662_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_boxed_4660_, v_type_4653_, v_borrow_boxed_4661_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_);
lean_dec(v_a_4658_);
lean_dec_ref(v_a_4657_);
lean_dec(v_a_4656_);
lean_dec_ref(v_a_4655_);
return v_res_4662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object* v_a_4663_){
_start:
{
lean_object* v_config_4665_; lean_object* v___x_4666_; 
v_config_4665_ = lean_ctor_get(v_a_4663_, 0);
lean_inc_ref(v_config_4665_);
v___x_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4666_, 0, v_config_4665_);
return v___x_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg___boxed(lean_object* v_a_4667_, lean_object* v_a_4668_){
_start:
{
lean_object* v_res_4669_; 
v_res_4669_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4667_);
lean_dec_ref(v_a_4667_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig(lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_){
_start:
{
lean_object* v___x_4675_; 
v___x_4675_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4670_);
return v___x_4675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___boxed(lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_){
_start:
{
lean_object* v_res_4681_; 
v_res_4681_ = l_Lean_Compiler_LCNF_getConfig(v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_);
lean_dec(v_a_4679_);
lean_dec_ref(v_a_4678_);
lean_dec(v_a_4677_);
lean_dec_ref(v_a_4676_);
return v_res_4681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object* v_x_4682_, lean_object* v_s_4683_, uint8_t v_phase_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_){
_start:
{
lean_object* v___x_4688_; lean_object* v_options_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; 
v___x_4688_ = lean_st_mk_ref(v_s_4683_);
v_options_4689_ = lean_ctor_get(v_a_4685_, 1);
v___x_4690_ = l_Lean_Compiler_LCNF_toConfigOptions(v_options_4689_);
v___x_4691_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4691_, 0, v___x_4690_);
lean_ctor_set_uint8(v___x_4691_, sizeof(void*)*1, v_phase_4684_);
lean_inc(v_a_4686_);
lean_inc_ref(v_a_4685_);
lean_inc(v___x_4688_);
v___x_4692_ = lean_apply_5(v_x_4682_, v___x_4691_, v___x_4688_, v_a_4685_, v_a_4686_, lean_box(0));
if (lean_obj_tag(v___x_4692_) == 0)
{
lean_object* v_a_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4701_; 
v_a_4693_ = lean_ctor_get(v___x_4692_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4692_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4695_ = v___x_4692_;
v_isShared_4696_ = v_isSharedCheck_4701_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_a_4693_);
lean_dec(v___x_4692_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4701_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v___x_4697_; lean_object* v___x_4699_; 
v___x_4697_ = lean_st_ref_get(v___x_4688_);
lean_dec(v___x_4688_);
lean_dec(v___x_4697_);
if (v_isShared_4696_ == 0)
{
v___x_4699_ = v___x_4695_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4693_);
v___x_4699_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
return v___x_4699_;
}
}
}
else
{
lean_dec(v___x_4688_);
return v___x_4692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg___boxed(lean_object* v_x_4702_, lean_object* v_s_4703_, lean_object* v_phase_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_){
_start:
{
uint8_t v_phase_boxed_4708_; lean_object* v_res_4709_; 
v_phase_boxed_4708_ = lean_unbox(v_phase_4704_);
v_res_4709_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4702_, v_s_4703_, v_phase_boxed_4708_, v_a_4705_, v_a_4706_);
lean_dec(v_a_4706_);
lean_dec_ref(v_a_4705_);
return v_res_4709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run(lean_object* v_00_u03b1_4710_, lean_object* v_x_4711_, lean_object* v_s_4712_, uint8_t v_phase_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_){
_start:
{
lean_object* v___x_4717_; 
v___x_4717_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4711_, v_s_4712_, v_phase_4713_, v_a_4714_, v_a_4715_);
return v___x_4717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___boxed(lean_object* v_00_u03b1_4718_, lean_object* v_x_4719_, lean_object* v_s_4720_, lean_object* v_phase_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_){
_start:
{
uint8_t v_phase_boxed_4725_; lean_object* v_res_4726_; 
v_phase_boxed_4725_ = lean_unbox(v_phase_4721_);
v_res_4726_ = l_Lean_Compiler_LCNF_CompilerM_run(v_00_u03b1_4718_, v_x_4719_, v_s_4720_, v_phase_boxed_4725_, v_a_4722_, v_a_4723_);
lean_dec(v_a_4723_);
lean_dec_ref(v_a_4722_);
return v_res_4726_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0(void){
_start:
{
lean_object* v___x_4727_; 
v___x_4727_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(lean_object* v_00_u03b1_4728_, lean_object* v_00_u03b2_4729_, lean_object* v_inst_4730_, lean_object* v_inst_4731_){
_start:
{
lean_object* v___x_4732_; 
v___x_4732_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(lean_object* v_00_u03b1_4733_, lean_object* v_00_u03b2_4734_, lean_object* v_inst_4735_, lean_object* v_inst_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(v_00_u03b1_4733_, v_00_u03b2_4734_, v_inst_4735_, v_inst_4736_);
lean_dec_ref(v_inst_4736_);
lean_dec_ref(v_inst_4735_);
return v_res_4737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension(lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_){
_start:
{
lean_object* v___x_4742_; 
v___x_4742_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___boxed(lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_){
_start:
{
lean_object* v_res_4747_; 
v_res_4747_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension(v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_);
lean_dec_ref(v_a_4746_);
lean_dec_ref(v_a_4745_);
return v_res_4747_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; 
v___x_4751_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2));
v___x_4752_ = lean_unsigned_to_nat(14u);
v___x_4753_ = lean_unsigned_to_nat(178u);
v___x_4754_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1));
v___x_4755_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0));
v___x_4756_ = l_mkPanicMessageWithDecl(v___x_4755_, v___x_4754_, v___x_4753_, v___x_4752_, v___x_4751_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(lean_object* v_inst_4757_, lean_object* v_inst_4758_, lean_object* v_snd_4759_, lean_object* v_inst_4760_, lean_object* v_s_4761_, lean_object* v_e_4762_){
_start:
{
lean_object* v_fst_4763_; lean_object* v_snd_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4779_; 
v_fst_4763_ = lean_ctor_get(v_s_4761_, 0);
v_snd_4764_ = lean_ctor_get(v_s_4761_, 1);
v_isSharedCheck_4779_ = !lean_is_exclusive(v_s_4761_);
if (v_isSharedCheck_4779_ == 0)
{
v___x_4766_ = v_s_4761_;
v_isShared_4767_ = v_isSharedCheck_4779_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_snd_4764_);
lean_inc(v_fst_4763_);
lean_dec(v_s_4761_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4779_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v___x_4768_; lean_object* v___y_4770_; lean_object* v___x_4775_; 
lean_inc_n(v_e_4762_, 2);
v___x_4768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4768_, 0, v_e_4762_);
lean_ctor_set(v___x_4768_, 1, v_fst_4763_);
lean_inc_ref(v_inst_4758_);
lean_inc_ref(v_inst_4757_);
v___x_4775_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4757_, v_inst_4758_, v_snd_4759_, v_e_4762_);
if (lean_obj_tag(v___x_4775_) == 0)
{
lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4776_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3);
v___x_4777_ = l_panic___redArg(v_inst_4760_, v___x_4776_);
v___y_4770_ = v___x_4777_;
goto v___jp_4769_;
}
else
{
lean_object* v_val_4778_; 
v_val_4778_ = lean_ctor_get(v___x_4775_, 0);
lean_inc(v_val_4778_);
lean_dec_ref_known(v___x_4775_, 1);
v___y_4770_ = v_val_4778_;
goto v___jp_4769_;
}
v___jp_4769_:
{
lean_object* v___x_4771_; lean_object* v___x_4773_; 
v___x_4771_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4757_, v_inst_4758_, v_snd_4764_, v_e_4762_, v___y_4770_);
if (v_isShared_4767_ == 0)
{
lean_ctor_set(v___x_4766_, 1, v___x_4771_);
lean_ctor_set(v___x_4766_, 0, v___x_4768_);
v___x_4773_ = v___x_4766_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v___x_4768_);
lean_ctor_set(v_reuseFailAlloc_4774_, 1, v___x_4771_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed(lean_object* v_inst_4780_, lean_object* v_inst_4781_, lean_object* v_snd_4782_, lean_object* v_inst_4783_, lean_object* v_s_4784_, lean_object* v_e_4785_){
_start:
{
lean_object* v_res_4786_; 
v_res_4786_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(v_inst_4780_, v_inst_4781_, v_snd_4782_, v_inst_4783_, v_s_4784_, v_e_4785_);
lean_dec(v_inst_4783_);
lean_dec(v_snd_4782_);
return v_res_4786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(lean_object* v_inst_4789_, lean_object* v_inst_4790_, lean_object* v_inst_4791_, lean_object* v_oldState_4792_, lean_object* v_newState_4793_, lean_object* v_x_4794_, lean_object* v_s_4795_){
_start:
{
lean_object* v_fst_4796_; lean_object* v_snd_4797_; lean_object* v_fst_4798_; lean_object* v___f_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v_newEntries_4804_; lean_object* v___x_4805_; 
v_fst_4796_ = lean_ctor_get(v_newState_4793_, 0);
lean_inc_n(v_fst_4796_, 2);
v_snd_4797_ = lean_ctor_get(v_newState_4793_, 1);
lean_inc(v_snd_4797_);
lean_dec_ref(v_newState_4793_);
v_fst_4798_ = lean_ctor_get(v_oldState_4792_, 0);
v___f_4799_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_4799_, 0, v_inst_4789_);
lean_closure_set(v___f_4799_, 1, v_inst_4790_);
lean_closure_set(v___f_4799_, 2, v_snd_4797_);
lean_closure_set(v___f_4799_, 3, v_inst_4791_);
v___x_4800_ = l_List_lengthTR___redArg(v_fst_4796_);
v___x_4801_ = l_List_lengthTR___redArg(v_fst_4798_);
v___x_4802_ = lean_nat_sub(v___x_4800_, v___x_4801_);
lean_dec(v___x_4801_);
lean_dec(v___x_4800_);
v___x_4803_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0));
v_newEntries_4804_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_fst_4796_, v_fst_4796_, v___x_4802_, v___x_4803_);
lean_dec(v_fst_4796_);
v___x_4805_ = l_List_foldl___redArg(v___f_4799_, v_s_4795_, v_newEntries_4804_);
return v___x_4805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(lean_object* v_inst_4806_, lean_object* v_inst_4807_, lean_object* v_inst_4808_, lean_object* v_oldState_4809_, lean_object* v_newState_4810_, lean_object* v_x_4811_, lean_object* v_s_4812_){
_start:
{
lean_object* v_res_4813_; 
v_res_4813_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(v_inst_4806_, v_inst_4807_, v_inst_4808_, v_oldState_4809_, v_newState_4810_, v_x_4811_, v_s_4812_);
lean_dec(v_x_4811_);
lean_dec_ref(v_oldState_4809_);
return v_res_4813_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0(void){
_start:
{
lean_object* v___x_4814_; 
v___x_4814_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4814_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1(void){
_start:
{
lean_object* v___x_4815_; lean_object* v___x_4816_; 
v___x_4815_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0);
v___x_4816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4816_, 0, v___x_4815_);
return v___x_4816_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2(void){
_start:
{
lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; 
v___x_4817_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1);
v___x_4818_ = lean_box(0);
v___x_4819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4819_, 0, v___x_4818_);
lean_ctor_set(v___x_4819_, 1, v___x_4817_);
return v___x_4819_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3(void){
_start:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; 
v___x_4820_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2);
v___x_4821_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_4821_, 0, lean_box(0));
lean_closure_set(v___x_4821_, 1, lean_box(0));
lean_closure_set(v___x_4821_, 2, v___x_4820_);
return v___x_4821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object* v_inst_4822_, lean_object* v_inst_4823_, lean_object* v_inst_4824_){
_start:
{
lean_object* v___f_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; 
v___f_4826_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4826_, 0, v_inst_4822_);
lean_closure_set(v___f_4826_, 1, v_inst_4823_);
lean_closure_set(v___f_4826_, 2, v_inst_4824_);
v___x_4827_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3);
v___x_4828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4828_, 0, v___f_4826_);
v___x_4829_ = lean_box(0);
v___x_4830_ = l_Lean_registerEnvExtension___redArg(v___x_4827_, v___x_4828_, v___x_4829_);
if (lean_obj_tag(v___x_4830_) == 0)
{
lean_object* v_a_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4838_; 
v_a_4831_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4833_ = v___x_4830_;
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_a_4831_);
lean_dec(v___x_4830_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v___x_4836_; 
if (v_isShared_4834_ == 0)
{
v___x_4836_ = v___x_4833_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_a_4831_);
v___x_4836_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
return v___x_4836_;
}
}
}
else
{
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4846_; 
v_a_4839_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4841_ = v___x_4830_;
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v___x_4830_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v___x_4844_; 
if (v_isShared_4842_ == 0)
{
v___x_4844_ = v___x_4841_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_a_4839_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
return v___x_4844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object* v_inst_4847_, lean_object* v_inst_4848_, lean_object* v_inst_4849_, lean_object* v_a_4850_){
_start:
{
lean_object* v_res_4851_; 
v_res_4851_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4847_, v_inst_4848_, v_inst_4849_);
return v_res_4851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object* v_00_u03b1_4852_, lean_object* v_00_u03b2_4853_, lean_object* v_inst_4854_, lean_object* v_inst_4855_, lean_object* v_inst_4856_){
_start:
{
lean_object* v___x_4858_; 
v___x_4858_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4854_, v_inst_4855_, v_inst_4856_);
return v___x_4858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object* v_00_u03b1_4859_, lean_object* v_00_u03b2_4860_, lean_object* v_inst_4861_, lean_object* v_inst_4862_, lean_object* v_inst_4863_, lean_object* v_a_4864_){
_start:
{
lean_object* v_res_4865_; 
v_res_4865_ = l_Lean_Compiler_LCNF_CacheExtension_register(v_00_u03b1_4859_, v_00_u03b2_4860_, v_inst_4861_, v_inst_4862_, v_inst_4863_);
return v_res_4865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object* v_a_4866_, lean_object* v_inst_4867_, lean_object* v_inst_4868_, lean_object* v_b_4869_, lean_object* v_x_4870_){
_start:
{
lean_object* v_fst_4871_; lean_object* v_snd_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4881_; 
v_fst_4871_ = lean_ctor_get(v_x_4870_, 0);
v_snd_4872_ = lean_ctor_get(v_x_4870_, 1);
v_isSharedCheck_4881_ = !lean_is_exclusive(v_x_4870_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4874_ = v_x_4870_;
v_isShared_4875_ = v_isSharedCheck_4881_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_snd_4872_);
lean_inc(v_fst_4871_);
lean_dec(v_x_4870_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4881_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4879_; 
lean_inc(v_a_4866_);
v___x_4876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4876_, 0, v_a_4866_);
lean_ctor_set(v___x_4876_, 1, v_fst_4871_);
v___x_4877_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4867_, v_inst_4868_, v_snd_4872_, v_a_4866_, v_b_4869_);
if (v_isShared_4875_ == 0)
{
lean_ctor_set(v___x_4874_, 1, v___x_4877_);
lean_ctor_set(v___x_4874_, 0, v___x_4876_);
v___x_4879_ = v___x_4874_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v___x_4876_);
lean_ctor_set(v_reuseFailAlloc_4880_, 1, v___x_4877_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_4882_; 
v___x_4882_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4882_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_4883_; lean_object* v___x_4884_; 
v___x_4883_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0);
v___x_4884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4884_, 0, v___x_4883_);
return v___x_4884_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2(void){
_start:
{
lean_object* v___x_4885_; lean_object* v___x_4886_; 
v___x_4885_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1);
v___x_4886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4886_, 0, v___x_4885_);
lean_ctor_set(v___x_4886_, 1, v___x_4885_);
return v___x_4886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object* v_inst_4887_, lean_object* v_inst_4888_, lean_object* v_ext_4889_, lean_object* v_a_4890_, lean_object* v_b_4891_, lean_object* v_a_4892_){
_start:
{
lean_object* v___x_4894_; lean_object* v_env_4895_; lean_object* v_nextMacroScope_4896_; lean_object* v_ngen_4897_; lean_object* v_auxDeclNGen_4898_; lean_object* v_traceState_4899_; lean_object* v_messages_4900_; lean_object* v_infoState_4901_; lean_object* v_snapshotTasks_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4917_; 
v___x_4894_ = lean_st_ref_take(v_a_4892_);
v_env_4895_ = lean_ctor_get(v___x_4894_, 0);
v_nextMacroScope_4896_ = lean_ctor_get(v___x_4894_, 1);
v_ngen_4897_ = lean_ctor_get(v___x_4894_, 2);
v_auxDeclNGen_4898_ = lean_ctor_get(v___x_4894_, 3);
v_traceState_4899_ = lean_ctor_get(v___x_4894_, 4);
v_messages_4900_ = lean_ctor_get(v___x_4894_, 6);
v_infoState_4901_ = lean_ctor_get(v___x_4894_, 7);
v_snapshotTasks_4902_ = lean_ctor_get(v___x_4894_, 8);
v_isSharedCheck_4917_ = !lean_is_exclusive(v___x_4894_);
if (v_isSharedCheck_4917_ == 0)
{
lean_object* v_unused_4918_; 
v_unused_4918_ = lean_ctor_get(v___x_4894_, 5);
lean_dec(v_unused_4918_);
v___x_4904_ = v___x_4894_;
v_isShared_4905_ = v_isSharedCheck_4917_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_snapshotTasks_4902_);
lean_inc(v_infoState_4901_);
lean_inc(v_messages_4900_);
lean_inc(v_traceState_4899_);
lean_inc(v_auxDeclNGen_4898_);
lean_inc(v_ngen_4897_);
lean_inc(v_nextMacroScope_4896_);
lean_inc(v_env_4895_);
lean_dec(v___x_4894_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4917_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v_asyncMode_4906_; lean_object* v___f_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4912_; 
v_asyncMode_4906_ = lean_ctor_get(v_ext_4889_, 2);
lean_inc(v_asyncMode_4906_);
v___f_4907_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4907_, 0, v_a_4890_);
lean_closure_set(v___f_4907_, 1, v_inst_4887_);
lean_closure_set(v___f_4907_, 2, v_inst_4888_);
lean_closure_set(v___f_4907_, 3, v_b_4891_);
v___x_4908_ = lean_box(0);
v___x_4909_ = l_Lean_EnvExtension_modifyState___redArg(v_ext_4889_, v_env_4895_, v___f_4907_, v_asyncMode_4906_, v___x_4908_);
lean_dec(v_asyncMode_4906_);
v___x_4910_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2);
if (v_isShared_4905_ == 0)
{
lean_ctor_set(v___x_4904_, 5, v___x_4910_);
lean_ctor_set(v___x_4904_, 0, v___x_4909_);
v___x_4912_ = v___x_4904_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v___x_4909_);
lean_ctor_set(v_reuseFailAlloc_4916_, 1, v_nextMacroScope_4896_);
lean_ctor_set(v_reuseFailAlloc_4916_, 2, v_ngen_4897_);
lean_ctor_set(v_reuseFailAlloc_4916_, 3, v_auxDeclNGen_4898_);
lean_ctor_set(v_reuseFailAlloc_4916_, 4, v_traceState_4899_);
lean_ctor_set(v_reuseFailAlloc_4916_, 5, v___x_4910_);
lean_ctor_set(v_reuseFailAlloc_4916_, 6, v_messages_4900_);
lean_ctor_set(v_reuseFailAlloc_4916_, 7, v_infoState_4901_);
lean_ctor_set(v_reuseFailAlloc_4916_, 8, v_snapshotTasks_4902_);
v___x_4912_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; 
v___x_4913_ = lean_st_ref_put(v_a_4892_, v___x_4912_);
v___x_4914_ = lean_box(0);
v___x_4915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4915_, 0, v___x_4914_);
return v___x_4915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object* v_inst_4919_, lean_object* v_inst_4920_, lean_object* v_ext_4921_, lean_object* v_a_4922_, lean_object* v_b_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_){
_start:
{
lean_object* v_res_4926_; 
v_res_4926_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4919_, v_inst_4920_, v_ext_4921_, v_a_4922_, v_b_4923_, v_a_4924_);
lean_dec(v_a_4924_);
return v_res_4926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object* v_00_u03b1_4927_, lean_object* v_00_u03b2_4928_, lean_object* v_inst_4929_, lean_object* v_inst_4930_, lean_object* v_inst_4931_, lean_object* v_ext_4932_, lean_object* v_a_4933_, lean_object* v_b_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_){
_start:
{
lean_object* v___x_4938_; 
v___x_4938_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4929_, v_inst_4930_, v_ext_4932_, v_a_4933_, v_b_4934_, v_a_4936_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object* v_00_u03b1_4939_, lean_object* v_00_u03b2_4940_, lean_object* v_inst_4941_, lean_object* v_inst_4942_, lean_object* v_inst_4943_, lean_object* v_ext_4944_, lean_object* v_a_4945_, lean_object* v_b_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_){
_start:
{
lean_object* v_res_4950_; 
v_res_4950_ = l_Lean_Compiler_LCNF_CacheExtension_insert(v_00_u03b1_4939_, v_00_u03b2_4940_, v_inst_4941_, v_inst_4942_, v_inst_4943_, v_ext_4944_, v_a_4945_, v_b_4946_, v_a_4947_, v_a_4948_);
lean_dec(v_a_4948_);
lean_dec_ref(v_a_4947_);
lean_dec(v_inst_4943_);
return v_res_4950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(lean_object* v_inst_4951_, lean_object* v_inst_4952_, lean_object* v_ext_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_){
_start:
{
lean_object* v___x_4957_; lean_object* v_env_4958_; lean_object* v_asyncMode_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v_snd_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; 
v___x_4957_ = lean_st_ref_get(v_a_4955_);
v_env_4958_ = lean_ctor_get(v___x_4957_, 0);
lean_inc_ref(v_env_4958_);
lean_dec(v___x_4957_);
v_asyncMode_4959_ = lean_ctor_get(v_ext_4953_, 2);
v___x_4960_ = lean_box(0);
v___x_4961_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v_inst_4951_, v_inst_4952_);
v___x_4962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4962_, 0, v___x_4960_);
lean_ctor_set(v___x_4962_, 1, v___x_4961_);
v___x_4963_ = lean_box(0);
v___x_4964_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4962_, v_ext_4953_, v_env_4958_, v_asyncMode_4959_, v___x_4963_);
lean_dec_ref_known(v___x_4962_, 2);
v_snd_4965_ = lean_ctor_get(v___x_4964_, 1);
lean_inc(v_snd_4965_);
lean_dec(v___x_4964_);
v___x_4966_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4951_, v_inst_4952_, v_snd_4965_, v_a_4954_);
lean_dec(v_snd_4965_);
v___x_4967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4967_, 0, v___x_4966_);
return v___x_4967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(lean_object* v_inst_4968_, lean_object* v_inst_4969_, lean_object* v_ext_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_){
_start:
{
lean_object* v_res_4974_; 
v_res_4974_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4968_, v_inst_4969_, v_ext_4970_, v_a_4971_, v_a_4972_);
lean_dec(v_a_4972_);
lean_dec_ref(v_ext_4970_);
return v_res_4974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_object* v_00_u03b1_4975_, lean_object* v_00_u03b2_4976_, lean_object* v_inst_4977_, lean_object* v_inst_4978_, lean_object* v_inst_4979_, lean_object* v_ext_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_){
_start:
{
lean_object* v___x_4985_; 
v___x_4985_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4977_, v_inst_4978_, v_ext_4980_, v_a_4981_, v_a_4983_);
return v___x_4985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(lean_object* v_00_u03b1_4986_, lean_object* v_00_u03b2_4987_, lean_object* v_inst_4988_, lean_object* v_inst_4989_, lean_object* v_inst_4990_, lean_object* v_ext_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_){
_start:
{
lean_object* v_res_4996_; 
v_res_4996_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f(v_00_u03b1_4986_, v_00_u03b2_4987_, v_inst_4988_, v_inst_4989_, v_inst_4990_, v_ext_4991_, v_a_4992_, v_a_4993_, v_a_4994_);
lean_dec(v_a_4994_);
lean_dec_ref(v_a_4993_);
lean_dec_ref(v_ext_4991_);
lean_dec(v_inst_4990_);
return v_res_4996_;
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
