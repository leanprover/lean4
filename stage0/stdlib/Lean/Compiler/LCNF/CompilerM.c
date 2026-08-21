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
v_options_357_ = lean_ctor_get(v___y_342_, 2);
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
v_options_394_ = lean_ctor_get(v___y_391_, 2);
v_ref_395_ = lean_ctor_get(v___y_391_, 5);
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
lean_object* v_fn_1501_; lean_object* v_arg_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; uint8_t v___y_1506_; size_t v___x_1510_; size_t v___x_1511_; uint8_t v___x_1512_; 
v_fn_1501_ = lean_ctor_get(v_e_1487_, 0);
v_arg_1502_ = lean_ctor_get(v_e_1487_, 1);
lean_inc_ref(v_fn_1501_);
v___x_1503_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1484_, v_s_1485_, v_translator_1486_, v_fn_1501_);
lean_inc_ref(v_arg_1502_);
v___x_1504_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1484_, v_s_1485_, v_translator_1486_, v_arg_1502_);
v___x_1510_ = lean_ptr_addr(v_fn_1501_);
v___x_1511_ = lean_ptr_addr(v___x_1503_);
v___x_1512_ = lean_usize_dec_eq(v___x_1510_, v___x_1511_);
if (v___x_1512_ == 0)
{
v___y_1506_ = v___x_1512_;
goto v___jp_1505_;
}
else
{
size_t v___x_1513_; size_t v___x_1514_; uint8_t v___x_1515_; 
v___x_1513_ = lean_ptr_addr(v_arg_1502_);
v___x_1514_ = lean_ptr_addr(v___x_1504_);
v___x_1515_ = lean_usize_dec_eq(v___x_1513_, v___x_1514_);
v___y_1506_ = v___x_1515_;
goto v___jp_1505_;
}
v___jp_1505_:
{
if (v___y_1506_ == 0)
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
lean_dec_ref_known(v_e_1487_, 2);
v___x_1507_ = l_Lean_Expr_app___override(v___x_1503_, v___x_1504_);
v___x_1508_ = l_Lean_Expr_headBeta(v___x_1507_);
return v___x_1508_;
}
else
{
lean_object* v___x_1509_; 
lean_dec_ref(v___x_1504_);
lean_dec_ref(v___x_1503_);
v___x_1509_ = l_Lean_Expr_headBeta(v_e_1487_);
return v___x_1509_;
}
}
}
case 6:
{
lean_object* v_binderName_1516_; lean_object* v_binderType_1517_; lean_object* v_body_1518_; uint8_t v_binderInfo_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; uint8_t v___y_1523_; size_t v___x_1527_; size_t v___x_1528_; uint8_t v___x_1529_; 
v_binderName_1516_ = lean_ctor_get(v_e_1487_, 0);
v_binderType_1517_ = lean_ctor_get(v_e_1487_, 1);
v_body_1518_ = lean_ctor_get(v_e_1487_, 2);
v_binderInfo_1519_ = lean_ctor_get_uint8(v_e_1487_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1517_);
v___x_1520_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1484_, v_s_1485_, v_translator_1486_, v_binderType_1517_);
lean_inc_ref(v_body_1518_);
v___x_1521_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1484_, v_s_1485_, v_translator_1486_, v_body_1518_);
v___x_1527_ = lean_ptr_addr(v_binderType_1517_);
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
v___x_1530_ = lean_ptr_addr(v_body_1518_);
v___x_1531_ = lean_ptr_addr(v___x_1521_);
v___x_1532_ = lean_usize_dec_eq(v___x_1530_, v___x_1531_);
v___y_1523_ = v___x_1532_;
goto v___jp_1522_;
}
v___jp_1522_:
{
if (v___y_1523_ == 0)
{
lean_object* v___x_1524_; 
lean_inc(v_binderName_1516_);
lean_dec_ref_known(v_e_1487_, 3);
v___x_1524_ = l_Lean_Expr_lam___override(v_binderName_1516_, v___x_1520_, v___x_1521_, v_binderInfo_1519_);
return v___x_1524_;
}
else
{
uint8_t v___x_1525_; 
v___x_1525_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1519_, v_binderInfo_1519_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; 
lean_inc(v_binderName_1516_);
lean_dec_ref_known(v_e_1487_, 3);
v___x_1526_ = l_Lean_Expr_lam___override(v_binderName_1516_, v___x_1520_, v___x_1521_, v_binderInfo_1519_);
return v___x_1526_;
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
lean_object* v_binderName_1533_; lean_object* v_binderType_1534_; lean_object* v_body_1535_; uint8_t v_binderInfo_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___y_1540_; size_t v___x_1544_; size_t v___x_1545_; uint8_t v___x_1546_; 
v_binderName_1533_ = lean_ctor_get(v_e_1487_, 0);
v_binderType_1534_ = lean_ctor_get(v_e_1487_, 1);
v_body_1535_ = lean_ctor_get(v_e_1487_, 2);
v_binderInfo_1536_ = lean_ctor_get_uint8(v_e_1487_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1534_);
v___x_1537_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1484_, v_s_1485_, v_translator_1486_, v_binderType_1534_);
lean_inc_ref(v_body_1535_);
v___x_1538_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1484_, v_s_1485_, v_translator_1486_, v_body_1535_);
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
lean_dec_ref_known(v_e_1487_, 3);
v___x_1541_ = l_Lean_Expr_forallE___override(v_binderName_1533_, v___x_1537_, v___x_1538_, v_binderInfo_1536_);
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
lean_dec_ref_known(v_e_1487_, 3);
v___x_1543_ = l_Lean_Expr_forallE___override(v_binderName_1533_, v___x_1537_, v___x_1538_, v_binderInfo_1536_);
return v___x_1543_;
}
else
{
lean_dec_ref(v___x_1538_);
lean_dec_ref(v___x_1537_);
return v_e_1487_;
}
}
}
}
case 8:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec_ref_known(v_e_1487_, 4);
v___x_1550_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3, &l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3);
v___x_1551_ = l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(v___x_1550_);
return v___x_1551_;
}
case 10:
{
lean_object* v_data_1552_; lean_object* v_expr_1553_; lean_object* v___x_1554_; size_t v___x_1555_; size_t v___x_1556_; uint8_t v___x_1557_; 
v_data_1552_ = lean_ctor_get(v_e_1487_, 0);
v_expr_1553_ = lean_ctor_get(v_e_1487_, 1);
lean_inc_ref(v_expr_1553_);
v___x_1554_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1484_, v_s_1485_, v_translator_1486_, v_expr_1553_);
v___x_1555_ = lean_ptr_addr(v_expr_1553_);
v___x_1556_ = lean_ptr_addr(v___x_1554_);
v___x_1557_ = lean_usize_dec_eq(v___x_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; 
lean_inc(v_data_1552_);
lean_dec_ref_known(v_e_1487_, 2);
v___x_1558_ = l_Lean_Expr_mdata___override(v_data_1552_, v___x_1554_);
return v___x_1558_;
}
else
{
lean_dec_ref(v___x_1554_);
return v_e_1487_;
}
}
case 11:
{
lean_object* v_typeName_1559_; lean_object* v_idx_1560_; lean_object* v_struct_1561_; lean_object* v___x_1562_; size_t v___x_1563_; size_t v___x_1564_; uint8_t v___x_1565_; 
v_typeName_1559_ = lean_ctor_get(v_e_1487_, 0);
v_idx_1560_ = lean_ctor_get(v_e_1487_, 1);
v_struct_1561_ = lean_ctor_get(v_e_1487_, 2);
lean_inc_ref(v_struct_1561_);
v___x_1562_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1484_, v_s_1485_, v_translator_1486_, v_struct_1561_);
v___x_1563_ = lean_ptr_addr(v_struct_1561_);
v___x_1564_ = lean_ptr_addr(v___x_1562_);
v___x_1565_ = lean_usize_dec_eq(v___x_1563_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; 
lean_inc(v_idx_1560_);
lean_inc(v_typeName_1559_);
lean_dec_ref_known(v_e_1487_, 3);
v___x_1566_ = l_Lean_Expr_proj___override(v_typeName_1559_, v_idx_1560_, v___x_1562_);
return v___x_1566_;
}
else
{
lean_dec_ref(v___x_1562_);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(uint8_t v_pu_1567_, lean_object* v_s_1568_, uint8_t v_translator_1569_, lean_object* v_e_1570_){
_start:
{
if (lean_obj_tag(v_e_1570_) == 5)
{
lean_object* v_fn_1571_; lean_object* v_arg_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___y_1576_; size_t v___x_1578_; size_t v___x_1579_; uint8_t v___x_1580_; 
v_fn_1571_ = lean_ctor_get(v_e_1570_, 0);
v_arg_1572_ = lean_ctor_get(v_e_1570_, 1);
lean_inc_ref(v_fn_1571_);
v___x_1573_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1567_, v_s_1568_, v_translator_1569_, v_fn_1571_);
lean_inc_ref(v_arg_1572_);
v___x_1574_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1567_, v_s_1568_, v_translator_1569_, v_arg_1572_);
v___x_1578_ = lean_ptr_addr(v_fn_1571_);
v___x_1579_ = lean_ptr_addr(v___x_1573_);
v___x_1580_ = lean_usize_dec_eq(v___x_1578_, v___x_1579_);
if (v___x_1580_ == 0)
{
v___y_1576_ = v___x_1580_;
goto v___jp_1575_;
}
else
{
size_t v___x_1581_; size_t v___x_1582_; uint8_t v___x_1583_; 
v___x_1581_ = lean_ptr_addr(v_arg_1572_);
v___x_1582_ = lean_ptr_addr(v___x_1574_);
v___x_1583_ = lean_usize_dec_eq(v___x_1581_, v___x_1582_);
v___y_1576_ = v___x_1583_;
goto v___jp_1575_;
}
v___jp_1575_:
{
if (v___y_1576_ == 0)
{
lean_object* v___x_1577_; 
lean_dec_ref_known(v_e_1570_, 2);
v___x_1577_ = l_Lean_Expr_app___override(v___x_1573_, v___x_1574_);
return v___x_1577_;
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
lean_object* v___x_1584_; 
v___x_1584_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1567_, v_s_1568_, v_translator_1569_, v_e_1570_);
return v___x_1584_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(lean_object* v_pu_1585_, lean_object* v_s_1586_, lean_object* v_translator_1587_, lean_object* v_e_1588_){
_start:
{
uint8_t v_pu_boxed_1589_; uint8_t v_translator_boxed_1590_; lean_object* v_res_1591_; 
v_pu_boxed_1589_ = lean_unbox(v_pu_1585_);
v_translator_boxed_1590_ = lean_unbox(v_translator_1587_);
v_res_1591_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_boxed_1589_, v_s_1586_, v_translator_boxed_1590_, v_e_1588_);
lean_dec_ref(v_s_1586_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(lean_object* v_pu_1592_, lean_object* v_s_1593_, lean_object* v_translator_1594_, lean_object* v_e_1595_){
_start:
{
uint8_t v_pu_boxed_1596_; uint8_t v_translator_boxed_1597_; lean_object* v_res_1598_; 
v_pu_boxed_1596_ = lean_unbox(v_pu_1592_);
v_translator_boxed_1597_ = lean_unbox(v_translator_1594_);
v_res_1598_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_boxed_1596_, v_s_1593_, v_translator_boxed_1597_, v_e_1595_);
lean_dec_ref(v_s_1593_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(uint8_t v_pu_1599_, lean_object* v_s_1600_, lean_object* v_e_1601_, uint8_t v_translator_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1599_, v_s_1600_, v_translator_1602_, v_e_1601_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(lean_object* v_pu_1604_, lean_object* v_s_1605_, lean_object* v_e_1606_, lean_object* v_translator_1607_){
_start:
{
uint8_t v_pu_boxed_1608_; uint8_t v_translator_boxed_1609_; lean_object* v_res_1610_; 
v_pu_boxed_1608_ = lean_unbox(v_pu_1604_);
v_translator_boxed_1609_ = lean_unbox(v_translator_1607_);
v_res_1610_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(v_pu_boxed_1608_, v_s_1605_, v_e_1606_, v_translator_boxed_1609_);
lean_dec_ref(v_s_1605_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(lean_object* v_x_1611_){
_start:
{
if (lean_obj_tag(v_x_1611_) == 0)
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_unsigned_to_nat(0u);
return v___x_1612_;
}
else
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_unsigned_to_nat(1u);
return v___x_1613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___boxed(lean_object* v_x_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(v_x_1614_);
lean_dec(v_x_1614_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(lean_object* v_t_1616_, lean_object* v_k_1617_){
_start:
{
if (lean_obj_tag(v_t_1616_) == 0)
{
lean_object* v_fvarId_1618_; lean_object* v___x_1619_; 
v_fvarId_1618_ = lean_ctor_get(v_t_1616_, 0);
lean_inc(v_fvarId_1618_);
lean_dec_ref_known(v_t_1616_, 1);
v___x_1619_ = lean_apply_1(v_k_1617_, v_fvarId_1618_);
return v___x_1619_;
}
else
{
return v_k_1617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(lean_object* v_motive_1620_, lean_object* v_ctorIdx_1621_, lean_object* v_t_1622_, lean_object* v_h_1623_, lean_object* v_k_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1622_, v_k_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___boxed(lean_object* v_motive_1626_, lean_object* v_ctorIdx_1627_, lean_object* v_t_1628_, lean_object* v_h_1629_, lean_object* v_k_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(v_motive_1626_, v_ctorIdx_1627_, v_t_1628_, v_h_1629_, v_k_1630_);
lean_dec(v_ctorIdx_1627_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim___redArg(lean_object* v_t_1632_, lean_object* v_fvar_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1632_, v_fvar_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim(lean_object* v_motive_1635_, lean_object* v_t_1636_, lean_object* v_h_1637_, lean_object* v_fvar_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1636_, v_fvar_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim___redArg(lean_object* v_t_1640_, lean_object* v_erased_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1640_, v_erased_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim(lean_object* v_motive_1643_, lean_object* v_t_1644_, lean_object* v_h_1645_, lean_object* v_erased_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1644_, v_erased_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object* v_s_1652_, lean_object* v_fvarId_1653_, uint8_t v_translator_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1652_, v_fvarId_1653_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1656_, 0, v_fvarId_1653_);
return v___x_1656_;
}
else
{
lean_object* v_val_1657_; 
lean_dec(v_fvarId_1653_);
v_val_1657_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_val_1657_);
lean_dec_ref_known(v___x_1655_, 1);
if (lean_obj_tag(v_val_1657_) == 1)
{
if (v_translator_1654_ == 0)
{
lean_object* v_fvarId_1658_; 
v_fvarId_1658_ = lean_ctor_get(v_val_1657_, 0);
lean_inc(v_fvarId_1658_);
lean_dec_ref_known(v_val_1657_, 1);
v_fvarId_1653_ = v_fvarId_1658_;
goto _start;
}
else
{
lean_object* v_fvarId_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
v_fvarId_1660_ = lean_ctor_get(v_val_1657_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_val_1657_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v_val_1657_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_fvarId_1660_);
lean_dec(v_val_1657_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
lean_ctor_set_tag(v___x_1662_, 0);
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_fvarId_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
else
{
lean_object* v___x_1668_; 
lean_dec(v_val_1657_);
v___x_1668_ = lean_box(1);
return v___x_1668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg___boxed(lean_object* v_s_1669_, lean_object* v_fvarId_1670_, lean_object* v_translator_1671_){
_start:
{
uint8_t v_translator_boxed_1672_; lean_object* v_res_1673_; 
v_translator_boxed_1672_ = lean_unbox(v_translator_1671_);
v_res_1673_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1669_, v_fvarId_1670_, v_translator_boxed_1672_);
lean_dec_ref(v_s_1669_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp(uint8_t v_pu_1674_, lean_object* v_s_1675_, lean_object* v_fvarId_1676_, uint8_t v_translator_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1675_, v_fvarId_1676_, v_translator_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___boxed(lean_object* v_pu_1679_, lean_object* v_s_1680_, lean_object* v_fvarId_1681_, lean_object* v_translator_1682_){
_start:
{
uint8_t v_pu_boxed_1683_; uint8_t v_translator_boxed_1684_; lean_object* v_res_1685_; 
v_pu_boxed_1683_ = lean_unbox(v_pu_1679_);
v_translator_boxed_1684_ = lean_unbox(v_translator_1682_);
v_res_1685_ = l_Lean_Compiler_LCNF_normFVarImp(v_pu_boxed_1683_, v_s_1680_, v_fvarId_1681_, v_translator_boxed_1684_);
lean_dec_ref(v_s_1680_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t v_pu_1686_, lean_object* v_s_1687_, lean_object* v_arg_1688_, uint8_t v_translator_1689_){
_start:
{
switch(lean_obj_tag(v_arg_1688_))
{
case 0:
{
return v_arg_1688_;
}
case 1:
{
lean_object* v_fvarId_1690_; lean_object* v___x_1691_; 
v_fvarId_1690_ = lean_ctor_get(v_arg_1688_, 0);
v___x_1691_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1687_, v_fvarId_1690_);
if (lean_obj_tag(v___x_1691_) == 0)
{
return v_arg_1688_;
}
else
{
lean_object* v_val_1692_; 
lean_dec_ref_known(v_arg_1688_, 1);
v_val_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_val_1692_);
lean_dec_ref_known(v___x_1691_, 1);
switch(lean_obj_tag(v_val_1692_))
{
case 0:
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_box(0);
return v___x_1693_;
}
case 1:
{
lean_object* v_fvarId_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1702_; 
v_fvarId_1694_ = lean_ctor_get(v_val_1692_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_val_1692_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1696_ = v_val_1692_;
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_fvarId_1694_);
lean_dec(v_val_1692_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_fvarId_1694_);
v___x_1699_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
if (v_translator_1689_ == 0)
{
v_arg_1688_ = v___x_1699_;
goto _start;
}
else
{
return v___x_1699_;
}
}
}
}
default: 
{
lean_object* v_expr_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
v_expr_1703_ = lean_ctor_get(v_val_1692_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_val_1692_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v_val_1692_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_expr_1703_);
lean_dec(v_val_1692_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_expr_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
}
default: 
{
lean_object* v_expr_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_expr_1711_ = lean_ctor_get(v_arg_1688_, 0);
lean_inc_ref(v_expr_1711_);
v___x_1712_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1686_, v_s_1687_, v_translator_1689_, v_expr_1711_);
v___x_1713_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1686_, v_arg_1688_, v___x_1712_);
return v___x_1713_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp___boxed(lean_object* v_pu_1714_, lean_object* v_s_1715_, lean_object* v_arg_1716_, lean_object* v_translator_1717_){
_start:
{
uint8_t v_pu_boxed_1718_; uint8_t v_translator_boxed_1719_; lean_object* v_res_1720_; 
v_pu_boxed_1718_ = lean_unbox(v_pu_1714_);
v_translator_boxed_1719_ = lean_unbox(v_translator_1717_);
v_res_1720_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_boxed_1718_, v_s_1715_, v_arg_1716_, v_translator_boxed_1719_);
lean_dec_ref(v_s_1715_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(uint8_t v_pu_1721_, lean_object* v_s_1722_, uint8_t v_translator_1723_, lean_object* v_i_1724_, lean_object* v_as_1725_){
_start:
{
lean_object* v___x_1726_; uint8_t v___x_1727_; 
v___x_1726_ = lean_array_get_size(v_as_1725_);
v___x_1727_ = lean_nat_dec_lt(v_i_1724_, v___x_1726_);
if (v___x_1727_ == 0)
{
lean_dec(v_i_1724_);
return v_as_1725_;
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1729_; size_t v___x_1730_; size_t v___x_1731_; uint8_t v___x_1732_; 
v_a_1728_ = lean_array_fget_borrowed(v_as_1725_, v_i_1724_);
lean_inc(v_a_1728_);
v___x_1729_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1721_, v_s_1722_, v_a_1728_, v_translator_1723_);
v___x_1730_ = lean_ptr_addr(v_a_1728_);
v___x_1731_ = lean_ptr_addr(v___x_1729_);
v___x_1732_ = lean_usize_dec_eq(v___x_1730_, v___x_1731_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1733_ = lean_unsigned_to_nat(1u);
v___x_1734_ = lean_nat_add(v_i_1724_, v___x_1733_);
v___x_1735_ = lean_array_fset(v_as_1725_, v_i_1724_, v___x_1729_);
lean_dec(v_i_1724_);
v_i_1724_ = v___x_1734_;
v_as_1725_ = v___x_1735_;
goto _start;
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_dec(v___x_1729_);
v___x_1737_ = lean_unsigned_to_nat(1u);
v___x_1738_ = lean_nat_add(v_i_1724_, v___x_1737_);
lean_dec(v_i_1724_);
v_i_1724_ = v___x_1738_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0___boxed(lean_object* v_pu_1740_, lean_object* v_s_1741_, lean_object* v_translator_1742_, lean_object* v_i_1743_, lean_object* v_as_1744_){
_start:
{
uint8_t v_pu_boxed_1745_; uint8_t v_translator_boxed_1746_; lean_object* v_res_1747_; 
v_pu_boxed_1745_ = lean_unbox(v_pu_1740_);
v_translator_boxed_1746_ = lean_unbox(v_translator_1742_);
v_res_1747_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_boxed_1745_, v_s_1741_, v_translator_boxed_1746_, v_i_1743_, v_as_1744_);
lean_dec_ref(v_s_1741_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t v_pu_1748_, lean_object* v_s_1749_, lean_object* v_args_1750_, uint8_t v_translator_1751_){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = lean_unsigned_to_nat(0u);
v___x_1753_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_1748_, v_s_1749_, v_translator_1751_, v___x_1752_, v_args_1750_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp___boxed(lean_object* v_pu_1754_, lean_object* v_s_1755_, lean_object* v_args_1756_, lean_object* v_translator_1757_){
_start:
{
uint8_t v_pu_boxed_1758_; uint8_t v_translator_boxed_1759_; lean_object* v_res_1760_; 
v_pu_boxed_1758_ = lean_unbox(v_pu_1754_);
v_translator_boxed_1759_ = lean_unbox(v_translator_1757_);
v_res_1760_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_boxed_1758_, v_s_1755_, v_args_1756_, v_translator_boxed_1759_);
lean_dec_ref(v_s_1755_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t v_pu_1761_, lean_object* v_s_1762_, lean_object* v_e_1763_, uint8_t v_translator_1764_){
_start:
{
lean_object* v_fvarId_1766_; lean_object* v_args_1772_; 
switch(lean_obj_tag(v_e_1763_))
{
case 2:
{
lean_object* v_struct_1775_; lean_object* v___x_1776_; 
v_struct_1775_ = lean_ctor_get(v_e_1763_, 2);
lean_inc(v_struct_1775_);
v___x_1776_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1762_, v_struct_1775_, v_translator_1764_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_fvarId_1777_; lean_object* v___x_1778_; 
v_fvarId_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_fvarId_1777_);
lean_dec_ref_known(v___x_1776_, 1);
v___x_1778_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1761_, v_e_1763_, v_fvarId_1777_);
return v___x_1778_;
}
else
{
lean_object* v___x_1779_; 
lean_dec_ref_known(v_e_1763_, 3);
v___x_1779_ = lean_box(1);
return v___x_1779_;
}
}
case 3:
{
lean_object* v_args_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v_args_1780_ = lean_ctor_get(v_e_1763_, 2);
lean_inc_ref(v_args_1780_);
v___x_1781_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1761_, v_s_1762_, v_args_1780_, v_translator_1764_);
v___x_1782_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1761_, v_e_1763_, v___x_1781_);
return v___x_1782_;
}
case 4:
{
lean_object* v_fvarId_1783_; lean_object* v_args_1784_; lean_object* v___x_1785_; 
v_fvarId_1783_ = lean_ctor_get(v_e_1763_, 0);
v_args_1784_ = lean_ctor_get(v_e_1763_, 1);
lean_inc(v_fvarId_1783_);
v___x_1785_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1762_, v_fvarId_1783_, v_translator_1764_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_fvarId_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_fvarId_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_fvarId_1786_);
lean_dec_ref_known(v___x_1785_, 1);
lean_inc_ref(v_args_1784_);
v___x_1787_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1761_, v_s_1762_, v_args_1784_, v_translator_1764_);
v___x_1788_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_1761_, v_e_1763_, v_fvarId_1786_, v___x_1787_);
lean_dec_ref_known(v_e_1763_, 2);
return v___x_1788_;
}
else
{
lean_object* v___x_1789_; 
lean_dec_ref_known(v_e_1763_, 2);
v___x_1789_ = lean_box(1);
return v___x_1789_;
}
}
case 5:
{
lean_object* v_args_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v_args_1790_ = lean_ctor_get(v_e_1763_, 1);
lean_inc_ref(v_args_1790_);
v___x_1791_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1761_, v_s_1762_, v_args_1790_, v_translator_1764_);
v___x_1792_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1761_, v_e_1763_, v___x_1791_);
return v___x_1792_;
}
case 6:
{
lean_object* v_var_1793_; 
v_var_1793_ = lean_ctor_get(v_e_1763_, 1);
lean_inc(v_var_1793_);
v_fvarId_1766_ = v_var_1793_;
goto v___jp_1765_;
}
case 7:
{
lean_object* v_var_1794_; 
v_var_1794_ = lean_ctor_get(v_e_1763_, 1);
lean_inc(v_var_1794_);
v_fvarId_1766_ = v_var_1794_;
goto v___jp_1765_;
}
case 8:
{
lean_object* v_var_1795_; lean_object* v___x_1796_; 
v_var_1795_ = lean_ctor_get(v_e_1763_, 2);
lean_inc(v_var_1795_);
v___x_1796_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1762_, v_var_1795_, v_translator_1764_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_fvarId_1797_; lean_object* v___x_1798_; 
v_fvarId_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_fvarId_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___x_1798_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1761_, v_e_1763_, v_fvarId_1797_);
return v___x_1798_;
}
else
{
lean_object* v___x_1799_; 
lean_dec_ref_known(v_e_1763_, 3);
v___x_1799_ = lean_box(1);
return v___x_1799_;
}
}
case 9:
{
lean_object* v_args_1800_; 
v_args_1800_ = lean_ctor_get(v_e_1763_, 1);
lean_inc_ref(v_args_1800_);
v_args_1772_ = v_args_1800_;
goto v___jp_1771_;
}
case 10:
{
lean_object* v_args_1801_; 
v_args_1801_ = lean_ctor_get(v_e_1763_, 1);
lean_inc_ref(v_args_1801_);
v_args_1772_ = v_args_1801_;
goto v___jp_1771_;
}
case 11:
{
lean_object* v_n_1802_; lean_object* v_var_1803_; lean_object* v___x_1804_; 
v_n_1802_ = lean_ctor_get(v_e_1763_, 0);
lean_inc(v_n_1802_);
v_var_1803_ = lean_ctor_get(v_e_1763_, 1);
lean_inc(v_var_1803_);
v___x_1804_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1762_, v_var_1803_, v_translator_1764_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_fvarId_1805_; lean_object* v___x_1806_; 
v_fvarId_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_fvarId_1805_);
lean_dec_ref_known(v___x_1804_, 1);
v___x_1806_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_1761_, v_e_1763_, v_n_1802_, v_fvarId_1805_);
lean_dec_ref_known(v_e_1763_, 2);
return v___x_1806_;
}
else
{
lean_object* v___x_1807_; 
lean_dec(v_n_1802_);
lean_dec_ref_known(v_e_1763_, 2);
v___x_1807_ = lean_box(1);
return v___x_1807_;
}
}
case 12:
{
lean_object* v_var_1808_; lean_object* v_i_1809_; uint8_t v_updateHeader_1810_; lean_object* v_args_1811_; lean_object* v___x_1812_; 
v_var_1808_ = lean_ctor_get(v_e_1763_, 0);
v_i_1809_ = lean_ctor_get(v_e_1763_, 1);
lean_inc_ref(v_i_1809_);
v_updateHeader_1810_ = lean_ctor_get_uint8(v_e_1763_, sizeof(void*)*3);
v_args_1811_ = lean_ctor_get(v_e_1763_, 2);
lean_inc(v_var_1808_);
v___x_1812_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1762_, v_var_1808_, v_translator_1764_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_fvarId_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v_fvarId_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_fvarId_1813_);
lean_dec_ref_known(v___x_1812_, 1);
lean_inc_ref(v_args_1811_);
v___x_1814_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1761_, v_s_1762_, v_args_1811_, v_translator_1764_);
v___x_1815_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_1761_, v_e_1763_, v_fvarId_1813_, v_i_1809_, v_updateHeader_1810_, v___x_1814_);
return v___x_1815_;
}
else
{
lean_object* v___x_1816_; 
lean_dec_ref(v_i_1809_);
lean_dec_ref_known(v_e_1763_, 3);
v___x_1816_ = lean_box(1);
return v___x_1816_;
}
}
case 13:
{
lean_object* v_ty_1817_; lean_object* v_fvarId_1818_; lean_object* v___x_1819_; 
v_ty_1817_ = lean_ctor_get(v_e_1763_, 0);
lean_inc_ref(v_ty_1817_);
v_fvarId_1818_ = lean_ctor_get(v_e_1763_, 1);
lean_inc(v_fvarId_1818_);
v___x_1819_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1762_, v_fvarId_1818_, v_translator_1764_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_fvarId_1820_; lean_object* v___x_1821_; 
v_fvarId_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_fvarId_1820_);
lean_dec_ref_known(v___x_1819_, 1);
v___x_1821_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_1761_, v_e_1763_, v_ty_1817_, v_fvarId_1820_);
lean_dec_ref_known(v_e_1763_, 2);
return v___x_1821_;
}
else
{
lean_object* v___x_1822_; 
lean_dec_ref_known(v_e_1763_, 2);
lean_dec_ref(v_ty_1817_);
v___x_1822_ = lean_box(1);
return v___x_1822_;
}
}
case 14:
{
lean_object* v_fvarId_1823_; lean_object* v___x_1824_; 
v_fvarId_1823_ = lean_ctor_get(v_e_1763_, 0);
lean_inc(v_fvarId_1823_);
v___x_1824_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1762_, v_fvarId_1823_, v_translator_1764_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_fvarId_1825_; lean_object* v___x_1826_; 
v_fvarId_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_fvarId_1825_);
lean_dec_ref_known(v___x_1824_, 1);
v___x_1826_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_1761_, v_e_1763_, v_fvarId_1825_);
return v___x_1826_;
}
else
{
lean_object* v___x_1827_; 
lean_dec_ref_known(v_e_1763_, 1);
v___x_1827_ = lean_box(1);
return v___x_1827_;
}
}
case 15:
{
lean_object* v_fvarId_1828_; lean_object* v___x_1829_; 
v_fvarId_1828_ = lean_ctor_get(v_e_1763_, 0);
lean_inc(v_fvarId_1828_);
v___x_1829_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1762_, v_fvarId_1828_, v_translator_1764_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_fvarId_1830_; lean_object* v___x_1831_; 
v_fvarId_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_fvarId_1830_);
lean_dec_ref_known(v___x_1829_, 1);
v___x_1831_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_1761_, v_e_1763_, v_fvarId_1830_);
return v___x_1831_;
}
else
{
lean_object* v___x_1832_; 
lean_dec_ref_known(v_e_1763_, 1);
v___x_1832_ = lean_box(1);
return v___x_1832_;
}
}
default: 
{
return v_e_1763_;
}
}
v___jp_1765_:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1762_, v_fvarId_1766_, v_translator_1764_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_fvarId_1768_; lean_object* v___x_1769_; 
v_fvarId_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_fvarId_1768_);
lean_dec_ref_known(v___x_1767_, 1);
v___x_1769_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1761_, v_e_1763_, v_fvarId_1768_);
return v___x_1769_;
}
else
{
lean_object* v___x_1770_; 
lean_dec(v_e_1763_);
v___x_1770_ = lean_box(1);
return v___x_1770_;
}
}
v___jp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1761_, v_s_1762_, v_args_1772_, v_translator_1764_);
v___x_1774_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1761_, v_e_1763_, v___x_1773_);
return v___x_1774_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp___boxed(lean_object* v_pu_1833_, lean_object* v_s_1834_, lean_object* v_e_1835_, lean_object* v_translator_1836_){
_start:
{
uint8_t v_pu_boxed_1837_; uint8_t v_translator_boxed_1838_; lean_object* v_res_1839_; 
v_pu_boxed_1837_ = lean_unbox(v_pu_1833_);
v_translator_boxed_1838_ = lean_unbox(v_translator_1836_);
v_res_1839_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_boxed_1837_, v_s_1834_, v_e_1835_, v_translator_boxed_1838_);
lean_dec_ref(v_s_1834_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___redArg(lean_object* v_inst_1840_, lean_object* v_inst_1841_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_apply_2(v_inst_1840_, lean_box(0), v_inst_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(uint8_t v_pu_1843_, uint8_t v_t_1844_, lean_object* v_m_1845_, lean_object* v_n_1846_, lean_object* v_inst_1847_, lean_object* v_inst_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_apply_2(v_inst_1847_, lean_box(0), v_inst_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___boxed(lean_object* v_pu_1850_, lean_object* v_t_1851_, lean_object* v_m_1852_, lean_object* v_n_1853_, lean_object* v_inst_1854_, lean_object* v_inst_1855_){
_start:
{
uint8_t v_pu_boxed_1856_; uint8_t v_t_boxed_1857_; lean_object* v_res_1858_; 
v_pu_boxed_1856_ = lean_unbox(v_pu_1850_);
v_t_boxed_1857_ = lean_unbox(v_t_1851_);
v_res_1858_ = l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(v_pu_boxed_1856_, v_t_boxed_1857_, v_m_1852_, v_n_1853_, v_inst_1854_, v_inst_1855_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0(lean_object* v_inst_1859_, lean_object* v_inst_1860_, lean_object* v_f_1861_){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = lean_apply_1(v_inst_1859_, v_f_1861_);
v___x_1863_ = lean_apply_2(v_inst_1860_, lean_box(0), v___x_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg(lean_object* v_inst_1864_, lean_object* v_inst_1865_){
_start:
{
lean_object* v___f_1866_; 
v___f_1866_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1866_, 0, v_inst_1865_);
lean_closure_set(v___f_1866_, 1, v_inst_1864_);
return v___f_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(uint8_t v_pu_1867_, lean_object* v_m_1868_, lean_object* v_n_1869_, lean_object* v_inst_1870_, lean_object* v_inst_1871_){
_start:
{
lean_object* v___f_1872_; 
v___f_1872_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1872_, 0, v_inst_1871_);
lean_closure_set(v___f_1872_, 1, v_inst_1870_);
return v___f_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___boxed(lean_object* v_pu_1873_, lean_object* v_m_1874_, lean_object* v_n_1875_, lean_object* v_inst_1876_, lean_object* v_inst_1877_){
_start:
{
uint8_t v_pu_boxed_1878_; lean_object* v_res_1879_; 
v_pu_boxed_1878_ = lean_unbox(v_pu_1873_);
v_res_1879_ = l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(v_pu_boxed_1878_, v_m_1874_, v_n_1875_, v_inst_1876_, v_inst_1877_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___lam__0(lean_object* v___x_1880_, lean_object* v___x_1881_, lean_object* v_fvarId_1882_, lean_object* v_arg_1883_, lean_object* v_s_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1880_, v___x_1881_, v_s_1884_, v_fvarId_1882_, v_arg_1883_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg(lean_object* v_inst_1888_, lean_object* v_fvarId_1889_, lean_object* v_arg_1890_){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___f_1893_; lean_object* v___x_1894_; 
v___x_1891_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1892_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1893_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1893_, 0, v___x_1891_);
lean_closure_set(v___f_1893_, 1, v___x_1892_);
lean_closure_set(v___f_1893_, 2, v_fvarId_1889_);
lean_closure_set(v___f_1893_, 3, v_arg_1890_);
v___x_1894_ = lean_apply_1(v_inst_1888_, v___f_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst(lean_object* v_m_1895_, uint8_t v_pu_1896_, lean_object* v_inst_1897_, lean_object* v_fvarId_1898_, lean_object* v_arg_1899_){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___f_1902_; lean_object* v___x_1903_; 
v___x_1900_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1901_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1902_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1902_, 0, v___x_1900_);
lean_closure_set(v___f_1902_, 1, v___x_1901_);
lean_closure_set(v___f_1902_, 2, v_fvarId_1898_);
lean_closure_set(v___f_1902_, 3, v_arg_1899_);
v___x_1903_ = lean_apply_1(v_inst_1897_, v___f_1902_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___boxed(lean_object* v_m_1904_, lean_object* v_pu_1905_, lean_object* v_inst_1906_, lean_object* v_fvarId_1907_, lean_object* v_arg_1908_){
_start:
{
uint8_t v_pu_boxed_1909_; lean_object* v_res_1910_; 
v_pu_boxed_1909_ = lean_unbox(v_pu_1905_);
v_res_1910_ = l_Lean_Compiler_LCNF_addSubst(v_m_1904_, v_pu_boxed_1909_, v_inst_1906_, v_fvarId_1907_, v_arg_1908_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0(lean_object* v_fvarId_x27_1911_, lean_object* v___x_1912_, lean_object* v___x_1913_, lean_object* v_fvarId_1914_, lean_object* v_s_1915_){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_fvarId_x27_1911_);
v___x_1917_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1912_, v___x_1913_, v_s_1915_, v_fvarId_1914_, v___x_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg(lean_object* v_inst_1918_, lean_object* v_fvarId_1919_, lean_object* v_fvarId_x27_1920_){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___f_1923_; lean_object* v___x_1924_; 
v___x_1921_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1922_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1923_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1923_, 0, v_fvarId_x27_1920_);
lean_closure_set(v___f_1923_, 1, v___x_1921_);
lean_closure_set(v___f_1923_, 2, v___x_1922_);
lean_closure_set(v___f_1923_, 3, v_fvarId_1919_);
v___x_1924_ = lean_apply_1(v_inst_1918_, v___f_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst(lean_object* v_m_1925_, uint8_t v_ph_1926_, lean_object* v_inst_1927_, lean_object* v_fvarId_1928_, lean_object* v_fvarId_x27_1929_){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___f_1932_; lean_object* v___x_1933_; 
v___x_1930_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1931_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1932_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1932_, 0, v_fvarId_x27_1929_);
lean_closure_set(v___f_1932_, 1, v___x_1930_);
lean_closure_set(v___f_1932_, 2, v___x_1931_);
lean_closure_set(v___f_1932_, 3, v_fvarId_1928_);
v___x_1933_ = lean_apply_1(v_inst_1927_, v___f_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___boxed(lean_object* v_m_1934_, lean_object* v_ph_1935_, lean_object* v_inst_1936_, lean_object* v_fvarId_1937_, lean_object* v_fvarId_x27_1938_){
_start:
{
uint8_t v_ph_boxed_1939_; lean_object* v_res_1940_; 
v_ph_boxed_1939_ = lean_unbox(v_ph_1935_);
v_res_1940_ = l_Lean_Compiler_LCNF_addFVarSubst(v_m_1934_, v_ph_boxed_1939_, v_inst_1936_, v_fvarId_1937_, v_fvarId_x27_1938_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(lean_object* v_fvarId_1941_, uint8_t v_t_1942_, lean_object* v_toPure_1943_, lean_object* v_____do__lift_1944_){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_____do__lift_1944_, v_fvarId_1941_, v_t_1942_);
v___x_1946_ = lean_apply_2(v_toPure_1943_, lean_box(0), v___x_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed(lean_object* v_fvarId_1947_, lean_object* v_t_1948_, lean_object* v_toPure_1949_, lean_object* v_____do__lift_1950_){
_start:
{
uint8_t v_t_boxed_1951_; lean_object* v_res_1952_; 
v_t_boxed_1951_ = lean_unbox(v_t_1948_);
v_res_1952_ = l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(v_fvarId_1947_, v_t_boxed_1951_, v_toPure_1949_, v_____do__lift_1950_);
lean_dec_ref(v_____do__lift_1950_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg(uint8_t v_t_1953_, lean_object* v_inst_1954_, lean_object* v_inst_1955_, lean_object* v_fvarId_1956_){
_start:
{
lean_object* v_toApplicative_1957_; lean_object* v_toBind_1958_; lean_object* v_toPure_1959_; lean_object* v___x_1960_; lean_object* v___f_1961_; lean_object* v___x_1962_; 
v_toApplicative_1957_ = lean_ctor_get(v_inst_1955_, 0);
lean_inc_ref(v_toApplicative_1957_);
v_toBind_1958_ = lean_ctor_get(v_inst_1955_, 1);
lean_inc(v_toBind_1958_);
lean_dec_ref(v_inst_1955_);
v_toPure_1959_ = lean_ctor_get(v_toApplicative_1957_, 1);
lean_inc(v_toPure_1959_);
lean_dec_ref(v_toApplicative_1957_);
v___x_1960_ = lean_box(v_t_1953_);
v___f_1961_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1961_, 0, v_fvarId_1956_);
lean_closure_set(v___f_1961_, 1, v___x_1960_);
lean_closure_set(v___f_1961_, 2, v_toPure_1959_);
v___x_1962_ = lean_apply_4(v_toBind_1958_, lean_box(0), lean_box(0), v_inst_1954_, v___f_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___boxed(lean_object* v_t_1963_, lean_object* v_inst_1964_, lean_object* v_inst_1965_, lean_object* v_fvarId_1966_){
_start:
{
uint8_t v_t_boxed_1967_; lean_object* v_res_1968_; 
v_t_boxed_1967_ = lean_unbox(v_t_1963_);
v_res_1968_ = l_Lean_Compiler_LCNF_normFVar___redArg(v_t_boxed_1967_, v_inst_1964_, v_inst_1965_, v_fvarId_1966_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar(lean_object* v_m_1969_, uint8_t v_pu_1970_, uint8_t v_t_1971_, lean_object* v_inst_1972_, lean_object* v_inst_1973_, lean_object* v_fvarId_1974_){
_start:
{
lean_object* v_toApplicative_1975_; lean_object* v_toBind_1976_; lean_object* v_toPure_1977_; lean_object* v___x_1978_; lean_object* v___f_1979_; lean_object* v___x_1980_; 
v_toApplicative_1975_ = lean_ctor_get(v_inst_1973_, 0);
lean_inc_ref(v_toApplicative_1975_);
v_toBind_1976_ = lean_ctor_get(v_inst_1973_, 1);
lean_inc(v_toBind_1976_);
lean_dec_ref(v_inst_1973_);
v_toPure_1977_ = lean_ctor_get(v_toApplicative_1975_, 1);
lean_inc(v_toPure_1977_);
lean_dec_ref(v_toApplicative_1975_);
v___x_1978_ = lean_box(v_t_1971_);
v___f_1979_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1979_, 0, v_fvarId_1974_);
lean_closure_set(v___f_1979_, 1, v___x_1978_);
lean_closure_set(v___f_1979_, 2, v_toPure_1977_);
v___x_1980_ = lean_apply_4(v_toBind_1976_, lean_box(0), lean_box(0), v_inst_1972_, v___f_1979_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___boxed(lean_object* v_m_1981_, lean_object* v_pu_1982_, lean_object* v_t_1983_, lean_object* v_inst_1984_, lean_object* v_inst_1985_, lean_object* v_fvarId_1986_){
_start:
{
uint8_t v_pu_boxed_1987_; uint8_t v_t_boxed_1988_; lean_object* v_res_1989_; 
v_pu_boxed_1987_ = lean_unbox(v_pu_1982_);
v_t_boxed_1988_ = lean_unbox(v_t_1983_);
v_res_1989_ = l_Lean_Compiler_LCNF_normFVar(v_m_1981_, v_pu_boxed_1987_, v_t_boxed_1988_, v_inst_1984_, v_inst_1985_, v_fvarId_1986_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(uint8_t v_pu_1990_, uint8_t v_t_1991_, lean_object* v_e_1992_, lean_object* v_toPure_1993_, lean_object* v_____do__lift_1994_){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1990_, v_____do__lift_1994_, v_t_1991_, v_e_1992_);
v___x_1996_ = lean_apply_2(v_toPure_1993_, lean_box(0), v___x_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed(lean_object* v_pu_1997_, lean_object* v_t_1998_, lean_object* v_e_1999_, lean_object* v_toPure_2000_, lean_object* v_____do__lift_2001_){
_start:
{
uint8_t v_pu_boxed_2002_; uint8_t v_t_boxed_2003_; lean_object* v_res_2004_; 
v_pu_boxed_2002_ = lean_unbox(v_pu_1997_);
v_t_boxed_2003_ = lean_unbox(v_t_1998_);
v_res_2004_ = l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(v_pu_boxed_2002_, v_t_boxed_2003_, v_e_1999_, v_toPure_2000_, v_____do__lift_2001_);
lean_dec_ref(v_____do__lift_2001_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg(uint8_t v_pu_2005_, uint8_t v_t_2006_, lean_object* v_inst_2007_, lean_object* v_inst_2008_, lean_object* v_e_2009_){
_start:
{
lean_object* v_toApplicative_2010_; lean_object* v_toBind_2011_; lean_object* v_toPure_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___f_2015_; lean_object* v___x_2016_; 
v_toApplicative_2010_ = lean_ctor_get(v_inst_2008_, 0);
lean_inc_ref(v_toApplicative_2010_);
v_toBind_2011_ = lean_ctor_get(v_inst_2008_, 1);
lean_inc(v_toBind_2011_);
lean_dec_ref(v_inst_2008_);
v_toPure_2012_ = lean_ctor_get(v_toApplicative_2010_, 1);
lean_inc(v_toPure_2012_);
lean_dec_ref(v_toApplicative_2010_);
v___x_2013_ = lean_box(v_pu_2005_);
v___x_2014_ = lean_box(v_t_2006_);
v___f_2015_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2015_, 0, v___x_2013_);
lean_closure_set(v___f_2015_, 1, v___x_2014_);
lean_closure_set(v___f_2015_, 2, v_e_2009_);
lean_closure_set(v___f_2015_, 3, v_toPure_2012_);
v___x_2016_ = lean_apply_4(v_toBind_2011_, lean_box(0), lean_box(0), v_inst_2007_, v___f_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___boxed(lean_object* v_pu_2017_, lean_object* v_t_2018_, lean_object* v_inst_2019_, lean_object* v_inst_2020_, lean_object* v_e_2021_){
_start:
{
uint8_t v_pu_boxed_2022_; uint8_t v_t_boxed_2023_; lean_object* v_res_2024_; 
v_pu_boxed_2022_ = lean_unbox(v_pu_2017_);
v_t_boxed_2023_ = lean_unbox(v_t_2018_);
v_res_2024_ = l_Lean_Compiler_LCNF_normExpr___redArg(v_pu_boxed_2022_, v_t_boxed_2023_, v_inst_2019_, v_inst_2020_, v_e_2021_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr(lean_object* v_m_2025_, uint8_t v_pu_2026_, uint8_t v_t_2027_, lean_object* v_inst_2028_, lean_object* v_inst_2029_, lean_object* v_e_2030_){
_start:
{
lean_object* v_toApplicative_2031_; lean_object* v_toBind_2032_; lean_object* v_toPure_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___f_2036_; lean_object* v___x_2037_; 
v_toApplicative_2031_ = lean_ctor_get(v_inst_2029_, 0);
lean_inc_ref(v_toApplicative_2031_);
v_toBind_2032_ = lean_ctor_get(v_inst_2029_, 1);
lean_inc(v_toBind_2032_);
lean_dec_ref(v_inst_2029_);
v_toPure_2033_ = lean_ctor_get(v_toApplicative_2031_, 1);
lean_inc(v_toPure_2033_);
lean_dec_ref(v_toApplicative_2031_);
v___x_2034_ = lean_box(v_pu_2026_);
v___x_2035_ = lean_box(v_t_2027_);
v___f_2036_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2036_, 0, v___x_2034_);
lean_closure_set(v___f_2036_, 1, v___x_2035_);
lean_closure_set(v___f_2036_, 2, v_e_2030_);
lean_closure_set(v___f_2036_, 3, v_toPure_2033_);
v___x_2037_ = lean_apply_4(v_toBind_2032_, lean_box(0), lean_box(0), v_inst_2028_, v___f_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___boxed(lean_object* v_m_2038_, lean_object* v_pu_2039_, lean_object* v_t_2040_, lean_object* v_inst_2041_, lean_object* v_inst_2042_, lean_object* v_e_2043_){
_start:
{
uint8_t v_pu_boxed_2044_; uint8_t v_t_boxed_2045_; lean_object* v_res_2046_; 
v_pu_boxed_2044_ = lean_unbox(v_pu_2039_);
v_t_boxed_2045_ = lean_unbox(v_t_2040_);
v_res_2046_ = l_Lean_Compiler_LCNF_normExpr(v_m_2038_, v_pu_boxed_2044_, v_t_boxed_2045_, v_inst_2041_, v_inst_2042_, v_e_2043_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0(uint8_t v_pu_2047_, lean_object* v_arg_2048_, uint8_t v_t_2049_, lean_object* v_toPure_2050_, lean_object* v_____do__lift_2051_){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2047_, v_____do__lift_2051_, v_arg_2048_, v_t_2049_);
v___x_2053_ = lean_apply_2(v_toPure_2050_, lean_box(0), v___x_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed(lean_object* v_pu_2054_, lean_object* v_arg_2055_, lean_object* v_t_2056_, lean_object* v_toPure_2057_, lean_object* v_____do__lift_2058_){
_start:
{
uint8_t v_pu_boxed_2059_; uint8_t v_t_boxed_2060_; lean_object* v_res_2061_; 
v_pu_boxed_2059_ = lean_unbox(v_pu_2054_);
v_t_boxed_2060_ = lean_unbox(v_t_2056_);
v_res_2061_ = l_Lean_Compiler_LCNF_normArg___redArg___lam__0(v_pu_boxed_2059_, v_arg_2055_, v_t_boxed_2060_, v_toPure_2057_, v_____do__lift_2058_);
lean_dec_ref(v_____do__lift_2058_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg(uint8_t v_pu_2062_, uint8_t v_t_2063_, lean_object* v_inst_2064_, lean_object* v_inst_2065_, lean_object* v_arg_2066_){
_start:
{
lean_object* v_toApplicative_2067_; lean_object* v_toBind_2068_; lean_object* v_toPure_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___f_2072_; lean_object* v___x_2073_; 
v_toApplicative_2067_ = lean_ctor_get(v_inst_2065_, 0);
lean_inc_ref(v_toApplicative_2067_);
v_toBind_2068_ = lean_ctor_get(v_inst_2065_, 1);
lean_inc(v_toBind_2068_);
lean_dec_ref(v_inst_2065_);
v_toPure_2069_ = lean_ctor_get(v_toApplicative_2067_, 1);
lean_inc(v_toPure_2069_);
lean_dec_ref(v_toApplicative_2067_);
v___x_2070_ = lean_box(v_pu_2062_);
v___x_2071_ = lean_box(v_t_2063_);
v___f_2072_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2072_, 0, v___x_2070_);
lean_closure_set(v___f_2072_, 1, v_arg_2066_);
lean_closure_set(v___f_2072_, 2, v___x_2071_);
lean_closure_set(v___f_2072_, 3, v_toPure_2069_);
v___x_2073_ = lean_apply_4(v_toBind_2068_, lean_box(0), lean_box(0), v_inst_2064_, v___f_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___boxed(lean_object* v_pu_2074_, lean_object* v_t_2075_, lean_object* v_inst_2076_, lean_object* v_inst_2077_, lean_object* v_arg_2078_){
_start:
{
uint8_t v_pu_boxed_2079_; uint8_t v_t_boxed_2080_; lean_object* v_res_2081_; 
v_pu_boxed_2079_ = lean_unbox(v_pu_2074_);
v_t_boxed_2080_ = lean_unbox(v_t_2075_);
v_res_2081_ = l_Lean_Compiler_LCNF_normArg___redArg(v_pu_boxed_2079_, v_t_boxed_2080_, v_inst_2076_, v_inst_2077_, v_arg_2078_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg(lean_object* v_m_2082_, uint8_t v_pu_2083_, uint8_t v_t_2084_, lean_object* v_inst_2085_, lean_object* v_inst_2086_, lean_object* v_arg_2087_){
_start:
{
lean_object* v_toApplicative_2088_; lean_object* v_toBind_2089_; lean_object* v_toPure_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___f_2093_; lean_object* v___x_2094_; 
v_toApplicative_2088_ = lean_ctor_get(v_inst_2086_, 0);
lean_inc_ref(v_toApplicative_2088_);
v_toBind_2089_ = lean_ctor_get(v_inst_2086_, 1);
lean_inc(v_toBind_2089_);
lean_dec_ref(v_inst_2086_);
v_toPure_2090_ = lean_ctor_get(v_toApplicative_2088_, 1);
lean_inc(v_toPure_2090_);
lean_dec_ref(v_toApplicative_2088_);
v___x_2091_ = lean_box(v_pu_2083_);
v___x_2092_ = lean_box(v_t_2084_);
v___f_2093_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2093_, 0, v___x_2091_);
lean_closure_set(v___f_2093_, 1, v_arg_2087_);
lean_closure_set(v___f_2093_, 2, v___x_2092_);
lean_closure_set(v___f_2093_, 3, v_toPure_2090_);
v___x_2094_ = lean_apply_4(v_toBind_2089_, lean_box(0), lean_box(0), v_inst_2085_, v___f_2093_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___boxed(lean_object* v_m_2095_, lean_object* v_pu_2096_, lean_object* v_t_2097_, lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_arg_2100_){
_start:
{
uint8_t v_pu_boxed_2101_; uint8_t v_t_boxed_2102_; lean_object* v_res_2103_; 
v_pu_boxed_2101_ = lean_unbox(v_pu_2096_);
v_t_boxed_2102_ = lean_unbox(v_t_2097_);
v_res_2103_ = l_Lean_Compiler_LCNF_normArg(v_m_2095_, v_pu_boxed_2101_, v_t_boxed_2102_, v_inst_2098_, v_inst_2099_, v_arg_2100_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(uint8_t v_pu_2104_, lean_object* v_e_2105_, uint8_t v_t_2106_, lean_object* v_toPure_2107_, lean_object* v_____do__lift_2108_){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_2104_, v_____do__lift_2108_, v_e_2105_, v_t_2106_);
v___x_2110_ = lean_apply_2(v_toPure_2107_, lean_box(0), v___x_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed(lean_object* v_pu_2111_, lean_object* v_e_2112_, lean_object* v_t_2113_, lean_object* v_toPure_2114_, lean_object* v_____do__lift_2115_){
_start:
{
uint8_t v_pu_boxed_2116_; uint8_t v_t_boxed_2117_; lean_object* v_res_2118_; 
v_pu_boxed_2116_ = lean_unbox(v_pu_2111_);
v_t_boxed_2117_ = lean_unbox(v_t_2113_);
v_res_2118_ = l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(v_pu_boxed_2116_, v_e_2112_, v_t_boxed_2117_, v_toPure_2114_, v_____do__lift_2115_);
lean_dec_ref(v_____do__lift_2115_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg(uint8_t v_pu_2119_, uint8_t v_t_2120_, lean_object* v_inst_2121_, lean_object* v_inst_2122_, lean_object* v_e_2123_){
_start:
{
lean_object* v_toApplicative_2124_; lean_object* v_toBind_2125_; lean_object* v_toPure_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___f_2129_; lean_object* v___x_2130_; 
v_toApplicative_2124_ = lean_ctor_get(v_inst_2122_, 0);
lean_inc_ref(v_toApplicative_2124_);
v_toBind_2125_ = lean_ctor_get(v_inst_2122_, 1);
lean_inc(v_toBind_2125_);
lean_dec_ref(v_inst_2122_);
v_toPure_2126_ = lean_ctor_get(v_toApplicative_2124_, 1);
lean_inc(v_toPure_2126_);
lean_dec_ref(v_toApplicative_2124_);
v___x_2127_ = lean_box(v_pu_2119_);
v___x_2128_ = lean_box(v_t_2120_);
v___f_2129_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2129_, 0, v___x_2127_);
lean_closure_set(v___f_2129_, 1, v_e_2123_);
lean_closure_set(v___f_2129_, 2, v___x_2128_);
lean_closure_set(v___f_2129_, 3, v_toPure_2126_);
v___x_2130_ = lean_apply_4(v_toBind_2125_, lean_box(0), lean_box(0), v_inst_2121_, v___f_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___boxed(lean_object* v_pu_2131_, lean_object* v_t_2132_, lean_object* v_inst_2133_, lean_object* v_inst_2134_, lean_object* v_e_2135_){
_start:
{
uint8_t v_pu_boxed_2136_; uint8_t v_t_boxed_2137_; lean_object* v_res_2138_; 
v_pu_boxed_2136_ = lean_unbox(v_pu_2131_);
v_t_boxed_2137_ = lean_unbox(v_t_2132_);
v_res_2138_ = l_Lean_Compiler_LCNF_normLetValue___redArg(v_pu_boxed_2136_, v_t_boxed_2137_, v_inst_2133_, v_inst_2134_, v_e_2135_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue(lean_object* v_m_2139_, uint8_t v_pu_2140_, uint8_t v_t_2141_, lean_object* v_inst_2142_, lean_object* v_inst_2143_, lean_object* v_e_2144_){
_start:
{
lean_object* v_toApplicative_2145_; lean_object* v_toBind_2146_; lean_object* v_toPure_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___f_2150_; lean_object* v___x_2151_; 
v_toApplicative_2145_ = lean_ctor_get(v_inst_2143_, 0);
lean_inc_ref(v_toApplicative_2145_);
v_toBind_2146_ = lean_ctor_get(v_inst_2143_, 1);
lean_inc(v_toBind_2146_);
lean_dec_ref(v_inst_2143_);
v_toPure_2147_ = lean_ctor_get(v_toApplicative_2145_, 1);
lean_inc(v_toPure_2147_);
lean_dec_ref(v_toApplicative_2145_);
v___x_2148_ = lean_box(v_pu_2140_);
v___x_2149_ = lean_box(v_t_2141_);
v___f_2150_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2150_, 0, v___x_2148_);
lean_closure_set(v___f_2150_, 1, v_e_2144_);
lean_closure_set(v___f_2150_, 2, v___x_2149_);
lean_closure_set(v___f_2150_, 3, v_toPure_2147_);
v___x_2151_ = lean_apply_4(v_toBind_2146_, lean_box(0), lean_box(0), v_inst_2142_, v___f_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___boxed(lean_object* v_m_2152_, lean_object* v_pu_2153_, lean_object* v_t_2154_, lean_object* v_inst_2155_, lean_object* v_inst_2156_, lean_object* v_e_2157_){
_start:
{
uint8_t v_pu_boxed_2158_; uint8_t v_t_boxed_2159_; lean_object* v_res_2160_; 
v_pu_boxed_2158_ = lean_unbox(v_pu_2153_);
v_t_boxed_2159_ = lean_unbox(v_t_2154_);
v_res_2160_ = l_Lean_Compiler_LCNF_normLetValue(v_m_2152_, v_pu_boxed_2158_, v_t_boxed_2159_, v_inst_2155_, v_inst_2156_, v_e_2157_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore(uint8_t v_pu_2161_, lean_object* v_s_2162_, lean_object* v_e_2163_, uint8_t v_translator_2164_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2161_, v_s_2162_, v_translator_2164_, v_e_2163_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore___boxed(lean_object* v_pu_2166_, lean_object* v_s_2167_, lean_object* v_e_2168_, lean_object* v_translator_2169_){
_start:
{
uint8_t v_pu_boxed_2170_; uint8_t v_translator_boxed_2171_; lean_object* v_res_2172_; 
v_pu_boxed_2170_ = lean_unbox(v_pu_2166_);
v_translator_boxed_2171_ = lean_unbox(v_translator_2169_);
v_res_2172_ = l_Lean_Compiler_LCNF_normExprCore(v_pu_boxed_2170_, v_s_2167_, v_e_2168_, v_translator_boxed_2171_);
lean_dec_ref(v_s_2167_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(uint8_t v_pu_2173_, lean_object* v_args_2174_, uint8_t v_t_2175_, lean_object* v_toPure_2176_, lean_object* v_____do__lift_2177_){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_2173_, v_____do__lift_2177_, v_args_2174_, v_t_2175_);
v___x_2179_ = lean_apply_2(v_toPure_2176_, lean_box(0), v___x_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed(lean_object* v_pu_2180_, lean_object* v_args_2181_, lean_object* v_t_2182_, lean_object* v_toPure_2183_, lean_object* v_____do__lift_2184_){
_start:
{
uint8_t v_pu_boxed_2185_; uint8_t v_t_boxed_2186_; lean_object* v_res_2187_; 
v_pu_boxed_2185_ = lean_unbox(v_pu_2180_);
v_t_boxed_2186_ = lean_unbox(v_t_2182_);
v_res_2187_ = l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(v_pu_boxed_2185_, v_args_2181_, v_t_boxed_2186_, v_toPure_2183_, v_____do__lift_2184_);
lean_dec_ref(v_____do__lift_2184_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg(uint8_t v_pu_2188_, uint8_t v_t_2189_, lean_object* v_inst_2190_, lean_object* v_inst_2191_, lean_object* v_args_2192_){
_start:
{
lean_object* v_toApplicative_2193_; lean_object* v_toBind_2194_; lean_object* v_toPure_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___f_2198_; lean_object* v___x_2199_; 
v_toApplicative_2193_ = lean_ctor_get(v_inst_2191_, 0);
lean_inc_ref(v_toApplicative_2193_);
v_toBind_2194_ = lean_ctor_get(v_inst_2191_, 1);
lean_inc(v_toBind_2194_);
lean_dec_ref(v_inst_2191_);
v_toPure_2195_ = lean_ctor_get(v_toApplicative_2193_, 1);
lean_inc(v_toPure_2195_);
lean_dec_ref(v_toApplicative_2193_);
v___x_2196_ = lean_box(v_pu_2188_);
v___x_2197_ = lean_box(v_t_2189_);
v___f_2198_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2198_, 0, v___x_2196_);
lean_closure_set(v___f_2198_, 1, v_args_2192_);
lean_closure_set(v___f_2198_, 2, v___x_2197_);
lean_closure_set(v___f_2198_, 3, v_toPure_2195_);
v___x_2199_ = lean_apply_4(v_toBind_2194_, lean_box(0), lean_box(0), v_inst_2190_, v___f_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___boxed(lean_object* v_pu_2200_, lean_object* v_t_2201_, lean_object* v_inst_2202_, lean_object* v_inst_2203_, lean_object* v_args_2204_){
_start:
{
uint8_t v_pu_boxed_2205_; uint8_t v_t_boxed_2206_; lean_object* v_res_2207_; 
v_pu_boxed_2205_ = lean_unbox(v_pu_2200_);
v_t_boxed_2206_ = lean_unbox(v_t_2201_);
v_res_2207_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_boxed_2205_, v_t_boxed_2206_, v_inst_2202_, v_inst_2203_, v_args_2204_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs(lean_object* v_m_2208_, uint8_t v_pu_2209_, uint8_t v_t_2210_, lean_object* v_inst_2211_, lean_object* v_inst_2212_, lean_object* v_args_2213_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_2209_, v_t_2210_, v_inst_2211_, v_inst_2212_, v_args_2213_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___boxed(lean_object* v_m_2215_, lean_object* v_pu_2216_, lean_object* v_t_2217_, lean_object* v_inst_2218_, lean_object* v_inst_2219_, lean_object* v_args_2220_){
_start:
{
uint8_t v_pu_boxed_2221_; uint8_t v_t_boxed_2222_; lean_object* v_res_2223_; 
v_pu_boxed_2221_ = lean_unbox(v_pu_2216_);
v_t_boxed_2222_ = lean_unbox(v_t_2217_);
v_res_2223_ = l_Lean_Compiler_LCNF_normArgs(v_m_2215_, v_pu_boxed_2221_, v_t_boxed_2222_, v_inst_2218_, v_inst_2219_, v_args_2220_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object* v_binderName_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v_lctx_2229_; lean_object* v_nextIdx_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2243_; 
v___x_2227_ = lean_st_ref_get(v_a_2225_);
v___x_2228_ = lean_st_ref_take(v_a_2225_);
v_lctx_2229_ = lean_ctor_get(v___x_2228_, 0);
v_nextIdx_2230_ = lean_ctor_get(v___x_2228_, 1);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2232_ = v___x_2228_;
v_isShared_2233_ = v_isSharedCheck_2243_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_nextIdx_2230_);
lean_inc(v_lctx_2229_);
lean_dec(v___x_2228_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2243_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2237_; 
v___x_2234_ = lean_unsigned_to_nat(1u);
v___x_2235_ = lean_nat_add(v_nextIdx_2230_, v___x_2234_);
lean_dec(v_nextIdx_2230_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 1, v___x_2235_);
v___x_2237_ = v___x_2232_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_lctx_2229_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
lean_object* v___x_2238_; lean_object* v_nextIdx_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2238_ = lean_st_ref_put(v_a_2225_, v___x_2237_);
v_nextIdx_2239_ = lean_ctor_get(v___x_2227_, 1);
lean_inc(v_nextIdx_2239_);
lean_dec(v___x_2227_);
v___x_2240_ = l_Lean_Name_num___override(v_binderName_2224_, v_nextIdx_2239_);
v___x_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
return v___x_2241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg___boxed(lean_object* v_binderName_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2244_, v_a_2245_);
lean_dec(v_a_2245_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object* v_binderName_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_){
_start:
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2248_, v_a_2250_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___boxed(lean_object* v_binderName_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_Compiler_LCNF_mkFreshBinderName(v_binderName_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
lean_dec(v_a_2259_);
lean_dec_ref(v_a_2258_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(lean_object* v_binderName_2262_, lean_object* v_baseName_2263_, lean_object* v_a_2264_){
_start:
{
uint8_t v___x_2266_; 
v___x_2266_ = l_Lean_Name_isAnonymous(v_binderName_2262_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; 
lean_dec(v_baseName_2263_);
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v_binderName_2262_);
return v___x_2267_;
}
else
{
lean_object* v___x_2268_; 
lean_dec(v_binderName_2262_);
v___x_2268_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_baseName_2263_, v_a_2264_);
return v___x_2268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg___boxed(lean_object* v_binderName_2269_, lean_object* v_baseName_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2269_, v_baseName_2270_, v_a_2271_);
lean_dec(v_a_2271_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous(lean_object* v_binderName_2274_, lean_object* v_baseName_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2274_, v_baseName_2275_, v_a_2277_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___boxed(lean_object* v_binderName_2282_, lean_object* v_baseName_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Lean_Compiler_LCNF_ensureNotAnonymous(v_binderName_2282_, v_baseName_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
lean_dec(v_a_2287_);
lean_dec_ref(v_a_2286_);
lean_dec(v_a_2285_);
lean_dec_ref(v_a_2284_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(lean_object* v___y_2290_){
_start:
{
lean_object* v___x_2292_; lean_object* v_ngen_2293_; lean_object* v_namePrefix_2294_; lean_object* v_idx_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2324_; 
v___x_2292_ = lean_st_ref_get(v___y_2290_);
v_ngen_2293_ = lean_ctor_get(v___x_2292_, 2);
lean_inc_ref(v_ngen_2293_);
lean_dec(v___x_2292_);
v_namePrefix_2294_ = lean_ctor_get(v_ngen_2293_, 0);
v_idx_2295_ = lean_ctor_get(v_ngen_2293_, 1);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_ngen_2293_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2297_ = v_ngen_2293_;
v_isShared_2298_ = v_isSharedCheck_2324_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_idx_2295_);
lean_inc(v_namePrefix_2294_);
lean_dec(v_ngen_2293_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2324_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2299_; lean_object* v_env_2300_; lean_object* v_nextMacroScope_2301_; lean_object* v_auxDeclNGen_2302_; lean_object* v_traceState_2303_; lean_object* v_cache_2304_; lean_object* v_messages_2305_; lean_object* v_infoState_2306_; lean_object* v_snapshotTasks_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2322_; 
v___x_2299_ = lean_st_ref_take(v___y_2290_);
v_env_2300_ = lean_ctor_get(v___x_2299_, 0);
v_nextMacroScope_2301_ = lean_ctor_get(v___x_2299_, 1);
v_auxDeclNGen_2302_ = lean_ctor_get(v___x_2299_, 3);
v_traceState_2303_ = lean_ctor_get(v___x_2299_, 4);
v_cache_2304_ = lean_ctor_get(v___x_2299_, 5);
v_messages_2305_ = lean_ctor_get(v___x_2299_, 6);
v_infoState_2306_ = lean_ctor_get(v___x_2299_, 7);
v_snapshotTasks_2307_ = lean_ctor_get(v___x_2299_, 8);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v___x_2299_, 2);
lean_dec(v_unused_2323_);
v___x_2309_ = v___x_2299_;
v_isShared_2310_ = v_isSharedCheck_2322_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_snapshotTasks_2307_);
lean_inc(v_infoState_2306_);
lean_inc(v_messages_2305_);
lean_inc(v_cache_2304_);
lean_inc(v_traceState_2303_);
lean_inc(v_auxDeclNGen_2302_);
lean_inc(v_nextMacroScope_2301_);
lean_inc(v_env_2300_);
lean_dec(v___x_2299_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2322_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v_r_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2315_; 
lean_inc(v_idx_2295_);
lean_inc(v_namePrefix_2294_);
v_r_2311_ = l_Lean_Name_num___override(v_namePrefix_2294_, v_idx_2295_);
v___x_2312_ = lean_unsigned_to_nat(1u);
v___x_2313_ = lean_nat_add(v_idx_2295_, v___x_2312_);
lean_dec(v_idx_2295_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 1, v___x_2313_);
v___x_2315_ = v___x_2297_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_namePrefix_2294_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
lean_object* v___x_2317_; 
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 2, v___x_2315_);
v___x_2317_ = v___x_2309_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_env_2300_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_nextMacroScope_2301_);
lean_ctor_set(v_reuseFailAlloc_2320_, 2, v___x_2315_);
lean_ctor_set(v_reuseFailAlloc_2320_, 3, v_auxDeclNGen_2302_);
lean_ctor_set(v_reuseFailAlloc_2320_, 4, v_traceState_2303_);
lean_ctor_set(v_reuseFailAlloc_2320_, 5, v_cache_2304_);
lean_ctor_set(v_reuseFailAlloc_2320_, 6, v_messages_2305_);
lean_ctor_set(v_reuseFailAlloc_2320_, 7, v_infoState_2306_);
lean_ctor_set(v_reuseFailAlloc_2320_, 8, v_snapshotTasks_2307_);
v___x_2317_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = lean_st_ref_put(v___y_2290_, v___x_2317_);
v___x_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2319_, 0, v_r_2311_);
return v___x_2319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg___boxed(lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2325_);
lean_dec(v___y_2325_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v___x_2333_; lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
v___x_2333_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2331_);
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2333_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0___boxed(lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t v_pu_2351_, lean_object* v_binderName_2352_, lean_object* v_type_2353_, uint8_t v_borrow_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2384_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2360_, 1);
v___x_2362_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_2363_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2352_, v___x_2362_, v_a_2356_);
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2366_ = v___x_2363_;
v_isShared_2367_ = v_isSharedCheck_2384_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2384_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v_lctx_2369_; lean_object* v_nextIdx_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2383_; 
v___x_2368_ = lean_st_ref_take(v_a_2356_);
v_lctx_2369_ = lean_ctor_get(v___x_2368_, 0);
v_nextIdx_2370_ = lean_ctor_get(v___x_2368_, 1);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2372_ = v___x_2368_;
v_isShared_2373_ = v_isSharedCheck_2383_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_nextIdx_2370_);
lean_inc(v_lctx_2369_);
lean_dec(v___x_2368_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2383_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2377_; 
v___x_2374_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2374_, 0, v_a_2361_);
lean_ctor_set(v___x_2374_, 1, v_a_2364_);
lean_ctor_set(v___x_2374_, 2, v_type_2353_);
lean_ctor_set_uint8(v___x_2374_, sizeof(void*)*3, v_borrow_2354_);
lean_inc_ref(v___x_2374_);
v___x_2375_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2351_, v_lctx_2369_, v___x_2374_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v___x_2375_);
v___x_2377_ = v___x_2372_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v_nextIdx_2370_);
v___x_2377_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2378_; lean_object* v___x_2380_; 
v___x_2378_ = lean_st_ref_put(v_a_2356_, v___x_2377_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v___x_2374_);
v___x_2380_ = v___x_2366_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2374_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_dec_ref(v_type_2353_);
lean_dec(v_binderName_2352_);
v_a_2385_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2360_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2360_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam___boxed(lean_object* v_pu_2393_, lean_object* v_binderName_2394_, lean_object* v_type_2395_, lean_object* v_borrow_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_){
_start:
{
uint8_t v_pu_boxed_2402_; uint8_t v_borrow_boxed_2403_; lean_object* v_res_2404_; 
v_pu_boxed_2402_ = lean_unbox(v_pu_2393_);
v_borrow_boxed_2403_ = lean_unbox(v_borrow_2396_);
v_res_2404_ = l_Lean_Compiler_LCNF_mkParam(v_pu_boxed_2402_, v_binderName_2394_, v_type_2395_, v_borrow_boxed_2403_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2408_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___boxed(lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t v_pu_2420_, lean_object* v_binderName_2421_, lean_object* v_type_2422_, lean_object* v_value_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2453_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2429_, 1);
v___x_2431_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2432_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2421_, v___x_2431_, v_a_2425_);
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2435_ = v___x_2432_;
v_isShared_2436_ = v_isSharedCheck_2453_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2432_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2453_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v_lctx_2438_; lean_object* v_nextIdx_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2452_; 
v___x_2437_ = lean_st_ref_take(v_a_2425_);
v_lctx_2438_ = lean_ctor_get(v___x_2437_, 0);
v_nextIdx_2439_ = lean_ctor_get(v___x_2437_, 1);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2441_ = v___x_2437_;
v_isShared_2442_ = v_isSharedCheck_2452_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_nextIdx_2439_);
lean_inc(v_lctx_2438_);
lean_dec(v___x_2437_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2452_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2446_; 
v___x_2443_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2443_, 0, v_a_2430_);
lean_ctor_set(v___x_2443_, 1, v_a_2433_);
lean_ctor_set(v___x_2443_, 2, v_type_2422_);
lean_ctor_set(v___x_2443_, 3, v_value_2423_);
lean_inc_ref(v___x_2443_);
v___x_2444_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2420_, v_lctx_2438_, v___x_2443_);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 0, v___x_2444_);
v___x_2446_ = v___x_2441_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v_nextIdx_2439_);
v___x_2446_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2447_ = lean_st_ref_put(v_a_2425_, v___x_2446_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v___x_2443_);
v___x_2449_ = v___x_2435_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2443_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec(v_value_2423_);
lean_dec_ref(v_type_2422_);
lean_dec(v_binderName_2421_);
v_a_2454_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2429_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2429_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl___boxed(lean_object* v_pu_2462_, lean_object* v_binderName_2463_, lean_object* v_type_2464_, lean_object* v_value_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
uint8_t v_pu_boxed_2471_; lean_object* v_res_2472_; 
v_pu_boxed_2471_ = lean_unbox(v_pu_2462_);
v_res_2472_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_boxed_2471_, v_binderName_2463_, v_type_2464_, v_value_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t v_pu_2476_, lean_object* v_binderName_2477_, lean_object* v_type_2478_, lean_object* v_params_2479_, lean_object* v_value_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2510_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2487_);
lean_dec_ref_known(v___x_2486_, 1);
v___x_2488_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFunDecl___closed__1));
v___x_2489_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2477_, v___x_2488_, v_a_2482_);
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2492_ = v___x_2489_;
v_isShared_2493_ = v_isSharedCheck_2510_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2489_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2510_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2494_; lean_object* v_lctx_2495_; lean_object* v_nextIdx_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2509_; 
v___x_2494_ = lean_st_ref_take(v_a_2482_);
v_lctx_2495_ = lean_ctor_get(v___x_2494_, 0);
v_nextIdx_2496_ = lean_ctor_get(v___x_2494_, 1);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2498_ = v___x_2494_;
v_isShared_2499_ = v_isSharedCheck_2509_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_nextIdx_2496_);
lean_inc(v_lctx_2495_);
lean_dec(v___x_2494_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2509_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2503_; 
v___x_2500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2500_, 0, v_a_2487_);
lean_ctor_set(v___x_2500_, 1, v_a_2490_);
lean_ctor_set(v___x_2500_, 2, v_params_2479_);
lean_ctor_set(v___x_2500_, 3, v_type_2478_);
lean_ctor_set(v___x_2500_, 4, v_value_2480_);
lean_inc_ref(v___x_2500_);
v___x_2501_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2476_, v_lctx_2495_, v___x_2500_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v___x_2501_);
v___x_2503_ = v___x_2498_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2501_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v_nextIdx_2496_);
v___x_2503_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
lean_object* v___x_2504_; lean_object* v___x_2506_; 
v___x_2504_ = lean_st_ref_put(v_a_2482_, v___x_2503_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 0, v___x_2500_);
v___x_2506_ = v___x_2492_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2500_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
lean_dec_ref(v_value_2480_);
lean_dec_ref(v_params_2479_);
lean_dec_ref(v_type_2478_);
lean_dec(v_binderName_2477_);
v_a_2511_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2513_ = v___x_2486_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2486_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
if (v_isShared_2514_ == 0)
{
v___x_2516_ = v___x_2513_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2511_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl___boxed(lean_object* v_pu_2519_, lean_object* v_binderName_2520_, lean_object* v_type_2521_, lean_object* v_params_2522_, lean_object* v_value_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_){
_start:
{
uint8_t v_pu_boxed_2529_; lean_object* v_res_2530_; 
v_pu_boxed_2529_ = lean_unbox(v_pu_2519_);
v_res_2530_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_boxed_2529_, v_binderName_2520_, v_type_2521_, v_params_2522_, v_value_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(uint8_t v_pu_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v_a_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2537_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2538_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2537_, v_a_2533_);
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref(v___x_2538_);
v___x_2540_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2541_ = lean_box(1);
v___x_2542_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2531_, v_a_2539_, v___x_2540_, v___x_2541_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased___boxed(lean_object* v_pu_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_){
_start:
{
uint8_t v_pu_boxed_2549_; lean_object* v_res_2550_; 
v_pu_boxed_2549_ = lean_unbox(v_pu_2543_);
v_res_2550_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_boxed_2549_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t v_pu_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2568_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2560_ = v___x_2557_;
v_isShared_2561_ = v_isSharedCheck_2568_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2557_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2568_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v_fvarId_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2566_; 
v_fvarId_2562_ = lean_ctor_get(v_a_2558_, 0);
lean_inc(v_fvarId_2562_);
v___x_2563_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2563_, 0, v_fvarId_2562_);
v___x_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2564_, 0, v_a_2558_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v___x_2564_);
v___x_2566_ = v___x_2560_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2564_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
v_a_2569_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2557_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2557_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased___boxed(lean_object* v_pu_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_){
_start:
{
uint8_t v_pu_boxed_2583_; lean_object* v_res_2584_; 
v_pu_boxed_2583_ = lean_unbox(v_pu_2577_);
v_res_2584_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_boxed_2583_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_);
lean_dec(v_a_2581_);
lean_dec_ref(v_a_2580_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t v_pu_2585_, lean_object* v_p_2586_, lean_object* v_type_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v_fvarId_2590_; lean_object* v_binderName_2591_; lean_object* v_type_2592_; uint8_t v_borrow_2593_; size_t v___x_2594_; size_t v___x_2595_; uint8_t v___x_2596_; 
v_fvarId_2590_ = lean_ctor_get(v_p_2586_, 0);
v_binderName_2591_ = lean_ctor_get(v_p_2586_, 1);
v_type_2592_ = lean_ctor_get(v_p_2586_, 2);
v_borrow_2593_ = lean_ctor_get_uint8(v_p_2586_, sizeof(void*)*3);
v___x_2594_ = lean_ptr_addr(v_type_2587_);
v___x_2595_ = lean_ptr_addr(v_type_2592_);
v___x_2596_ = lean_usize_dec_eq(v___x_2594_, v___x_2595_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2616_; 
lean_inc(v_binderName_2591_);
lean_inc(v_fvarId_2590_);
v_isSharedCheck_2616_ = !lean_is_exclusive(v_p_2586_);
if (v_isSharedCheck_2616_ == 0)
{
lean_object* v_unused_2617_; lean_object* v_unused_2618_; lean_object* v_unused_2619_; 
v_unused_2617_ = lean_ctor_get(v_p_2586_, 2);
lean_dec(v_unused_2617_);
v_unused_2618_ = lean_ctor_get(v_p_2586_, 1);
lean_dec(v_unused_2618_);
v_unused_2619_ = lean_ctor_get(v_p_2586_, 0);
lean_dec(v_unused_2619_);
v___x_2598_ = v_p_2586_;
v_isShared_2599_ = v_isSharedCheck_2616_;
goto v_resetjp_2597_;
}
else
{
lean_dec(v_p_2586_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2616_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2600_; lean_object* v_lctx_2601_; lean_object* v_nextIdx_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2615_; 
v___x_2600_ = lean_st_ref_take(v_a_2588_);
v_lctx_2601_ = lean_ctor_get(v___x_2600_, 0);
v_nextIdx_2602_ = lean_ctor_get(v___x_2600_, 1);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2604_ = v___x_2600_;
v_isShared_2605_ = v_isSharedCheck_2615_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_nextIdx_2602_);
lean_inc(v_lctx_2601_);
lean_dec(v___x_2600_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2615_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v_p_2607_; 
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 2, v_type_2587_);
v_p_2607_ = v___x_2598_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_fvarId_2590_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v_binderName_2591_);
lean_ctor_set(v_reuseFailAlloc_2614_, 2, v_type_2587_);
lean_ctor_set_uint8(v_reuseFailAlloc_2614_, sizeof(void*)*3, v_borrow_2593_);
v_p_2607_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
lean_object* v___x_2608_; lean_object* v___x_2610_; 
lean_inc_ref(v_p_2607_);
v___x_2608_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2585_, v_lctx_2601_, v_p_2607_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v___x_2608_);
v___x_2610_ = v___x_2604_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2608_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v_nextIdx_2602_);
v___x_2610_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = lean_st_ref_put(v_a_2588_, v___x_2610_);
v___x_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2612_, 0, v_p_2607_);
return v___x_2612_;
}
}
}
}
}
else
{
lean_object* v___x_2620_; 
lean_dec_ref(v_type_2587_);
v___x_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2620_, 0, v_p_2586_);
return v___x_2620_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg___boxed(lean_object* v_pu_2621_, lean_object* v_p_2622_, lean_object* v_type_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_){
_start:
{
uint8_t v_pu_boxed_2626_; lean_object* v_res_2627_; 
v_pu_boxed_2626_ = lean_unbox(v_pu_2621_);
v_res_2627_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_boxed_2626_, v_p_2622_, v_type_2623_, v_a_2624_);
lean_dec(v_a_2624_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(uint8_t v_pu_2628_, lean_object* v_p_2629_, lean_object* v_type_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_2628_, v_p_2629_, v_type_2630_, v_a_2632_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(lean_object* v_pu_2637_, lean_object* v_p_2638_, lean_object* v_type_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_){
_start:
{
uint8_t v_pu_boxed_2645_; lean_object* v_res_2646_; 
v_pu_boxed_2645_ = lean_unbox(v_pu_2637_);
v_res_2646_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(v_pu_boxed_2645_, v_p_2638_, v_type_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t v_pu_2647_, lean_object* v_p_2648_, uint8_t v_borrow_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v_fvarId_2652_; lean_object* v_binderName_2653_; lean_object* v_type_2654_; uint8_t v_borrow_2655_; 
v_fvarId_2652_ = lean_ctor_get(v_p_2648_, 0);
v_binderName_2653_ = lean_ctor_get(v_p_2648_, 1);
v_type_2654_ = lean_ctor_get(v_p_2648_, 2);
v_borrow_2655_ = lean_ctor_get_uint8(v_p_2648_, sizeof(void*)*3);
if (v_borrow_2649_ == 0)
{
if (v_borrow_2655_ == 0)
{
lean_object* v___x_2671_; 
v___x_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2671_, 0, v_p_2648_);
return v___x_2671_;
}
else
{
lean_inc_ref(v_type_2654_);
lean_inc(v_binderName_2653_);
lean_inc(v_fvarId_2652_);
lean_dec_ref(v_p_2648_);
goto v___jp_2656_;
}
}
else
{
if (v_borrow_2655_ == 0)
{
lean_inc_ref(v_type_2654_);
lean_inc(v_binderName_2653_);
lean_inc(v_fvarId_2652_);
lean_dec_ref(v_p_2648_);
goto v___jp_2656_;
}
else
{
lean_object* v___x_2672_; 
v___x_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2672_, 0, v_p_2648_);
return v___x_2672_;
}
}
v___jp_2656_:
{
lean_object* v___x_2657_; lean_object* v_lctx_2658_; lean_object* v_nextIdx_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2670_; 
v___x_2657_ = lean_st_ref_take(v_a_2650_);
v_lctx_2658_ = lean_ctor_get(v___x_2657_, 0);
v_nextIdx_2659_ = lean_ctor_get(v___x_2657_, 1);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2661_ = v___x_2657_;
v_isShared_2662_ = v_isSharedCheck_2670_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_nextIdx_2659_);
lean_inc(v_lctx_2658_);
lean_dec(v___x_2657_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2670_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v_p_2663_; lean_object* v___x_2664_; lean_object* v___x_2666_; 
v_p_2663_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_p_2663_, 0, v_fvarId_2652_);
lean_ctor_set(v_p_2663_, 1, v_binderName_2653_);
lean_ctor_set(v_p_2663_, 2, v_type_2654_);
lean_ctor_set_uint8(v_p_2663_, sizeof(void*)*3, v_borrow_2649_);
lean_inc_ref(v_p_2663_);
v___x_2664_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2647_, v_lctx_2658_, v_p_2663_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2664_);
v___x_2666_ = v___x_2661_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v_nextIdx_2659_);
v___x_2666_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2667_ = lean_st_ref_put(v_a_2650_, v___x_2666_);
v___x_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2668_, 0, v_p_2663_);
return v___x_2668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg___boxed(lean_object* v_pu_2673_, lean_object* v_p_2674_, lean_object* v_borrow_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_){
_start:
{
uint8_t v_pu_boxed_2678_; uint8_t v_borrow_boxed_2679_; lean_object* v_res_2680_; 
v_pu_boxed_2678_ = lean_unbox(v_pu_2673_);
v_borrow_boxed_2679_ = lean_unbox(v_borrow_2675_);
v_res_2680_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_boxed_2678_, v_p_2674_, v_borrow_boxed_2679_, v_a_2676_);
lean_dec(v_a_2676_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(uint8_t v_pu_2681_, lean_object* v_p_2682_, uint8_t v_borrow_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_2681_, v_p_2682_, v_borrow_2683_, v_a_2685_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___boxed(lean_object* v_pu_2690_, lean_object* v_p_2691_, lean_object* v_borrow_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
uint8_t v_pu_boxed_2698_; uint8_t v_borrow_boxed_2699_; lean_object* v_res_2700_; 
v_pu_boxed_2698_ = lean_unbox(v_pu_2690_);
v_borrow_boxed_2699_ = lean_unbox(v_borrow_2692_);
v_res_2700_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(v_pu_boxed_2698_, v_p_2691_, v_borrow_boxed_2699_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
lean_dec(v_a_2694_);
lean_dec_ref(v_a_2693_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t v_pu_2701_, lean_object* v_decl_2702_, lean_object* v_type_2703_, lean_object* v_value_2704_, lean_object* v_a_2705_){
_start:
{
lean_object* v_fvarId_2707_; lean_object* v_binderName_2708_; lean_object* v_type_2709_; lean_object* v_value_2710_; uint8_t v___y_2712_; size_t v___x_2738_; size_t v___x_2739_; uint8_t v___x_2740_; 
v_fvarId_2707_ = lean_ctor_get(v_decl_2702_, 0);
v_binderName_2708_ = lean_ctor_get(v_decl_2702_, 1);
v_type_2709_ = lean_ctor_get(v_decl_2702_, 2);
v_value_2710_ = lean_ctor_get(v_decl_2702_, 3);
v___x_2738_ = lean_ptr_addr(v_type_2703_);
v___x_2739_ = lean_ptr_addr(v_type_2709_);
v___x_2740_ = lean_usize_dec_eq(v___x_2738_, v___x_2739_);
if (v___x_2740_ == 0)
{
v___y_2712_ = v___x_2740_;
goto v___jp_2711_;
}
else
{
size_t v___x_2741_; size_t v___x_2742_; uint8_t v___x_2743_; 
v___x_2741_ = lean_ptr_addr(v_value_2704_);
v___x_2742_ = lean_ptr_addr(v_value_2710_);
v___x_2743_ = lean_usize_dec_eq(v___x_2741_, v___x_2742_);
v___y_2712_ = v___x_2743_;
goto v___jp_2711_;
}
v___jp_2711_:
{
if (v___y_2712_ == 0)
{
lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2732_; 
lean_inc(v_binderName_2708_);
lean_inc(v_fvarId_2707_);
v_isSharedCheck_2732_ = !lean_is_exclusive(v_decl_2702_);
if (v_isSharedCheck_2732_ == 0)
{
lean_object* v_unused_2733_; lean_object* v_unused_2734_; lean_object* v_unused_2735_; lean_object* v_unused_2736_; 
v_unused_2733_ = lean_ctor_get(v_decl_2702_, 3);
lean_dec(v_unused_2733_);
v_unused_2734_ = lean_ctor_get(v_decl_2702_, 2);
lean_dec(v_unused_2734_);
v_unused_2735_ = lean_ctor_get(v_decl_2702_, 1);
lean_dec(v_unused_2735_);
v_unused_2736_ = lean_ctor_get(v_decl_2702_, 0);
lean_dec(v_unused_2736_);
v___x_2714_ = v_decl_2702_;
v_isShared_2715_ = v_isSharedCheck_2732_;
goto v_resetjp_2713_;
}
else
{
lean_dec(v_decl_2702_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2732_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2716_; lean_object* v_lctx_2717_; lean_object* v_nextIdx_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2731_; 
v___x_2716_ = lean_st_ref_take(v_a_2705_);
v_lctx_2717_ = lean_ctor_get(v___x_2716_, 0);
v_nextIdx_2718_ = lean_ctor_get(v___x_2716_, 1);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2720_ = v___x_2716_;
v_isShared_2721_ = v_isSharedCheck_2731_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_nextIdx_2718_);
lean_inc(v_lctx_2717_);
lean_dec(v___x_2716_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2731_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v_decl_2723_; 
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 3, v_value_2704_);
lean_ctor_set(v___x_2714_, 2, v_type_2703_);
v_decl_2723_ = v___x_2714_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_fvarId_2707_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_binderName_2708_);
lean_ctor_set(v_reuseFailAlloc_2730_, 2, v_type_2703_);
lean_ctor_set(v_reuseFailAlloc_2730_, 3, v_value_2704_);
v_decl_2723_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
lean_object* v___x_2724_; lean_object* v___x_2726_; 
lean_inc_ref(v_decl_2723_);
v___x_2724_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2701_, v_lctx_2717_, v_decl_2723_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2724_);
v___x_2726_ = v___x_2720_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2724_);
lean_ctor_set(v_reuseFailAlloc_2729_, 1, v_nextIdx_2718_);
v___x_2726_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2727_ = lean_st_ref_put(v_a_2705_, v___x_2726_);
v___x_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2728_, 0, v_decl_2723_);
return v___x_2728_;
}
}
}
}
}
else
{
lean_object* v___x_2737_; 
lean_dec(v_value_2704_);
lean_dec_ref(v_type_2703_);
v___x_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2737_, 0, v_decl_2702_);
return v___x_2737_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg___boxed(lean_object* v_pu_2744_, lean_object* v_decl_2745_, lean_object* v_type_2746_, lean_object* v_value_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_){
_start:
{
uint8_t v_pu_boxed_2750_; lean_object* v_res_2751_; 
v_pu_boxed_2750_ = lean_unbox(v_pu_2744_);
v_res_2751_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_boxed_2750_, v_decl_2745_, v_type_2746_, v_value_2747_, v_a_2748_);
lean_dec(v_a_2748_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(uint8_t v_pu_2752_, lean_object* v_decl_2753_, lean_object* v_type_2754_, lean_object* v_value_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2752_, v_decl_2753_, v_type_2754_, v_value_2755_, v_a_2757_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(lean_object* v_pu_2762_, lean_object* v_decl_2763_, lean_object* v_type_2764_, lean_object* v_value_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
uint8_t v_pu_boxed_2771_; lean_object* v_res_2772_; 
v_pu_boxed_2771_ = lean_unbox(v_pu_2762_);
v_res_2772_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(v_pu_boxed_2771_, v_decl_2763_, v_type_2764_, v_value_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t v_pu_2773_, lean_object* v_decl_2774_, lean_object* v_value_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v_type_2778_; lean_object* v___x_2779_; 
v_type_2778_ = lean_ctor_get(v_decl_2774_, 2);
lean_inc_ref(v_type_2778_);
v___x_2779_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2773_, v_decl_2774_, v_type_2778_, v_value_2775_, v_a_2776_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg___boxed(lean_object* v_pu_2780_, lean_object* v_decl_2781_, lean_object* v_value_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_){
_start:
{
uint8_t v_pu_boxed_2785_; lean_object* v_res_2786_; 
v_pu_boxed_2785_ = lean_unbox(v_pu_2780_);
v_res_2786_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_boxed_2785_, v_decl_2781_, v_value_2782_, v_a_2783_);
lean_dec(v_a_2783_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(uint8_t v_pu_2787_, lean_object* v_decl_2788_, lean_object* v_value_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v___x_2795_; 
v___x_2795_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_2787_, v_decl_2788_, v_value_2789_, v_a_2791_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___boxed(lean_object* v_pu_2796_, lean_object* v_decl_2797_, lean_object* v_value_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_){
_start:
{
uint8_t v_pu_boxed_2804_; lean_object* v_res_2805_; 
v_pu_boxed_2804_ = lean_unbox(v_pu_2796_);
v_res_2805_ = l_Lean_Compiler_LCNF_LetDecl_updateValue(v_pu_boxed_2804_, v_decl_2797_, v_value_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t v_pu_2806_, lean_object* v_decl_2807_, lean_object* v_type_2808_, lean_object* v_params_2809_, lean_object* v_value_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v_fvarId_2813_; lean_object* v_binderName_2814_; lean_object* v_params_2815_; lean_object* v_type_2816_; lean_object* v_value_2817_; uint8_t v___y_2834_; size_t v___x_2839_; size_t v___x_2840_; uint8_t v___x_2841_; 
v_fvarId_2813_ = lean_ctor_get(v_decl_2807_, 0);
v_binderName_2814_ = lean_ctor_get(v_decl_2807_, 1);
v_params_2815_ = lean_ctor_get(v_decl_2807_, 2);
v_type_2816_ = lean_ctor_get(v_decl_2807_, 3);
v_value_2817_ = lean_ctor_get(v_decl_2807_, 4);
v___x_2839_ = lean_ptr_addr(v_type_2808_);
v___x_2840_ = lean_ptr_addr(v_type_2816_);
v___x_2841_ = lean_usize_dec_eq(v___x_2839_, v___x_2840_);
if (v___x_2841_ == 0)
{
v___y_2834_ = v___x_2841_;
goto v___jp_2833_;
}
else
{
size_t v___x_2842_; size_t v___x_2843_; uint8_t v___x_2844_; 
v___x_2842_ = lean_ptr_addr(v_params_2809_);
v___x_2843_ = lean_ptr_addr(v_params_2815_);
v___x_2844_ = lean_usize_dec_eq(v___x_2842_, v___x_2843_);
v___y_2834_ = v___x_2844_;
goto v___jp_2833_;
}
v___jp_2818_:
{
lean_object* v___x_2819_; lean_object* v_lctx_2820_; lean_object* v_nextIdx_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2832_; 
v___x_2819_ = lean_st_ref_take(v_a_2811_);
v_lctx_2820_ = lean_ctor_get(v___x_2819_, 0);
v_nextIdx_2821_ = lean_ctor_get(v___x_2819_, 1);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2823_ = v___x_2819_;
v_isShared_2824_ = v_isSharedCheck_2832_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_nextIdx_2821_);
lean_inc(v_lctx_2820_);
lean_dec(v___x_2819_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2832_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v_decl_2825_; lean_object* v___x_2826_; lean_object* v___x_2828_; 
v_decl_2825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_decl_2825_, 0, v_fvarId_2813_);
lean_ctor_set(v_decl_2825_, 1, v_binderName_2814_);
lean_ctor_set(v_decl_2825_, 2, v_params_2809_);
lean_ctor_set(v_decl_2825_, 3, v_type_2808_);
lean_ctor_set(v_decl_2825_, 4, v_value_2810_);
lean_inc_ref(v_decl_2825_);
v___x_2826_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2806_, v_lctx_2820_, v_decl_2825_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v___x_2826_);
v___x_2828_ = v___x_2823_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2826_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_nextIdx_2821_);
v___x_2828_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = lean_st_ref_put(v_a_2811_, v___x_2828_);
v___x_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2830_, 0, v_decl_2825_);
return v___x_2830_;
}
}
}
v___jp_2833_:
{
if (v___y_2834_ == 0)
{
lean_inc(v_binderName_2814_);
lean_inc(v_fvarId_2813_);
lean_dec_ref(v_decl_2807_);
goto v___jp_2818_;
}
else
{
size_t v___x_2835_; size_t v___x_2836_; uint8_t v___x_2837_; 
v___x_2835_ = lean_ptr_addr(v_value_2810_);
v___x_2836_ = lean_ptr_addr(v_value_2817_);
v___x_2837_ = lean_usize_dec_eq(v___x_2835_, v___x_2836_);
if (v___x_2837_ == 0)
{
lean_inc(v_binderName_2814_);
lean_inc(v_fvarId_2813_);
lean_dec_ref(v_decl_2807_);
goto v___jp_2818_;
}
else
{
lean_object* v___x_2838_; 
lean_dec_ref(v_value_2810_);
lean_dec_ref(v_params_2809_);
lean_dec_ref(v_type_2808_);
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v_decl_2807_);
return v___x_2838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg___boxed(lean_object* v_pu_2845_, lean_object* v_decl_2846_, lean_object* v_type_2847_, lean_object* v_params_2848_, lean_object* v_value_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
uint8_t v_pu_boxed_2852_; lean_object* v_res_2853_; 
v_pu_boxed_2852_ = lean_unbox(v_pu_2845_);
v_res_2853_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_boxed_2852_, v_decl_2846_, v_type_2847_, v_params_2848_, v_value_2849_, v_a_2850_);
lean_dec(v_a_2850_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(uint8_t v_pu_2854_, lean_object* v_decl_2855_, lean_object* v_type_2856_, lean_object* v_params_2857_, lean_object* v_value_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2854_, v_decl_2855_, v_type_2856_, v_params_2857_, v_value_2858_, v_a_2860_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(lean_object* v_pu_2865_, lean_object* v_decl_2866_, lean_object* v_type_2867_, lean_object* v_params_2868_, lean_object* v_value_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
uint8_t v_pu_boxed_2875_; lean_object* v_res_2876_; 
v_pu_boxed_2875_ = lean_unbox(v_pu_2865_);
v_res_2876_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(v_pu_boxed_2875_, v_decl_2866_, v_type_2867_, v_params_2868_, v_value_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
lean_dec(v_a_2873_);
lean_dec_ref(v_a_2872_);
lean_dec(v_a_2871_);
lean_dec_ref(v_a_2870_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(uint8_t v_pu_2877_, lean_object* v_decl_2878_, lean_object* v_type_2879_, lean_object* v_value_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v_params_2883_; lean_object* v___x_2884_; 
v_params_2883_ = lean_ctor_get(v_decl_2878_, 2);
lean_inc_ref(v_params_2883_);
v___x_2884_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2877_, v_decl_2878_, v_type_2879_, v_params_2883_, v_value_2880_, v_a_2881_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg___boxed(lean_object* v_pu_2885_, lean_object* v_decl_2886_, lean_object* v_type_2887_, lean_object* v_value_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_){
_start:
{
uint8_t v_pu_boxed_2891_; lean_object* v_res_2892_; 
v_pu_boxed_2891_ = lean_unbox(v_pu_2885_);
v_res_2892_ = l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(v_pu_boxed_2891_, v_decl_2886_, v_type_2887_, v_value_2888_, v_a_2889_);
lean_dec(v_a_2889_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27(uint8_t v_pu_2893_, lean_object* v_decl_2894_, lean_object* v_type_2895_, lean_object* v_value_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v_params_2902_; lean_object* v___x_2903_; 
v_params_2902_ = lean_ctor_get(v_decl_2894_, 2);
lean_inc_ref(v_params_2902_);
v___x_2903_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2893_, v_decl_2894_, v_type_2895_, v_params_2902_, v_value_2896_, v_a_2898_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___boxed(lean_object* v_pu_2904_, lean_object* v_decl_2905_, lean_object* v_type_2906_, lean_object* v_value_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
uint8_t v_pu_boxed_2913_; lean_object* v_res_2914_; 
v_pu_boxed_2913_ = lean_unbox(v_pu_2904_);
v_res_2914_ = l_Lean_Compiler_LCNF_FunDecl_update_x27(v_pu_boxed_2913_, v_decl_2905_, v_type_2906_, v_value_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(uint8_t v_pu_2915_, lean_object* v_decl_2916_, lean_object* v_value_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v_params_2920_; lean_object* v_type_2921_; lean_object* v___x_2922_; 
v_params_2920_ = lean_ctor_get(v_decl_2916_, 2);
lean_inc_ref(v_params_2920_);
v_type_2921_ = lean_ctor_get(v_decl_2916_, 3);
lean_inc_ref(v_type_2921_);
v___x_2922_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2915_, v_decl_2916_, v_type_2921_, v_params_2920_, v_value_2917_, v_a_2918_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg___boxed(lean_object* v_pu_2923_, lean_object* v_decl_2924_, lean_object* v_value_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_){
_start:
{
uint8_t v_pu_boxed_2928_; lean_object* v_res_2929_; 
v_pu_boxed_2928_ = lean_unbox(v_pu_2923_);
v_res_2929_ = l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(v_pu_boxed_2928_, v_decl_2924_, v_value_2925_, v_a_2926_);
lean_dec(v_a_2926_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue(uint8_t v_pu_2930_, lean_object* v_decl_2931_, lean_object* v_value_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v_params_2938_; lean_object* v_type_2939_; lean_object* v___x_2940_; 
v_params_2938_ = lean_ctor_get(v_decl_2931_, 2);
lean_inc_ref(v_params_2938_);
v_type_2939_ = lean_ctor_get(v_decl_2931_, 3);
lean_inc_ref(v_type_2939_);
v___x_2940_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2930_, v_decl_2931_, v_type_2939_, v_params_2938_, v_value_2932_, v_a_2934_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___boxed(lean_object* v_pu_2941_, lean_object* v_decl_2942_, lean_object* v_value_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_){
_start:
{
uint8_t v_pu_boxed_2949_; lean_object* v_res_2950_; 
v_pu_boxed_2949_ = lean_unbox(v_pu_2941_);
v_res_2950_ = l_Lean_Compiler_LCNF_FunDecl_updateValue(v_pu_boxed_2949_, v_decl_2942_, v_value_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0(uint8_t v_pu_2951_, lean_object* v_p_2952_, lean_object* v_inst_2953_, lean_object* v_____do__lift_2954_){
_start:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2955_ = lean_box(v_pu_2951_);
v___x_2956_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_2956_, 0, v___x_2955_);
lean_closure_set(v___x_2956_, 1, v_p_2952_);
lean_closure_set(v___x_2956_, 2, v_____do__lift_2954_);
v___x_2957_ = lean_apply_2(v_inst_2953_, lean_box(0), v___x_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed(lean_object* v_pu_2958_, lean_object* v_p_2959_, lean_object* v_inst_2960_, lean_object* v_____do__lift_2961_){
_start:
{
uint8_t v_pu_boxed_2962_; lean_object* v_res_2963_; 
v_pu_boxed_2962_ = lean_unbox(v_pu_2958_);
v_res_2963_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__0(v_pu_boxed_2962_, v_p_2959_, v_inst_2960_, v_____do__lift_2961_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1(uint8_t v_pu_2964_, uint8_t v_t_2965_, lean_object* v_type_2966_, lean_object* v_toPure_2967_, lean_object* v_____do__lift_2968_){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2969_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2964_, v_____do__lift_2968_, v_t_2965_, v_type_2966_);
v___x_2970_ = lean_apply_2(v_toPure_2967_, lean_box(0), v___x_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed(lean_object* v_pu_2971_, lean_object* v_t_2972_, lean_object* v_type_2973_, lean_object* v_toPure_2974_, lean_object* v_____do__lift_2975_){
_start:
{
uint8_t v_pu_boxed_2976_; uint8_t v_t_boxed_2977_; lean_object* v_res_2978_; 
v_pu_boxed_2976_ = lean_unbox(v_pu_2971_);
v_t_boxed_2977_ = lean_unbox(v_t_2972_);
v_res_2978_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__1(v_pu_boxed_2976_, v_t_boxed_2977_, v_type_2973_, v_toPure_2974_, v_____do__lift_2975_);
lean_dec_ref(v_____do__lift_2975_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg(uint8_t v_pu_2979_, uint8_t v_t_2980_, lean_object* v_inst_2981_, lean_object* v_inst_2982_, lean_object* v_inst_2983_, lean_object* v_p_2984_){
_start:
{
lean_object* v_toApplicative_2985_; lean_object* v_toBind_2986_; lean_object* v_type_2987_; lean_object* v_toPure_2988_; lean_object* v___x_2989_; lean_object* v___f_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___f_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v_toApplicative_2985_ = lean_ctor_get(v_inst_2982_, 0);
lean_inc_ref(v_toApplicative_2985_);
v_toBind_2986_ = lean_ctor_get(v_inst_2982_, 1);
lean_inc_n(v_toBind_2986_, 2);
lean_dec_ref(v_inst_2982_);
v_type_2987_ = lean_ctor_get(v_p_2984_, 2);
lean_inc_ref(v_type_2987_);
v_toPure_2988_ = lean_ctor_get(v_toApplicative_2985_, 1);
lean_inc(v_toPure_2988_);
lean_dec_ref(v_toApplicative_2985_);
v___x_2989_ = lean_box(v_pu_2979_);
v___f_2990_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2990_, 0, v___x_2989_);
lean_closure_set(v___f_2990_, 1, v_p_2984_);
lean_closure_set(v___f_2990_, 2, v_inst_2981_);
v___x_2991_ = lean_box(v_pu_2979_);
v___x_2992_ = lean_box(v_t_2980_);
v___f_2993_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2993_, 0, v___x_2991_);
lean_closure_set(v___f_2993_, 1, v___x_2992_);
lean_closure_set(v___f_2993_, 2, v_type_2987_);
lean_closure_set(v___f_2993_, 3, v_toPure_2988_);
v___x_2994_ = lean_apply_4(v_toBind_2986_, lean_box(0), lean_box(0), v_inst_2983_, v___f_2993_);
v___x_2995_ = lean_apply_4(v_toBind_2986_, lean_box(0), lean_box(0), v___x_2994_, v___f_2990_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___boxed(lean_object* v_pu_2996_, lean_object* v_t_2997_, lean_object* v_inst_2998_, lean_object* v_inst_2999_, lean_object* v_inst_3000_, lean_object* v_p_3001_){
_start:
{
uint8_t v_pu_boxed_3002_; uint8_t v_t_boxed_3003_; lean_object* v_res_3004_; 
v_pu_boxed_3002_ = lean_unbox(v_pu_2996_);
v_t_boxed_3003_ = lean_unbox(v_t_2997_);
v_res_3004_ = l_Lean_Compiler_LCNF_normParam___redArg(v_pu_boxed_3002_, v_t_boxed_3003_, v_inst_2998_, v_inst_2999_, v_inst_3000_, v_p_3001_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam(lean_object* v_m_3005_, uint8_t v_pu_3006_, uint8_t v_t_3007_, lean_object* v_inst_3008_, lean_object* v_inst_3009_, lean_object* v_inst_3010_, lean_object* v_p_3011_){
_start:
{
lean_object* v_toApplicative_3012_; lean_object* v_toBind_3013_; lean_object* v_type_3014_; lean_object* v_toPure_3015_; lean_object* v___x_3016_; lean_object* v___f_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___f_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v_toApplicative_3012_ = lean_ctor_get(v_inst_3009_, 0);
lean_inc_ref(v_toApplicative_3012_);
v_toBind_3013_ = lean_ctor_get(v_inst_3009_, 1);
lean_inc_n(v_toBind_3013_, 2);
lean_dec_ref(v_inst_3009_);
v_type_3014_ = lean_ctor_get(v_p_3011_, 2);
lean_inc_ref(v_type_3014_);
v_toPure_3015_ = lean_ctor_get(v_toApplicative_3012_, 1);
lean_inc(v_toPure_3015_);
lean_dec_ref(v_toApplicative_3012_);
v___x_3016_ = lean_box(v_pu_3006_);
v___f_3017_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3017_, 0, v___x_3016_);
lean_closure_set(v___f_3017_, 1, v_p_3011_);
lean_closure_set(v___f_3017_, 2, v_inst_3008_);
v___x_3018_ = lean_box(v_pu_3006_);
v___x_3019_ = lean_box(v_t_3007_);
v___f_3020_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3020_, 0, v___x_3018_);
lean_closure_set(v___f_3020_, 1, v___x_3019_);
lean_closure_set(v___f_3020_, 2, v_type_3014_);
lean_closure_set(v___f_3020_, 3, v_toPure_3015_);
v___x_3021_ = lean_apply_4(v_toBind_3013_, lean_box(0), lean_box(0), v_inst_3010_, v___f_3020_);
v___x_3022_ = lean_apply_4(v_toBind_3013_, lean_box(0), lean_box(0), v___x_3021_, v___f_3017_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___boxed(lean_object* v_m_3023_, lean_object* v_pu_3024_, lean_object* v_t_3025_, lean_object* v_inst_3026_, lean_object* v_inst_3027_, lean_object* v_inst_3028_, lean_object* v_p_3029_){
_start:
{
uint8_t v_pu_boxed_3030_; uint8_t v_t_boxed_3031_; lean_object* v_res_3032_; 
v_pu_boxed_3030_ = lean_unbox(v_pu_3024_);
v_t_boxed_3031_ = lean_unbox(v_t_3025_);
v_res_3032_ = l_Lean_Compiler_LCNF_normParam(v_m_3023_, v_pu_boxed_3030_, v_t_boxed_3031_, v_inst_3026_, v_inst_3027_, v_inst_3028_, v_p_3029_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg(uint8_t v_pu_3033_, uint8_t v_t_3034_, lean_object* v_inst_3035_, lean_object* v_inst_3036_, lean_object* v_inst_3037_, lean_object* v_ps_3038_){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3039_ = lean_box(v_pu_3033_);
v___x_3040_ = lean_box(v_t_3034_);
lean_inc_ref(v_inst_3036_);
v___x_3041_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___boxed), 7, 6);
lean_closure_set(v___x_3041_, 0, lean_box(0));
lean_closure_set(v___x_3041_, 1, v___x_3039_);
lean_closure_set(v___x_3041_, 2, v___x_3040_);
lean_closure_set(v___x_3041_, 3, v_inst_3035_);
lean_closure_set(v___x_3041_, 4, v_inst_3036_);
lean_closure_set(v___x_3041_, 5, v_inst_3037_);
v___x_3042_ = lean_unsigned_to_nat(0u);
v___x_3043_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_3036_, v___x_3041_, v___x_3042_, v_ps_3038_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg___boxed(lean_object* v_pu_3044_, lean_object* v_t_3045_, lean_object* v_inst_3046_, lean_object* v_inst_3047_, lean_object* v_inst_3048_, lean_object* v_ps_3049_){
_start:
{
uint8_t v_pu_boxed_3050_; uint8_t v_t_boxed_3051_; lean_object* v_res_3052_; 
v_pu_boxed_3050_ = lean_unbox(v_pu_3044_);
v_t_boxed_3051_ = lean_unbox(v_t_3045_);
v_res_3052_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_boxed_3050_, v_t_boxed_3051_, v_inst_3046_, v_inst_3047_, v_inst_3048_, v_ps_3049_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams(lean_object* v_m_3053_, uint8_t v_pu_3054_, uint8_t v_t_3055_, lean_object* v_inst_3056_, lean_object* v_inst_3057_, lean_object* v_inst_3058_, lean_object* v_ps_3059_){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_3054_, v_t_3055_, v_inst_3056_, v_inst_3057_, v_inst_3058_, v_ps_3059_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___boxed(lean_object* v_m_3061_, lean_object* v_pu_3062_, lean_object* v_t_3063_, lean_object* v_inst_3064_, lean_object* v_inst_3065_, lean_object* v_inst_3066_, lean_object* v_ps_3067_){
_start:
{
uint8_t v_pu_boxed_3068_; uint8_t v_t_boxed_3069_; lean_object* v_res_3070_; 
v_pu_boxed_3068_ = lean_unbox(v_pu_3062_);
v_t_boxed_3069_ = lean_unbox(v_t_3063_);
v_res_3070_ = l_Lean_Compiler_LCNF_normParams(v_m_3061_, v_pu_boxed_3068_, v_t_boxed_3069_, v_inst_3064_, v_inst_3065_, v_inst_3066_, v_ps_3067_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(uint8_t v_pu_3071_, lean_object* v_decl_3072_, lean_object* v_____do__lift_3073_, lean_object* v_inst_3074_, lean_object* v_____do__lift_3075_){
_start:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3076_ = lean_box(v_pu_3071_);
v___x_3077_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_3077_, 0, v___x_3076_);
lean_closure_set(v___x_3077_, 1, v_decl_3072_);
lean_closure_set(v___x_3077_, 2, v_____do__lift_3073_);
lean_closure_set(v___x_3077_, 3, v_____do__lift_3075_);
v___x_3078_ = lean_apply_2(v_inst_3074_, lean_box(0), v___x_3077_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed(lean_object* v_pu_3079_, lean_object* v_decl_3080_, lean_object* v_____do__lift_3081_, lean_object* v_inst_3082_, lean_object* v_____do__lift_3083_){
_start:
{
uint8_t v_pu_boxed_3084_; lean_object* v_res_3085_; 
v_pu_boxed_3084_ = lean_unbox(v_pu_3079_);
v_res_3085_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(v_pu_boxed_3084_, v_decl_3080_, v_____do__lift_3081_, v_inst_3082_, v_____do__lift_3083_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(uint8_t v_pu_3086_, lean_object* v_value_3087_, uint8_t v_t_3088_, lean_object* v_toPure_3089_, lean_object* v_____do__lift_3090_){
_start:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3091_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3086_, v_____do__lift_3090_, v_value_3087_, v_t_3088_);
v___x_3092_ = lean_apply_2(v_toPure_3089_, lean_box(0), v___x_3091_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed(lean_object* v_pu_3093_, lean_object* v_value_3094_, lean_object* v_t_3095_, lean_object* v_toPure_3096_, lean_object* v_____do__lift_3097_){
_start:
{
uint8_t v_pu_boxed_3098_; uint8_t v_t_boxed_3099_; lean_object* v_res_3100_; 
v_pu_boxed_3098_ = lean_unbox(v_pu_3093_);
v_t_boxed_3099_ = lean_unbox(v_t_3095_);
v_res_3100_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(v_pu_boxed_3098_, v_value_3094_, v_t_boxed_3099_, v_toPure_3096_, v_____do__lift_3097_);
lean_dec_ref(v_____do__lift_3097_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(uint8_t v_pu_3101_, lean_object* v_decl_3102_, lean_object* v_inst_3103_, lean_object* v_value_3104_, uint8_t v_t_3105_, lean_object* v_toPure_3106_, lean_object* v_toBind_3107_, lean_object* v_inst_3108_, lean_object* v_____do__lift_3109_){
_start:
{
lean_object* v___x_3110_; lean_object* v___f_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___f_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3110_ = lean_box(v_pu_3101_);
v___f_3111_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3111_, 0, v___x_3110_);
lean_closure_set(v___f_3111_, 1, v_decl_3102_);
lean_closure_set(v___f_3111_, 2, v_____do__lift_3109_);
lean_closure_set(v___f_3111_, 3, v_inst_3103_);
v___x_3112_ = lean_box(v_pu_3101_);
v___x_3113_ = lean_box(v_t_3105_);
v___f_3114_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3114_, 0, v___x_3112_);
lean_closure_set(v___f_3114_, 1, v_value_3104_);
lean_closure_set(v___f_3114_, 2, v___x_3113_);
lean_closure_set(v___f_3114_, 3, v_toPure_3106_);
lean_inc(v_toBind_3107_);
v___x_3115_ = lean_apply_4(v_toBind_3107_, lean_box(0), lean_box(0), v_inst_3108_, v___f_3114_);
v___x_3116_ = lean_apply_4(v_toBind_3107_, lean_box(0), lean_box(0), v___x_3115_, v___f_3111_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed(lean_object* v_pu_3117_, lean_object* v_decl_3118_, lean_object* v_inst_3119_, lean_object* v_value_3120_, lean_object* v_t_3121_, lean_object* v_toPure_3122_, lean_object* v_toBind_3123_, lean_object* v_inst_3124_, lean_object* v_____do__lift_3125_){
_start:
{
uint8_t v_pu_boxed_3126_; uint8_t v_t_boxed_3127_; lean_object* v_res_3128_; 
v_pu_boxed_3126_ = lean_unbox(v_pu_3117_);
v_t_boxed_3127_ = lean_unbox(v_t_3121_);
v_res_3128_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(v_pu_boxed_3126_, v_decl_3118_, v_inst_3119_, v_value_3120_, v_t_boxed_3127_, v_toPure_3122_, v_toBind_3123_, v_inst_3124_, v_____do__lift_3125_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg(uint8_t v_pu_3129_, uint8_t v_t_3130_, lean_object* v_inst_3131_, lean_object* v_inst_3132_, lean_object* v_inst_3133_, lean_object* v_decl_3134_){
_start:
{
lean_object* v_toApplicative_3135_; lean_object* v_toBind_3136_; lean_object* v_type_3137_; lean_object* v_value_3138_; lean_object* v_toPure_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___f_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___f_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v_toApplicative_3135_ = lean_ctor_get(v_inst_3132_, 0);
lean_inc_ref(v_toApplicative_3135_);
v_toBind_3136_ = lean_ctor_get(v_inst_3132_, 1);
lean_inc_n(v_toBind_3136_, 3);
lean_dec_ref(v_inst_3132_);
v_type_3137_ = lean_ctor_get(v_decl_3134_, 2);
lean_inc_ref(v_type_3137_);
v_value_3138_ = lean_ctor_get(v_decl_3134_, 3);
lean_inc(v_value_3138_);
v_toPure_3139_ = lean_ctor_get(v_toApplicative_3135_, 1);
lean_inc_n(v_toPure_3139_, 2);
lean_dec_ref(v_toApplicative_3135_);
v___x_3140_ = lean_box(v_pu_3129_);
v___x_3141_ = lean_box(v_t_3130_);
lean_inc(v_inst_3133_);
v___f_3142_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_3142_, 0, v___x_3140_);
lean_closure_set(v___f_3142_, 1, v_decl_3134_);
lean_closure_set(v___f_3142_, 2, v_inst_3131_);
lean_closure_set(v___f_3142_, 3, v_value_3138_);
lean_closure_set(v___f_3142_, 4, v___x_3141_);
lean_closure_set(v___f_3142_, 5, v_toPure_3139_);
lean_closure_set(v___f_3142_, 6, v_toBind_3136_);
lean_closure_set(v___f_3142_, 7, v_inst_3133_);
v___x_3143_ = lean_box(v_pu_3129_);
v___x_3144_ = lean_box(v_t_3130_);
v___f_3145_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3145_, 0, v___x_3143_);
lean_closure_set(v___f_3145_, 1, v___x_3144_);
lean_closure_set(v___f_3145_, 2, v_type_3137_);
lean_closure_set(v___f_3145_, 3, v_toPure_3139_);
v___x_3146_ = lean_apply_4(v_toBind_3136_, lean_box(0), lean_box(0), v_inst_3133_, v___f_3145_);
v___x_3147_ = lean_apply_4(v_toBind_3136_, lean_box(0), lean_box(0), v___x_3146_, v___f_3142_);
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___boxed(lean_object* v_pu_3148_, lean_object* v_t_3149_, lean_object* v_inst_3150_, lean_object* v_inst_3151_, lean_object* v_inst_3152_, lean_object* v_decl_3153_){
_start:
{
uint8_t v_pu_boxed_3154_; uint8_t v_t_boxed_3155_; lean_object* v_res_3156_; 
v_pu_boxed_3154_ = lean_unbox(v_pu_3148_);
v_t_boxed_3155_ = lean_unbox(v_t_3149_);
v_res_3156_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_boxed_3154_, v_t_boxed_3155_, v_inst_3150_, v_inst_3151_, v_inst_3152_, v_decl_3153_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl(lean_object* v_m_3157_, uint8_t v_pu_3158_, uint8_t v_t_3159_, lean_object* v_inst_3160_, lean_object* v_inst_3161_, lean_object* v_inst_3162_, lean_object* v_decl_3163_){
_start:
{
lean_object* v___x_3164_; 
v___x_3164_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_3158_, v_t_3159_, v_inst_3160_, v_inst_3161_, v_inst_3162_, v_decl_3163_);
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___boxed(lean_object* v_m_3165_, lean_object* v_pu_3166_, lean_object* v_t_3167_, lean_object* v_inst_3168_, lean_object* v_inst_3169_, lean_object* v_inst_3170_, lean_object* v_decl_3171_){
_start:
{
uint8_t v_pu_boxed_3172_; uint8_t v_t_boxed_3173_; lean_object* v_res_3174_; 
v_pu_boxed_3172_ = lean_unbox(v_pu_3166_);
v_t_boxed_3173_ = lean_unbox(v_t_3167_);
v_res_3174_ = l_Lean_Compiler_LCNF_normLetDecl(v_m_3165_, v_pu_boxed_3172_, v_t_boxed_3173_, v_inst_3168_, v_inst_3169_, v_inst_3170_, v_decl_3171_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(uint8_t v_pu_3175_, uint8_t v_t_3176_){
_start:
{
lean_object* v___x_3177_; lean_object* v_toApplicative_3178_; lean_object* v_toFunctor_3179_; lean_object* v_toSeq_3180_; lean_object* v_toSeqLeft_3181_; lean_object* v_toSeqRight_3182_; lean_object* v___f_3183_; lean_object* v___f_3184_; lean_object* v___f_3185_; lean_object* v___f_3186_; lean_object* v___x_3187_; lean_object* v___f_3188_; lean_object* v___f_3189_; lean_object* v___f_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v_toApplicative_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3222_; 
v___x_3177_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_3178_ = lean_ctor_get(v___x_3177_, 0);
v_toFunctor_3179_ = lean_ctor_get(v_toApplicative_3178_, 0);
v_toSeq_3180_ = lean_ctor_get(v_toApplicative_3178_, 2);
v_toSeqLeft_3181_ = lean_ctor_get(v_toApplicative_3178_, 3);
v_toSeqRight_3182_ = lean_ctor_get(v_toApplicative_3178_, 4);
v___f_3183_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_3184_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_3179_, 2);
v___f_3185_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3185_, 0, v_toFunctor_3179_);
v___f_3186_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3186_, 0, v_toFunctor_3179_);
v___x_3187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___f_3185_);
lean_ctor_set(v___x_3187_, 1, v___f_3186_);
lean_inc(v_toSeqRight_3182_);
v___f_3188_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3188_, 0, v_toSeqRight_3182_);
lean_inc(v_toSeqLeft_3181_);
v___f_3189_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3189_, 0, v_toSeqLeft_3181_);
lean_inc(v_toSeq_3180_);
v___f_3190_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3190_, 0, v_toSeq_3180_);
v___x_3191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3187_);
lean_ctor_set(v___x_3191_, 1, v___f_3183_);
lean_ctor_set(v___x_3191_, 2, v___f_3190_);
lean_ctor_set(v___x_3191_, 3, v___f_3189_);
lean_ctor_set(v___x_3191_, 4, v___f_3188_);
v___x_3192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
lean_ctor_set(v___x_3192_, 1, v___f_3184_);
v___x_3193_ = l_StateRefT_x27_instMonad___redArg(v___x_3192_);
v_toApplicative_3194_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3222_ == 0)
{
lean_object* v_unused_3223_; 
v_unused_3223_ = lean_ctor_get(v___x_3193_, 1);
lean_dec(v_unused_3223_);
v___x_3196_ = v___x_3193_;
v_isShared_3197_ = v_isSharedCheck_3222_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_toApplicative_3194_);
lean_dec(v___x_3193_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3222_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v_toFunctor_3198_; lean_object* v_toSeq_3199_; lean_object* v_toSeqLeft_3200_; lean_object* v_toSeqRight_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3220_; 
v_toFunctor_3198_ = lean_ctor_get(v_toApplicative_3194_, 0);
v_toSeq_3199_ = lean_ctor_get(v_toApplicative_3194_, 2);
v_toSeqLeft_3200_ = lean_ctor_get(v_toApplicative_3194_, 3);
v_toSeqRight_3201_ = lean_ctor_get(v_toApplicative_3194_, 4);
v_isSharedCheck_3220_ = !lean_is_exclusive(v_toApplicative_3194_);
if (v_isSharedCheck_3220_ == 0)
{
lean_object* v_unused_3221_; 
v_unused_3221_ = lean_ctor_get(v_toApplicative_3194_, 1);
lean_dec(v_unused_3221_);
v___x_3203_ = v_toApplicative_3194_;
v_isShared_3204_ = v_isSharedCheck_3220_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_toSeqRight_3201_);
lean_inc(v_toSeqLeft_3200_);
lean_inc(v_toSeq_3199_);
lean_inc(v_toFunctor_3198_);
lean_dec(v_toApplicative_3194_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3220_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___f_3205_; lean_object* v___f_3206_; lean_object* v___f_3207_; lean_object* v___f_3208_; lean_object* v___x_3209_; lean_object* v___f_3210_; lean_object* v___f_3211_; lean_object* v___f_3212_; lean_object* v___x_3214_; 
v___f_3205_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_3206_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_3198_);
v___f_3207_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3207_, 0, v_toFunctor_3198_);
v___f_3208_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3208_, 0, v_toFunctor_3198_);
v___x_3209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___f_3207_);
lean_ctor_set(v___x_3209_, 1, v___f_3208_);
v___f_3210_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3210_, 0, v_toSeqRight_3201_);
v___f_3211_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3211_, 0, v_toSeqLeft_3200_);
v___f_3212_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3212_, 0, v_toSeq_3199_);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 4, v___f_3210_);
lean_ctor_set(v___x_3203_, 3, v___f_3211_);
lean_ctor_set(v___x_3203_, 2, v___f_3212_);
lean_ctor_set(v___x_3203_, 1, v___f_3205_);
lean_ctor_set(v___x_3203_, 0, v___x_3209_);
v___x_3214_ = v___x_3203_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3209_);
lean_ctor_set(v_reuseFailAlloc_3219_, 1, v___f_3205_);
lean_ctor_set(v_reuseFailAlloc_3219_, 2, v___f_3212_);
lean_ctor_set(v_reuseFailAlloc_3219_, 3, v___f_3211_);
lean_ctor_set(v_reuseFailAlloc_3219_, 4, v___f_3210_);
v___x_3214_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
lean_object* v___x_3216_; 
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 1, v___f_3206_);
lean_ctor_set(v___x_3196_, 0, v___x_3214_);
v___x_3216_ = v___x_3196_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v___f_3206_);
v___x_3216_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_3217_, 0, lean_box(0));
lean_closure_set(v___x_3217_, 1, lean_box(0));
lean_closure_set(v___x_3217_, 2, v___x_3216_);
return v___x_3217_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___boxed(lean_object* v_pu_3224_, lean_object* v_t_3225_){
_start:
{
uint8_t v_pu_boxed_3226_; uint8_t v_t_boxed_3227_; lean_object* v_res_3228_; 
v_pu_boxed_3226_ = lean_unbox(v_pu_3224_);
v_t_boxed_3227_ = lean_unbox(v_t_3225_);
v_res_3228_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(v_pu_boxed_3226_, v_t_boxed_3227_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg(uint8_t v_pu_3229_, lean_object* v_inst_3230_, lean_object* v_result_3231_, lean_object* v_x_3232_){
_start:
{
if (lean_obj_tag(v_result_3231_) == 0)
{
lean_object* v_fvarId_3233_; lean_object* v___x_3234_; 
lean_dec(v_inst_3230_);
v_fvarId_3233_ = lean_ctor_get(v_result_3231_, 0);
lean_inc(v_fvarId_3233_);
lean_dec_ref_known(v_result_3231_, 1);
v___x_3234_ = lean_apply_1(v_x_3232_, v_fvarId_3233_);
return v___x_3234_;
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
lean_dec(v_x_3232_);
v___x_3235_ = lean_box(v_pu_3229_);
v___x_3236_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3236_, 0, v___x_3235_);
v___x_3237_ = lean_apply_2(v_inst_3230_, lean_box(0), v___x_3236_);
return v___x_3237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg___boxed(lean_object* v_pu_3238_, lean_object* v_inst_3239_, lean_object* v_result_3240_, lean_object* v_x_3241_){
_start:
{
uint8_t v_pu_boxed_3242_; lean_object* v_res_3243_; 
v_pu_boxed_3242_ = lean_unbox(v_pu_3238_);
v_res_3243_ = l_Lean_Compiler_LCNF_withNormFVarResult___redArg(v_pu_boxed_3242_, v_inst_3239_, v_result_3240_, v_x_3241_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult(lean_object* v_m_3244_, uint8_t v_pu_3245_, lean_object* v_inst_3246_, lean_object* v_inst_3247_, lean_object* v_result_3248_, lean_object* v_x_3249_){
_start:
{
if (lean_obj_tag(v_result_3248_) == 0)
{
lean_object* v_fvarId_3250_; lean_object* v___x_3251_; 
lean_dec(v_inst_3246_);
v_fvarId_3250_ = lean_ctor_get(v_result_3248_, 0);
lean_inc(v_fvarId_3250_);
lean_dec_ref_known(v_result_3248_, 1);
v___x_3251_ = lean_apply_1(v_x_3249_, v_fvarId_3250_);
return v___x_3251_;
}
else
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
lean_dec(v_x_3249_);
v___x_3252_ = lean_box(v_pu_3245_);
v___x_3253_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3253_, 0, v___x_3252_);
v___x_3254_ = lean_apply_2(v_inst_3246_, lean_box(0), v___x_3253_);
return v___x_3254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___boxed(lean_object* v_m_3255_, lean_object* v_pu_3256_, lean_object* v_inst_3257_, lean_object* v_inst_3258_, lean_object* v_result_3259_, lean_object* v_x_3260_){
_start:
{
uint8_t v_pu_boxed_3261_; lean_object* v_res_3262_; 
v_pu_boxed_3261_ = lean_unbox(v_pu_3256_);
v_res_3262_ = l_Lean_Compiler_LCNF_withNormFVarResult(v_m_3255_, v_pu_boxed_3261_, v_inst_3257_, v_inst_3258_, v_result_3259_, v_x_3260_);
lean_dec_ref(v_inst_3258_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(uint8_t v_pu_3263_, uint8_t v_t_3264_, lean_object* v_args_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3268_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_3263_, v___y_3266_, v_args_3265_, v_t_3264_);
v___x_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg___boxed(lean_object* v_pu_3270_, lean_object* v_t_3271_, lean_object* v_args_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
uint8_t v_pu_boxed_3275_; uint8_t v_t_boxed_3276_; lean_object* v_res_3277_; 
v_pu_boxed_3275_ = lean_unbox(v_pu_3270_);
v_t_boxed_3276_ = lean_unbox(v_t_3271_);
v_res_3277_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_boxed_3275_, v_t_boxed_3276_, v_args_3272_, v___y_3273_);
lean_dec_ref(v___y_3273_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(uint8_t v_pu_3278_, uint8_t v_t_3279_, lean_object* v_i_3280_, lean_object* v_as_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v___x_3285_; uint8_t v___x_3286_; 
v___x_3285_ = lean_array_get_size(v_as_3281_);
v___x_3286_ = lean_nat_dec_lt(v_i_3280_, v___x_3285_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; 
lean_dec(v_i_3280_);
v___x_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3287_, 0, v_as_3281_);
return v___x_3287_;
}
else
{
lean_object* v_a_3288_; lean_object* v_type_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v_a_3288_ = lean_array_fget_borrowed(v_as_3281_, v_i_3280_);
v_type_3289_ = lean_ctor_get(v_a_3288_, 2);
lean_inc_ref(v_type_3289_);
v___x_3290_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3278_, v___y_3282_, v_t_3279_, v_type_3289_);
lean_inc(v_a_3288_);
v___x_3291_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_3278_, v_a_3288_, v___x_3290_, v___y_3283_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3292_; size_t v___x_3293_; size_t v___x_3294_; uint8_t v___x_3295_; 
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_a_3292_);
lean_dec_ref_known(v___x_3291_, 1);
v___x_3293_ = lean_ptr_addr(v_a_3288_);
v___x_3294_ = lean_ptr_addr(v_a_3292_);
v___x_3295_ = lean_usize_dec_eq(v___x_3293_, v___x_3294_);
if (v___x_3295_ == 0)
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3296_ = lean_unsigned_to_nat(1u);
v___x_3297_ = lean_nat_add(v_i_3280_, v___x_3296_);
v___x_3298_ = lean_array_fset(v_as_3281_, v_i_3280_, v_a_3292_);
lean_dec(v_i_3280_);
v_i_3280_ = v___x_3297_;
v_as_3281_ = v___x_3298_;
goto _start;
}
else
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
lean_dec(v_a_3292_);
v___x_3300_ = lean_unsigned_to_nat(1u);
v___x_3301_ = lean_nat_add(v_i_3280_, v___x_3300_);
lean_dec(v_i_3280_);
v_i_3280_ = v___x_3301_;
goto _start;
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_dec_ref(v_as_3281_);
lean_dec(v_i_3280_);
v_a_3303_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3291_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3291_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg___boxed(lean_object* v_pu_3311_, lean_object* v_t_3312_, lean_object* v_i_3313_, lean_object* v_as_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
uint8_t v_pu_boxed_3318_; uint8_t v_t_boxed_3319_; lean_object* v_res_3320_; 
v_pu_boxed_3318_ = lean_unbox(v_pu_3311_);
v_t_boxed_3319_ = lean_unbox(v_t_3312_);
v_res_3320_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_boxed_3318_, v_t_boxed_3319_, v_i_3313_, v_as_3314_, v___y_3315_, v___y_3316_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(uint8_t v_pu_3321_, uint8_t v_t_3322_, lean_object* v_ps_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3330_ = lean_unsigned_to_nat(0u);
v___x_3331_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_3321_, v_t_3322_, v___x_3330_, v_ps_3323_, v___y_3324_, v___y_3326_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg___boxed(lean_object* v_pu_3332_, lean_object* v_t_3333_, lean_object* v_ps_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
uint8_t v_pu_boxed_3341_; uint8_t v_t_boxed_3342_; lean_object* v_res_3343_; 
v_pu_boxed_3341_ = lean_unbox(v_pu_3332_);
v_t_boxed_3342_ = lean_unbox(v_t_3333_);
v_res_3343_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_boxed_3341_, v_t_boxed_3342_, v_ps_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec_ref(v___y_3335_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(uint8_t v_pu_3344_, uint8_t v_t_3345_, lean_object* v_decl_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v_type_3350_; lean_object* v_value_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v_type_3350_ = lean_ctor_get(v_decl_3346_, 2);
v_value_3351_ = lean_ctor_get(v_decl_3346_, 3);
lean_inc_ref(v_type_3350_);
v___x_3352_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3344_, v___y_3347_, v_t_3345_, v_type_3350_);
lean_inc(v_value_3351_);
v___x_3353_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3344_, v___y_3347_, v_value_3351_, v_t_3345_);
v___x_3354_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_3344_, v_decl_3346_, v___x_3352_, v___x_3353_, v___y_3348_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg___boxed(lean_object* v_pu_3355_, lean_object* v_t_3356_, lean_object* v_decl_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
uint8_t v_pu_boxed_3361_; uint8_t v_t_boxed_3362_; lean_object* v_res_3363_; 
v_pu_boxed_3361_ = lean_unbox(v_pu_3355_);
v_t_boxed_3362_ = lean_unbox(v_t_3356_);
v_res_3363_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_boxed_3361_, v_t_boxed_3362_, v_decl_3357_, v___y_3358_, v___y_3359_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(uint8_t v_pu_3364_, uint8_t v_t_3365_, lean_object* v_i_3366_, lean_object* v_as_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v___x_3374_; uint8_t v___x_3375_; 
v___x_3374_ = lean_array_get_size(v_as_3367_);
v___x_3375_ = lean_nat_dec_lt(v_i_3366_, v___x_3374_);
if (v___x_3375_ == 0)
{
lean_object* v___x_3376_; 
lean_dec(v_i_3366_);
v___x_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3376_, 0, v_as_3367_);
return v___x_3376_;
}
else
{
lean_object* v_a_3377_; lean_object* v_a_3379_; 
v_a_3377_ = lean_array_fget_borrowed(v_as_3367_, v_i_3366_);
switch(lean_obj_tag(v_a_3377_))
{
case 0:
{
lean_object* v_params_3390_; lean_object* v_code_3391_; lean_object* v___x_3392_; 
v_params_3390_ = lean_ctor_get(v_a_3377_, 1);
v_code_3391_ = lean_ctor_get(v_a_3377_, 2);
lean_inc_ref(v_params_3390_);
v___x_3392_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_3364_, v_t_3365_, v_params_3390_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; lean_object* v___x_3394_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v___x_3392_, 1);
lean_inc_ref(v_code_3391_);
v___x_3394_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3364_, v_t_3365_, v_code_3391_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; lean_object* v___x_3396_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_a_3395_);
lean_dec_ref_known(v___x_3394_, 1);
lean_inc_ref(v_a_3377_);
v___x_3396_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_3364_, v_a_3377_, v_a_3393_, v_a_3395_);
v_a_3379_ = v___x_3396_;
goto v___jp_3378_;
}
else
{
lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3404_; 
lean_dec(v_a_3393_);
lean_dec_ref(v_as_3367_);
lean_dec(v_i_3366_);
v_a_3397_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3399_ = v___x_3394_;
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3394_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3402_; 
if (v_isShared_3400_ == 0)
{
v___x_3402_ = v___x_3399_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_a_3397_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
lean_dec_ref(v_as_3367_);
lean_dec(v_i_3366_);
v_a_3405_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___x_3392_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3392_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3405_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
case 1:
{
lean_object* v_code_3413_; lean_object* v___x_3414_; 
v_code_3413_ = lean_ctor_get(v_a_3377_, 1);
lean_inc_ref(v_code_3413_);
v___x_3414_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3364_, v_t_3365_, v_code_3413_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; lean_object* v___x_3416_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc(v_a_3415_);
lean_dec_ref_known(v___x_3414_, 1);
lean_inc_ref(v_a_3377_);
v___x_3416_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3377_, v_a_3415_);
v_a_3379_ = v___x_3416_;
goto v___jp_3378_;
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
lean_dec_ref(v_as_3367_);
lean_dec(v_i_3366_);
v_a_3417_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3414_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3414_);
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
default: 
{
lean_object* v_code_3425_; lean_object* v___x_3426_; 
v_code_3425_ = lean_ctor_get(v_a_3377_, 0);
lean_inc_ref(v_code_3425_);
v___x_3426_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3364_, v_t_3365_, v_code_3425_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; lean_object* v___x_3428_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_a_3427_);
lean_dec_ref_known(v___x_3426_, 1);
lean_inc_ref(v_a_3377_);
v___x_3428_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3377_, v_a_3427_);
v_a_3379_ = v___x_3428_;
goto v___jp_3378_;
}
else
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_dec_ref(v_as_3367_);
lean_dec(v_i_3366_);
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
}
v___jp_3378_:
{
size_t v___x_3380_; size_t v___x_3381_; uint8_t v___x_3382_; 
v___x_3380_ = lean_ptr_addr(v_a_3377_);
v___x_3381_ = lean_ptr_addr(v_a_3379_);
v___x_3382_ = lean_usize_dec_eq(v___x_3380_, v___x_3381_);
if (v___x_3382_ == 0)
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3383_ = lean_unsigned_to_nat(1u);
v___x_3384_ = lean_nat_add(v_i_3366_, v___x_3383_);
v___x_3385_ = lean_array_fset(v_as_3367_, v_i_3366_, v_a_3379_);
lean_dec(v_i_3366_);
v_i_3366_ = v___x_3384_;
v_as_3367_ = v___x_3385_;
goto _start;
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
lean_dec_ref(v_a_3379_);
v___x_3387_ = lean_unsigned_to_nat(1u);
v___x_3388_ = lean_nat_add(v_i_3366_, v___x_3387_);
lean_dec(v_i_3366_);
v_i_3366_ = v___x_3388_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp(uint8_t v_pu_3437_, uint8_t v_t_3438_, lean_object* v_code_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_){
_start:
{
switch(lean_obj_tag(v_code_3439_))
{
case 0:
{
lean_object* v_decl_3446_; lean_object* v_k_3447_; lean_object* v___x_3448_; 
v_decl_3446_ = lean_ctor_get(v_code_3439_, 0);
v_k_3447_ = lean_ctor_get(v_code_3439_, 1);
lean_inc_ref(v_decl_3446_);
v___x_3448_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_3437_, v_t_3438_, v_decl_3446_, v_a_3440_, v_a_3442_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3450_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3449_);
lean_dec_ref_known(v___x_3448_, 1);
lean_inc_ref(v_k_3447_);
v___x_3450_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3437_, v_t_3438_, v_k_3447_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3478_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3453_ = v___x_3450_;
v_isShared_3454_ = v_isSharedCheck_3478_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3450_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3478_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
uint8_t v___y_3456_; size_t v___x_3472_; size_t v___x_3473_; uint8_t v___x_3474_; 
v___x_3472_ = lean_ptr_addr(v_k_3447_);
v___x_3473_ = lean_ptr_addr(v_a_3451_);
v___x_3474_ = lean_usize_dec_eq(v___x_3472_, v___x_3473_);
if (v___x_3474_ == 0)
{
v___y_3456_ = v___x_3474_;
goto v___jp_3455_;
}
else
{
size_t v___x_3475_; size_t v___x_3476_; uint8_t v___x_3477_; 
v___x_3475_ = lean_ptr_addr(v_decl_3446_);
v___x_3476_ = lean_ptr_addr(v_a_3449_);
v___x_3477_ = lean_usize_dec_eq(v___x_3475_, v___x_3476_);
v___y_3456_ = v___x_3477_;
goto v___jp_3455_;
}
v___jp_3455_:
{
if (v___y_3456_ == 0)
{
lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3466_; 
v_isSharedCheck_3466_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_3466_ == 0)
{
lean_object* v_unused_3467_; lean_object* v_unused_3468_; 
v_unused_3467_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_3467_);
v_unused_3468_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_3468_);
v___x_3458_ = v_code_3439_;
v_isShared_3459_ = v_isSharedCheck_3466_;
goto v_resetjp_3457_;
}
else
{
lean_dec(v_code_3439_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3466_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 1, v_a_3451_);
lean_ctor_set(v___x_3458_, 0, v_a_3449_);
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3449_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_a_3451_);
v___x_3461_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
lean_object* v___x_3463_; 
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 0, v___x_3461_);
v___x_3463_ = v___x_3453_;
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
lean_dec(v_a_3451_);
lean_dec(v_a_3449_);
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 0, v_code_3439_);
v___x_3470_ = v___x_3453_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_code_3439_);
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
lean_dec(v_a_3449_);
lean_dec_ref_known(v_code_3439_, 2);
return v___x_3450_;
}
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_dec_ref_known(v_code_3439_, 2);
v_a_3479_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3448_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3448_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
case 1:
{
lean_object* v_decl_3487_; lean_object* v_k_3488_; lean_object* v___x_3489_; 
v_decl_3487_ = lean_ctor_get(v_code_3439_, 0);
v_k_3488_ = lean_ctor_get(v_code_3439_, 1);
lean_inc_ref(v_decl_3487_);
v___x_3489_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3437_, v_t_3438_, v_decl_3487_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3491_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
lean_dec_ref_known(v___x_3489_, 1);
lean_inc_ref(v_k_3488_);
v___x_3491_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3437_, v_t_3438_, v_k_3488_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3519_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3494_ = v___x_3491_;
v_isShared_3495_ = v_isSharedCheck_3519_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3491_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3519_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
uint8_t v___y_3497_; size_t v___x_3513_; size_t v___x_3514_; uint8_t v___x_3515_; 
v___x_3513_ = lean_ptr_addr(v_k_3488_);
v___x_3514_ = lean_ptr_addr(v_a_3492_);
v___x_3515_ = lean_usize_dec_eq(v___x_3513_, v___x_3514_);
if (v___x_3515_ == 0)
{
v___y_3497_ = v___x_3515_;
goto v___jp_3496_;
}
else
{
size_t v___x_3516_; size_t v___x_3517_; uint8_t v___x_3518_; 
v___x_3516_ = lean_ptr_addr(v_decl_3487_);
v___x_3517_ = lean_ptr_addr(v_a_3490_);
v___x_3518_ = lean_usize_dec_eq(v___x_3516_, v___x_3517_);
v___y_3497_ = v___x_3518_;
goto v___jp_3496_;
}
v___jp_3496_:
{
if (v___y_3497_ == 0)
{
lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3507_; 
v_isSharedCheck_3507_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_3507_ == 0)
{
lean_object* v_unused_3508_; lean_object* v_unused_3509_; 
v_unused_3508_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_3508_);
v_unused_3509_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_3509_);
v___x_3499_ = v_code_3439_;
v_isShared_3500_ = v_isSharedCheck_3507_;
goto v_resetjp_3498_;
}
else
{
lean_dec(v_code_3439_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3507_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 1, v_a_3492_);
lean_ctor_set(v___x_3499_, 0, v_a_3490_);
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3490_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v_a_3492_);
v___x_3502_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
lean_object* v___x_3504_; 
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 0, v___x_3502_);
v___x_3504_ = v___x_3494_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3502_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
else
{
lean_object* v___x_3511_; 
lean_dec(v_a_3492_);
lean_dec(v_a_3490_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 0, v_code_3439_);
v___x_3511_ = v___x_3494_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_code_3439_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
}
}
else
{
lean_dec(v_a_3490_);
lean_dec_ref_known(v_code_3439_, 2);
return v___x_3491_;
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec_ref_known(v_code_3439_, 2);
v_a_3520_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3489_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3489_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
case 2:
{
lean_object* v_decl_3528_; lean_object* v_k_3529_; lean_object* v___x_3530_; 
v_decl_3528_ = lean_ctor_get(v_code_3439_, 0);
v_k_3529_ = lean_ctor_get(v_code_3439_, 1);
lean_inc_ref(v_decl_3528_);
v___x_3530_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3437_, v_t_3438_, v_decl_3528_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3532_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3530_, 1);
lean_inc_ref(v_k_3529_);
v___x_3532_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3437_, v_t_3438_, v_k_3529_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3560_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3535_ = v___x_3532_;
v_isShared_3536_ = v_isSharedCheck_3560_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3532_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3560_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
uint8_t v___y_3538_; size_t v___x_3554_; size_t v___x_3555_; uint8_t v___x_3556_; 
v___x_3554_ = lean_ptr_addr(v_k_3529_);
v___x_3555_ = lean_ptr_addr(v_a_3533_);
v___x_3556_ = lean_usize_dec_eq(v___x_3554_, v___x_3555_);
if (v___x_3556_ == 0)
{
v___y_3538_ = v___x_3556_;
goto v___jp_3537_;
}
else
{
size_t v___x_3557_; size_t v___x_3558_; uint8_t v___x_3559_; 
v___x_3557_ = lean_ptr_addr(v_decl_3528_);
v___x_3558_ = lean_ptr_addr(v_a_3531_);
v___x_3559_ = lean_usize_dec_eq(v___x_3557_, v___x_3558_);
v___y_3538_ = v___x_3559_;
goto v___jp_3537_;
}
v___jp_3537_:
{
if (v___y_3538_ == 0)
{
lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3548_; 
v_isSharedCheck_3548_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_3548_ == 0)
{
lean_object* v_unused_3549_; lean_object* v_unused_3550_; 
v_unused_3549_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_3549_);
v_unused_3550_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_3550_);
v___x_3540_ = v_code_3439_;
v_isShared_3541_ = v_isSharedCheck_3548_;
goto v_resetjp_3539_;
}
else
{
lean_dec(v_code_3439_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3548_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 1, v_a_3533_);
lean_ctor_set(v___x_3540_, 0, v_a_3531_);
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3531_);
lean_ctor_set(v_reuseFailAlloc_3547_, 1, v_a_3533_);
v___x_3543_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_object* v___x_3545_; 
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v___x_3543_);
v___x_3545_ = v___x_3535_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
else
{
lean_object* v___x_3552_; 
lean_dec(v_a_3533_);
lean_dec(v_a_3531_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v_code_3439_);
v___x_3552_ = v___x_3535_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_code_3439_);
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
}
else
{
lean_dec(v_a_3531_);
lean_dec_ref_known(v_code_3439_, 2);
return v___x_3532_;
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_dec_ref_known(v_code_3439_, 2);
v_a_3561_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3530_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3530_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3569_; lean_object* v_args_3570_; lean_object* v___x_3571_; 
v_fvarId_3569_ = lean_ctor_get(v_code_3439_, 0);
v_args_3570_ = lean_ctor_get(v_code_3439_, 1);
lean_inc(v_fvarId_3569_);
v___x_3571_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3440_, v_fvarId_3569_, v_t_3438_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_fvarId_3572_; lean_object* v___x_3573_; 
v_fvarId_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_fvarId_3572_);
lean_dec_ref_known(v___x_3571_, 1);
lean_inc_ref(v_args_3570_);
v___x_3573_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_3437_, v_t_3438_, v_args_3570_, v_a_3440_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3599_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3576_ = v___x_3573_;
v_isShared_3577_ = v_isSharedCheck_3599_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3573_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3599_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
uint8_t v___y_3579_; uint8_t v___x_3595_; 
v___x_3595_ = l_Lean_instBEqFVarId_beq(v_fvarId_3569_, v_fvarId_3572_);
if (v___x_3595_ == 0)
{
v___y_3579_ = v___x_3595_;
goto v___jp_3578_;
}
else
{
size_t v___x_3596_; size_t v___x_3597_; uint8_t v___x_3598_; 
v___x_3596_ = lean_ptr_addr(v_args_3570_);
v___x_3597_ = lean_ptr_addr(v_a_3574_);
v___x_3598_ = lean_usize_dec_eq(v___x_3596_, v___x_3597_);
v___y_3579_ = v___x_3598_;
goto v___jp_3578_;
}
v___jp_3578_:
{
if (v___y_3579_ == 0)
{
lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3589_; 
v_isSharedCheck_3589_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_3589_ == 0)
{
lean_object* v_unused_3590_; lean_object* v_unused_3591_; 
v_unused_3590_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_3590_);
v_unused_3591_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_3591_);
v___x_3581_ = v_code_3439_;
v_isShared_3582_ = v_isSharedCheck_3589_;
goto v_resetjp_3580_;
}
else
{
lean_dec(v_code_3439_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3589_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v_a_3574_);
lean_ctor_set(v___x_3581_, 0, v_fvarId_3572_);
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_fvarId_3572_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_a_3574_);
v___x_3584_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3586_; 
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 0, v___x_3584_);
v___x_3586_ = v___x_3576_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3584_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
else
{
lean_object* v___x_3593_; 
lean_dec(v_a_3574_);
lean_dec(v_fvarId_3572_);
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 0, v_code_3439_);
v___x_3593_ = v___x_3576_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_code_3439_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
lean_dec(v_fvarId_3572_);
lean_dec_ref_known(v_code_3439_, 2);
v_a_3600_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3573_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3573_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
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
else
{
lean_object* v___x_3608_; 
lean_dec_ref_known(v_code_3439_, 2);
v___x_3608_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3437_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
return v___x_3608_;
}
}
case 4:
{
lean_object* v_cases_3609_; lean_object* v_typeName_3610_; lean_object* v_resultType_3611_; lean_object* v_discr_3612_; lean_object* v_alts_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3660_; 
v_cases_3609_ = lean_ctor_get(v_code_3439_, 0);
lean_inc_ref(v_cases_3609_);
v_typeName_3610_ = lean_ctor_get(v_cases_3609_, 0);
v_resultType_3611_ = lean_ctor_get(v_cases_3609_, 1);
v_discr_3612_ = lean_ctor_get(v_cases_3609_, 2);
v_alts_3613_ = lean_ctor_get(v_cases_3609_, 3);
v_isSharedCheck_3660_ = !lean_is_exclusive(v_cases_3609_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3615_ = v_cases_3609_;
v_isShared_3616_ = v_isSharedCheck_3660_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_alts_3613_);
lean_inc(v_discr_3612_);
lean_inc(v_resultType_3611_);
lean_inc(v_typeName_3610_);
lean_dec(v_cases_3609_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3660_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
lean_inc_ref(v_resultType_3611_);
v___x_3617_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3437_, v_a_3440_, v_t_3438_, v_resultType_3611_);
lean_inc(v_discr_3612_);
v___x_3618_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3440_, v_discr_3612_, v_t_3438_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_fvarId_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3658_; 
v_fvarId_3619_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3621_ = v___x_3618_;
v_isShared_3622_ = v_isSharedCheck_3658_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_fvarId_3619_);
lean_dec(v___x_3618_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3658_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; 
v___x_3623_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3613_);
v___x_3624_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_3437_, v_t_3438_, v___x_3623_, v_alts_3613_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3649_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3627_ = v___x_3624_;
v_isShared_3628_ = v_isSharedCheck_3649_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3624_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3649_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
uint8_t v___y_3640_; size_t v___x_3643_; size_t v___x_3644_; uint8_t v___x_3645_; 
v___x_3643_ = lean_ptr_addr(v_alts_3613_);
lean_dec_ref(v_alts_3613_);
v___x_3644_ = lean_ptr_addr(v_a_3625_);
v___x_3645_ = lean_usize_dec_eq(v___x_3643_, v___x_3644_);
if (v___x_3645_ == 0)
{
lean_dec_ref(v_resultType_3611_);
v___y_3640_ = v___x_3645_;
goto v___jp_3639_;
}
else
{
size_t v___x_3646_; size_t v___x_3647_; uint8_t v___x_3648_; 
v___x_3646_ = lean_ptr_addr(v_resultType_3611_);
lean_dec_ref(v_resultType_3611_);
v___x_3647_ = lean_ptr_addr(v___x_3617_);
v___x_3648_ = lean_usize_dec_eq(v___x_3646_, v___x_3647_);
v___y_3640_ = v___x_3648_;
goto v___jp_3639_;
}
v___jp_3629_:
{
lean_object* v___x_3631_; 
if (v_isShared_3616_ == 0)
{
lean_ctor_set(v___x_3615_, 3, v_a_3625_);
lean_ctor_set(v___x_3615_, 2, v_fvarId_3619_);
lean_ctor_set(v___x_3615_, 1, v___x_3617_);
v___x_3631_ = v___x_3615_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_typeName_3610_);
lean_ctor_set(v_reuseFailAlloc_3638_, 1, v___x_3617_);
lean_ctor_set(v_reuseFailAlloc_3638_, 2, v_fvarId_3619_);
lean_ctor_set(v_reuseFailAlloc_3638_, 3, v_a_3625_);
v___x_3631_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
lean_object* v___x_3633_; 
if (v_isShared_3622_ == 0)
{
lean_ctor_set_tag(v___x_3621_, 4);
lean_ctor_set(v___x_3621_, 0, v___x_3631_);
v___x_3633_ = v___x_3621_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3631_);
v___x_3633_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
lean_object* v___x_3635_; 
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 0, v___x_3633_);
v___x_3635_ = v___x_3627_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3633_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
v___jp_3639_:
{
if (v___y_3640_ == 0)
{
lean_dec(v_discr_3612_);
lean_dec_ref_known(v_code_3439_, 1);
goto v___jp_3629_;
}
else
{
uint8_t v___x_3641_; 
v___x_3641_ = l_Lean_instBEqFVarId_beq(v_discr_3612_, v_fvarId_3619_);
lean_dec(v_discr_3612_);
if (v___x_3641_ == 0)
{
lean_dec_ref_known(v_code_3439_, 1);
goto v___jp_3629_;
}
else
{
lean_object* v___x_3642_; 
lean_del_object(v___x_3627_);
lean_dec(v_a_3625_);
lean_del_object(v___x_3621_);
lean_dec(v_fvarId_3619_);
lean_dec_ref(v___x_3617_);
lean_del_object(v___x_3615_);
lean_dec(v_typeName_3610_);
v___x_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3642_, 0, v_code_3439_);
return v___x_3642_;
}
}
}
}
}
else
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3657_; 
lean_del_object(v___x_3621_);
lean_dec(v_fvarId_3619_);
lean_dec_ref(v___x_3617_);
lean_del_object(v___x_3615_);
lean_dec_ref(v_alts_3613_);
lean_dec(v_discr_3612_);
lean_dec_ref(v_resultType_3611_);
lean_dec(v_typeName_3610_);
lean_dec_ref_known(v_code_3439_, 1);
v_a_3650_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3652_ = v___x_3624_;
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3624_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
if (v_isShared_3653_ == 0)
{
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
}
}
else
{
lean_object* v___x_3659_; 
lean_dec_ref(v___x_3617_);
lean_del_object(v___x_3615_);
lean_dec_ref(v_alts_3613_);
lean_dec(v_discr_3612_);
lean_dec_ref(v_resultType_3611_);
lean_dec(v_typeName_3610_);
lean_dec_ref_known(v_code_3439_, 1);
v___x_3659_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3437_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
return v___x_3659_;
}
}
}
case 5:
{
lean_object* v_fvarId_3661_; lean_object* v___x_3662_; 
v_fvarId_3661_ = lean_ctor_get(v_code_3439_, 0);
lean_inc(v_fvarId_3661_);
v___x_3662_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3440_, v_fvarId_3661_, v_t_3438_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_fvarId_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3682_; 
v_fvarId_3663_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3665_ = v___x_3662_;
v_isShared_3666_ = v_isSharedCheck_3682_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_fvarId_3663_);
lean_dec(v___x_3662_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3682_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
uint8_t v___x_3667_; 
v___x_3667_ = l_Lean_instBEqFVarId_beq(v_fvarId_3661_, v_fvarId_3663_);
if (v___x_3667_ == 0)
{
lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3677_; 
v_isSharedCheck_3677_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_3677_ == 0)
{
lean_object* v_unused_3678_; 
v_unused_3678_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_3678_);
v___x_3669_ = v_code_3439_;
v_isShared_3670_ = v_isSharedCheck_3677_;
goto v_resetjp_3668_;
}
else
{
lean_dec(v_code_3439_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3677_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v_fvarId_3663_);
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_fvarId_3663_);
v___x_3672_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
lean_object* v___x_3674_; 
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 0, v___x_3672_);
v___x_3674_ = v___x_3665_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3672_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
}
else
{
lean_object* v___x_3680_; 
lean_dec(v_fvarId_3663_);
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 0, v_code_3439_);
v___x_3680_ = v___x_3665_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_code_3439_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
else
{
lean_object* v___x_3683_; 
lean_dec_ref_known(v_code_3439_, 1);
v___x_3683_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3437_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
return v___x_3683_;
}
}
case 6:
{
lean_object* v_type_3684_; lean_object* v___x_3685_; size_t v___x_3686_; size_t v___x_3687_; uint8_t v___x_3688_; 
v_type_3684_ = lean_ctor_get(v_code_3439_, 0);
lean_inc_ref(v_type_3684_);
v___x_3685_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3437_, v_a_3440_, v_t_3438_, v_type_3684_);
v___x_3686_ = lean_ptr_addr(v_type_3684_);
v___x_3687_ = lean_ptr_addr(v___x_3685_);
v___x_3688_ = lean_usize_dec_eq(v___x_3686_, v___x_3687_);
if (v___x_3688_ == 0)
{
lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3696_; 
v_isSharedCheck_3696_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_3696_ == 0)
{
lean_object* v_unused_3697_; 
v_unused_3697_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_3697_);
v___x_3690_ = v_code_3439_;
v_isShared_3691_ = v_isSharedCheck_3696_;
goto v_resetjp_3689_;
}
else
{
lean_dec(v_code_3439_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3696_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
if (v_isShared_3691_ == 0)
{
lean_ctor_set(v___x_3690_, 0, v___x_3685_);
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3685_);
v___x_3693_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
lean_object* v___x_3694_; 
v___x_3694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3693_);
return v___x_3694_;
}
}
}
else
{
lean_object* v___x_3698_; 
lean_dec_ref(v___x_3685_);
v___x_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3698_, 0, v_code_3439_);
return v___x_3698_;
}
}
case 7:
{
lean_object* v_fvarId_3699_; lean_object* v_i_3700_; lean_object* v_y_3701_; lean_object* v_k_3702_; lean_object* v___x_3703_; 
v_fvarId_3699_ = lean_ctor_get(v_code_3439_, 0);
v_i_3700_ = lean_ctor_get(v_code_3439_, 1);
v_y_3701_ = lean_ctor_get(v_code_3439_, 2);
v_k_3702_ = lean_ctor_get(v_code_3439_, 3);
lean_inc(v_fvarId_3699_);
v___x_3703_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3440_, v_fvarId_3699_, v_t_3438_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v_fvarId_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v_fvarId_3704_ = lean_ctor_get(v___x_3703_, 0);
lean_inc(v_fvarId_3704_);
lean_dec_ref_known(v___x_3703_, 1);
lean_inc(v_y_3701_);
v___x_3705_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_3437_, v_a_3440_, v_y_3701_, v_t_3438_);
lean_inc_ref(v_k_3702_);
v___x_3706_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3437_, v_t_3438_, v_k_3702_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3768_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3709_ = v___x_3706_;
v_isShared_3710_ = v_isSharedCheck_3768_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3706_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3768_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
uint8_t v___y_3712_; size_t v___x_3764_; size_t v___x_3765_; uint8_t v___x_3766_; 
v___x_3764_ = lean_ptr_addr(v_fvarId_3699_);
v___x_3765_ = lean_ptr_addr(v_fvarId_3704_);
v___x_3766_ = lean_usize_dec_eq(v___x_3764_, v___x_3765_);
if (v___x_3766_ == 0)
{
v___y_3712_ = v___x_3766_;
goto v___jp_3711_;
}
else
{
uint8_t v___x_3767_; 
v___x_3767_ = lean_nat_dec_eq(v_i_3700_, v_i_3700_);
v___y_3712_ = v___x_3767_;
goto v___jp_3711_;
}
v___jp_3711_:
{
if (v___y_3712_ == 0)
{
lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3722_; 
lean_inc(v_i_3700_);
v_isSharedCheck_3722_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_3722_ == 0)
{
lean_object* v_unused_3723_; lean_object* v_unused_3724_; lean_object* v_unused_3725_; lean_object* v_unused_3726_; 
v_unused_3723_ = lean_ctor_get(v_code_3439_, 3);
lean_dec(v_unused_3723_);
v_unused_3724_ = lean_ctor_get(v_code_3439_, 2);
lean_dec(v_unused_3724_);
v_unused_3725_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_3725_);
v_unused_3726_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_3726_);
v___x_3714_ = v_code_3439_;
v_isShared_3715_ = v_isSharedCheck_3722_;
goto v_resetjp_3713_;
}
else
{
lean_dec(v_code_3439_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3722_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 3, v_a_3707_);
lean_ctor_set(v___x_3714_, 2, v___x_3705_);
lean_ctor_set(v___x_3714_, 0, v_fvarId_3704_);
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_fvarId_3704_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v_i_3700_);
lean_ctor_set(v_reuseFailAlloc_3721_, 2, v___x_3705_);
lean_ctor_set(v_reuseFailAlloc_3721_, 3, v_a_3707_);
v___x_3717_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
lean_object* v___x_3719_; 
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 0, v___x_3717_);
v___x_3719_ = v___x_3709_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v___x_3717_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
}
else
{
size_t v___x_3727_; size_t v___x_3728_; uint8_t v___x_3729_; 
v___x_3727_ = lean_ptr_addr(v_y_3701_);
v___x_3728_ = lean_ptr_addr(v___x_3705_);
v___x_3729_ = lean_usize_dec_eq(v___x_3727_, v___x_3728_);
if (v___x_3729_ == 0)
{
lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3739_; 
lean_inc(v_i_3700_);
v_isSharedCheck_3739_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_3739_ == 0)
{
lean_object* v_unused_3740_; lean_object* v_unused_3741_; lean_object* v_unused_3742_; lean_object* v_unused_3743_; 
v_unused_3740_ = lean_ctor_get(v_code_3439_, 3);
lean_dec(v_unused_3740_);
v_unused_3741_ = lean_ctor_get(v_code_3439_, 2);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_3742_);
v_unused_3743_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_3743_);
v___x_3731_ = v_code_3439_;
v_isShared_3732_ = v_isSharedCheck_3739_;
goto v_resetjp_3730_;
}
else
{
lean_dec(v_code_3439_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3739_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
lean_ctor_set(v___x_3731_, 3, v_a_3707_);
lean_ctor_set(v___x_3731_, 2, v___x_3705_);
lean_ctor_set(v___x_3731_, 0, v_fvarId_3704_);
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_fvarId_3704_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_i_3700_);
lean_ctor_set(v_reuseFailAlloc_3738_, 2, v___x_3705_);
lean_ctor_set(v_reuseFailAlloc_3738_, 3, v_a_3707_);
v___x_3734_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
lean_object* v___x_3736_; 
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 0, v___x_3734_);
v___x_3736_ = v___x_3709_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3734_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
else
{
size_t v___x_3744_; size_t v___x_3745_; uint8_t v___x_3746_; 
v___x_3744_ = lean_ptr_addr(v_k_3702_);
v___x_3745_ = lean_ptr_addr(v_a_3707_);
v___x_3746_ = lean_usize_dec_eq(v___x_3744_, v___x_3745_);
if (v___x_3746_ == 0)
{
lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3756_; 
lean_inc(v_i_3700_);
v_isSharedCheck_3756_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_3756_ == 0)
{
lean_object* v_unused_3757_; lean_object* v_unused_3758_; lean_object* v_unused_3759_; lean_object* v_unused_3760_; 
v_unused_3757_ = lean_ctor_get(v_code_3439_, 3);
lean_dec(v_unused_3757_);
v_unused_3758_ = lean_ctor_get(v_code_3439_, 2);
lean_dec(v_unused_3758_);
v_unused_3759_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_3759_);
v_unused_3760_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_3760_);
v___x_3748_ = v_code_3439_;
v_isShared_3749_ = v_isSharedCheck_3756_;
goto v_resetjp_3747_;
}
else
{
lean_dec(v_code_3439_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3756_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 3, v_a_3707_);
lean_ctor_set(v___x_3748_, 2, v___x_3705_);
lean_ctor_set(v___x_3748_, 0, v_fvarId_3704_);
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_fvarId_3704_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v_i_3700_);
lean_ctor_set(v_reuseFailAlloc_3755_, 2, v___x_3705_);
lean_ctor_set(v_reuseFailAlloc_3755_, 3, v_a_3707_);
v___x_3751_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
lean_object* v___x_3753_; 
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 0, v___x_3751_);
v___x_3753_ = v___x_3709_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v___x_3751_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
else
{
lean_object* v___x_3762_; 
lean_dec(v_a_3707_);
lean_dec(v___x_3705_);
lean_dec(v_fvarId_3704_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 0, v_code_3439_);
v___x_3762_ = v___x_3709_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_code_3439_);
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
}
}
}
else
{
lean_dec(v___x_3705_);
lean_dec(v_fvarId_3704_);
lean_dec_ref_known(v_code_3439_, 4);
return v___x_3706_;
}
}
else
{
lean_object* v___x_3769_; 
lean_dec_ref_known(v_code_3439_, 4);
v___x_3769_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3437_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
return v___x_3769_;
}
}
case 8:
{
lean_object* v_fvarId_3770_; lean_object* v_i_3771_; lean_object* v_y_3772_; lean_object* v_k_3773_; lean_object* v___x_3774_; 
v_fvarId_3770_ = lean_ctor_get(v_code_3439_, 0);
v_i_3771_ = lean_ctor_get(v_code_3439_, 1);
v_y_3772_ = lean_ctor_get(v_code_3439_, 2);
v_k_3773_ = lean_ctor_get(v_code_3439_, 3);
lean_inc(v_fvarId_3770_);
v___x_3774_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3440_, v_fvarId_3770_, v_t_3438_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v_fvarId_3775_; lean_object* v___x_3776_; 
v_fvarId_3775_ = lean_ctor_get(v___x_3774_, 0);
lean_inc(v_fvarId_3775_);
lean_dec_ref_known(v___x_3774_, 1);
lean_inc(v_y_3772_);
v___x_3776_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3440_, v_y_3772_, v_t_3438_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v_fvarId_3777_; lean_object* v___x_3778_; 
v_fvarId_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc(v_fvarId_3777_);
lean_dec_ref_known(v___x_3776_, 1);
lean_inc_ref(v_k_3773_);
v___x_3778_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3437_, v_t_3438_, v_k_3773_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3840_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3781_ = v___x_3778_;
v_isShared_3782_ = v_isSharedCheck_3840_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3778_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3840_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
uint8_t v___y_3784_; size_t v___x_3836_; size_t v___x_3837_; uint8_t v___x_3838_; 
v___x_3836_ = lean_ptr_addr(v_fvarId_3770_);
v___x_3837_ = lean_ptr_addr(v_fvarId_3775_);
v___x_3838_ = lean_usize_dec_eq(v___x_3836_, v___x_3837_);
if (v___x_3838_ == 0)
{
v___y_3784_ = v___x_3838_;
goto v___jp_3783_;
}
else
{
uint8_t v___x_3839_; 
v___x_3839_ = lean_nat_dec_eq(v_i_3771_, v_i_3771_);
v___y_3784_ = v___x_3839_;
goto v___jp_3783_;
}
v___jp_3783_:
{
if (v___y_3784_ == 0)
{
lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3794_; 
lean_inc(v_i_3771_);
v_isSharedCheck_3794_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_3794_ == 0)
{
lean_object* v_unused_3795_; lean_object* v_unused_3796_; lean_object* v_unused_3797_; lean_object* v_unused_3798_; 
v_unused_3795_ = lean_ctor_get(v_code_3439_, 3);
lean_dec(v_unused_3795_);
v_unused_3796_ = lean_ctor_get(v_code_3439_, 2);
lean_dec(v_unused_3796_);
v_unused_3797_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_3797_);
v_unused_3798_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_3798_);
v___x_3786_ = v_code_3439_;
v_isShared_3787_ = v_isSharedCheck_3794_;
goto v_resetjp_3785_;
}
else
{
lean_dec(v_code_3439_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3794_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 3, v_a_3779_);
lean_ctor_set(v___x_3786_, 2, v_fvarId_3777_);
lean_ctor_set(v___x_3786_, 0, v_fvarId_3775_);
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_fvarId_3775_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_i_3771_);
lean_ctor_set(v_reuseFailAlloc_3793_, 2, v_fvarId_3777_);
lean_ctor_set(v_reuseFailAlloc_3793_, 3, v_a_3779_);
v___x_3789_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
lean_object* v___x_3791_; 
if (v_isShared_3782_ == 0)
{
lean_ctor_set(v___x_3781_, 0, v___x_3789_);
v___x_3791_ = v___x_3781_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3789_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
else
{
size_t v___x_3799_; size_t v___x_3800_; uint8_t v___x_3801_; 
v___x_3799_ = lean_ptr_addr(v_y_3772_);
v___x_3800_ = lean_ptr_addr(v_fvarId_3777_);
v___x_3801_ = lean_usize_dec_eq(v___x_3799_, v___x_3800_);
if (v___x_3801_ == 0)
{
lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3811_; 
lean_inc(v_i_3771_);
v_isSharedCheck_3811_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_3811_ == 0)
{
lean_object* v_unused_3812_; lean_object* v_unused_3813_; lean_object* v_unused_3814_; lean_object* v_unused_3815_; 
v_unused_3812_ = lean_ctor_get(v_code_3439_, 3);
lean_dec(v_unused_3812_);
v_unused_3813_ = lean_ctor_get(v_code_3439_, 2);
lean_dec(v_unused_3813_);
v_unused_3814_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_3814_);
v_unused_3815_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_3815_);
v___x_3803_ = v_code_3439_;
v_isShared_3804_ = v_isSharedCheck_3811_;
goto v_resetjp_3802_;
}
else
{
lean_dec(v_code_3439_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3811_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
lean_ctor_set(v___x_3803_, 3, v_a_3779_);
lean_ctor_set(v___x_3803_, 2, v_fvarId_3777_);
lean_ctor_set(v___x_3803_, 0, v_fvarId_3775_);
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_fvarId_3775_);
lean_ctor_set(v_reuseFailAlloc_3810_, 1, v_i_3771_);
lean_ctor_set(v_reuseFailAlloc_3810_, 2, v_fvarId_3777_);
lean_ctor_set(v_reuseFailAlloc_3810_, 3, v_a_3779_);
v___x_3806_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
lean_object* v___x_3808_; 
if (v_isShared_3782_ == 0)
{
lean_ctor_set(v___x_3781_, 0, v___x_3806_);
v___x_3808_ = v___x_3781_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3806_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
else
{
size_t v___x_3816_; size_t v___x_3817_; uint8_t v___x_3818_; 
v___x_3816_ = lean_ptr_addr(v_k_3773_);
v___x_3817_ = lean_ptr_addr(v_a_3779_);
v___x_3818_ = lean_usize_dec_eq(v___x_3816_, v___x_3817_);
if (v___x_3818_ == 0)
{
lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3828_; 
lean_inc(v_i_3771_);
v_isSharedCheck_3828_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_3828_ == 0)
{
lean_object* v_unused_3829_; lean_object* v_unused_3830_; lean_object* v_unused_3831_; lean_object* v_unused_3832_; 
v_unused_3829_ = lean_ctor_get(v_code_3439_, 3);
lean_dec(v_unused_3829_);
v_unused_3830_ = lean_ctor_get(v_code_3439_, 2);
lean_dec(v_unused_3830_);
v_unused_3831_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_3831_);
v_unused_3832_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_3832_);
v___x_3820_ = v_code_3439_;
v_isShared_3821_ = v_isSharedCheck_3828_;
goto v_resetjp_3819_;
}
else
{
lean_dec(v_code_3439_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3828_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 3, v_a_3779_);
lean_ctor_set(v___x_3820_, 2, v_fvarId_3777_);
lean_ctor_set(v___x_3820_, 0, v_fvarId_3775_);
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_fvarId_3775_);
lean_ctor_set(v_reuseFailAlloc_3827_, 1, v_i_3771_);
lean_ctor_set(v_reuseFailAlloc_3827_, 2, v_fvarId_3777_);
lean_ctor_set(v_reuseFailAlloc_3827_, 3, v_a_3779_);
v___x_3823_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
lean_object* v___x_3825_; 
if (v_isShared_3782_ == 0)
{
lean_ctor_set(v___x_3781_, 0, v___x_3823_);
v___x_3825_ = v___x_3781_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3823_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
else
{
lean_object* v___x_3834_; 
lean_dec(v_a_3779_);
lean_dec(v_fvarId_3777_);
lean_dec(v_fvarId_3775_);
if (v_isShared_3782_ == 0)
{
lean_ctor_set(v___x_3781_, 0, v_code_3439_);
v___x_3834_ = v___x_3781_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_code_3439_);
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
}
}
}
else
{
lean_dec(v_fvarId_3777_);
lean_dec(v_fvarId_3775_);
lean_dec_ref_known(v_code_3439_, 4);
return v___x_3778_;
}
}
else
{
lean_object* v___x_3841_; 
lean_dec(v_fvarId_3775_);
lean_dec_ref_known(v_code_3439_, 4);
v___x_3841_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3437_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
return v___x_3841_;
}
}
else
{
lean_object* v___x_3842_; 
lean_dec_ref_known(v_code_3439_, 4);
v___x_3842_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3437_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
return v___x_3842_;
}
}
case 9:
{
lean_object* v_fvarId_3843_; lean_object* v_i_3844_; lean_object* v_offset_3845_; lean_object* v_y_3846_; lean_object* v_ty_3847_; lean_object* v_k_3848_; lean_object* v___x_3849_; 
v_fvarId_3843_ = lean_ctor_get(v_code_3439_, 0);
v_i_3844_ = lean_ctor_get(v_code_3439_, 1);
v_offset_3845_ = lean_ctor_get(v_code_3439_, 2);
v_y_3846_ = lean_ctor_get(v_code_3439_, 3);
v_ty_3847_ = lean_ctor_get(v_code_3439_, 4);
v_k_3848_ = lean_ctor_get(v_code_3439_, 5);
lean_inc(v_fvarId_3843_);
v___x_3849_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3440_, v_fvarId_3843_, v_t_3438_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_fvarId_3850_; lean_object* v___x_3851_; 
v_fvarId_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_fvarId_3850_);
lean_dec_ref_known(v___x_3849_, 1);
lean_inc(v_y_3846_);
v___x_3851_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3440_, v_y_3846_, v_t_3438_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_fvarId_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v_fvarId_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_fvarId_3852_);
lean_dec_ref_known(v___x_3851_, 1);
lean_inc_ref(v_ty_3847_);
v___x_3853_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3437_, v_a_3440_, v_t_3438_, v_ty_3847_);
lean_inc_ref(v_k_3848_);
v___x_3854_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3437_, v_t_3438_, v_k_3848_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3958_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3857_ = v___x_3854_;
v_isShared_3858_ = v_isSharedCheck_3958_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3854_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3958_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
uint8_t v___y_3860_; size_t v___x_3954_; size_t v___x_3955_; uint8_t v___x_3956_; 
v___x_3954_ = lean_ptr_addr(v_fvarId_3843_);
v___x_3955_ = lean_ptr_addr(v_fvarId_3850_);
v___x_3956_ = lean_usize_dec_eq(v___x_3954_, v___x_3955_);
if (v___x_3956_ == 0)
{
v___y_3860_ = v___x_3956_;
goto v___jp_3859_;
}
else
{
uint8_t v___x_3957_; 
v___x_3957_ = lean_nat_dec_eq(v_i_3844_, v_i_3844_);
v___y_3860_ = v___x_3957_;
goto v___jp_3859_;
}
v___jp_3859_:
{
if (v___y_3860_ == 0)
{
lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3870_; 
lean_inc(v_offset_3845_);
lean_inc(v_i_3844_);
v_isSharedCheck_3870_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_3870_ == 0)
{
lean_object* v_unused_3871_; lean_object* v_unused_3872_; lean_object* v_unused_3873_; lean_object* v_unused_3874_; lean_object* v_unused_3875_; lean_object* v_unused_3876_; 
v_unused_3871_ = lean_ctor_get(v_code_3439_, 5);
lean_dec(v_unused_3871_);
v_unused_3872_ = lean_ctor_get(v_code_3439_, 4);
lean_dec(v_unused_3872_);
v_unused_3873_ = lean_ctor_get(v_code_3439_, 3);
lean_dec(v_unused_3873_);
v_unused_3874_ = lean_ctor_get(v_code_3439_, 2);
lean_dec(v_unused_3874_);
v_unused_3875_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_3875_);
v_unused_3876_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_3876_);
v___x_3862_ = v_code_3439_;
v_isShared_3863_ = v_isSharedCheck_3870_;
goto v_resetjp_3861_;
}
else
{
lean_dec(v_code_3439_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3870_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 5, v_a_3855_);
lean_ctor_set(v___x_3862_, 4, v___x_3853_);
lean_ctor_set(v___x_3862_, 3, v_fvarId_3852_);
lean_ctor_set(v___x_3862_, 0, v_fvarId_3850_);
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_fvarId_3850_);
lean_ctor_set(v_reuseFailAlloc_3869_, 1, v_i_3844_);
lean_ctor_set(v_reuseFailAlloc_3869_, 2, v_offset_3845_);
lean_ctor_set(v_reuseFailAlloc_3869_, 3, v_fvarId_3852_);
lean_ctor_set(v_reuseFailAlloc_3869_, 4, v___x_3853_);
lean_ctor_set(v_reuseFailAlloc_3869_, 5, v_a_3855_);
v___x_3865_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
lean_object* v___x_3867_; 
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 0, v___x_3865_);
v___x_3867_ = v___x_3857_;
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
uint8_t v___x_3877_; 
v___x_3877_ = lean_nat_dec_eq(v_offset_3845_, v_offset_3845_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3887_; 
lean_inc(v_offset_3845_);
lean_inc(v_i_3844_);
v_isSharedCheck_3887_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_3887_ == 0)
{
lean_object* v_unused_3888_; lean_object* v_unused_3889_; lean_object* v_unused_3890_; lean_object* v_unused_3891_; lean_object* v_unused_3892_; lean_object* v_unused_3893_; 
v_unused_3888_ = lean_ctor_get(v_code_3439_, 5);
lean_dec(v_unused_3888_);
v_unused_3889_ = lean_ctor_get(v_code_3439_, 4);
lean_dec(v_unused_3889_);
v_unused_3890_ = lean_ctor_get(v_code_3439_, 3);
lean_dec(v_unused_3890_);
v_unused_3891_ = lean_ctor_get(v_code_3439_, 2);
lean_dec(v_unused_3891_);
v_unused_3892_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_3892_);
v_unused_3893_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_3893_);
v___x_3879_ = v_code_3439_;
v_isShared_3880_ = v_isSharedCheck_3887_;
goto v_resetjp_3878_;
}
else
{
lean_dec(v_code_3439_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3887_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 5, v_a_3855_);
lean_ctor_set(v___x_3879_, 4, v___x_3853_);
lean_ctor_set(v___x_3879_, 3, v_fvarId_3852_);
lean_ctor_set(v___x_3879_, 0, v_fvarId_3850_);
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_fvarId_3850_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v_i_3844_);
lean_ctor_set(v_reuseFailAlloc_3886_, 2, v_offset_3845_);
lean_ctor_set(v_reuseFailAlloc_3886_, 3, v_fvarId_3852_);
lean_ctor_set(v_reuseFailAlloc_3886_, 4, v___x_3853_);
lean_ctor_set(v_reuseFailAlloc_3886_, 5, v_a_3855_);
v___x_3882_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
lean_object* v___x_3884_; 
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 0, v___x_3882_);
v___x_3884_ = v___x_3857_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v___x_3882_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
else
{
size_t v___x_3894_; size_t v___x_3895_; uint8_t v___x_3896_; 
v___x_3894_ = lean_ptr_addr(v_y_3846_);
v___x_3895_ = lean_ptr_addr(v_fvarId_3852_);
v___x_3896_ = lean_usize_dec_eq(v___x_3894_, v___x_3895_);
if (v___x_3896_ == 0)
{
lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3906_; 
lean_inc(v_offset_3845_);
lean_inc(v_i_3844_);
v_isSharedCheck_3906_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_3906_ == 0)
{
lean_object* v_unused_3907_; lean_object* v_unused_3908_; lean_object* v_unused_3909_; lean_object* v_unused_3910_; lean_object* v_unused_3911_; lean_object* v_unused_3912_; 
v_unused_3907_ = lean_ctor_get(v_code_3439_, 5);
lean_dec(v_unused_3907_);
v_unused_3908_ = lean_ctor_get(v_code_3439_, 4);
lean_dec(v_unused_3908_);
v_unused_3909_ = lean_ctor_get(v_code_3439_, 3);
lean_dec(v_unused_3909_);
v_unused_3910_ = lean_ctor_get(v_code_3439_, 2);
lean_dec(v_unused_3910_);
v_unused_3911_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_3911_);
v_unused_3912_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_3912_);
v___x_3898_ = v_code_3439_;
v_isShared_3899_ = v_isSharedCheck_3906_;
goto v_resetjp_3897_;
}
else
{
lean_dec(v_code_3439_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3906_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3901_; 
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 5, v_a_3855_);
lean_ctor_set(v___x_3898_, 4, v___x_3853_);
lean_ctor_set(v___x_3898_, 3, v_fvarId_3852_);
lean_ctor_set(v___x_3898_, 0, v_fvarId_3850_);
v___x_3901_ = v___x_3898_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_fvarId_3850_);
lean_ctor_set(v_reuseFailAlloc_3905_, 1, v_i_3844_);
lean_ctor_set(v_reuseFailAlloc_3905_, 2, v_offset_3845_);
lean_ctor_set(v_reuseFailAlloc_3905_, 3, v_fvarId_3852_);
lean_ctor_set(v_reuseFailAlloc_3905_, 4, v___x_3853_);
lean_ctor_set(v_reuseFailAlloc_3905_, 5, v_a_3855_);
v___x_3901_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
lean_object* v___x_3903_; 
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 0, v___x_3901_);
v___x_3903_ = v___x_3857_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3901_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
}
else
{
size_t v___x_3913_; size_t v___x_3914_; uint8_t v___x_3915_; 
v___x_3913_ = lean_ptr_addr(v_ty_3847_);
v___x_3914_ = lean_ptr_addr(v___x_3853_);
v___x_3915_ = lean_usize_dec_eq(v___x_3913_, v___x_3914_);
if (v___x_3915_ == 0)
{
lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3925_; 
lean_inc(v_offset_3845_);
lean_inc(v_i_3844_);
v_isSharedCheck_3925_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_3925_ == 0)
{
lean_object* v_unused_3926_; lean_object* v_unused_3927_; lean_object* v_unused_3928_; lean_object* v_unused_3929_; lean_object* v_unused_3930_; lean_object* v_unused_3931_; 
v_unused_3926_ = lean_ctor_get(v_code_3439_, 5);
lean_dec(v_unused_3926_);
v_unused_3927_ = lean_ctor_get(v_code_3439_, 4);
lean_dec(v_unused_3927_);
v_unused_3928_ = lean_ctor_get(v_code_3439_, 3);
lean_dec(v_unused_3928_);
v_unused_3929_ = lean_ctor_get(v_code_3439_, 2);
lean_dec(v_unused_3929_);
v_unused_3930_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_3930_);
v_unused_3931_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_3931_);
v___x_3917_ = v_code_3439_;
v_isShared_3918_ = v_isSharedCheck_3925_;
goto v_resetjp_3916_;
}
else
{
lean_dec(v_code_3439_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3925_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
lean_ctor_set(v___x_3917_, 5, v_a_3855_);
lean_ctor_set(v___x_3917_, 4, v___x_3853_);
lean_ctor_set(v___x_3917_, 3, v_fvarId_3852_);
lean_ctor_set(v___x_3917_, 0, v_fvarId_3850_);
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_fvarId_3850_);
lean_ctor_set(v_reuseFailAlloc_3924_, 1, v_i_3844_);
lean_ctor_set(v_reuseFailAlloc_3924_, 2, v_offset_3845_);
lean_ctor_set(v_reuseFailAlloc_3924_, 3, v_fvarId_3852_);
lean_ctor_set(v_reuseFailAlloc_3924_, 4, v___x_3853_);
lean_ctor_set(v_reuseFailAlloc_3924_, 5, v_a_3855_);
v___x_3920_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
lean_object* v___x_3922_; 
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 0, v___x_3920_);
v___x_3922_ = v___x_3857_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3920_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
else
{
size_t v___x_3932_; size_t v___x_3933_; uint8_t v___x_3934_; 
v___x_3932_ = lean_ptr_addr(v_k_3848_);
v___x_3933_ = lean_ptr_addr(v_a_3855_);
v___x_3934_ = lean_usize_dec_eq(v___x_3932_, v___x_3933_);
if (v___x_3934_ == 0)
{
lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3944_; 
lean_inc(v_offset_3845_);
lean_inc(v_i_3844_);
v_isSharedCheck_3944_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_3944_ == 0)
{
lean_object* v_unused_3945_; lean_object* v_unused_3946_; lean_object* v_unused_3947_; lean_object* v_unused_3948_; lean_object* v_unused_3949_; lean_object* v_unused_3950_; 
v_unused_3945_ = lean_ctor_get(v_code_3439_, 5);
lean_dec(v_unused_3945_);
v_unused_3946_ = lean_ctor_get(v_code_3439_, 4);
lean_dec(v_unused_3946_);
v_unused_3947_ = lean_ctor_get(v_code_3439_, 3);
lean_dec(v_unused_3947_);
v_unused_3948_ = lean_ctor_get(v_code_3439_, 2);
lean_dec(v_unused_3948_);
v_unused_3949_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_3949_);
v_unused_3950_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_3950_);
v___x_3936_ = v_code_3439_;
v_isShared_3937_ = v_isSharedCheck_3944_;
goto v_resetjp_3935_;
}
else
{
lean_dec(v_code_3439_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3944_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
lean_ctor_set(v___x_3936_, 5, v_a_3855_);
lean_ctor_set(v___x_3936_, 4, v___x_3853_);
lean_ctor_set(v___x_3936_, 3, v_fvarId_3852_);
lean_ctor_set(v___x_3936_, 0, v_fvarId_3850_);
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_fvarId_3850_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v_i_3844_);
lean_ctor_set(v_reuseFailAlloc_3943_, 2, v_offset_3845_);
lean_ctor_set(v_reuseFailAlloc_3943_, 3, v_fvarId_3852_);
lean_ctor_set(v_reuseFailAlloc_3943_, 4, v___x_3853_);
lean_ctor_set(v_reuseFailAlloc_3943_, 5, v_a_3855_);
v___x_3939_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
lean_object* v___x_3941_; 
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 0, v___x_3939_);
v___x_3941_ = v___x_3857_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v___x_3939_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
else
{
lean_object* v___x_3952_; 
lean_dec(v_a_3855_);
lean_dec_ref(v___x_3853_);
lean_dec(v_fvarId_3852_);
lean_dec(v_fvarId_3850_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 0, v_code_3439_);
v___x_3952_ = v___x_3857_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_code_3439_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
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
lean_dec_ref(v___x_3853_);
lean_dec(v_fvarId_3852_);
lean_dec(v_fvarId_3850_);
lean_dec_ref_known(v_code_3439_, 6);
return v___x_3854_;
}
}
else
{
lean_object* v___x_3959_; 
lean_dec(v_fvarId_3850_);
lean_dec_ref_known(v_code_3439_, 6);
v___x_3959_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3437_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
return v___x_3959_;
}
}
else
{
lean_object* v___x_3960_; 
lean_dec_ref_known(v_code_3439_, 6);
v___x_3960_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3437_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
return v___x_3960_;
}
}
case 10:
{
lean_object* v_fvarId_3961_; lean_object* v_cidx_3962_; lean_object* v_k_3963_; lean_object* v___x_3964_; 
v_fvarId_3961_ = lean_ctor_get(v_code_3439_, 0);
v_cidx_3962_ = lean_ctor_get(v_code_3439_, 1);
v_k_3963_ = lean_ctor_get(v_code_3439_, 2);
lean_inc(v_fvarId_3961_);
v___x_3964_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3440_, v_fvarId_3961_, v_t_3438_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_fvarId_3965_; lean_object* v___x_3966_; 
v_fvarId_3965_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_fvarId_3965_);
lean_dec_ref_known(v___x_3964_, 1);
lean_inc_ref(v_k_3963_);
v___x_3966_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3437_, v_t_3438_, v_k_3963_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_4009_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_3969_ = v___x_3966_;
v_isShared_3970_ = v_isSharedCheck_4009_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3966_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_4009_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
uint8_t v___y_3972_; size_t v___x_4005_; size_t v___x_4006_; uint8_t v___x_4007_; 
v___x_4005_ = lean_ptr_addr(v_fvarId_3961_);
v___x_4006_ = lean_ptr_addr(v_fvarId_3965_);
v___x_4007_ = lean_usize_dec_eq(v___x_4005_, v___x_4006_);
if (v___x_4007_ == 0)
{
v___y_3972_ = v___x_4007_;
goto v___jp_3971_;
}
else
{
uint8_t v___x_4008_; 
v___x_4008_ = lean_nat_dec_eq(v_cidx_3962_, v_cidx_3962_);
v___y_3972_ = v___x_4008_;
goto v___jp_3971_;
}
v___jp_3971_:
{
if (v___y_3972_ == 0)
{
lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3982_; 
lean_inc(v_cidx_3962_);
v_isSharedCheck_3982_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_3982_ == 0)
{
lean_object* v_unused_3983_; lean_object* v_unused_3984_; lean_object* v_unused_3985_; 
v_unused_3983_ = lean_ctor_get(v_code_3439_, 2);
lean_dec(v_unused_3983_);
v_unused_3984_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_3984_);
v_unused_3985_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_3985_);
v___x_3974_ = v_code_3439_;
v_isShared_3975_ = v_isSharedCheck_3982_;
goto v_resetjp_3973_;
}
else
{
lean_dec(v_code_3439_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3982_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 2, v_a_3967_);
lean_ctor_set(v___x_3974_, 0, v_fvarId_3965_);
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_fvarId_3965_);
lean_ctor_set(v_reuseFailAlloc_3981_, 1, v_cidx_3962_);
lean_ctor_set(v_reuseFailAlloc_3981_, 2, v_a_3967_);
v___x_3977_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
lean_object* v___x_3979_; 
if (v_isShared_3970_ == 0)
{
lean_ctor_set(v___x_3969_, 0, v___x_3977_);
v___x_3979_ = v___x_3969_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3977_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
}
else
{
size_t v___x_3986_; size_t v___x_3987_; uint8_t v___x_3988_; 
v___x_3986_ = lean_ptr_addr(v_k_3963_);
v___x_3987_ = lean_ptr_addr(v_a_3967_);
v___x_3988_ = lean_usize_dec_eq(v___x_3986_, v___x_3987_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3998_; 
lean_inc(v_cidx_3962_);
v_isSharedCheck_3998_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_3998_ == 0)
{
lean_object* v_unused_3999_; lean_object* v_unused_4000_; lean_object* v_unused_4001_; 
v_unused_3999_ = lean_ctor_get(v_code_3439_, 2);
lean_dec(v_unused_3999_);
v_unused_4000_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_4000_);
v_unused_4001_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_4001_);
v___x_3990_ = v_code_3439_;
v_isShared_3991_ = v_isSharedCheck_3998_;
goto v_resetjp_3989_;
}
else
{
lean_dec(v_code_3439_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3998_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 2, v_a_3967_);
lean_ctor_set(v___x_3990_, 0, v_fvarId_3965_);
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_fvarId_3965_);
lean_ctor_set(v_reuseFailAlloc_3997_, 1, v_cidx_3962_);
lean_ctor_set(v_reuseFailAlloc_3997_, 2, v_a_3967_);
v___x_3993_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
lean_object* v___x_3995_; 
if (v_isShared_3970_ == 0)
{
lean_ctor_set(v___x_3969_, 0, v___x_3993_);
v___x_3995_ = v___x_3969_;
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
lean_object* v___x_4003_; 
lean_dec(v_a_3967_);
lean_dec(v_fvarId_3965_);
if (v_isShared_3970_ == 0)
{
lean_ctor_set(v___x_3969_, 0, v_code_3439_);
v___x_4003_ = v___x_3969_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_code_3439_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_3965_);
lean_dec_ref_known(v_code_3439_, 3);
return v___x_3966_;
}
}
else
{
lean_object* v___x_4010_; 
lean_dec_ref_known(v_code_3439_, 3);
v___x_4010_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3437_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
return v___x_4010_;
}
}
case 11:
{
lean_object* v_fvarId_4011_; lean_object* v_n_4012_; uint8_t v_check_4013_; uint8_t v_persistent_4014_; lean_object* v_k_4015_; lean_object* v___x_4016_; 
v_fvarId_4011_ = lean_ctor_get(v_code_3439_, 0);
v_n_4012_ = lean_ctor_get(v_code_3439_, 1);
v_check_4013_ = lean_ctor_get_uint8(v_code_3439_, sizeof(void*)*3);
v_persistent_4014_ = lean_ctor_get_uint8(v_code_3439_, sizeof(void*)*3 + 1);
v_k_4015_ = lean_ctor_get(v_code_3439_, 2);
lean_inc(v_fvarId_4011_);
v___x_4016_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3440_, v_fvarId_4011_, v_t_3438_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_fvarId_4017_; lean_object* v___x_4018_; 
v_fvarId_4017_ = lean_ctor_get(v___x_4016_, 0);
lean_inc(v_fvarId_4017_);
lean_dec_ref_known(v___x_4016_, 1);
lean_inc_ref(v_k_4015_);
v___x_4018_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3437_, v_t_3438_, v_k_4015_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v_a_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4061_; 
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4021_ = v___x_4018_;
v_isShared_4022_ = v_isSharedCheck_4061_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_a_4019_);
lean_dec(v___x_4018_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4061_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
uint8_t v___y_4024_; size_t v___x_4057_; size_t v___x_4058_; uint8_t v___x_4059_; 
v___x_4057_ = lean_ptr_addr(v_fvarId_4011_);
v___x_4058_ = lean_ptr_addr(v_fvarId_4017_);
v___x_4059_ = lean_usize_dec_eq(v___x_4057_, v___x_4058_);
if (v___x_4059_ == 0)
{
v___y_4024_ = v___x_4059_;
goto v___jp_4023_;
}
else
{
uint8_t v___x_4060_; 
v___x_4060_ = lean_nat_dec_eq(v_n_4012_, v_n_4012_);
v___y_4024_ = v___x_4060_;
goto v___jp_4023_;
}
v___jp_4023_:
{
if (v___y_4024_ == 0)
{
lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4034_; 
lean_inc(v_n_4012_);
v_isSharedCheck_4034_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_4034_ == 0)
{
lean_object* v_unused_4035_; lean_object* v_unused_4036_; lean_object* v_unused_4037_; 
v_unused_4035_ = lean_ctor_get(v_code_3439_, 2);
lean_dec(v_unused_4035_);
v_unused_4036_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_4036_);
v_unused_4037_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_4037_);
v___x_4026_ = v_code_3439_;
v_isShared_4027_ = v_isSharedCheck_4034_;
goto v_resetjp_4025_;
}
else
{
lean_dec(v_code_3439_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4034_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4029_; 
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 2, v_a_4019_);
lean_ctor_set(v___x_4026_, 0, v_fvarId_4017_);
v___x_4029_ = v___x_4026_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_fvarId_4017_);
lean_ctor_set(v_reuseFailAlloc_4033_, 1, v_n_4012_);
lean_ctor_set(v_reuseFailAlloc_4033_, 2, v_a_4019_);
lean_ctor_set_uint8(v_reuseFailAlloc_4033_, sizeof(void*)*3, v_check_4013_);
lean_ctor_set_uint8(v_reuseFailAlloc_4033_, sizeof(void*)*3 + 1, v_persistent_4014_);
v___x_4029_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
lean_object* v___x_4031_; 
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v___x_4029_);
v___x_4031_ = v___x_4021_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v___x_4029_);
v___x_4031_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
return v___x_4031_;
}
}
}
}
else
{
size_t v___x_4038_; size_t v___x_4039_; uint8_t v___x_4040_; 
v___x_4038_ = lean_ptr_addr(v_k_4015_);
v___x_4039_ = lean_ptr_addr(v_a_4019_);
v___x_4040_ = lean_usize_dec_eq(v___x_4038_, v___x_4039_);
if (v___x_4040_ == 0)
{
lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4050_; 
lean_inc(v_n_4012_);
v_isSharedCheck_4050_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_4050_ == 0)
{
lean_object* v_unused_4051_; lean_object* v_unused_4052_; lean_object* v_unused_4053_; 
v_unused_4051_ = lean_ctor_get(v_code_3439_, 2);
lean_dec(v_unused_4051_);
v_unused_4052_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_4052_);
v_unused_4053_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_4053_);
v___x_4042_ = v_code_3439_;
v_isShared_4043_ = v_isSharedCheck_4050_;
goto v_resetjp_4041_;
}
else
{
lean_dec(v_code_3439_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4050_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4045_; 
if (v_isShared_4043_ == 0)
{
lean_ctor_set(v___x_4042_, 2, v_a_4019_);
lean_ctor_set(v___x_4042_, 0, v_fvarId_4017_);
v___x_4045_ = v___x_4042_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_fvarId_4017_);
lean_ctor_set(v_reuseFailAlloc_4049_, 1, v_n_4012_);
lean_ctor_set(v_reuseFailAlloc_4049_, 2, v_a_4019_);
lean_ctor_set_uint8(v_reuseFailAlloc_4049_, sizeof(void*)*3, v_check_4013_);
lean_ctor_set_uint8(v_reuseFailAlloc_4049_, sizeof(void*)*3 + 1, v_persistent_4014_);
v___x_4045_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
lean_object* v___x_4047_; 
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v___x_4045_);
v___x_4047_ = v___x_4021_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v___x_4045_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
else
{
lean_object* v___x_4055_; 
lean_dec(v_a_4019_);
lean_dec(v_fvarId_4017_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v_code_3439_);
v___x_4055_ = v___x_4021_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_code_3439_);
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
}
}
else
{
lean_dec(v_fvarId_4017_);
lean_dec_ref_known(v_code_3439_, 3);
return v___x_4018_;
}
}
else
{
lean_object* v___x_4062_; 
lean_dec_ref_known(v_code_3439_, 3);
v___x_4062_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3437_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
return v___x_4062_;
}
}
case 12:
{
lean_object* v_fvarId_4063_; lean_object* v_n_4064_; uint8_t v_check_4065_; uint8_t v_persistent_4066_; lean_object* v_objs_x3f_4067_; lean_object* v_k_4068_; lean_object* v___x_4069_; 
v_fvarId_4063_ = lean_ctor_get(v_code_3439_, 0);
v_n_4064_ = lean_ctor_get(v_code_3439_, 1);
v_check_4065_ = lean_ctor_get_uint8(v_code_3439_, sizeof(void*)*4);
v_persistent_4066_ = lean_ctor_get_uint8(v_code_3439_, sizeof(void*)*4 + 1);
v_objs_x3f_4067_ = lean_ctor_get(v_code_3439_, 2);
v_k_4068_ = lean_ctor_get(v_code_3439_, 3);
lean_inc(v_fvarId_4063_);
v___x_4069_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3440_, v_fvarId_4063_, v_t_3438_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_fvarId_4070_; lean_object* v___x_4071_; 
v_fvarId_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc(v_fvarId_4070_);
lean_dec_ref_known(v___x_4069_, 1);
lean_inc_ref(v_k_4068_);
v___x_4071_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3437_, v_t_3438_, v_k_4068_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4132_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4074_ = v___x_4071_;
v_isShared_4075_ = v_isSharedCheck_4132_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_a_4072_);
lean_dec(v___x_4071_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4132_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
uint8_t v___y_4077_; size_t v___x_4128_; size_t v___x_4129_; uint8_t v___x_4130_; 
v___x_4128_ = lean_ptr_addr(v_fvarId_4063_);
v___x_4129_ = lean_ptr_addr(v_fvarId_4070_);
v___x_4130_ = lean_usize_dec_eq(v___x_4128_, v___x_4129_);
if (v___x_4130_ == 0)
{
v___y_4077_ = v___x_4130_;
goto v___jp_4076_;
}
else
{
uint8_t v___x_4131_; 
v___x_4131_ = lean_nat_dec_eq(v_n_4064_, v_n_4064_);
v___y_4077_ = v___x_4131_;
goto v___jp_4076_;
}
v___jp_4076_:
{
if (v___y_4077_ == 0)
{
lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4087_; 
lean_inc(v_objs_x3f_4067_);
lean_inc(v_n_4064_);
v_isSharedCheck_4087_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_4087_ == 0)
{
lean_object* v_unused_4088_; lean_object* v_unused_4089_; lean_object* v_unused_4090_; lean_object* v_unused_4091_; 
v_unused_4088_ = lean_ctor_get(v_code_3439_, 3);
lean_dec(v_unused_4088_);
v_unused_4089_ = lean_ctor_get(v_code_3439_, 2);
lean_dec(v_unused_4089_);
v_unused_4090_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_4090_);
v_unused_4091_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_4091_);
v___x_4079_ = v_code_3439_;
v_isShared_4080_ = v_isSharedCheck_4087_;
goto v_resetjp_4078_;
}
else
{
lean_dec(v_code_3439_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4087_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4082_; 
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 3, v_a_4072_);
lean_ctor_set(v___x_4079_, 0, v_fvarId_4070_);
v___x_4082_ = v___x_4079_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_fvarId_4070_);
lean_ctor_set(v_reuseFailAlloc_4086_, 1, v_n_4064_);
lean_ctor_set(v_reuseFailAlloc_4086_, 2, v_objs_x3f_4067_);
lean_ctor_set(v_reuseFailAlloc_4086_, 3, v_a_4072_);
lean_ctor_set_uint8(v_reuseFailAlloc_4086_, sizeof(void*)*4, v_check_4065_);
lean_ctor_set_uint8(v_reuseFailAlloc_4086_, sizeof(void*)*4 + 1, v_persistent_4066_);
v___x_4082_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
lean_object* v___x_4084_; 
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 0, v___x_4082_);
v___x_4084_ = v___x_4074_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v___x_4082_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
else
{
size_t v___x_4092_; uint8_t v___x_4093_; 
v___x_4092_ = lean_ptr_addr(v_objs_x3f_4067_);
v___x_4093_ = lean_usize_dec_eq(v___x_4092_, v___x_4092_);
if (v___x_4093_ == 0)
{
lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4103_; 
lean_inc(v_objs_x3f_4067_);
lean_inc(v_n_4064_);
v_isSharedCheck_4103_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_4103_ == 0)
{
lean_object* v_unused_4104_; lean_object* v_unused_4105_; lean_object* v_unused_4106_; lean_object* v_unused_4107_; 
v_unused_4104_ = lean_ctor_get(v_code_3439_, 3);
lean_dec(v_unused_4104_);
v_unused_4105_ = lean_ctor_get(v_code_3439_, 2);
lean_dec(v_unused_4105_);
v_unused_4106_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_4106_);
v_unused_4107_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_4107_);
v___x_4095_ = v_code_3439_;
v_isShared_4096_ = v_isSharedCheck_4103_;
goto v_resetjp_4094_;
}
else
{
lean_dec(v_code_3439_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4103_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4098_; 
if (v_isShared_4096_ == 0)
{
lean_ctor_set(v___x_4095_, 3, v_a_4072_);
lean_ctor_set(v___x_4095_, 0, v_fvarId_4070_);
v___x_4098_ = v___x_4095_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_fvarId_4070_);
lean_ctor_set(v_reuseFailAlloc_4102_, 1, v_n_4064_);
lean_ctor_set(v_reuseFailAlloc_4102_, 2, v_objs_x3f_4067_);
lean_ctor_set(v_reuseFailAlloc_4102_, 3, v_a_4072_);
lean_ctor_set_uint8(v_reuseFailAlloc_4102_, sizeof(void*)*4, v_check_4065_);
lean_ctor_set_uint8(v_reuseFailAlloc_4102_, sizeof(void*)*4 + 1, v_persistent_4066_);
v___x_4098_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
lean_object* v___x_4100_; 
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 0, v___x_4098_);
v___x_4100_ = v___x_4074_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v___x_4098_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
}
}
else
{
size_t v___x_4108_; size_t v___x_4109_; uint8_t v___x_4110_; 
v___x_4108_ = lean_ptr_addr(v_k_4068_);
v___x_4109_ = lean_ptr_addr(v_a_4072_);
v___x_4110_ = lean_usize_dec_eq(v___x_4108_, v___x_4109_);
if (v___x_4110_ == 0)
{
lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4120_; 
lean_inc(v_objs_x3f_4067_);
lean_inc(v_n_4064_);
v_isSharedCheck_4120_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_4120_ == 0)
{
lean_object* v_unused_4121_; lean_object* v_unused_4122_; lean_object* v_unused_4123_; lean_object* v_unused_4124_; 
v_unused_4121_ = lean_ctor_get(v_code_3439_, 3);
lean_dec(v_unused_4121_);
v_unused_4122_ = lean_ctor_get(v_code_3439_, 2);
lean_dec(v_unused_4122_);
v_unused_4123_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_4123_);
v_unused_4124_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_4124_);
v___x_4112_ = v_code_3439_;
v_isShared_4113_ = v_isSharedCheck_4120_;
goto v_resetjp_4111_;
}
else
{
lean_dec(v_code_3439_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4120_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4115_; 
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 3, v_a_4072_);
lean_ctor_set(v___x_4112_, 0, v_fvarId_4070_);
v___x_4115_ = v___x_4112_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_fvarId_4070_);
lean_ctor_set(v_reuseFailAlloc_4119_, 1, v_n_4064_);
lean_ctor_set(v_reuseFailAlloc_4119_, 2, v_objs_x3f_4067_);
lean_ctor_set(v_reuseFailAlloc_4119_, 3, v_a_4072_);
lean_ctor_set_uint8(v_reuseFailAlloc_4119_, sizeof(void*)*4, v_check_4065_);
lean_ctor_set_uint8(v_reuseFailAlloc_4119_, sizeof(void*)*4 + 1, v_persistent_4066_);
v___x_4115_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
lean_object* v___x_4117_; 
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 0, v___x_4115_);
v___x_4117_ = v___x_4074_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___x_4115_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
}
}
else
{
lean_object* v___x_4126_; 
lean_dec(v_a_4072_);
lean_dec(v_fvarId_4070_);
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 0, v_code_3439_);
v___x_4126_ = v___x_4074_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_code_3439_);
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
}
}
}
else
{
lean_dec(v_fvarId_4070_);
lean_dec_ref_known(v_code_3439_, 4);
return v___x_4071_;
}
}
else
{
lean_object* v___x_4133_; 
lean_dec_ref_known(v_code_3439_, 4);
v___x_4133_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3437_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
return v___x_4133_;
}
}
default: 
{
lean_object* v_fvarId_4134_; lean_object* v_k_4135_; lean_object* v___x_4136_; 
v_fvarId_4134_ = lean_ctor_get(v_code_3439_, 0);
v_k_4135_ = lean_ctor_get(v_code_3439_, 1);
lean_inc(v_fvarId_4134_);
v___x_4136_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3440_, v_fvarId_4134_, v_t_3438_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_object* v_fvarId_4137_; lean_object* v___x_4138_; 
v_fvarId_4137_ = lean_ctor_get(v___x_4136_, 0);
lean_inc(v_fvarId_4137_);
lean_dec_ref_known(v___x_4136_, 1);
lean_inc_ref(v_k_4135_);
v___x_4138_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3437_, v_t_3438_, v_k_4135_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4166_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4141_ = v___x_4138_;
v_isShared_4142_ = v_isSharedCheck_4166_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4138_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4166_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
uint8_t v___y_4144_; size_t v___x_4160_; size_t v___x_4161_; uint8_t v___x_4162_; 
v___x_4160_ = lean_ptr_addr(v_fvarId_4134_);
v___x_4161_ = lean_ptr_addr(v_fvarId_4137_);
v___x_4162_ = lean_usize_dec_eq(v___x_4160_, v___x_4161_);
if (v___x_4162_ == 0)
{
v___y_4144_ = v___x_4162_;
goto v___jp_4143_;
}
else
{
size_t v___x_4163_; size_t v___x_4164_; uint8_t v___x_4165_; 
v___x_4163_ = lean_ptr_addr(v_k_4135_);
v___x_4164_ = lean_ptr_addr(v_a_4139_);
v___x_4165_ = lean_usize_dec_eq(v___x_4163_, v___x_4164_);
v___y_4144_ = v___x_4165_;
goto v___jp_4143_;
}
v___jp_4143_:
{
if (v___y_4144_ == 0)
{
lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4154_; 
v_isSharedCheck_4154_ = !lean_is_exclusive(v_code_3439_);
if (v_isSharedCheck_4154_ == 0)
{
lean_object* v_unused_4155_; lean_object* v_unused_4156_; 
v_unused_4155_ = lean_ctor_get(v_code_3439_, 1);
lean_dec(v_unused_4155_);
v_unused_4156_ = lean_ctor_get(v_code_3439_, 0);
lean_dec(v_unused_4156_);
v___x_4146_ = v_code_3439_;
v_isShared_4147_ = v_isSharedCheck_4154_;
goto v_resetjp_4145_;
}
else
{
lean_dec(v_code_3439_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4154_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 1, v_a_4139_);
lean_ctor_set(v___x_4146_, 0, v_fvarId_4137_);
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_fvarId_4137_);
lean_ctor_set(v_reuseFailAlloc_4153_, 1, v_a_4139_);
v___x_4149_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
lean_object* v___x_4151_; 
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 0, v___x_4149_);
v___x_4151_ = v___x_4141_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v___x_4149_);
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
else
{
lean_object* v___x_4158_; 
lean_dec(v_a_4139_);
lean_dec(v_fvarId_4137_);
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 0, v_code_3439_);
v___x_4158_ = v___x_4141_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_code_3439_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_4137_);
lean_dec_ref_known(v_code_3439_, 2);
return v___x_4138_;
}
}
else
{
lean_object* v___x_4167_; 
lean_dec_ref_known(v_code_3439_, 2);
v___x_4167_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3437_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
return v___x_4167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t v_pu_4168_, uint8_t v_t_4169_, lean_object* v_decl_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_){
_start:
{
lean_object* v_params_4177_; lean_object* v_type_4178_; lean_object* v_value_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
v_params_4177_ = lean_ctor_get(v_decl_4170_, 2);
v_type_4178_ = lean_ctor_get(v_decl_4170_, 3);
v_value_4179_ = lean_ctor_get(v_decl_4170_, 4);
lean_inc_ref(v_type_4178_);
v___x_4180_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4168_, v_a_4171_, v_t_4169_, v_type_4178_);
lean_inc_ref(v_params_4177_);
v___x_4181_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4168_, v_t_4169_, v_params_4177_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_);
if (lean_obj_tag(v___x_4181_) == 0)
{
lean_object* v_a_4182_; lean_object* v___x_4183_; 
v_a_4182_ = lean_ctor_get(v___x_4181_, 0);
lean_inc(v_a_4182_);
lean_dec_ref_known(v___x_4181_, 1);
lean_inc_ref(v_value_4179_);
v___x_4183_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4168_, v_t_4169_, v_value_4179_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; lean_object* v___x_4185_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4184_);
lean_dec_ref_known(v___x_4183_, 1);
v___x_4185_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_4168_, v_decl_4170_, v___x_4180_, v_a_4182_, v_a_4184_, v_a_4173_);
return v___x_4185_;
}
else
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4193_; 
lean_dec(v_a_4182_);
lean_dec_ref(v___x_4180_);
lean_dec_ref(v_decl_4170_);
v_a_4186_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4193_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4188_ = v___x_4183_;
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_4183_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
if (v_isShared_4189_ == 0)
{
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_a_4186_);
v___x_4191_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
return v___x_4191_;
}
}
}
}
else
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
lean_dec_ref(v___x_4180_);
lean_dec_ref(v_decl_4170_);
v_a_4194_ = lean_ctor_get(v___x_4181_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4196_ = v___x_4181_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4181_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4199_; 
if (v_isShared_4197_ == 0)
{
v___x_4199_ = v___x_4196_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_a_4194_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp___boxed(lean_object* v_pu_4202_, lean_object* v_t_4203_, lean_object* v_decl_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_){
_start:
{
uint8_t v_pu_boxed_4211_; uint8_t v_t_boxed_4212_; lean_object* v_res_4213_; 
v_pu_boxed_4211_ = lean_unbox(v_pu_4202_);
v_t_boxed_4212_ = lean_unbox(v_t_4203_);
v_res_4213_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_boxed_4211_, v_t_boxed_4212_, v_decl_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_);
lean_dec(v_a_4209_);
lean_dec_ref(v_a_4208_);
lean_dec(v_a_4207_);
lean_dec_ref(v_a_4206_);
lean_dec_ref(v_a_4205_);
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4___boxed(lean_object* v_pu_4214_, lean_object* v_t_4215_, lean_object* v_i_4216_, lean_object* v_as_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
uint8_t v_pu_boxed_4224_; uint8_t v_t_boxed_4225_; lean_object* v_res_4226_; 
v_pu_boxed_4224_ = lean_unbox(v_pu_4214_);
v_t_boxed_4225_ = lean_unbox(v_t_4215_);
v_res_4226_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_boxed_4224_, v_t_boxed_4225_, v_i_4216_, v_as_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec_ref(v___y_4218_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp___boxed(lean_object* v_pu_4227_, lean_object* v_t_4228_, lean_object* v_code_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_){
_start:
{
uint8_t v_pu_boxed_4236_; uint8_t v_t_boxed_4237_; lean_object* v_res_4238_; 
v_pu_boxed_4236_ = lean_unbox(v_pu_4227_);
v_t_boxed_4237_ = lean_unbox(v_t_4228_);
v_res_4238_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_boxed_4236_, v_t_boxed_4237_, v_code_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_);
lean_dec(v_a_4234_);
lean_dec_ref(v_a_4233_);
lean_dec(v_a_4232_);
lean_dec_ref(v_a_4231_);
lean_dec_ref(v_a_4230_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(uint8_t v_pu_4239_, uint8_t v_t_4240_, uint8_t v_pu_4241_, uint8_t v_t_4242_, lean_object* v_decl_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_4241_, v_t_4242_, v_decl_4243_, v___y_4244_, v___y_4246_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___boxed(lean_object* v_pu_4251_, lean_object* v_t_4252_, lean_object* v_pu_4253_, lean_object* v_t_4254_, lean_object* v_decl_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_){
_start:
{
uint8_t v_pu_boxed_4262_; uint8_t v_t_boxed_4263_; uint8_t v_pu_boxed_4264_; uint8_t v_t_boxed_4265_; lean_object* v_res_4266_; 
v_pu_boxed_4262_ = lean_unbox(v_pu_4251_);
v_t_boxed_4263_ = lean_unbox(v_t_4252_);
v_pu_boxed_4264_ = lean_unbox(v_pu_4253_);
v_t_boxed_4265_ = lean_unbox(v_t_4254_);
v_res_4266_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(v_pu_boxed_4262_, v_t_boxed_4263_, v_pu_boxed_4264_, v_t_boxed_4265_, v_decl_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec_ref(v___y_4256_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(uint8_t v_pu_4267_, uint8_t v_t_4268_, uint8_t v_pu_4269_, uint8_t v_t_4270_, lean_object* v_args_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
lean_object* v___x_4278_; 
v___x_4278_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_4269_, v_t_4270_, v_args_4271_, v___y_4272_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___boxed(lean_object* v_pu_4279_, lean_object* v_t_4280_, lean_object* v_pu_4281_, lean_object* v_t_4282_, lean_object* v_args_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
uint8_t v_pu_boxed_4290_; uint8_t v_t_boxed_4291_; uint8_t v_pu_boxed_4292_; uint8_t v_t_boxed_4293_; lean_object* v_res_4294_; 
v_pu_boxed_4290_ = lean_unbox(v_pu_4279_);
v_t_boxed_4291_ = lean_unbox(v_t_4280_);
v_pu_boxed_4292_ = lean_unbox(v_pu_4281_);
v_t_boxed_4293_ = lean_unbox(v_t_4282_);
v_res_4294_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(v_pu_boxed_4290_, v_t_boxed_4291_, v_pu_boxed_4292_, v_t_boxed_4293_, v_args_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
lean_dec_ref(v___y_4284_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(uint8_t v_pu_4295_, uint8_t v_t_4296_, uint8_t v_pu_4297_, uint8_t v_t_4298_, lean_object* v_ps_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v___x_4306_; 
v___x_4306_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4297_, v_t_4298_, v_ps_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___boxed(lean_object* v_pu_4307_, lean_object* v_t_4308_, lean_object* v_pu_4309_, lean_object* v_t_4310_, lean_object* v_ps_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_){
_start:
{
uint8_t v_pu_boxed_4318_; uint8_t v_t_boxed_4319_; uint8_t v_pu_boxed_4320_; uint8_t v_t_boxed_4321_; lean_object* v_res_4322_; 
v_pu_boxed_4318_ = lean_unbox(v_pu_4307_);
v_t_boxed_4319_ = lean_unbox(v_t_4308_);
v_pu_boxed_4320_ = lean_unbox(v_pu_4309_);
v_t_boxed_4321_ = lean_unbox(v_t_4310_);
v_res_4322_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(v_pu_boxed_4318_, v_t_boxed_4319_, v_pu_boxed_4320_, v_t_boxed_4321_, v_ps_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
lean_dec_ref(v___y_4312_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(uint8_t v_pu_4323_, uint8_t v_t_4324_, lean_object* v_i_4325_, lean_object* v_as_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_){
_start:
{
lean_object* v___x_4333_; 
v___x_4333_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_4323_, v_t_4324_, v_i_4325_, v_as_4326_, v___y_4327_, v___y_4329_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___boxed(lean_object* v_pu_4334_, lean_object* v_t_4335_, lean_object* v_i_4336_, lean_object* v_as_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_){
_start:
{
uint8_t v_pu_boxed_4344_; uint8_t v_t_boxed_4345_; lean_object* v_res_4346_; 
v_pu_boxed_4344_ = lean_unbox(v_pu_4334_);
v_t_boxed_4345_ = lean_unbox(v_t_4335_);
v_res_4346_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(v_pu_boxed_4344_, v_t_boxed_4345_, v_i_4336_, v_as_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec_ref(v___y_4338_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(uint8_t v_pu_4347_, uint8_t v_t_4348_, lean_object* v_decl_4349_, lean_object* v_inst_4350_, lean_object* v_____do__lift_4351_){
_start:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v___x_4352_ = lean_box(v_pu_4347_);
v___x_4353_ = lean_box(v_t_4348_);
v___x_4354_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDeclImp___boxed), 9, 4);
lean_closure_set(v___x_4354_, 0, v___x_4352_);
lean_closure_set(v___x_4354_, 1, v___x_4353_);
lean_closure_set(v___x_4354_, 2, v_decl_4349_);
lean_closure_set(v___x_4354_, 3, v_____do__lift_4351_);
v___x_4355_ = lean_apply_2(v_inst_4350_, lean_box(0), v___x_4354_);
return v___x_4355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed(lean_object* v_pu_4356_, lean_object* v_t_4357_, lean_object* v_decl_4358_, lean_object* v_inst_4359_, lean_object* v_____do__lift_4360_){
_start:
{
uint8_t v_pu_boxed_4361_; uint8_t v_t_boxed_4362_; lean_object* v_res_4363_; 
v_pu_boxed_4361_ = lean_unbox(v_pu_4356_);
v_t_boxed_4362_ = lean_unbox(v_t_4357_);
v_res_4363_ = l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(v_pu_boxed_4361_, v_t_boxed_4362_, v_decl_4358_, v_inst_4359_, v_____do__lift_4360_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg(uint8_t v_pu_4364_, uint8_t v_t_4365_, lean_object* v_inst_4366_, lean_object* v_inst_4367_, lean_object* v_inst_4368_, lean_object* v_decl_4369_){
_start:
{
lean_object* v_toBind_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___f_4373_; lean_object* v___x_4374_; 
v_toBind_4370_ = lean_ctor_get(v_inst_4367_, 1);
lean_inc(v_toBind_4370_);
lean_dec_ref(v_inst_4367_);
v___x_4371_ = lean_box(v_pu_4364_);
v___x_4372_ = lean_box(v_t_4365_);
v___f_4373_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4373_, 0, v___x_4371_);
lean_closure_set(v___f_4373_, 1, v___x_4372_);
lean_closure_set(v___f_4373_, 2, v_decl_4369_);
lean_closure_set(v___f_4373_, 3, v_inst_4366_);
v___x_4374_ = lean_apply_4(v_toBind_4370_, lean_box(0), lean_box(0), v_inst_4368_, v___f_4373_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___boxed(lean_object* v_pu_4375_, lean_object* v_t_4376_, lean_object* v_inst_4377_, lean_object* v_inst_4378_, lean_object* v_inst_4379_, lean_object* v_decl_4380_){
_start:
{
uint8_t v_pu_boxed_4381_; uint8_t v_t_boxed_4382_; lean_object* v_res_4383_; 
v_pu_boxed_4381_ = lean_unbox(v_pu_4375_);
v_t_boxed_4382_ = lean_unbox(v_t_4376_);
v_res_4383_ = l_Lean_Compiler_LCNF_normFunDecl___redArg(v_pu_boxed_4381_, v_t_boxed_4382_, v_inst_4377_, v_inst_4378_, v_inst_4379_, v_decl_4380_);
return v_res_4383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl(lean_object* v_m_4384_, uint8_t v_pu_4385_, uint8_t v_t_4386_, lean_object* v_inst_4387_, lean_object* v_inst_4388_, lean_object* v_inst_4389_, lean_object* v_decl_4390_){
_start:
{
lean_object* v_toBind_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___f_4394_; lean_object* v___x_4395_; 
v_toBind_4391_ = lean_ctor_get(v_inst_4388_, 1);
lean_inc(v_toBind_4391_);
lean_dec_ref(v_inst_4388_);
v___x_4392_ = lean_box(v_pu_4385_);
v___x_4393_ = lean_box(v_t_4386_);
v___f_4394_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4394_, 0, v___x_4392_);
lean_closure_set(v___f_4394_, 1, v___x_4393_);
lean_closure_set(v___f_4394_, 2, v_decl_4390_);
lean_closure_set(v___f_4394_, 3, v_inst_4387_);
v___x_4395_ = lean_apply_4(v_toBind_4391_, lean_box(0), lean_box(0), v_inst_4389_, v___f_4394_);
return v___x_4395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___boxed(lean_object* v_m_4396_, lean_object* v_pu_4397_, lean_object* v_t_4398_, lean_object* v_inst_4399_, lean_object* v_inst_4400_, lean_object* v_inst_4401_, lean_object* v_decl_4402_){
_start:
{
uint8_t v_pu_boxed_4403_; uint8_t v_t_boxed_4404_; lean_object* v_res_4405_; 
v_pu_boxed_4403_ = lean_unbox(v_pu_4397_);
v_t_boxed_4404_ = lean_unbox(v_t_4398_);
v_res_4405_ = l_Lean_Compiler_LCNF_normFunDecl(v_m_4396_, v_pu_boxed_4403_, v_t_boxed_4404_, v_inst_4399_, v_inst_4400_, v_inst_4401_, v_decl_4402_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0(uint8_t v_pu_4406_, uint8_t v_t_4407_, lean_object* v_code_4408_, lean_object* v_inst_4409_, lean_object* v_____do__lift_4410_){
_start:
{
lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4411_ = lean_box(v_pu_4406_);
v___x_4412_ = lean_box(v_t_4407_);
v___x_4413_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCodeImp___boxed), 9, 4);
lean_closure_set(v___x_4413_, 0, v___x_4411_);
lean_closure_set(v___x_4413_, 1, v___x_4412_);
lean_closure_set(v___x_4413_, 2, v_code_4408_);
lean_closure_set(v___x_4413_, 3, v_____do__lift_4410_);
v___x_4414_ = lean_apply_2(v_inst_4409_, lean_box(0), v___x_4413_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed(lean_object* v_pu_4415_, lean_object* v_t_4416_, lean_object* v_code_4417_, lean_object* v_inst_4418_, lean_object* v_____do__lift_4419_){
_start:
{
uint8_t v_pu_boxed_4420_; uint8_t v_t_boxed_4421_; lean_object* v_res_4422_; 
v_pu_boxed_4420_ = lean_unbox(v_pu_4415_);
v_t_boxed_4421_ = lean_unbox(v_t_4416_);
v_res_4422_ = l_Lean_Compiler_LCNF_normCode___redArg___lam__0(v_pu_boxed_4420_, v_t_boxed_4421_, v_code_4417_, v_inst_4418_, v_____do__lift_4419_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg(uint8_t v_pu_4423_, uint8_t v_t_4424_, lean_object* v_inst_4425_, lean_object* v_inst_4426_, lean_object* v_inst_4427_, lean_object* v_code_4428_){
_start:
{
lean_object* v_toBind_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___f_4432_; lean_object* v___x_4433_; 
v_toBind_4429_ = lean_ctor_get(v_inst_4426_, 1);
lean_inc(v_toBind_4429_);
lean_dec_ref(v_inst_4426_);
v___x_4430_ = lean_box(v_pu_4423_);
v___x_4431_ = lean_box(v_t_4424_);
v___f_4432_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4432_, 0, v___x_4430_);
lean_closure_set(v___f_4432_, 1, v___x_4431_);
lean_closure_set(v___f_4432_, 2, v_code_4428_);
lean_closure_set(v___f_4432_, 3, v_inst_4425_);
v___x_4433_ = lean_apply_4(v_toBind_4429_, lean_box(0), lean_box(0), v_inst_4427_, v___f_4432_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___boxed(lean_object* v_pu_4434_, lean_object* v_t_4435_, lean_object* v_inst_4436_, lean_object* v_inst_4437_, lean_object* v_inst_4438_, lean_object* v_code_4439_){
_start:
{
uint8_t v_pu_boxed_4440_; uint8_t v_t_boxed_4441_; lean_object* v_res_4442_; 
v_pu_boxed_4440_ = lean_unbox(v_pu_4434_);
v_t_boxed_4441_ = lean_unbox(v_t_4435_);
v_res_4442_ = l_Lean_Compiler_LCNF_normCode___redArg(v_pu_boxed_4440_, v_t_boxed_4441_, v_inst_4436_, v_inst_4437_, v_inst_4438_, v_code_4439_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode(lean_object* v_m_4443_, uint8_t v_pu_4444_, uint8_t v_t_4445_, lean_object* v_inst_4446_, lean_object* v_inst_4447_, lean_object* v_inst_4448_, lean_object* v_code_4449_){
_start:
{
lean_object* v_toBind_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___f_4453_; lean_object* v___x_4454_; 
v_toBind_4450_ = lean_ctor_get(v_inst_4447_, 1);
lean_inc(v_toBind_4450_);
lean_dec_ref(v_inst_4447_);
v___x_4451_ = lean_box(v_pu_4444_);
v___x_4452_ = lean_box(v_t_4445_);
v___f_4453_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4453_, 0, v___x_4451_);
lean_closure_set(v___f_4453_, 1, v___x_4452_);
lean_closure_set(v___f_4453_, 2, v_code_4449_);
lean_closure_set(v___f_4453_, 3, v_inst_4446_);
v___x_4454_ = lean_apply_4(v_toBind_4450_, lean_box(0), lean_box(0), v_inst_4448_, v___f_4453_);
return v___x_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___boxed(lean_object* v_m_4455_, lean_object* v_pu_4456_, lean_object* v_t_4457_, lean_object* v_inst_4458_, lean_object* v_inst_4459_, lean_object* v_inst_4460_, lean_object* v_code_4461_){
_start:
{
uint8_t v_pu_boxed_4462_; uint8_t v_t_boxed_4463_; lean_object* v_res_4464_; 
v_pu_boxed_4462_ = lean_unbox(v_pu_4456_);
v_t_boxed_4463_ = lean_unbox(v_t_4457_);
v_res_4464_ = l_Lean_Compiler_LCNF_normCode(v_m_4455_, v_pu_boxed_4462_, v_t_boxed_4463_, v_inst_4458_, v_inst_4459_, v_inst_4460_, v_code_4461_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t v_pu_4465_, lean_object* v_e_4466_, lean_object* v_s_4467_, uint8_t v_translator_4468_){
_start:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4470_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4465_, v_s_4467_, v_translator_4468_, v_e_4466_);
v___x_4471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4470_);
return v___x_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg___boxed(lean_object* v_pu_4472_, lean_object* v_e_4473_, lean_object* v_s_4474_, lean_object* v_translator_4475_, lean_object* v_a_4476_){
_start:
{
uint8_t v_pu_boxed_4477_; uint8_t v_translator_boxed_4478_; lean_object* v_res_4479_; 
v_pu_boxed_4477_ = lean_unbox(v_pu_4472_);
v_translator_boxed_4478_ = lean_unbox(v_translator_4475_);
v_res_4479_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_boxed_4477_, v_e_4473_, v_s_4474_, v_translator_boxed_4478_);
lean_dec_ref(v_s_4474_);
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(uint8_t v_pu_4480_, lean_object* v_e_4481_, lean_object* v_s_4482_, uint8_t v_translator_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_){
_start:
{
lean_object* v___x_4489_; 
v___x_4489_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_4480_, v_e_4481_, v_s_4482_, v_translator_4483_);
return v___x_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___boxed(lean_object* v_pu_4490_, lean_object* v_e_4491_, lean_object* v_s_4492_, lean_object* v_translator_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_){
_start:
{
uint8_t v_pu_boxed_4499_; uint8_t v_translator_boxed_4500_; lean_object* v_res_4501_; 
v_pu_boxed_4499_ = lean_unbox(v_pu_4490_);
v_translator_boxed_4500_ = lean_unbox(v_translator_4493_);
v_res_4501_ = l_Lean_Compiler_LCNF_replaceExprFVars(v_pu_boxed_4499_, v_e_4491_, v_s_4492_, v_translator_boxed_4500_, v_a_4494_, v_a_4495_, v_a_4496_, v_a_4497_);
lean_dec(v_a_4497_);
lean_dec_ref(v_a_4496_);
lean_dec(v_a_4495_);
lean_dec_ref(v_a_4494_);
lean_dec_ref(v_s_4492_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t v_pu_4502_, lean_object* v_code_4503_, lean_object* v_s_4504_, uint8_t v_translator_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_){
_start:
{
lean_object* v___x_4511_; 
v___x_4511_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4502_, v_translator_4505_, v_code_4503_, v_s_4504_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_);
return v___x_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars___boxed(lean_object* v_pu_4512_, lean_object* v_code_4513_, lean_object* v_s_4514_, lean_object* v_translator_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_){
_start:
{
uint8_t v_pu_boxed_4521_; uint8_t v_translator_boxed_4522_; lean_object* v_res_4523_; 
v_pu_boxed_4521_ = lean_unbox(v_pu_4512_);
v_translator_boxed_4522_ = lean_unbox(v_translator_4515_);
v_res_4523_ = l_Lean_Compiler_LCNF_replaceFVars(v_pu_boxed_4521_, v_code_4513_, v_s_4514_, v_translator_boxed_4522_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_);
lean_dec(v_a_4519_);
lean_dec_ref(v_a_4518_);
lean_dec(v_a_4517_);
lean_dec_ref(v_a_4516_);
lean_dec_ref(v_s_4514_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg(lean_object* v_a_4527_){
_start:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4529_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1));
v___x_4530_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4529_, v_a_4527_);
return v___x_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___boxed(lean_object* v_a_4531_, lean_object* v_a_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4531_);
lean_dec(v_a_4531_);
return v_res_4533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName(lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_){
_start:
{
lean_object* v___x_4539_; 
v___x_4539_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4535_);
return v___x_4539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___boxed(lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l_Lean_Compiler_LCNF_mkFreshJpName(v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
lean_dec(v_a_4543_);
lean_dec_ref(v_a_4542_);
lean_dec(v_a_4541_);
lean_dec_ref(v_a_4540_);
return v_res_4545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t v_pu_4546_, lean_object* v_type_4547_, uint8_t v_borrow_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_){
_start:
{
lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v_a_4556_; lean_object* v___x_4557_; 
v___x_4554_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_4555_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4554_, v_a_4550_);
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
lean_inc(v_a_4556_);
lean_dec_ref(v___x_4555_);
v___x_4557_ = l_Lean_Compiler_LCNF_mkParam(v_pu_4546_, v_a_4556_, v_type_4547_, v_borrow_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_);
return v___x_4557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam___boxed(lean_object* v_pu_4558_, lean_object* v_type_4559_, lean_object* v_borrow_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_){
_start:
{
uint8_t v_pu_boxed_4566_; uint8_t v_borrow_boxed_4567_; lean_object* v_res_4568_; 
v_pu_boxed_4566_ = lean_unbox(v_pu_4558_);
v_borrow_boxed_4567_ = lean_unbox(v_borrow_4560_);
v_res_4568_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_boxed_4566_, v_type_4559_, v_borrow_boxed_4567_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_);
lean_dec(v_a_4564_);
lean_dec_ref(v_a_4563_);
lean_dec(v_a_4562_);
lean_dec_ref(v_a_4561_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object* v_a_4569_){
_start:
{
lean_object* v_config_4571_; lean_object* v___x_4572_; 
v_config_4571_ = lean_ctor_get(v_a_4569_, 0);
lean_inc_ref(v_config_4571_);
v___x_4572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4572_, 0, v_config_4571_);
return v___x_4572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg___boxed(lean_object* v_a_4573_, lean_object* v_a_4574_){
_start:
{
lean_object* v_res_4575_; 
v_res_4575_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4573_);
lean_dec_ref(v_a_4573_);
return v_res_4575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig(lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_){
_start:
{
lean_object* v___x_4581_; 
v___x_4581_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4576_);
return v___x_4581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___boxed(lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_){
_start:
{
lean_object* v_res_4587_; 
v_res_4587_ = l_Lean_Compiler_LCNF_getConfig(v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
lean_dec(v_a_4585_);
lean_dec_ref(v_a_4584_);
lean_dec(v_a_4583_);
lean_dec_ref(v_a_4582_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object* v_x_4588_, lean_object* v_s_4589_, uint8_t v_phase_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_){
_start:
{
lean_object* v___x_4594_; lean_object* v_options_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; 
v___x_4594_ = lean_st_mk_ref(v_s_4589_);
v_options_4595_ = lean_ctor_get(v_a_4591_, 2);
v___x_4596_ = l_Lean_Compiler_LCNF_toConfigOptions(v_options_4595_);
v___x_4597_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4597_, 0, v___x_4596_);
lean_ctor_set_uint8(v___x_4597_, sizeof(void*)*1, v_phase_4590_);
lean_inc(v_a_4592_);
lean_inc_ref(v_a_4591_);
lean_inc(v___x_4594_);
v___x_4598_ = lean_apply_5(v_x_4588_, v___x_4597_, v___x_4594_, v_a_4591_, v_a_4592_, lean_box(0));
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4607_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4601_ = v___x_4598_;
v_isShared_4602_ = v_isSharedCheck_4607_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_a_4599_);
lean_dec(v___x_4598_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4607_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v___x_4603_; lean_object* v___x_4605_; 
v___x_4603_ = lean_st_ref_get(v___x_4594_);
lean_dec(v___x_4594_);
lean_dec(v___x_4603_);
if (v_isShared_4602_ == 0)
{
v___x_4605_ = v___x_4601_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v_a_4599_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
else
{
lean_dec(v___x_4594_);
return v___x_4598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg___boxed(lean_object* v_x_4608_, lean_object* v_s_4609_, lean_object* v_phase_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_){
_start:
{
uint8_t v_phase_boxed_4614_; lean_object* v_res_4615_; 
v_phase_boxed_4614_ = lean_unbox(v_phase_4610_);
v_res_4615_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4608_, v_s_4609_, v_phase_boxed_4614_, v_a_4611_, v_a_4612_);
lean_dec(v_a_4612_);
lean_dec_ref(v_a_4611_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run(lean_object* v_00_u03b1_4616_, lean_object* v_x_4617_, lean_object* v_s_4618_, uint8_t v_phase_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_){
_start:
{
lean_object* v___x_4623_; 
v___x_4623_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4617_, v_s_4618_, v_phase_4619_, v_a_4620_, v_a_4621_);
return v___x_4623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___boxed(lean_object* v_00_u03b1_4624_, lean_object* v_x_4625_, lean_object* v_s_4626_, lean_object* v_phase_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_){
_start:
{
uint8_t v_phase_boxed_4631_; lean_object* v_res_4632_; 
v_phase_boxed_4631_ = lean_unbox(v_phase_4627_);
v_res_4632_ = l_Lean_Compiler_LCNF_CompilerM_run(v_00_u03b1_4624_, v_x_4625_, v_s_4626_, v_phase_boxed_4631_, v_a_4628_, v_a_4629_);
lean_dec(v_a_4629_);
lean_dec_ref(v_a_4628_);
return v_res_4632_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0(void){
_start:
{
lean_object* v___x_4633_; 
v___x_4633_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_4633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(lean_object* v_00_u03b1_4634_, lean_object* v_00_u03b2_4635_, lean_object* v_inst_4636_, lean_object* v_inst_4637_){
_start:
{
lean_object* v___x_4638_; 
v___x_4638_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(lean_object* v_00_u03b1_4639_, lean_object* v_00_u03b2_4640_, lean_object* v_inst_4641_, lean_object* v_inst_4642_){
_start:
{
lean_object* v_res_4643_; 
v_res_4643_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(v_00_u03b1_4639_, v_00_u03b2_4640_, v_inst_4641_, v_inst_4642_);
lean_dec_ref(v_inst_4642_);
lean_dec_ref(v_inst_4641_);
return v_res_4643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension(lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_){
_start:
{
lean_object* v___x_4648_; 
v___x_4648_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___boxed(lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_){
_start:
{
lean_object* v_res_4653_; 
v_res_4653_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension(v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_);
lean_dec_ref(v_a_4652_);
lean_dec_ref(v_a_4651_);
return v_res_4653_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4657_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2));
v___x_4658_ = lean_unsigned_to_nat(14u);
v___x_4659_ = lean_unsigned_to_nat(178u);
v___x_4660_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1));
v___x_4661_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0));
v___x_4662_ = l_mkPanicMessageWithDecl(v___x_4661_, v___x_4660_, v___x_4659_, v___x_4658_, v___x_4657_);
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(lean_object* v_inst_4663_, lean_object* v_inst_4664_, lean_object* v_snd_4665_, lean_object* v_inst_4666_, lean_object* v_s_4667_, lean_object* v_e_4668_){
_start:
{
lean_object* v_fst_4669_; lean_object* v_snd_4670_; lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4685_; 
v_fst_4669_ = lean_ctor_get(v_s_4667_, 0);
v_snd_4670_ = lean_ctor_get(v_s_4667_, 1);
v_isSharedCheck_4685_ = !lean_is_exclusive(v_s_4667_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4672_ = v_s_4667_;
v_isShared_4673_ = v_isSharedCheck_4685_;
goto v_resetjp_4671_;
}
else
{
lean_inc(v_snd_4670_);
lean_inc(v_fst_4669_);
lean_dec(v_s_4667_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4685_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
lean_object* v___x_4674_; lean_object* v___y_4676_; lean_object* v___x_4681_; 
lean_inc_n(v_e_4668_, 2);
v___x_4674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4674_, 0, v_e_4668_);
lean_ctor_set(v___x_4674_, 1, v_fst_4669_);
lean_inc_ref(v_inst_4664_);
lean_inc_ref(v_inst_4663_);
v___x_4681_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4663_, v_inst_4664_, v_snd_4665_, v_e_4668_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4682_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3);
v___x_4683_ = l_panic___redArg(v_inst_4666_, v___x_4682_);
v___y_4676_ = v___x_4683_;
goto v___jp_4675_;
}
else
{
lean_object* v_val_4684_; 
v_val_4684_ = lean_ctor_get(v___x_4681_, 0);
lean_inc(v_val_4684_);
lean_dec_ref_known(v___x_4681_, 1);
v___y_4676_ = v_val_4684_;
goto v___jp_4675_;
}
v___jp_4675_:
{
lean_object* v___x_4677_; lean_object* v___x_4679_; 
v___x_4677_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4663_, v_inst_4664_, v_snd_4670_, v_e_4668_, v___y_4676_);
if (v_isShared_4673_ == 0)
{
lean_ctor_set(v___x_4672_, 1, v___x_4677_);
lean_ctor_set(v___x_4672_, 0, v___x_4674_);
v___x_4679_ = v___x_4672_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v___x_4674_);
lean_ctor_set(v_reuseFailAlloc_4680_, 1, v___x_4677_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed(lean_object* v_inst_4686_, lean_object* v_inst_4687_, lean_object* v_snd_4688_, lean_object* v_inst_4689_, lean_object* v_s_4690_, lean_object* v_e_4691_){
_start:
{
lean_object* v_res_4692_; 
v_res_4692_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(v_inst_4686_, v_inst_4687_, v_snd_4688_, v_inst_4689_, v_s_4690_, v_e_4691_);
lean_dec(v_inst_4689_);
lean_dec(v_snd_4688_);
return v_res_4692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(lean_object* v_inst_4695_, lean_object* v_inst_4696_, lean_object* v_inst_4697_, lean_object* v_oldState_4698_, lean_object* v_newState_4699_, lean_object* v_x_4700_, lean_object* v_s_4701_){
_start:
{
lean_object* v_fst_4702_; lean_object* v_snd_4703_; lean_object* v_fst_4704_; lean_object* v___f_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v_newEntries_4710_; lean_object* v___x_4711_; 
v_fst_4702_ = lean_ctor_get(v_newState_4699_, 0);
lean_inc_n(v_fst_4702_, 2);
v_snd_4703_ = lean_ctor_get(v_newState_4699_, 1);
lean_inc(v_snd_4703_);
lean_dec_ref(v_newState_4699_);
v_fst_4704_ = lean_ctor_get(v_oldState_4698_, 0);
v___f_4705_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_4705_, 0, v_inst_4695_);
lean_closure_set(v___f_4705_, 1, v_inst_4696_);
lean_closure_set(v___f_4705_, 2, v_snd_4703_);
lean_closure_set(v___f_4705_, 3, v_inst_4697_);
v___x_4706_ = l_List_lengthTR___redArg(v_fst_4702_);
v___x_4707_ = l_List_lengthTR___redArg(v_fst_4704_);
v___x_4708_ = lean_nat_sub(v___x_4706_, v___x_4707_);
lean_dec(v___x_4707_);
lean_dec(v___x_4706_);
v___x_4709_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0));
v_newEntries_4710_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_fst_4702_, v_fst_4702_, v___x_4708_, v___x_4709_);
lean_dec(v_fst_4702_);
v___x_4711_ = l_List_foldl___redArg(v___f_4705_, v_s_4701_, v_newEntries_4710_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(lean_object* v_inst_4712_, lean_object* v_inst_4713_, lean_object* v_inst_4714_, lean_object* v_oldState_4715_, lean_object* v_newState_4716_, lean_object* v_x_4717_, lean_object* v_s_4718_){
_start:
{
lean_object* v_res_4719_; 
v_res_4719_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(v_inst_4712_, v_inst_4713_, v_inst_4714_, v_oldState_4715_, v_newState_4716_, v_x_4717_, v_s_4718_);
lean_dec(v_x_4717_);
lean_dec_ref(v_oldState_4715_);
return v_res_4719_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0(void){
_start:
{
lean_object* v___x_4720_; 
v___x_4720_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4720_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1(void){
_start:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; 
v___x_4721_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0);
v___x_4722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4722_, 0, v___x_4721_);
return v___x_4722_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2(void){
_start:
{
lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; 
v___x_4723_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1);
v___x_4724_ = lean_box(0);
v___x_4725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4725_, 0, v___x_4724_);
lean_ctor_set(v___x_4725_, 1, v___x_4723_);
return v___x_4725_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3(void){
_start:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4726_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2);
v___x_4727_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_4727_, 0, lean_box(0));
lean_closure_set(v___x_4727_, 1, lean_box(0));
lean_closure_set(v___x_4727_, 2, v___x_4726_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object* v_inst_4728_, lean_object* v_inst_4729_, lean_object* v_inst_4730_){
_start:
{
lean_object* v___f_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; 
v___f_4732_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4732_, 0, v_inst_4728_);
lean_closure_set(v___f_4732_, 1, v_inst_4729_);
lean_closure_set(v___f_4732_, 2, v_inst_4730_);
v___x_4733_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3);
v___x_4734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4734_, 0, v___f_4732_);
v___x_4735_ = lean_box(0);
v___x_4736_ = l_Lean_registerEnvExtension___redArg(v___x_4733_, v___x_4734_, v___x_4735_);
if (lean_obj_tag(v___x_4736_) == 0)
{
lean_object* v_a_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4744_; 
v_a_4737_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4744_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4739_ = v___x_4736_;
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_a_4737_);
lean_dec(v___x_4736_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4742_; 
if (v_isShared_4740_ == 0)
{
v___x_4742_ = v___x_4739_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v_a_4737_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
}
else
{
lean_object* v_a_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4752_; 
v_a_4745_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4747_ = v___x_4736_;
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_a_4745_);
lean_dec(v___x_4736_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4750_; 
if (v_isShared_4748_ == 0)
{
v___x_4750_ = v___x_4747_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_a_4745_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object* v_inst_4753_, lean_object* v_inst_4754_, lean_object* v_inst_4755_, lean_object* v_a_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4753_, v_inst_4754_, v_inst_4755_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object* v_00_u03b1_4758_, lean_object* v_00_u03b2_4759_, lean_object* v_inst_4760_, lean_object* v_inst_4761_, lean_object* v_inst_4762_){
_start:
{
lean_object* v___x_4764_; 
v___x_4764_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4760_, v_inst_4761_, v_inst_4762_);
return v___x_4764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object* v_00_u03b1_4765_, lean_object* v_00_u03b2_4766_, lean_object* v_inst_4767_, lean_object* v_inst_4768_, lean_object* v_inst_4769_, lean_object* v_a_4770_){
_start:
{
lean_object* v_res_4771_; 
v_res_4771_ = l_Lean_Compiler_LCNF_CacheExtension_register(v_00_u03b1_4765_, v_00_u03b2_4766_, v_inst_4767_, v_inst_4768_, v_inst_4769_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object* v_a_4772_, lean_object* v_inst_4773_, lean_object* v_inst_4774_, lean_object* v_b_4775_, lean_object* v_x_4776_){
_start:
{
lean_object* v_fst_4777_; lean_object* v_snd_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4787_; 
v_fst_4777_ = lean_ctor_get(v_x_4776_, 0);
v_snd_4778_ = lean_ctor_get(v_x_4776_, 1);
v_isSharedCheck_4787_ = !lean_is_exclusive(v_x_4776_);
if (v_isSharedCheck_4787_ == 0)
{
v___x_4780_ = v_x_4776_;
v_isShared_4781_ = v_isSharedCheck_4787_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_snd_4778_);
lean_inc(v_fst_4777_);
lean_dec(v_x_4776_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4787_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4785_; 
lean_inc(v_a_4772_);
v___x_4782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4782_, 0, v_a_4772_);
lean_ctor_set(v___x_4782_, 1, v_fst_4777_);
v___x_4783_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4773_, v_inst_4774_, v_snd_4778_, v_a_4772_, v_b_4775_);
if (v_isShared_4781_ == 0)
{
lean_ctor_set(v___x_4780_, 1, v___x_4783_);
lean_ctor_set(v___x_4780_, 0, v___x_4782_);
v___x_4785_ = v___x_4780_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4782_);
lean_ctor_set(v_reuseFailAlloc_4786_, 1, v___x_4783_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
return v___x_4785_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_4788_; 
v___x_4788_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4788_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_4789_; lean_object* v___x_4790_; 
v___x_4789_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0);
v___x_4790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4790_, 0, v___x_4789_);
return v___x_4790_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2(void){
_start:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___x_4791_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1);
v___x_4792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4792_, 0, v___x_4791_);
lean_ctor_set(v___x_4792_, 1, v___x_4791_);
return v___x_4792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object* v_inst_4793_, lean_object* v_inst_4794_, lean_object* v_ext_4795_, lean_object* v_a_4796_, lean_object* v_b_4797_, lean_object* v_a_4798_){
_start:
{
lean_object* v___x_4800_; lean_object* v_env_4801_; lean_object* v_nextMacroScope_4802_; lean_object* v_ngen_4803_; lean_object* v_auxDeclNGen_4804_; lean_object* v_traceState_4805_; lean_object* v_messages_4806_; lean_object* v_infoState_4807_; lean_object* v_snapshotTasks_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4823_; 
v___x_4800_ = lean_st_ref_take(v_a_4798_);
v_env_4801_ = lean_ctor_get(v___x_4800_, 0);
v_nextMacroScope_4802_ = lean_ctor_get(v___x_4800_, 1);
v_ngen_4803_ = lean_ctor_get(v___x_4800_, 2);
v_auxDeclNGen_4804_ = lean_ctor_get(v___x_4800_, 3);
v_traceState_4805_ = lean_ctor_get(v___x_4800_, 4);
v_messages_4806_ = lean_ctor_get(v___x_4800_, 6);
v_infoState_4807_ = lean_ctor_get(v___x_4800_, 7);
v_snapshotTasks_4808_ = lean_ctor_get(v___x_4800_, 8);
v_isSharedCheck_4823_ = !lean_is_exclusive(v___x_4800_);
if (v_isSharedCheck_4823_ == 0)
{
lean_object* v_unused_4824_; 
v_unused_4824_ = lean_ctor_get(v___x_4800_, 5);
lean_dec(v_unused_4824_);
v___x_4810_ = v___x_4800_;
v_isShared_4811_ = v_isSharedCheck_4823_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_snapshotTasks_4808_);
lean_inc(v_infoState_4807_);
lean_inc(v_messages_4806_);
lean_inc(v_traceState_4805_);
lean_inc(v_auxDeclNGen_4804_);
lean_inc(v_ngen_4803_);
lean_inc(v_nextMacroScope_4802_);
lean_inc(v_env_4801_);
lean_dec(v___x_4800_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4823_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
lean_object* v_asyncMode_4812_; lean_object* v___f_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4818_; 
v_asyncMode_4812_ = lean_ctor_get(v_ext_4795_, 2);
lean_inc(v_asyncMode_4812_);
v___f_4813_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4813_, 0, v_a_4796_);
lean_closure_set(v___f_4813_, 1, v_inst_4793_);
lean_closure_set(v___f_4813_, 2, v_inst_4794_);
lean_closure_set(v___f_4813_, 3, v_b_4797_);
v___x_4814_ = lean_box(0);
v___x_4815_ = l_Lean_EnvExtension_modifyState___redArg(v_ext_4795_, v_env_4801_, v___f_4813_, v_asyncMode_4812_, v___x_4814_);
lean_dec(v_asyncMode_4812_);
v___x_4816_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2);
if (v_isShared_4811_ == 0)
{
lean_ctor_set(v___x_4810_, 5, v___x_4816_);
lean_ctor_set(v___x_4810_, 0, v___x_4815_);
v___x_4818_ = v___x_4810_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v___x_4815_);
lean_ctor_set(v_reuseFailAlloc_4822_, 1, v_nextMacroScope_4802_);
lean_ctor_set(v_reuseFailAlloc_4822_, 2, v_ngen_4803_);
lean_ctor_set(v_reuseFailAlloc_4822_, 3, v_auxDeclNGen_4804_);
lean_ctor_set(v_reuseFailAlloc_4822_, 4, v_traceState_4805_);
lean_ctor_set(v_reuseFailAlloc_4822_, 5, v___x_4816_);
lean_ctor_set(v_reuseFailAlloc_4822_, 6, v_messages_4806_);
lean_ctor_set(v_reuseFailAlloc_4822_, 7, v_infoState_4807_);
lean_ctor_set(v_reuseFailAlloc_4822_, 8, v_snapshotTasks_4808_);
v___x_4818_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
v___x_4819_ = lean_st_ref_put(v_a_4798_, v___x_4818_);
v___x_4820_ = lean_box(0);
v___x_4821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4820_);
return v___x_4821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object* v_inst_4825_, lean_object* v_inst_4826_, lean_object* v_ext_4827_, lean_object* v_a_4828_, lean_object* v_b_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_){
_start:
{
lean_object* v_res_4832_; 
v_res_4832_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4825_, v_inst_4826_, v_ext_4827_, v_a_4828_, v_b_4829_, v_a_4830_);
lean_dec(v_a_4830_);
return v_res_4832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object* v_00_u03b1_4833_, lean_object* v_00_u03b2_4834_, lean_object* v_inst_4835_, lean_object* v_inst_4836_, lean_object* v_inst_4837_, lean_object* v_ext_4838_, lean_object* v_a_4839_, lean_object* v_b_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_){
_start:
{
lean_object* v___x_4844_; 
v___x_4844_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4835_, v_inst_4836_, v_ext_4838_, v_a_4839_, v_b_4840_, v_a_4842_);
return v___x_4844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object* v_00_u03b1_4845_, lean_object* v_00_u03b2_4846_, lean_object* v_inst_4847_, lean_object* v_inst_4848_, lean_object* v_inst_4849_, lean_object* v_ext_4850_, lean_object* v_a_4851_, lean_object* v_b_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_){
_start:
{
lean_object* v_res_4856_; 
v_res_4856_ = l_Lean_Compiler_LCNF_CacheExtension_insert(v_00_u03b1_4845_, v_00_u03b2_4846_, v_inst_4847_, v_inst_4848_, v_inst_4849_, v_ext_4850_, v_a_4851_, v_b_4852_, v_a_4853_, v_a_4854_);
lean_dec(v_a_4854_);
lean_dec_ref(v_a_4853_);
lean_dec(v_inst_4849_);
return v_res_4856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(lean_object* v_inst_4857_, lean_object* v_inst_4858_, lean_object* v_ext_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_){
_start:
{
lean_object* v___x_4863_; lean_object* v_env_4864_; lean_object* v_asyncMode_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v_snd_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4863_ = lean_st_ref_get(v_a_4861_);
v_env_4864_ = lean_ctor_get(v___x_4863_, 0);
lean_inc_ref(v_env_4864_);
lean_dec(v___x_4863_);
v_asyncMode_4865_ = lean_ctor_get(v_ext_4859_, 2);
v___x_4866_ = lean_box(0);
v___x_4867_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v_inst_4857_, v_inst_4858_);
v___x_4868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4868_, 0, v___x_4866_);
lean_ctor_set(v___x_4868_, 1, v___x_4867_);
v___x_4869_ = lean_box(0);
v___x_4870_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4868_, v_ext_4859_, v_env_4864_, v_asyncMode_4865_, v___x_4869_);
lean_dec_ref_known(v___x_4868_, 2);
v_snd_4871_ = lean_ctor_get(v___x_4870_, 1);
lean_inc(v_snd_4871_);
lean_dec(v___x_4870_);
v___x_4872_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4857_, v_inst_4858_, v_snd_4871_, v_a_4860_);
lean_dec(v_snd_4871_);
v___x_4873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4872_);
return v___x_4873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(lean_object* v_inst_4874_, lean_object* v_inst_4875_, lean_object* v_ext_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_){
_start:
{
lean_object* v_res_4880_; 
v_res_4880_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4874_, v_inst_4875_, v_ext_4876_, v_a_4877_, v_a_4878_);
lean_dec(v_a_4878_);
lean_dec_ref(v_ext_4876_);
return v_res_4880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_object* v_00_u03b1_4881_, lean_object* v_00_u03b2_4882_, lean_object* v_inst_4883_, lean_object* v_inst_4884_, lean_object* v_inst_4885_, lean_object* v_ext_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_){
_start:
{
lean_object* v___x_4891_; 
v___x_4891_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4883_, v_inst_4884_, v_ext_4886_, v_a_4887_, v_a_4889_);
return v___x_4891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(lean_object* v_00_u03b1_4892_, lean_object* v_00_u03b2_4893_, lean_object* v_inst_4894_, lean_object* v_inst_4895_, lean_object* v_inst_4896_, lean_object* v_ext_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_){
_start:
{
lean_object* v_res_4902_; 
v_res_4902_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f(v_00_u03b1_4892_, v_00_u03b2_4893_, v_inst_4894_, v_inst_4895_, v_inst_4896_, v_ext_4897_, v_a_4898_, v_a_4899_, v_a_4900_);
lean_dec(v_a_4900_);
lean_dec_ref(v_a_4899_);
lean_dec_ref(v_ext_4897_);
lean_dec(v_inst_4896_);
return v_res_4902_;
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
